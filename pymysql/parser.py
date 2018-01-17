from __future__ import print_function
from ._compat import (PY2, range_type, text_type, str_type,
JYTHON, IRONPYTHON)

import errno
from functools import partial
from collections import namedtuple
import operator
import io
import struct
import sys

from .constants import FIELD_TYPE, SERVER_STATUS
from . import converters
from .cursors import Cursor
from .optionfile import Parser
from .util import byte2int, int2byte
from . import err

try:
    import ssl
    SSL_ENABLED = True
except ImportError:
    ssl = None
    SSL_ENABLED = False

try:
    import getpass
    DEFAULT_USER = getpass.getuser()
    del getpass
except (ImportError, KeyError):
    # KeyError occurs when there's no entry in OS database for a current user.
    DEFAULT_USER = None

DEBUG = False

if sys.version_info.major == 3:
    if sys.version_info.minor < 6:
        # See http://bugs.python.org/issue24870
        _surrogateescape_table = [chr(i) if i < 0x80 else chr(i + 0xdc00) for i in range(256)]

        def _fast_surrogateescape(s):
            return s.decode('latin1').translate(_surrogateescape_table)
    else:
        def _fast_surrogateescape(s):
            return s.decode('ascii', 'surrogateescape')

# socket.makefile() in Python 2 is not usable because very inefficient and
# bad behavior about timeout.
# XXX: ._socketio doesn't work under IronPython.
if PY2 and not IRONPYTHON:
    # read method of file-like returned by sock.makefile() is very slow.
    # So we copy io-based one from Python 3.
    from ._socketio import SocketIO

    def _makefile(sock, mode):
        return io.BufferedReader(SocketIO(sock, mode))
else:
    # socket.makefile in Python 3 is nice.
    def _makefile(sock, mode):
        return sock.makefile(mode)

MBLENGTH = {
        8:1,
        33:3,
        88:2,
        91:2
        }

TEXT_TYPES = set((
    FIELD_TYPE.BIT,
    FIELD_TYPE.BLOB,
    FIELD_TYPE.LONG_BLOB,
    FIELD_TYPE.MEDIUM_BLOB,
    FIELD_TYPE.STRING,
    FIELD_TYPE.TINY_BLOB,
    FIELD_TYPE.VAR_STRING,
    FIELD_TYPE.VARCHAR,
    FIELD_TYPE.GEOMETRY))

FIELD = namedtuple('Field', ['type', 'size', 'view'])

NULL_COLUMN = 251
UNSIGNED_CHAR_COLUMN = 251
UNSIGNED_SHORT_COLUMN = 252
UNSIGNED_INT24_COLUMN = 253
UNSIGNED_INT64_COLUMN = 254

DEFAULT_CHARSET = 'latin1'

MAX_PACKET_LEN = 2**24-1

class InvalidPacketError(Exception):
    pass

def dump_packet(data): # pragma: no cover
    def is_ascii(data):
        if 65 <= byte2int(data) <= 122:
            if isinstance(data, int):
                return chr(data)
            return data
        return '.'

    try:
        print("packet length:", len(data))
        for i in range(1, 6):
            f = sys._getframe(i)
            print("call[%d]: %s (line %d)" % (i, f.f_code.co_name, f.f_lineno))
        print("-" * 66)
    except ValueError:
        pass
    dump_data = [data[i:i+16] for i in range_type(0, min(len(data), 256), 16)]
    for d in dump_data:
        print(' '.join(map(lambda x: "{:02X}".format(byte2int(x)), d)) +
              '   ' * (16 - len(d)) + ' ' * 2 +
              ''.join(map(lambda x: "{}".format(is_ascii(x)), d)))
    print("-" * 66)
    print()


if PY2:
    def read_uint8(data, offset=0):
        return ord(data[offset])
else:
    def read_uint8(data, offset=0):
        return data[offset]

read_uint16 = partial(struct.unpack_from, '<H')
read_uint24 = partial(struct.unpack_from, '<HB')
read_uint32 = partial(struct.unpack_from, '<I')
read_uint64 = partial(struct.unpack_from, '<Q')

def read(data, nbytes, offset=0):
    if nbytes is None:
        result = data[offset:]
    else:
        result = data[offset:offset+nbytes]

    if len(result) == nbytes:
        return result
    else:
        error = ('Result length not requested length:\n'
                 'Expected=%s.  Actual=%s.  Position: %s.  Data Length: %s'
                 % (nbytes, len(result), offset, len(data)))
        if DEBUG:
            print(error)
        raise AssertionError(error)

def read_length_encoded_integer(data, offset=0):
    """
    Read a length encoded integer.
    Args:
        data:
        offset:

    Returns:
        (size, int):
    """
    col = read_uint8(data, offset=offset)
    if col == NULL_COLUMN:
        return 1, None

    if col < UNSIGNED_CHAR_COLUMN:
        return 1, col
    elif col == UNSIGNED_SHORT_COLUMN:
        return 3, read_uint16(data, offset=offset)
    elif col == UNSIGNED_INT24_COLUMN:
        return 4, read_uint24(data, offset=offset)
    elif col == UNSIGNED_INT64_COLUMN:
        return 9, read_uint64(data, offset=offset)

def read_length_coded_string(data, offset=0):
    size, length = read_length_encoded_integer(data, offset=offset)
    if length:
        return size + length, read(data, length, offset=offset+size)

def read_string(data, offset=0):
    end = data.find(b'\0', offset)
    if end >= 0:
        return data[offset:end]

def is_ok_packet(packet):
    # https://dev.mysql.com/doc/internals/en/packet-OK_Packet.html
    return read_uint8(packet.payload) == 0 and packet.size >= 7

def is_eof_packet(packet):
    # http://dev.mysql.com/doc/internals/en/generic-response-packets.html#packet-EOF_Packet
    # Caution: \xFE may be LengthEncodedInteger.
    # If \xFE is LengthEncodedInteger header, 8bytes followed.
    return read_uint8(packet.payload) == 254 and packet.size < 9

def is_auth_switch_request(packet):
    # http://dev.mysql.com/doc/internals/en/connection-phase-packets.html#packet-Protocol::AuthSwitchRequest
    return read_uint8(packet.payload) == 254

def is_load_local(packet):
    return read_uint8(packet.payload) == 251

def is_resultset_packet(packet):
    return 1 <= read_uint8(packet.payload) <= 250

def check_error(packet):
    if read_uint8(packet.payload) == 255:
        errno = read_uint16(packet.payload, offset=1)
        if DEBUG: print("errno = ", errno)
        err.raise_mysql_exception(packet.payload)

def parse_ok_packet(packet):
    if not is_ok_packet(packet):
        raise InvalidPacketError()

    pos = 1
    data = packet.payload

    size, affected_rows = read_length_encoded_integer(data, offset=pos)
    pos += size

    size, insert_id = read_length_encoded_integer(data, offset=pos)
    pos += size

    server_status, warning_count = struct.unpack_from('<HH', data, offset=pos)
    pos += 4

    # Read the rest of the packet
    message = read(data, None, offset=pos)
    #pos += len(message)

    return {'affected_rows': affected_rows,
            'insert_id': insert_id,
            'server_status': server_status,
            'warning_count': warning_count,
            'message': message,
            'has_next': server_status & SERVER_STATUS.SERVER_MORE_RESULTS_EXISTS}

def parse_eof_packet(packet):
    if not is_eof_packet(packet):
        raise InvalidPacketError()

    pos = 1
    data = packet.payload

    warning_count, server_status = struct.unpack_from('<hh', data, offset=pos)
    pos += 4

    if DEBUG: print("server_status=", server_status)
    return {'warning_count': warning_count,
            'server_status': server_status,
            'has_next': server_status & SERVER_STATUS.SERVER_MORE_RESULTS_EXISTS}

def parse_load_local_packet(packet):
    pos = 1
    data = packet.payload

    filename = read(data, None, offset=pos)
    if DEBUG: print("filename=", filename)

    return {'filename': filename}

def parse_field_descriptor_packet(packet, encoding=DEFAULT_CHARSET):
    pos = 0
    data = packet.payload

    size, catalog = read_length_encoded_integer(data, offset=pos)
    pos += size

    size, db = read_length_coded_string(data, offset=pos)
    pos += size

    size, table_name = read_length_coded_string(data, offset=pos)
    pos += size

    size, org_table = read_length_coded_string(data, offset=pos)
    pos += size

    size, name = read_length_coded_string(data, offset=pos)
    pos += size

    size, org_name = read_length_coded_string(data, offset=pos)
    pos += size

    pos += 1
    charsetnr, length, type_code, flags, scale = struct.unpack_from('<HIBHB', data, offset=pos)

    result =  {'catalog': catalog,
            'db': db,
            'table_name': table_name.decode(encoding),
            'org_table': org_table.decode(encoding),
            'name': name.decode(encoding),
            'org_name': org_name.decode(encoding),
            'charsetnr': charsetnr,
            'length': length,
            'type_code': type_code,
            'flags': flags,
            'scale': scale}

    column_length = length
    if type_code == FIELD_TYPE.VAR_STRING:
        column_length //=  MBLENGTH.get(charsetnr, 1)

    result['description'] = (result['name'],
                             type_code,
                             None,
                             column_length,
                             column_length,
                             scale,
                             flags % 2 == 0)
    return result


def parse_result_stream(stream, encoding=DEFAULT_CHARSET, use_unicode=False,
                        converters=None):
    """
    Parse stream of packets in a result stream.
    Args:
        stream:
        encoding:

    Returns:
        (iterator):
            0: Field descriptions
            1: Groups of rows (each packet)
    """
    first = next(stream)
    _, field_count = read_length_encoded_integer(first.payload)

    # the next field_count packets are field descriptor packets.
    fields = [None] * field_count
    f_encodings = [None] * field_count
    f_converters = [None] * field_count
    for i in range_type(field_count):
        p = next(stream)
        fields[i] = field = parse_field_descriptor_packet(p, encoding=encoding)
        field_type = field['field_type']
        if use_unicode:
            if field['charsetnr'] == 63 and field_type in TEXT_TYPES:
                # TEXTs with charset=binary means BINARY types
                encoding = None
            elif field_type == FIELD_TYPE.JSON or field_type in TEXT_TYPES:
                # When SELECT from JSON column: charset = binary
                # When SELECT CAST(... AS JSON): charset = connection encoding
                # This behavior is different from TEXT / BLOB.
                # We should decode result by connection encoding regardless charsetnr.
                # See https://github.com/PyMySQL/PyMySQL/issues/488
                encoding = encoding  # SELECT CAST(... AS JSON)
            else:
                encoding = 'ascii'
        else:
            encoding = None
        f_encodings[i] = encoding

        converter = converters.get(field_type)
        if converter is converters.through:
            converter = None
        field['converter'] = converter
        f_converters[i] = converter
        if DEBUG: print("DEBUG: field={}, converter={}".format(field, converter))

    # Expect an EOF packet
    if not is_eof_packet(next(stream)):
        raise InvalidPacketError

    # Yield the descriptions
    yield tuple(fields)

    # Rest of the packets contain rows (1 packet == 1 row)
    # Parsing of packets
    #rows = []
    curr_packet = next(stream)
    while not is_eof_packet(curr_packet):
        position = 0
        row = [None] * field_count
        i = 0
        while position < curr_packet.size:
            size, data = read_length_coded_string(curr_packet.payload, offset=position)
            position += size

            if data is not None:
                if f_encodings[i]:
                    data = data.decode(f_encodings[i])
                if DEBUG: print("DEBUG: DATA = ", data)
                if f_converters[i]:
                    data = f_converters[i](data)
            row[i] = data
            i += 1
        assert len(row) == field_count
        yield tuple(row)
        curr_packet = next(stream)
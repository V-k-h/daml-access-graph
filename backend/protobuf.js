// backend/protobuf.js
//
// A minimal protobuf WIRE FORMAT reader. No schema compiler, no dependencies:
// the caller supplies field numbers from the .proto it cares about (see
// lf2-schema.js) and reads them off the decoded field list.
//
// Only what a DALF needs is implemented: varint, 64-bit, length-delimited, and
// 32-bit wire types, plus packed repeated scalars. Groups (wire types 3 and 4)
// are deprecated and never appear in Daml-LF, so hitting one is an error rather
// than something silently skipped.

export const WIRE = { VARINT: 0, I64: 1, BYTES: 2, I32: 5 };

/**
 * Decode one protobuf message into a Map from field number to an array of
 * values. Varints arrive as numbers, length-delimited fields as Buffers.
 *
 * Returning ALL values per field number (rather than the last) is what makes
 * `repeated` fields work.
 *
 * @param {Buffer|Uint8Array} buf
 * @returns {Map<number, Array<number|Buffer>>}
 */
export function decodeMessage(buf) {
  /** @type {Map<number, Array<number|Buffer>>} */
  const out = new Map();
  let i = 0;
  const n = buf.length;

  const push = (fn, v) => {
    const list = out.get(fn);
    if (list) list.push(v);
    else out.set(fn, [v]);
  };

  while (i < n) {
    const [key, next] = readVarint(buf, i);
    i = next;
    const fieldNumber = key >>> 3;
    const wireType = key & 7;
    if (fieldNumber === 0) {
      throw new Error('protobuf: field number 0 is invalid');
    }

    switch (wireType) {
      case WIRE.VARINT: {
        const [v, j] = readVarint(buf, i);
        i = j;
        push(fieldNumber, v);
        break;
      }
      case WIRE.I64:
        i += 8;
        break;
      case WIRE.BYTES: {
        const [len, j] = readVarint(buf, i);
        i = j;
        if (i + len > n) throw new Error('protobuf: length-delimited field runs past end of buffer');
        push(fieldNumber, buf.subarray(i, i + len));
        i += len;
        break;
      }
      case WIRE.I32:
        i += 4;
        break;
      default:
        throw new Error(`protobuf: unsupported wire type ${wireType} (groups are not supported)`);
    }
    if (i > n) throw new Error('protobuf: truncated message');
  }
  return out;
}

/** Read a base-128 varint. Returns [value, nextIndex]. */
export function readVarint(buf, start) {
  let result = 0;
  let shift = 0;
  let i = start;
  for (;;) {
    if (i >= buf.length) throw new Error('protobuf: truncated varint');
    const byte = buf[i++];
    // Number is exact to 2^53; Daml-LF indices and enum tags are far below that.
    result += (byte & 0x7f) * Math.pow(2, shift);
    if ((byte & 0x80) === 0) break;
    shift += 7;
    if (shift > 63) throw new Error('protobuf: varint too long');
  }
  return [result, i];
}

/**
 * Read a `repeated` scalar field that may be either packed (one
 * length-delimited blob of varints) or unpacked (one varint per occurrence).
 * proto3 defaults to packed, but both encodings are legal, so both are read.
 *
 * @param {Map<number, Array<number|Buffer>>} msg
 * @param {number} fieldNumber
 * @returns {number[]}
 */
export function readPackedVarints(msg, fieldNumber) {
  const values = msg.get(fieldNumber) || [];
  const out = [];
  for (const v of values) {
    if (typeof v === 'number') {
      out.push(v);
      continue;
    }
    let i = 0;
    while (i < v.length) {
      const [x, j] = readVarint(v, i);
      i = j;
      out.push(x);
    }
  }
  return out;
}

/** First value of a field, or undefined. */
export const one = (msg, fieldNumber) => {
  const v = msg.get(fieldNumber);
  return v ? v[0] : undefined;
};

/** All values of a field as an array (empty when absent). */
export const many = (msg, fieldNumber) => msg.get(fieldNumber) || [];

/**
 * First value of a field decoded as a submessage, or undefined.
 * @returns {Map<number, Array<number|Buffer>>|undefined}
 */
export function sub(msg, fieldNumber) {
  const v = one(msg, fieldNumber);
  return v instanceof Uint8Array ? decodeMessage(v) : undefined;
}

/** All values of a field decoded as submessages. */
export function subs(msg, fieldNumber) {
  return many(msg, fieldNumber)
    .filter((v) => v instanceof Uint8Array)
    .map((v) => decodeMessage(v));
}

/**
 * A varint field read as an integer, with a default.
 * proto3 elides fields equal to their default, so an absent index legitimately
 * means 0 - which for Daml-LF interned tables is a real entry, not "missing".
 */
export function int(msg, fieldNumber, dflt = 0) {
  const v = one(msg, fieldNumber);
  return typeof v === 'number' ? v : dflt;
}

/** A bool field (proto3 elides false). */
export const bool = (msg, fieldNumber) => int(msg, fieldNumber, 0) !== 0;

/** Whether a field is present at all, regardless of value. */
export const has = (msg, fieldNumber) => msg.has(fieldNumber);

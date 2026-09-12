// backend/zip.js
//
// A minimal, dependency-free ZIP reader, enough to read a DAR.
//
// A DAR is a zip containing META-INF/MANIFEST.MF plus one .dalf per package.
// The previous DAR helper shelled out to `unzip`, which made the backend
// depend on an external binary and fail opaquely where it is missing. Node has
// raw-deflate in `node:zlib`, so reading the archive directly is both fewer
// moving parts and portable.
//
// Central-directory based (not a streaming scan), so entries are found by name
// without inflating the whole archive.

import { inflateRawSync } from 'node:zlib';

const EOCD_SIG = 0x06054b50;
const EOCD64_LOCATOR_SIG = 0x07064b50;
const CEN_SIG = 0x02014b50;
const LOC_SIG = 0x04034b50;

const STORED = 0;
const DEFLATED = 8;

/**
 * @typedef {Object} ZipEntry
 * @property {string} name
 * @property {number} method
 * @property {number} compressedSize
 * @property {number} uncompressedSize
 * @property {number} localHeaderOffset
 */

/**
 * Parse the central directory of a zip.
 * @param {Buffer} buf
 * @returns {ZipEntry[]}
 */
export function listEntries(buf) {
  const eocd = findEocd(buf);
  if (eocd === -1) throw new Error('not a zip archive: end-of-central-directory record not found');

  let count = buf.readUInt16LE(eocd + 10);
  let cenOffset = buf.readUInt32LE(eocd + 16);

  // Zip64: the 32-bit fields saturate and the real values live in the zip64
  // EOCD record. DARs are small, but a saturated field must not be read as a
  // literal offset.
  if (cenOffset === 0xffffffff || count === 0xffff) {
    const loc = findBackwards(buf, EOCD64_LOCATOR_SIG, eocd);
    if (loc === -1) throw new Error('zip64 archive without a zip64 EOCD locator');
    const zip64Eocd = Number(buf.readBigUInt64LE(loc + 8));
    count = Number(buf.readBigUInt64LE(zip64Eocd + 32));
    cenOffset = Number(buf.readBigUInt64LE(zip64Eocd + 48));
  }

  /** @type {ZipEntry[]} */
  const entries = [];
  let p = cenOffset;
  for (let i = 0; i < count; i++) {
    if (buf.readUInt32LE(p) !== CEN_SIG) {
      throw new Error(`corrupt zip: bad central directory signature at entry ${i}`);
    }
    const method = buf.readUInt16LE(p + 10);
    const compressedSize = buf.readUInt32LE(p + 20);
    const uncompressedSize = buf.readUInt32LE(p + 24);
    const nameLen = buf.readUInt16LE(p + 28);
    const extraLen = buf.readUInt16LE(p + 30);
    const commentLen = buf.readUInt16LE(p + 32);
    const localHeaderOffset = buf.readUInt32LE(p + 42);
    const name = buf.toString('utf8', p + 46, p + 46 + nameLen);
    entries.push({ name, method, compressedSize, uncompressedSize, localHeaderOffset });
    p += 46 + nameLen + extraLen + commentLen;
  }
  return entries;
}

/**
 * Read and decompress one entry.
 * @param {Buffer} buf
 * @param {ZipEntry} entry
 * @returns {Buffer}
 */
export function readEntry(buf, entry) {
  const p = entry.localHeaderOffset;
  if (buf.readUInt32LE(p) !== LOC_SIG) {
    throw new Error(`corrupt zip: bad local header for ${entry.name}`);
  }
  const nameLen = buf.readUInt16LE(p + 26);
  const extraLen = buf.readUInt16LE(p + 28);
  const start = p + 30 + nameLen + extraLen;
  const raw = buf.subarray(start, start + entry.compressedSize);

  if (entry.method === STORED) return Buffer.from(raw);
  if (entry.method === DEFLATED) return inflateRawSync(raw);
  throw new Error(`unsupported zip compression method ${entry.method} for ${entry.name}`);
}

/** Read an entry by exact name, or undefined. */
export function readByName(buf, entries, name) {
  const e = entries.find((x) => x.name === name);
  return e ? readEntry(buf, e) : undefined;
}

function findEocd(buf) {
  // The EOCD sits at the end, after an optional comment of up to 64KB.
  const from = Math.max(0, buf.length - (0xffff + 22));
  return findBackwards(buf, EOCD_SIG, buf.length - 22, from);
}

function findBackwards(buf, sig, fromIndex, stopAt = 0) {
  for (let i = Math.min(fromIndex, buf.length - 4); i >= stopAt; i--) {
    if (buf.readUInt32LE(i) === sig) return i;
  }
  return -1;
}

/**
 * Parse a jar-style MANIFEST.MF, joining its continuation lines.
 *
 * Manifest values wrap at 72 bytes with a single leading space on the
 * continuation, so `Main-Dalf:` arrives split across several lines and must be
 * rejoined before it names a real entry.
 *
 * @param {string} text
 * @returns {Record<string,string>}
 */
export function parseManifest(text) {
  /** @type {Record<string,string>} */
  const out = {};
  let key = null;
  let value = '';
  const flush = () => {
    if (key) out[key] = value.trim();
    key = null;
    value = '';
  };
  for (const rawLine of text.split(/\r?\n/)) {
    if (rawLine.startsWith(' ')) {
      value += rawLine.slice(1);
      continue;
    }
    flush();
    const m = rawLine.match(/^([A-Za-z0-9][A-Za-z0-9_-]*):\s?(.*)$/);
    if (m) {
      key = m[1];
      value = m[2];
    }
  }
  flush();
  return out;
}

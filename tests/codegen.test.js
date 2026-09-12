// tests/codegen.test.js
//
//   node --test
//
// The generated schema, and the wire-format reader it feeds.
//
// Three things are checked here, in increasing strength:
//
//   1. DRIFT. Regenerating from the vendored protos must reproduce the
//      committed `lf2-schema.generated.js` byte for byte. If someone updates a
//      proto without running `npm run codegen`, or hand-edits the generated
//      file, this fails.
//   2. GROUNDING. The field numbers that are easy to get wrong are asserted to
//      come out of the proto with the values the proto actually states. This
//      is what makes "generated" more than a claim.
//   3. ROUND-TRIP. For every message in the real schema, encoding a random
//      instance and decoding it returns the same field numbers and values.
//      That exercises `backend/protobuf.js` against the actual shapes the
//      Daml-LF schema uses, not a toy example.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

import { parseProto, fieldNumbers } from '../tools/proto-parse.js';
import { render, buildDescriptor, SOURCES } from '../tools/codegen.js';
import { decodeMessage, readPackedVarints, one, many, int } from '../backend/protobuf.js';
import * as S from '../backend/lf2-schema.js';
import { MESSAGES, message } from '../backend/lf2-schema.generated.js';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');

// ---------------------------------------------------------------------------
// 1. drift
// ---------------------------------------------------------------------------

test('generated schema is in sync with the vendored protos', () => {
  const committed = readFileSync(join(root, 'backend/lf2-schema.generated.js'), 'utf8');
  assert.equal(
    render(),
    committed,
    'backend/lf2-schema.generated.js is stale or hand-edited. Run: npm run codegen'
  );
});

test('every vendored proto parses', () => {
  for (const src of SOURCES) {
    const schema = parseProto(readFileSync(join(root, src.file), 'utf8'));
    assert.equal(schema.syntax, 'proto3', `${src.file} should be proto3`);
    assert.ok(schema.messages.size > 0, `${src.file} should declare messages`);
  }
});

// ---------------------------------------------------------------------------
// 2. grounding
// ---------------------------------------------------------------------------

test('the field numbers that are easy to confuse come straight from the proto', () => {
  // Read the proto here, independently of the generated file, and compare.
  const lf2 = parseProto(readFileSync(join(root, 'backend/proto/daml_lf2.proto'), 'utf8'));
  const numbersOf = (qn) => fieldNumbers(lf2.messages.get(qn));

  // The trap: three near-identical messages, three different slots.
  assert.equal(numbersOf('Expr.RecProj').fieldInternedStr, 4);
  assert.equal(numbersOf('Expr.RecUpd').fieldInternedStr, 2);
  assert.equal(numbersOf('FieldWithExpr').fieldInternedStr, 3);

  // And the generated module agrees with the proto it was generated from.
  assert.equal(S.RecProj.fieldInternedStr, 4);
  assert.equal(S.RecUpd.fieldInternedStr, 2);
  assert.equal(S.FieldWithExpr.fieldInternedStr, 3);

  // Reading RecProj with RecUpd's number is exactly the silent failure this
  // whole arrangement exists to prevent.
  assert.notEqual(
    S.RecProj.fieldInternedStr,
    S.RecUpd.fieldInternedStr,
    'if these ever coincide, the guard below is meaningless'
  );
});

test('LF 2 numbering is asserted, not assumed from LF 1', () => {
  // LF 1 put `Module.name_interned_dname` at 8 and templates at 7; LF 2 moved
  // them. A decoder built on LF 1 numbering decodes an LF 2 package into
  // nonsense, so pin the LF 2 values.
  assert.equal(S.Module.nameInternedDname, 1);
  assert.equal(S.Module.dataTypes, 4);
  assert.equal(S.Module.values, 5);
  assert.equal(S.Module.templates, 6);
  assert.equal(S.Module.interfaces, 8);

  assert.equal(S.DefInterface.methods, 3);
  assert.equal(S.DefInterface.choices, 5);
  assert.equal(S.TemplateChoice.nameInternedStr, 2);
  assert.equal(S.TemplateChoice.consuming, 3);
  assert.equal(S.TemplateChoice.controllers, 4);
});

test('every alias the decoder uses resolves to a real message', () => {
  // The alias layer is the only hand-written surface left, and a wrong alias
  // throws at import time via message(). Assert the set is non-empty and that
  // each alias carries field numbers.
  const aliases = [
    'Archive', 'ArchivePayload', 'Package', 'PackageMetadata', 'PackageImports',
    'InternedDottedName', 'Module', 'DefValue', 'NameWithType', 'ValueId',
    'DefTemplate', 'DefKey', 'Implements', 'InterfaceInstanceBody',
    'InterfaceInstanceMethod', 'DefInterface', 'InterfaceMethod', 'TemplateChoice',
    'TypeConId', 'ModuleId', 'SelfOrImportedPackageId', 'Type', 'TypeCon', 'Expr',
    'RecProj', 'RecUpd', 'RecCon', 'StructProj', 'Cons', 'FieldWithExpr',
    'VarWithType', 'Block', 'Binding', 'Update',
  ];
  for (const name of aliases) {
    assert.ok(S[name], `alias ${name} should be exported`);
    assert.ok(Object.keys(S[name]).length > 0, `alias ${name} should have field numbers`);
  }
});

test('message() fails loudly on an unknown name', () => {
  assert.throws(() => message('Expr.NoSuchThing'), /no such message/);
});

test('UPDATE_OPS reads its field numbers from the schema', () => {
  const ops = S.UPDATE_OPS;
  const exercise = ops[S.Update.exercise];
  assert.equal(exercise.kind, 'exercise');
  // Update.Exercise puts the choice name at 6, ExerciseByKey at 2. Easy to mix
  // up by hand; both come from the generated schema here.
  assert.equal(exercise.choiceField, message('Update.Exercise').choiceInternedStr);
  assert.equal(exercise.choiceField, 6);
  assert.equal(ops[S.Update.exerciseByKey].choiceField, 2);

  // interface-targeted cases name their target differently
  assert.equal(ops[S.Update.exerciseInterface].byInterface, true);
  assert.equal(
    ops[S.Update.exerciseInterface].targetField,
    message('Update.ExerciseInterface').interface
  );
  // fetchByKey and lookupByKey share the RetrieveByKey shape but are distinct ops
  assert.equal(ops[S.Update.fetchByKey].kind, 'fetchByKey');
  assert.equal(ops[S.Update.lookupByKey].kind, 'lookupByKey');
});

test('the proto parser refuses constructs it does not implement', () => {
  assert.throws(
    () => parseProto('syntax = "proto3";\nservice Foo { }\n'),
    /only the subset/,
    'a service definition must be refused, not skipped'
  );
  assert.throws(() => parseProto('syntax = "proto2";\n'), /expected proto3/);
});

test('the proto parser records oneof membership and repeated-ness', () => {
  const schema = parseProto(`syntax = "proto3";
message M {
  repeated int32 xs = 1;
  oneof pick {
    string a = 2;
    bytes b = 3;
  }
  int32 plain = 4;
}
`);
  const m = schema.messages.get('M');
  const by = Object.fromEntries(m.fields.map((f) => [f.name, f]));
  assert.equal(by.xs.repeated, true);
  assert.equal(by.plain.repeated, false);
  assert.equal(by.a.oneof, 'pick');
  assert.equal(by.b.oneof, 'pick');
  assert.equal(by.plain.oneof, null);
  assert.deepEqual(fieldNumbers(m), { xs: 1, a: 2, b: 3, plain: 4 });
});

// ---------------------------------------------------------------------------
// 3. round-trip
// ---------------------------------------------------------------------------

/** Minimal protobuf encoder, driven by a field descriptor. Test-only. */
function encodeVarint(n) {
  const bytes = [];
  let v = n;
  do {
    let b = v & 0x7f;
    v = Math.floor(v / 128);
    if (v > 0) b |= 0x80;
    bytes.push(b);
  } while (v > 0);
  return Buffer.from(bytes);
}

const VARINT_TYPES = new Set([
  'int32', 'int64', 'uint32', 'uint64', 'bool', 'sint32', 'sint64',
]);

/**
 * Encode one field. Returns null for field types this helper does not model
 * (floats and fixed-width ints, which the Daml-LF schema barely uses and the
 * decoder deliberately skips).
 *
 * `enumTypes` matters: an enum-typed field is a VARINT on the wire even though
 * its type name is capitalized like a message. Treating it as a submessage was
 * a bug in this helper, caught by `Archive.hash_function`.
 */
function encodeField(field, value, enumTypes = new Set()) {
  const key = (wt) => encodeVarint(field.number * 8 + wt);
  if (VARINT_TYPES.has(field.type) || enumTypes.has(field.type)) {
    return Buffer.concat([key(0), encodeVarint(value)]);
  }
  if (field.type === 'string' || field.type === 'bytes') {
    const buf = Buffer.from(String(value), 'utf8');
    return Buffer.concat([key(2), encodeVarint(buf.length), buf]);
  }
  if (/^[A-Z]/.test(field.type.split('.')[0])) {
    // a submessage: encode an opaque but non-empty body
    const body = Buffer.concat([encodeVarint(1 * 8 + 0), encodeVarint(value)]);
    return Buffer.concat([key(2), encodeVarint(body.length), body]);
  }
  return null;
}

/** A deterministic pseudo-random generator, so failures reproduce. */
function makeRng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s * 1664525 + 1013904223) >>> 0;
    return s / 0x100000000;
  };
}

test('round-trip: every message in the real schema encodes and decodes back', () => {
  const { messages, enums } = buildDescriptor();
  // Enum types are varints on the wire; collect both their simple and
  // qualified spellings, since a field can reference either.
  const enumTypes = new Set();
  for (const qn of enums.keys()) {
    enumTypes.add(qn);
    enumTypes.add(qn.slice(qn.lastIndexOf('.') + 1));
  }
  const rng = makeRng(20260911);
  let checked = 0;
  let fieldsChecked = 0;

  for (const [qn, m] of messages) {
    const parts = [];
    /** @type {Array<{field: Object, value: number|string}>} */
    const expected = [];

    for (const field of m.fields) {
      const isVarint = VARINT_TYPES.has(field.type) || enumTypes.has(field.type);
      const isBytes = field.type === 'string' || field.type === 'bytes';
      // A submessage body is written as `inner field 1 = <varint>`, so its
      // value has to be numeric too. Generating a string here produced a
      // silently corrupt varint, which is how `Unit`-typed fields caught this.
      const value = isBytes ? `v${Math.floor(rng() * 1000)}` : Math.floor(rng() * 100000);
      const encoded = encodeField(field, value, enumTypes);
      if (!encoded) continue;
      parts.push(encoded);
      expected.push({ field, value, isVarint, isBytes });
    }
    if (expected.length === 0) continue;

    const decoded = decodeMessage(Buffer.concat(parts));

    for (const { field, value, isVarint, isBytes } of expected) {
      const got = one(decoded, field.number);
      assert.notEqual(got, undefined, `${qn}.${field.name} (field ${field.number}) should decode`);
      if (isVarint) {
        assert.equal(got, value, `${qn}.${field.name} varint value`);
      } else if (isBytes) {
        assert.equal(Buffer.from(got).toString('utf8'), value, `${qn}.${field.name} bytes value`);
      } else {
        // submessage: its inner field 1 carries the value we encoded
        assert.equal(int(decodeMessage(got), 1), value, `${qn}.${field.name} submessage`);
      }
      fieldsChecked++;
    }
    checked++;
  }

  // Guard against the test silently becoming a no-op.
  assert.ok(checked > 90, `expected to round-trip most of the schema, did ${checked}`);
  assert.ok(fieldsChecked > 300, `expected many fields checked, did ${fieldsChecked}`);
});

test('round-trip: repeated fields preserve every value and their order', () => {
  // `Package.interned_strings` is the table every name in a DALF resolves
  // through, so losing or reordering entries would corrupt every name.
  const field = { number: S.Package.internedStrings, type: 'string' };
  const values = ['Tok', 'Token', 'issuer', 'owner', ''];
  const buf = Buffer.concat(values.map((v) => encodeField(field, v)));

  const decoded = decodeMessage(buf);
  const back = many(decoded, field.number).map((b) => Buffer.from(b).toString('utf8'));
  assert.deepEqual(back, values);
});

test('round-trip: packed repeated varints survive, as interned dotted names', () => {
  // InternedDottedName.segments_interned_str is packed in practice; the
  // decoder has to accept packed and unpacked alike.
  const segments = [0, 1, 300, 5];
  const packed = Buffer.concat(segments.map(encodeVarint));
  const buf = Buffer.concat([
    encodeVarint(S.InternedDottedName.segmentsInternedStr * 8 + 2),
    encodeVarint(packed.length),
    packed,
  ]);
  const decoded = decodeMessage(buf);
  assert.deepEqual(readPackedVarints(decoded, S.InternedDottedName.segmentsInternedStr), segments);
});

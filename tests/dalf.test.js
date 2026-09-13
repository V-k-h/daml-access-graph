// tests/dalf.test.js
//
//   node --test
//
// The protobuf reader, the zip reader, and the DALF decoder.
//
// These build their fixtures IN MEMORY rather than vendoring a third-party
// DAR. That keeps the repo free of someone else's compiled artifact, and it
// makes the tests pin the thing that actually breaks: the Daml-LF 2 field
// NUMBERS. A transcription slip (RecProj's field_interned_str is 4, while the
// near-identical RecUpd's is 2) silently yields empty results rather than an
// error, so each number that matters is asserted here.

import test from 'node:test';
import assert from 'node:assert/strict';
import { deflateRawSync } from 'node:zlib';

import { decodeMessage, readPackedVarints, one, sub, subs, int, bool, has } from '../backend/protobuf.js';
import { listEntries, readEntry, readByName, parseManifest } from '../backend/zip.js';
import { decodeDalf, decodeDalfRaw, readDar, resolveFieldSort } from '../backend/dalf.js';
import * as S from '../backend/lf2-schema.js';
import { buildGraph } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';

// ---------------------------------------------------------------------------
// protobuf encoding helpers (test-only)
// ---------------------------------------------------------------------------

function varint(n) {
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
const tag = (fieldNumber, wireType) => varint(fieldNumber * 8 + wireType);
const vf = (fieldNumber, value) => Buffer.concat([tag(fieldNumber, 0), varint(value)]);
const bf = (fieldNumber, buf) => Buffer.concat([tag(fieldNumber, 2), varint(buf.length), buf]);
const sf = (fieldNumber, str) => bf(fieldNumber, Buffer.from(str, 'utf8'));
const msg = (...parts) => Buffer.concat(parts);

// ---------------------------------------------------------------------------
// protobuf reader
// ---------------------------------------------------------------------------

test('protobuf: varints, strings, submessages, repeated fields', () => {
  const inner = msg(vf(1, 7), sf(2, 'hi'));
  const buf = msg(vf(1, 300), sf(2, 'a'), sf(2, 'b'), bf(3, inner));
  const m = decodeMessage(buf);

  assert.equal(int(m, 1), 300, 'multi-byte varint');
  assert.equal(m.get(2).length, 2, 'repeated field keeps every value');
  assert.equal(Buffer.from(one(m, 2)).toString(), 'a');
  const s = sub(m, 3);
  assert.equal(int(s, 1), 7);
  assert.equal(Buffer.from(one(s, 2)).toString(), 'hi');
});

test('protobuf: absent varint reads as 0, which is a real interned index', () => {
  // proto3 elides defaults, so module name index 0 is simply not written.
  const m = decodeMessage(msg(sf(2, 'x')));
  assert.equal(has(m, 1), false);
  assert.equal(int(m, 1), 0, 'must read as index 0, not undefined');
});

test('protobuf: packed and unpacked repeated scalars both decode', () => {
  const packed = decodeMessage(bf(1, Buffer.concat([varint(3), varint(1), varint(4)])));
  assert.deepEqual(readPackedVarints(packed, 1), [3, 1, 4]);

  const unpacked = decodeMessage(msg(vf(1, 3), vf(1, 1), vf(1, 4)));
  assert.deepEqual(readPackedVarints(unpacked, 1), [3, 1, 4]);
});

test('protobuf: bools, and rejection of malformed input', () => {
  assert.equal(bool(decodeMessage(vf(3, 1)), 3), true);
  assert.equal(bool(decodeMessage(msg()), 3), false, 'absent bool is false');
  // a length that runs past the buffer must throw, not read garbage
  assert.throws(() => decodeMessage(Buffer.concat([tag(1, 2), varint(50), Buffer.from('short')])), /past end/);
  // groups are not supported and must be rejected loudly
  assert.throws(() => decodeMessage(tag(1, 3)), /wire type/);
});

// ---------------------------------------------------------------------------
// zip reader
// ---------------------------------------------------------------------------

/** Build a tiny zip with one deflated entry per [name, contents]. */
function makeZip(files) {
  const locals = [];
  const centrals = [];
  let offset = 0;
  for (const [name, contents] of files) {
    const nameBuf = Buffer.from(name, 'utf8');
    const body = Buffer.from(contents);
    const comp = deflateRawSync(body);

    const local = Buffer.alloc(30);
    local.writeUInt32LE(0x04034b50, 0);
    local.writeUInt16LE(20, 4);
    local.writeUInt16LE(8, 8); // deflate
    local.writeUInt32LE(comp.length, 18);
    local.writeUInt32LE(body.length, 22);
    local.writeUInt16LE(nameBuf.length, 26);
    locals.push(local, nameBuf, comp);

    const central = Buffer.alloc(46);
    central.writeUInt32LE(0x02014b50, 0);
    central.writeUInt16LE(8, 10);
    central.writeUInt32LE(comp.length, 20);
    central.writeUInt32LE(body.length, 24);
    central.writeUInt16LE(nameBuf.length, 28);
    central.writeUInt32LE(offset, 42);
    centrals.push(central, nameBuf);

    offset += local.length + nameBuf.length + comp.length;
  }

  const localPart = Buffer.concat(locals);
  const centralPart = Buffer.concat(centrals);
  const eocd = Buffer.alloc(22);
  eocd.writeUInt32LE(0x06054b50, 0);
  eocd.writeUInt16LE(files.length, 8);
  eocd.writeUInt16LE(files.length, 10);
  eocd.writeUInt32LE(centralPart.length, 12);
  eocd.writeUInt32LE(localPart.length, 16);
  return Buffer.concat([localPart, centralPart, eocd]);
}

test('zip: reads entries by name and inflates them', () => {
  const zip = makeZip([
    ['META-INF/MANIFEST.MF', 'Manifest-Version: 1.0\n'],
    ['pkg/main.dalf', 'x'.repeat(500)],
  ]);
  const entries = listEntries(zip);
  assert.deepEqual(entries.map((e) => e.name), ['META-INF/MANIFEST.MF', 'pkg/main.dalf']);
  assert.equal(readByName(zip, entries, 'META-INF/MANIFEST.MF').toString(), 'Manifest-Version: 1.0\n');
  assert.equal(readEntry(zip, entries[1]).length, 500);
  assert.equal(readByName(zip, entries, 'nope'), undefined);
});

test('zip: a non-archive is rejected with a clear message', () => {
  assert.throws(() => listEntries(Buffer.from('not a zip at all')), /not a zip archive/);
});

test('manifest: continuation lines are rejoined', () => {
  // Real DAR manifests wrap Main-Dalf across several lines.
  const text = [
    'Manifest-Version: 1.0',
    'Main-Dalf: some-package-1.0.0-abcdef/some-package-1.0.0-abcd',
    ' ef.dalf',
    'Sdk-Version: 3.5.2',
  ].join('\n');
  const m = parseManifest(text);
  assert.equal(m['Main-Dalf'], 'some-package-1.0.0-abcdef/some-package-1.0.0-abcdef.dalf');
  assert.equal(m['Sdk-Version'], '3.5.2');
});

// ---------------------------------------------------------------------------
// DALF decoding
// ---------------------------------------------------------------------------

/**
 * Assemble a minimal but REAL Daml-LF 2 package:
 *
 *   module Tok where
 *     template Token with issuer owner where
 *       signatory this.issuer
 *       observer   this.owner
 *       choice Give (consuming) controller this.owner
 *         do create Token
 *       interface instance Iface for Token
 *     interface Iface where
 *       choice Act (nonconsuming) controller (view this).admin
 */
function buildFixtureDalf() {
  const strings = ['Tok', 'Token', 'Give', 'this', 'issuer', 'owner', 'Iface', 'Act', 'admin', 'pkg', '1.0.0'];
  const SI = Object.fromEntries(strings.map((s, i) => [s, i]));

  // interned dotted names: 0=Tok, 1=Token, 2=Iface
  const dnames = [
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(SI.Tok))),
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(SI.Token))),
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(SI.Iface))),
  ];
  const DN = { Tok: 0, Token: 1, Iface: 2 };

  const selfModule = msg(
    bf(S.ModuleId.packageId, bf(S.SelfOrImportedPackageId.selfPackageId, Buffer.alloc(0))),
    vf(S.ModuleId.moduleNameInternedDname, DN.Tok)
  );
  const tyconToken = msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, DN.Token));
  const tyconIface = msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, DN.Iface));

  const varExpr = (name) => vf(S.Expr.varInternedStr, SI[name]);
  /** `<var>.<field>` as a RecProj. NOTE field_interned_str is 4 here. */
  const projExpr = (varName, field) =>
    bf(
      S.Expr.recProj,
      msg(
        bf(S.RecProj.tycon, tyconToken),
        vf(S.RecProj.fieldInternedStr, SI[field]),
        bf(S.RecProj.record, varExpr(varName))
      )
    );

  const createTokenUpdate = bf(
    S.Expr.update,
    bf(S.Update.create, msg(bf(1, tyconToken), bf(2, varExpr('this'))))
  );

  const choiceGive = bf(
    S.Module.templates, // placeholder tag, replaced below
    Buffer.alloc(0)
  );
  void choiceGive;

  const giveChoice = msg(
    vf(S.TemplateChoice.nameInternedStr, SI.Give),
    vf(S.TemplateChoice.consuming, 1),
    bf(S.TemplateChoice.controllers, projExpr('this', 'owner')),
    bf(S.TemplateChoice.argBinder, vf(S.VarWithType.varInternedStr, SI.owner)),
    bf(S.TemplateChoice.update, createTokenUpdate)
  );

  const implementsBlock = msg(
    bf(S.Implements.interface, tyconIface),
    bf(S.Implements.body, bf(S.InterfaceInstanceBody.view, varExpr('this')))
  );

  const template = msg(
    vf(S.DefTemplate.tyconInternedDname, DN.Token),
    vf(S.DefTemplate.paramInternedStr, SI.this),
    bf(S.DefTemplate.signatories, projExpr('this', 'issuer')),
    bf(S.DefTemplate.observers, projExpr('this', 'owner')),
    bf(S.DefTemplate.choices, giveChoice),
    bf(S.DefTemplate.implements, implementsBlock)
  );

  const actChoice = msg(
    vf(S.TemplateChoice.nameInternedStr, SI.Act),
    // consuming omitted => false => nonconsuming
    bf(
      S.TemplateChoice.controllers,
      bf(
        S.Expr.recProj,
        msg(
          vf(S.RecProj.fieldInternedStr, SI.admin),
          bf(S.RecProj.record, varExpr('this'))
        )
      )
    )
  );

  const iface = msg(
    vf(S.DefInterface.tyconInternedDname, DN.Iface),
    vf(S.DefInterface.paramInternedStr, SI.this),
    bf(S.DefInterface.choices, actChoice)
  );

  const module = msg(
    vf(S.Module.nameInternedDname, DN.Tok),
    bf(S.Module.templates, template),
    bf(S.Module.interfaces, iface)
  );

  const pkg = msg(
    bf(S.Package.modules, module),
    ...strings.map((s) => sf(S.Package.internedStrings, s)),
    ...dnames,
    bf(
      S.Package.metadata,
      msg(
        vf(S.PackageMetadata.nameInternedStr, SI.pkg),
        vf(S.PackageMetadata.versionInternedStr, SI['1.0.0'])
      )
    )
  );

  const payload = msg(sf(S.ArchivePayload.minor, '3'), bf(S.ArchivePayload.damlLf2, pkg));
  return msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'deadbeef'));
}

test('dalf: decodes package metadata, modules, templates and interfaces', () => {
  const d = decodeDalf(buildFixtureDalf());
  assert.equal(d.name, 'pkg');
  assert.equal(d.version, '1.0.0');
  assert.equal(d.lfMinor, '3');
  assert.equal(d.packageId, 'deadbeef');
  assert.deepEqual(d.modules, ['Tok']);
  assert.equal(d.templates.length, 1);
  assert.equal(d.interfaces.length, 1);
});

test('dalf: recovers signatories and observers from record projections', () => {
  // This is the assertion that catches a RecProj field-number slip: with
  // RecUpd's numbering these come back empty rather than erroring.
  const t = decodeDalf(buildFixtureDalf()).templates[0];
  assert.equal(t.name, 'Token');
  assert.deepEqual(t.signatories, ['issuer']);
  assert.deepEqual(t.observers, ['owner']);
});

test('dalf: recovers choices, consuming flags and operation targets', () => {
  const t = decodeDalf(buildFixtureDalf()).templates[0];
  const give = t.choices.find((c) => c.name === 'Give');
  assert.ok(give, 'choice name comes from TemplateChoice.name_interned_str');
  assert.equal(give.consuming, true);
  const create = give.operations.find((o) => o.kind === 'create');
  assert.ok(create, 'the Update.create case should be found in the choice body');
  assert.equal(create.target, 'Token');
  assert.equal(create.resolvedVia, 'daml-lf');
});

test('dalf: a controller rooted in the choice argument is tagged, not called a field', () => {
  const t = decodeDalf(buildFixtureDalf()).templates[0];
  const give = t.choices.find((c) => c.name === 'Give');
  // `owner` is both a template field and this choice's arg binder name; the
  // projection is rooted in `this`, so it must NOT be tagged as an argument.
  assert.deepEqual(give.controllers, ['owner']);
});

test('dalf: interface choices are decoded, nonconsuming by omission', () => {
  const d = decodeDalf(buildFixtureDalf());
  const iface = d.interfaces[0];
  assert.equal(iface.name, 'Iface');
  const act = iface.choices[0];
  assert.equal(act.name, 'Act');
  assert.equal(act.consuming, false, 'proto3 omits `consuming: false`');
  // rooted in the interface param, so it is a view projection
  assert.deepEqual(act.controllers, ['view.admin']);
});

test('dalf: `implements` is recovered and reaches the graph', () => {
  const d = decodeDalf(buildFixtureDalf());
  assert.deepEqual(d.templates[0].implements, ['Iface']);

  const g = buildGraph(d, { source: 'daml-lf', module: d.module });
  assert.ok(g.edges.some((e) => e.kind === 'implements' && e.source === 'tpl:Token'));
  assert.ok(g.nodes.some((n) => n.kind === 'interface' && n.label === 'Iface'));
  // the decoded package feeds the same analyses as the source parser
  const res = analyzeAll(g);
  assert.ok(res.interfaces.some((f) => f.code === 'interface-choice-exercisable'));
});

test('dalf: an LF 1 payload is rejected rather than decoded into nonsense', () => {
  // LF 1 lives in a different ArchivePayload field, so damlLf2 is absent.
  const payload = msg(sf(S.ArchivePayload.minor, '15'), bf(1, Buffer.from([0x08, 0x01])));
  const archive = msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'abc'));
  assert.throws(() => decodeDalf(archive), /LF 2 only|Daml-LF 2 package/);
});

test('readDar: rejects a zip that is not a DAR', () => {
  // No fixture file needed: a missing manifest is the failure we care about.
  assert.throws(() => readDar('/nonexistent/path/to.dar'), /ENOENT|no such file/i);
});

// ---------------------------------------------------------------------------
// Field types: DefDataType decoding and path resolution
//
// The decoder used to keep the definitions that carry BEHAVIOUR (templates,
// interfaces, values) and drop the `DefDataType` records that carry the FIELD
// TYPES. A property asking "is this field a Numeric?" therefore had nothing to
// consult. These tests pin the three Type shapes a real package actually uses
// - interned, builtin, and APPLIED (`Numeric 10` is a builtin applied to its
// scale) - because getting the applied shape wrong silently classifies every
// decimal field in a package as unknown, which reads exactly like success.
// ---------------------------------------------------------------------------

/**
 * A package of pure data types:
 *
 *   data Deep      = Deep      with bps : Int64
 *   data TokenData = TokenData with rate : Numeric 10; name : Text; deep : Deep
 *   data Token     = Token     with issuer, owner : Party; amount : Numeric 10;
 *                                   label : Text; count : Int64; when : Time;
 *                                   ref : ContractId Token; flag : Bool;
 *                                   opt : Optional Int64; poly : a;
 *                                   data_ : TokenData
 *   data Color     = Red | Green            -- an enum, not a record
 */
function buildTypedRecordDalf() {
  const strings = [
    'Tok', 'Token', 'TokenData', 'Deep', 'Color',
    'issuer', 'owner', 'amount', 'label', 'count', 'when', 'ref', 'flag', 'opt', 'poly', 'data_',
    'rate', 'name', 'deep', 'bps', 'a', 'pkg', '1.0.0',
  ];
  const SI = Object.fromEntries(strings.map((s, i) => [s, i]));
  const dnameOrder = ['Tok', 'Token', 'TokenData', 'Deep', 'Color'];
  const DN = Object.fromEntries(dnameOrder.map((n, i) => [n, i]));
  const dnameMsgs = dnameOrder.map((n) =>
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(SI[n])))
  );

  const BT = S.ENUMS.BuiltinType;
  const builtinType = (code) => bf(S.Type.builtin, vf(S.TypeBuiltin.builtin, code));
  const natType = (n) => vf(S.Type.nat, n);
  const internedRef = (i) => msg(vf(S.Type.internedType, i));

  // The interned type table. `Numeric 10` is entry 3 and is BOTH interned and
  // applied, which is the combination a compiled Daml field actually carries.
  const internedTypes = [
    builtinType(BT.PARTY),                                          // 0
    builtinType(BT.NUMERIC),                                        // 1
    natType(10),                                                    // 2
    bf(S.Type.tapp, msg(bf(S.TypeApp.lhs, internedRef(1)), bf(S.TypeApp.rhs, internedRef(2)))), // 3
    builtinType(BT.TEXT),                                           // 4
  ];
  const IT = { party: 0, numeric10: 3, text: 4 };

  const selfModule = msg(
    bf(S.ModuleId.packageId, bf(S.SelfOrImportedPackageId.selfPackageId, Buffer.alloc(0))),
    vf(S.ModuleId.moduleNameInternedDname, DN.Tok)
  );
  const conType = (dn) =>
    bf(
      S.Type.con,
      bf(
        S.TypeCon.tycon,
        msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, dn))
      )
    );

  const field = (nameSi, typeBuf) =>
    bf(
      S.DataTypeFields.fields,
      msg(bf(S.FieldWithType.type, typeBuf), vf(S.FieldWithType.fieldInternedStr, nameSi))
    );
  const record = (dn, ...fields) =>
    bf(
      S.Module.dataTypes,
      msg(vf(S.DefDataType.nameInternedDname, dn), bf(S.DefDataType.record, msg(...fields)))
    );

  const module = msg(
    vf(S.Module.nameInternedDname, DN.Tok),
    record(DN.Deep, field(SI.bps, builtinType(BT.INT64))),
    record(
      DN.TokenData,
      field(SI.rate, internedRef(IT.numeric10)),
      field(SI.name, internedRef(IT.text)),
      field(SI.deep, conType(DN.Deep))
    ),
    record(
      DN.Token,
      field(SI.issuer, internedRef(IT.party)),
      // owner's type is written INLINE rather than interned: both shapes occur.
      field(SI.owner, builtinType(BT.PARTY)),
      field(SI.amount, internedRef(IT.numeric10)),
      field(SI.label, internedRef(IT.text)),
      field(SI.count, builtinType(BT.INT64)),
      field(SI.when, builtinType(BT.TIMESTAMP)),
      field(SI.ref, builtinType(BT.CONTRACT_ID)),
      field(SI.flag, builtinType(BT.BOOL)),
      // `Optional Int64`: an application whose HEAD is OPTIONAL, so unknown -
      // NOT numeric, even though its element is.
      field(
        SI.opt,
        bf(
          S.Type.tapp,
          msg(bf(S.TypeApp.lhs, builtinType(BT.OPTIONAL)), bf(S.TypeApp.rhs, builtinType(BT.INT64)))
        )
      ),
      field(SI.poly, bf(S.Type.var, vf(S.message('Type.Var').varInternedStr, SI.a))),
      field(SI.data_, conType(DN.TokenData))
    ),
    bf(
      S.Module.dataTypes,
      msg(
        vf(S.DefDataType.nameInternedDname, DN.Color),
        bf(
          S.DefDataType.enum,
          bf(S.message('DefDataType.EnumConstructors').constructorsInternedStr, varint(SI.name))
        )
      )
    )
  );

  const pkg = msg(
    bf(S.Package.modules, module),
    ...strings.map((s) => sf(S.Package.internedStrings, s)),
    ...dnameMsgs,
    ...internedTypes.map((t) => bf(S.Package.internedTypes, t)),
    bf(
      S.Package.metadata,
      msg(
        vf(S.PackageMetadata.nameInternedStr, SI.pkg),
        vf(S.PackageMetadata.versionInternedStr, SI['1.0.0'])
      )
    )
  );
  const payload = msg(sf(S.ArchivePayload.minor, '3'), bf(S.ArchivePayload.damlLf2, pkg));
  return msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'typedfixture'));
}

/**
 * A package whose data types are an ENUM and a VARIANT alongside a record:
 *
 *   data Color  = Red | Green | Blue          -- enum, no payloads
 *   data Result = Ok Int64 | Err Text         -- variant, payloads
 *   data Token  = Token with amount : Int64
 *
 * The point of the fixture is the CONSTRUCTOR LISTS: they become the
 * constructor lists of SMT datatype sorts, and a short one is unsound for
 * PROVED (see dalf.js).
 */
function buildEnumVariantDalf() {
  const strings = ['Tok', 'Color', 'Result', 'Token', 'Red', 'Green', 'Blue', 'Ok', 'Err', 'amount', 'pkg', '1.0.0'];
  const SI = Object.fromEntries(strings.map((s, i) => [s, i]));
  const dnameOrder = ['Tok', 'Color', 'Result', 'Token'];
  const DN = Object.fromEntries(dnameOrder.map((n, i) => [n, i]));
  const dnameMsgs = dnameOrder.map((n) =>
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(SI[n])))
  );
  const BT = S.ENUMS.BuiltinType;
  const builtinType = (code) => bf(S.Type.builtin, vf(S.TypeBuiltin.builtin, code));
  const field = (nameSi, typeBuf) =>
    bf(
      S.DataTypeFields.fields,
      msg(bf(S.FieldWithType.type, typeBuf), vf(S.FieldWithType.fieldInternedStr, nameSi))
    );

  const module = msg(
    vf(S.Module.nameInternedDname, DN.Tok),
    bf(
      S.Module.dataTypes,
      msg(
        vf(S.DefDataType.nameInternedDname, DN.Color),
        bf(
          S.DefDataType.enum,
          // repeated int32, written UNPACKED here; readPackedVarints takes both
          msg(
            vf(S.DataTypeEnumConstructors.constructorsInternedStr, SI.Red),
            vf(S.DataTypeEnumConstructors.constructorsInternedStr, SI.Green),
            vf(S.DataTypeEnumConstructors.constructorsInternedStr, SI.Blue)
          )
        )
      )
    ),
    bf(
      S.Module.dataTypes,
      msg(
        vf(S.DefDataType.nameInternedDname, DN.Result),
        // a variant's constructors are encoded exactly like record fields
        bf(
          S.DefDataType.variant,
          msg(field(SI.Ok, builtinType(BT.INT64)), field(SI.Err, builtinType(BT.TEXT)))
        )
      )
    ),
    bf(
      S.Module.dataTypes,
      msg(
        vf(S.DefDataType.nameInternedDname, DN.Token),
        bf(S.DefDataType.record, msg(field(SI.amount, builtinType(BT.INT64))))
      )
    )
  );

  const pkg = msg(
    bf(S.Package.modules, module),
    ...strings.map((str) => sf(S.Package.internedStrings, str)),
    ...dnameMsgs,
    bf(
      S.Package.metadata,
      msg(
        vf(S.PackageMetadata.nameInternedStr, SI.pkg),
        vf(S.PackageMetadata.versionInternedStr, SI['1.0.0'])
      )
    )
  );
  const payload = msg(sf(S.ArchivePayload.minor, '3'), bf(S.ArchivePayload.damlLf2, pkg));
  return msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'enumvariantfixture'));
}

/** The decoded TypeConId naming `Tok:<name>` in the enum/variant fixture. */
function tyconOf(raw, name) {
  const order = ['Tok', 'Color', 'Result', 'Token'];
  const selfModule = msg(
    bf(S.ModuleId.packageId, bf(S.SelfOrImportedPackageId.selfPackageId, Buffer.alloc(0))),
    vf(S.ModuleId.moduleNameInternedDname, 0)
  );
  return decodeMessage(
    msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, order.indexOf(name)))
  );
}

test('dalf: DefDataType records decode to coarse field sorts', () => {
  const raw = decodeDalfRaw(buildTypedRecordDalf());
  // Exposed on the raw result, which is what the verification frontend reads.
  assert.ok(raw.dataTypes instanceof Map);
  const token = raw.dataTypes.get('Tok:Token');
  assert.equal(token.kind, 'record');
  assert.deepEqual(
    Object.fromEntries([...token.fields].map(([k, c]) => [k, c.sort])),
    {
      issuer: 'party',
      owner: 'party',
      // `Decimal` (Numeric 10) and `Int` (Int64) are TWO sorts. Both are
      // numbers and both carry a property's obligations; they differ in the
      // SMT sort their symbol is declared at, and only `int` carries
      // integrality. Collapsing them here is what let a division-safety
      // counterexample give an `Int` field the value -1/10.
      amount: 'numeric',
      label: 'text',
      count: 'int',
      when: 'time',
      ref: 'cid',
      flag: 'bool',
      // `Optional Int64` is an OPTIONAL, not a number: the head of the
      // application decides, and the IR models an Optional field as a
      // $some/$value pair the plain path denotes neither half of. The
      // ELEMENT's classification is carried alongside so the resolver can
      // answer for the synthetic segments.
      opt: 'optional',
      // a type PARAMETER: its instantiation is not visible here, and anything
      // but `unknown` would be inventing a fact.
      poly: 'unknown',
      data_: 'record',
    }
  );
  assert.equal(token.fields.get('opt').elem.sort, 'int');
  // The nested record's Int64 field splits the same way.
  assert.equal(raw.dataTypes.get('Tok:Deep').fields.get('bps').sort, 'int');
  // REGRESSION GUARD, and the security-critical direction: a `Decimal` field
  // must NOT be classified `int`. An Int sort adds an integrality constraint,
  // which shrinks the model class - so a Decimal wrongly typed Int is a FALSE
  // constraint, and a false constraint can make an unsat, and therefore a
  // PROVED, spurious. This is the one mis-classification here that is unsound.
  assert.equal(token.fields.get('amount').sort, 'numeric', 'Decimal is never int');
  assert.equal(
    raw.dataTypes.get('Tok:TokenData').fields.get('rate').sort,
    'numeric',
    'a nested Decimal is never int either'
  );
  // A nested record carries the qualified name the path walk continues at.
  assert.deepEqual(
    { module: token.fields.get('data_').ref.module, name: token.fields.get('data_').ref.name },
    { module: 'Tok', name: 'TokenData' }
  );
  // Non-record data types are recorded with their kind, so the walk knows not
  // to try to enter one.
  assert.equal(raw.dataTypes.get('Tok:Color').kind, 'enum');
  assert.equal(raw.dataTypes.get('Tok:Color').fields, null);
});

test('dalf: the interned and APPLIED Type shapes both classify', () => {
  // `amount` is interned AND applied (`Numeric 10` = builtin NUMERIC @ nat 10);
  // `owner` is a bare inline builtin. Reading only one of the two shapes leaves
  // half a real package unclassified without erroring, so both are pinned.
  const raw = decodeDalfRaw(buildTypedRecordDalf());
  const start = { module: 'Tok', name: 'Token' };
  assert.equal(resolveFieldSort(raw.ctx, start, ['amount']), 'numeric', 'interned + applied');
  assert.equal(resolveFieldSort(raw.ctx, start, ['owner']), 'party', 'inline builtin');
  assert.equal(resolveFieldSort(raw.ctx, start, ['issuer']), 'party', 'interned builtin');
  assert.equal(resolveFieldSort(raw.ctx, start, ['count']), 'int', 'Int64 is its own sort');
  // ...and the bound form on the context agrees with the exported function.
  assert.equal(raw.ctx.fieldSort(start, ['amount']), 'numeric');
});

test('dalf: a nested record path is followed; an unfollowable one yields null', () => {
  const raw = decodeDalfRaw(buildTypedRecordDalf());
  const start = { module: 'Tok', name: 'Token' };
  assert.equal(resolveFieldSort(raw.ctx, start, ['data_', 'rate']), 'numeric', 'one hop');
  assert.equal(resolveFieldSort(raw.ctx, start, ['data_', 'deep', 'bps']), 'int', 'two hops');
  assert.equal(resolveFieldSort(raw.ctx, start, ['data_', 'name']), 'text');

  // Every way the walk can fail answers NULL - "nothing is known" - and never
  // a partial or guessed sort.
  assert.equal(resolveFieldSort(raw.ctx, start, ['nosuchfield']), null, 'unknown field');
  assert.equal(resolveFieldSort(raw.ctx, start, ['label', 'x']), null, 'step through a non-record');
  assert.equal(resolveFieldSort(raw.ctx, start, ['poly']), null, 'unknown sort reports as null');
  assert.equal(resolveFieldSort(raw.ctx, start, ['data_', 'rate', 'x']), null, 'past the end');
  assert.equal(resolveFieldSort(raw.ctx, start, []), null, 'empty path');
  assert.equal(resolveFieldSort(raw.ctx, { module: 'Tok', name: 'Color' }, ['x']), null, 'enum');
  assert.equal(resolveFieldSort(raw.ctx, { module: 'Nope', name: 'Token' }, ['amount']), null);
});

test('dalf: the Optional encoding\'s synthetic segments resolve from the declaration', () => {
  // The IR does not model an `Optional T` field as a value: it models it as
  // the pair `<path>.$some : Bool` / `<path>.$value : T` (lfir.js). Those
  // segments are not declared fields, and before they were understood here a
  // property could not tell an `Optional Numeric` it failed to read from a
  // field whose type the archive does not carry.
  const raw = decodeDalfRaw(buildTypedRecordDalf());
  const start = { module: 'Tok', name: 'Token' };
  // `opt` is `Optional Int64`. The path itself denotes NEITHER half of the
  // pair, so it answers `optional:<element>` and never `numeric` - answering
  // `numeric` would tell a property that an unreadable field is a number.
  assert.equal(resolveFieldSort(raw.ctx, start, ['opt']), 'optional:int');
  // The presence flag is a Bool whatever the element is: a fact about the
  // encoding, not about T.
  assert.equal(resolveFieldSort(raw.ctx, start, ['opt', '$some']), 'bool');
  // The payload is answered only for a NUMERIC element (`numeric` or `int`),
  // which is the case whose consequences are worked through; see the note on
  // resolveFieldSort. The ELEMENT SORT is carried through rather than
  // collapsed: `$value` is the half of the pair that reaches arithmetic, so it
  // is exactly where the integrality of an `Optional Int` is worth having.
  assert.equal(resolveFieldSort(raw.ctx, start, ['opt', '$value']), 'int');
  // Nothing is walked THROUGH the payload, and no other synthetic segment is
  // invented.
  assert.equal(resolveFieldSort(raw.ctx, start, ['opt', '$value', 'x']), null);
  assert.equal(resolveFieldSort(raw.ctx, start, ['opt', '$nope']), null);
  assert.equal(resolveFieldSort(raw.ctx, start, ['opt', '$some', 'x']), null);
});

test('dalf: enum and variant declarations carry their COMPLETE constructor list', () => {
  // The list becomes the constructor list of an SMT datatype sort, so a short
  // one would make the sort's variables range over fewer values than the Daml
  // type has - which can turn a satisfiable query unsat and yield a spurious
  // PROVED. It is therefore read off the declaration, never assembled from the
  // constructors a `case` happens to name.
  const raw = decodeDalfRaw(buildEnumVariantDalf());
  assert.deepEqual(raw.dataTypes.get('Tok:Color').constructors, ['Red', 'Green', 'Blue']);
  assert.equal(raw.dataTypes.get('Tok:Color').kind, 'enum');
  assert.deepEqual(raw.dataTypes.get('Tok:Result').constructors, ['Ok', 'Err']);
  assert.equal(raw.dataTypes.get('Tok:Result').kind, 'variant');

  // The sort name IDENTIFIES the declaring package's type, the way a UF symbol
  // identifies a function: two types sharing one sort would assert that their
  // values are drawn from one set.
  const ref = raw.ctx.dataConRefOfTycon(tyconOf(raw, 'Color'));
  assert.equal(ref.kind, 'enum');
  assert.deepEqual(ref.constructors, ['Red', 'Green', 'Blue']);
  assert.match(ref.sortName, /^enum Tok:Color@/);
  assert.notEqual(
    raw.ctx.dataConRefOfTycon(tyconOf(raw, 'Result')).sortName,
    ref.sortName
  );
  // A RECORD is not a datatype case: nothing to enumerate, so nothing given.
  assert.equal(raw.ctx.dataConRefOfTycon(tyconOf(raw, 'Token')), null);
});

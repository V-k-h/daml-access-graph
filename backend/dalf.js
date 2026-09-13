// backend/dalf.js
//
// Decode a compiled Daml package (.dalf, or the main package of a .dar) into
// the SAME structural model `src/graph.js` consumes, so a built package and a
// source tree produce the same normalized graph.
//
// Why this replaces scraping `damlc inspect`:
//
//   * No Daml SDK required. The old backend shelled out to `damlc`, so it
//     could not read a DAR on a machine without the toolchain - which is most
//     CI images, and was the case here.
//   * The textual output of `damlc inspect` is not a stable API and drifts
//     between LF versions. This reads the protobuf against transcribed field
//     numbers from the official daml_lf2.proto (see lf2-schema.js).
//   * It sees things the text form obscures: interfaces, their choices and
//     controllers, contract keys and maintainers, and `interface instance`
//     view bodies.
//
// Honest limits, all reported rather than hidden:
//   * Party extraction walks an expression for record projections
//     (`this.issuer`), which is how signatory/observer/controller expressions
//     are compiled. A party computed some other way (a helper call, a list
//     built at runtime) yields no field name, and the template is reported as
//     having an unresolved stakeholder expression.
//   * Only LF 2 is handled. An LF 1 package is rejected with a clear message
//     rather than decoded into nonsense.

import { readFileSync } from 'node:fs';

import {
  decodeMessage,
  readPackedVarints,
  one,
  many,
  sub,
  subs,
  int,
  bool,
  has,
} from './protobuf.js';
import * as S from './lf2-schema.js';
import { listEntries, readEntry, readByName, parseManifest } from './zip.js';

/**
 * @typedef {Object} DecodedPackage
 * @property {string|null} packageId
 * @property {string|null} name
 * @property {string|null} version
 * @property {string|null} lfMinor
 * @property {string[]} modules
 * @property {Object[]} templates
 * @property {Object[]} interfaces
 * @property {Object[]} functions    always empty: compiled code has no
 *                                   source-level helper indirection to follow
 * @property {Object[]} diagnostics
 */

// ---------------------------------------------------------------------------
// DAR / DALF entry points
// ---------------------------------------------------------------------------

/**
 * Read a .dar and decode its MAIN package.
 *
 * Dependency packages are listed but not decoded: their templates are not part
 * of this package's access structure, and decoding daml-prim/daml-stdlib would
 * bury the graph. `dependencies` is returned so a caller can decode them
 * selectively (that is how project mode resolves an interface declared in an
 * imported package).
 *
 * @param {string} path
 * @returns {DecodedPackage & {dependencies: Array<{name: string, entry: object}>}}
 */
export function readDar(path) {
  const buf = readFileSync(path);
  const entries = listEntries(buf);

  const manifestBuf = readByName(buf, entries, 'META-INF/MANIFEST.MF');
  if (!manifestBuf) throw new Error(`${path}: not a DAR (no META-INF/MANIFEST.MF)`);
  const manifest = parseManifest(manifestBuf.toString('utf8'));

  const mainName = manifest['Main-Dalf'];
  const dalfEntries = entries.filter((e) => e.name.endsWith('.dalf'));
  const mainEntry =
    (mainName && dalfEntries.find((e) => e.name === mainName)) ||
    // Fall back to the only dalf that is not a well-known runtime package.
    dalfEntries.find((e) => !/\/(daml-prim|daml-stdlib)[-.]/.test(e.name));
  if (!mainEntry) throw new Error(`${path}: could not identify the main DALF`);

  const decoded = decodeDalf(readEntry(buf, mainEntry));
  decoded.diagnostics.unshift({
    severity: 'info',
    code: 'dar-read',
    message:
      `Read ${path.split('/').pop()}: main package ${decoded.name || '?'} ` +
      `${decoded.version || ''} (LF 2.${decoded.lfMinor || '?'}), ` +
      `${dalfEntries.length - 1} dependency package(s) not decoded.`,
  });

  return {
    ...decoded,
    sdkVersion: manifest['Sdk-Version'] || null,
    dependencies: dalfEntries
      .filter((e) => e !== mainEntry)
      .map((e) => ({ name: e.name.split('/').pop(), entry: e })),
    /** Decode one dependency on demand. */
    readDependency: (entry) => decodeDalf(readEntry(buf, entry)),
  };
}

/**
 * Decode a DAR down to the RAW definition messages plus the interning context,
 * for consumers that need the expressions themselves rather than the access
 * structure - specifically the verification frontend in `lfir.js`.
 *
 * The access graph only needs to know THAT a choice performs a create; a proof
 * needs the arithmetic inside it, so this returns the undigested protobuf.
 *
 * @param {string} path
 */
export function readDarRaw(path) {
  const buf = readFileSync(path);
  const entries = listEntries(buf);
  const manifestBuf = readByName(buf, entries, 'META-INF/MANIFEST.MF');
  if (!manifestBuf) throw new Error(`${path}: not a DAR (no META-INF/MANIFEST.MF)`);
  const manifest = parseManifest(manifestBuf.toString('utf8'));
  const dalfEntries = entries.filter((e) => e.name.endsWith('.dalf'));
  const mainEntry =
    (manifest['Main-Dalf'] && dalfEntries.find((e) => e.name === manifest['Main-Dalf'])) ||
    dalfEntries.find((e) => !/\/(daml-prim|daml-stdlib)[-.]/.test(e.name));
  if (!mainEntry) throw new Error(`${path}: could not identify the main DALF`);

  // Index every DALF in the archive by its package id, reading only the
  // Archive envelope (two fields), not the package inside it. Dependency
  // packages are decoded LAZILY and cached: the verification frontend follows
  // cross-package value references (an `ensure` calling a daml-stdlib helper,
  // an interface declared in a sibling package), and this is what lets it
  // resolve them against the actual compiled dependency instead of giving up.
  const entryByPackageId = new Map();
  for (const e of dalfEntries) {
    const archive = decodeMessage(readEntry(buf, e));
    const hash = one(archive, S.Archive.hash);
    if (hash instanceof Uint8Array) {
      entryByPackageId.set(Buffer.from(hash).toString('utf8'), e);
    }
  }
  const cache = new Map();
  const getPackage = (pkgId) => {
    if (cache.has(pkgId)) return cache.get(pkgId);
    const entry = entryByPackageId.get(pkgId);
    // Cache the miss too, so an id that is not in the DAR is not re-searched.
    const decoded = entry ? decodeDalfRaw(readEntry(buf, entry), getPackage) : null;
    cache.set(pkgId, decoded);
    return decoded;
  };

  const main = decodeDalfRaw(readEntry(buf, mainEntry), getPackage);
  cache.set(main.packageId, main);
  return { ...main, getPackage };
}

/**
 * Raw decode: interning tables, the value table, and the undigested
 * template/interface definition messages.
 */
export function decodeDalfRaw(bytes, getPackage = null) {
  const archive = decodeMessage(bytes);
  const payloadBytes = one(archive, S.Archive.payload);
  if (!(payloadBytes instanceof Uint8Array)) throw new Error('DALF: no ArchivePayload');
  const hashBytes = one(archive, S.Archive.hash);
  const packageId =
    hashBytes instanceof Uint8Array ? Buffer.from(hashBytes).toString('utf8') : null;
  const payload = decodeMessage(payloadBytes);
  const pkgBytes = one(payload, S.ArchivePayload.damlLf2);
  if (!(pkgBytes instanceof Uint8Array)) {
    throw new Error('DALF: not a Daml-LF 2 package; this decoder handles LF 2 only.');
  }
  const pkg = decodeMessage(pkgBytes);
  const ctx = buildContext(pkg);
  ctx.selfPackageId = packageId;
  // Cross-package resolution hook: package id -> the decoded raw package (with
  // its OWN interning context), or null when the id is not in the DAR. Wired by
  // readDarRaw; absent for a bare decodeDalfRaw call, in which case external
  // value references stay unresolved (and are reported, not guessed at).
  ctx.getImportedPackage = getPackage ? (pkgId) => (getPackage(pkgId) || {}).ctx || null : null;

  const modules = [];
  for (const mod of subs(pkg, S.Package.modules)) {
    modules.push({
      name: ctx.dname(int(mod, S.Module.nameInternedDname)),
      templates: subs(mod, S.Module.templates),
      interfaces: subs(mod, S.Module.interfaces),
    });
  }

  const minorBytes = one(payload, S.ArchivePayload.minor);
  return {
    ctx,
    modules,
    /**
     * "Module:Name" -> the definition's shape, with a record's fields mapped to
     * their coarse sorts. Exposed so the verification frontend can ask what a
     * field IS rather than inferring it from how the code uses it.
     */
    dataTypes: ctx.dataTypes,
    packageId,
    name: ctx.packageName,
    version: ctx.packageVersion,
    lfMinor: minorBytes instanceof Uint8Array ? Buffer.from(minorBytes).toString('utf8') : null,
  };
}

/**
 * Decode a DALF byte buffer (an `Archive`) into a structural model.
 * @param {Buffer} bytes
 * @returns {DecodedPackage}
 */
export function decodeDalf(bytes) {
  const archive = decodeMessage(bytes);
  const payloadBytes = one(archive, S.Archive.payload);
  const hashBytes = one(archive, S.Archive.hash);
  const packageId = hashBytes instanceof Uint8Array ? Buffer.from(hashBytes).toString('utf8') : null;

  if (!(payloadBytes instanceof Uint8Array)) {
    throw new Error('DALF: no ArchivePayload found (field 3)');
  }
  const payload = decodeMessage(payloadBytes);

  const minorBytes = one(payload, S.ArchivePayload.minor);
  const lfMinor =
    minorBytes instanceof Uint8Array ? Buffer.from(minorBytes).toString('utf8') : null;

  const pkgBytes = one(payload, S.ArchivePayload.damlLf2);
  if (!(pkgBytes instanceof Uint8Array)) {
    throw new Error(
      'DALF: no Daml-LF 2 package in the archive payload. ' +
        'This decoder handles LF 2 only (SDK 3.x); an LF 1 package needs the LF 1 schema.'
    );
  }

  return decodePackage(decodeMessage(pkgBytes), { packageId, lfMinor });
}

// ---------------------------------------------------------------------------
// Package
// ---------------------------------------------------------------------------

/**
 * Build the interning context: the string, dotted-name, type and expression
 * tables, plus the hoisted-value table. Shared by the structural decode and
 * the raw decode, so both resolve names identically.
 */
function buildContext(pkg, diagnostics = []) {
  const strings = many(pkg, S.Package.internedStrings).map((b) =>
    b instanceof Uint8Array ? Buffer.from(b).toString('utf8') : String(b)
  );
  const dottedNames = subs(pkg, S.Package.internedDottedNames).map((dn) =>
    readPackedVarints(dn, S.InternedDottedName.segmentsInternedStr)
      .map((i) => strings[i] ?? `<str:${i}>`)
      .join('.')
  );
  const internedTypes = many(pkg, S.Package.internedTypes).map((b) =>
    b instanceof Uint8Array ? decodeMessage(b) : null
  );
  const internedExprs = many(pkg, S.Package.internedExprs).map((b) =>
    b instanceof Uint8Array ? decodeMessage(b) : null
  );
  const importedPackages = (() => {
    const pi = sub(pkg, S.Package.packageImports);
    if (!pi) return [];
    return many(pi, S.PackageImports.importedPackages).map((b) =>
      b instanceof Uint8Array ? Buffer.from(b).toString('utf8') : String(b)
    );
  })();

  const meta = sub(pkg, S.Package.metadata);
  const name = meta ? strings[int(meta, S.PackageMetadata.nameInternedStr)] ?? null : null;
  const version = meta ? strings[int(meta, S.PackageMetadata.versionInternedStr)] ?? null : null;

  const ctx = {
    packageName: name,
    packageVersion: version,
    strings,
    dottedNames,
    internedTypes,
    internedExprs,
    importedPackages,
    diagnostics,
    /** "Module:name" (and bare name) -> the value's body expression. */
    values: new Map(),
    str: (i) => strings[i] ?? `<str:${i}>`,
    dname: (i) => dottedNames[i] ?? `<dname:${i}>`,
  };

  const modules = subs(pkg, S.Package.modules);

  // The compiler HOISTS choice controller / signatory / observer expressions
  // into top-level values, so a choice's `controllers` field is usually just a
  // ValueId reference. Without this table every stakeholder expression looks
  // empty. Keyed by "Module:name" and by bare name for same-package lookups.
  for (const mod of modules) {
    const moduleName = ctx.dname(int(mod, S.Module.nameInternedDname));
    for (const val of subs(mod, S.Module.values)) {
      const nwt = sub(val, S.DefValue.nameWithType);
      if (!nwt) continue;
      const vname = ctx.dname(int(nwt, S.NameWithType.nameInternedDname));
      const body = sub(val, S.DefValue.expr);
      if (!body) continue;
      ctx.values.set(`${moduleName}:${vname}`, body);
      if (!ctx.values.has(vname)) ctx.values.set(vname, body);
    }
  }

  // FIELD TYPES.
  //
  // A `DefTemplate` says what a template DOES; it does not say what shape its
  // record has. The fields and their types live in the `DefDataType` of the
  // same qualified name, which this decoder used to drop. That gap was not
  // cosmetic: without it a property asking "is this field a Numeric?" has
  // nothing to consult, and the only remaining options are to infer numeric-ness
  // from how the compiled code happens to use the field, or to guess from its
  // NAME. The second is not something a proof may rest on, so the types are
  // decoded instead.
  //
  // Keyed "Module:Name", which is how a TypeConId addresses a definition, and
  // built for EVERY package the archive decodes - so a field whose type comes
  // from a dependency resolves through that dependency's own table rather than
  // being written off.
  ctx.dataTypes = new Map();
  for (const mod of modules) {
    const moduleName = ctx.dname(int(mod, S.Module.nameInternedDname));
    for (const dt of subs(mod, S.Module.dataTypes)) {
      const dname = ctx.dname(int(dt, S.DefDataType.nameInternedDname));
      const entry = { module: moduleName, name: dname, kind: 'other', fields: null };
      if (has(dt, S.DefDataType.record)) {
        entry.kind = 'record';
        entry.fields = new Map();
        // A record with no fields encodes as a zero-length `Fields`, so the
        // presence test above is what decides the kind, not the field count.
        for (const f of subs(sub(dt, S.DefDataType.record), S.DataTypeFields.fields)) {
          const fname = ctx.str(int(f, S.FieldWithType.fieldInternedStr));
          entry.fields.set(fname, classifyType(sub(f, S.FieldWithType.type), ctx));
        }
      } else if (has(dt, S.DefDataType.variant)) {
        entry.kind = 'variant';
        // A variant's CONSTRUCTORS are encoded exactly like record fields
        // (name + payload type). Only the names are kept: the discriminant is
        // what the translator models (see lfir.js: translateCase), and the
        // payload types belong to values the IR has no term for.
        entry.constructors = subs(sub(dt, S.DefDataType.variant), S.DataTypeFields.fields).map(
          (f) => ctx.str(int(f, S.FieldWithType.fieldInternedStr))
        );
      } else if (has(dt, S.DefDataType.enum)) {
        entry.kind = 'enum';
        // The COMPLETE constructor list, and completeness is load-bearing: it
        // becomes the constructor list of an SMT datatype sort, so a list with
        // a constructor missing would shrink the set of values the sort's
        // variables range over - which can turn a satisfiable query unsat and
        // make a PROVED spurious. It is therefore read off the declaration and
        // never assembled from the constructors a `case` happens to name.
        entry.constructors = readPackedVarints(
          sub(dt, S.DefDataType.enum),
          S.DataTypeEnumConstructors.constructorsInternedStr
        ).map((i) => ctx.str(i));
      } else if (has(dt, S.DefDataType.interface)) entry.kind = 'interface';
      ctx.dataTypes.set(`${moduleName}:${dname}`, entry);
    }
  }

  /**
   * The coarse sort of `start.segments`, or null when the path cannot be
   * followed. Null means NOTHING IS KNOWN and is never a guess: see
   * resolveFieldSort.
   */
  ctx.fieldSort = (start, segments) => resolveFieldSort(ctx, start, segments);
  /** The record a Type denotes, as a {pkg, module, name} start for fieldSort. */
  ctx.recordTypeRef = (type) => recordTypeRef(type, ctx);
  /** The same, for the bare TypeConId a `create` names its target with. */
  ctx.recordRefOfTycon = (tycon) => recordRefOfTycon(tycon, ctx);
  /** The same, addressed by qualified name in THIS package. */
  ctx.recordRef = (module, name) => {
    const e = ctx.dataTypes.get(`${module}:${name}`);
    return e && e.kind === 'record' ? { pkg: ctx, module, name } : null;
  };
  /**
   * The ENUM or VARIANT a TypeConId names, with its complete constructor list
   * and the SMT sort name the emitter will declare it under - or null when the
   * type is not one of those, or is declared in a package this archive does
   * not carry.
   */
  ctx.dataConRefOfTycon = (tycon) => dataConRefOfTycon(tycon, ctx);

  // Bound form, so consumers outside this module (the verification frontend)
  // can follow a ValueId without reaching for internals.
  ctx.resolveValue = (expr) => resolveValue(expr, ctx);

  return ctx;
}

/**
 * Decode a package into the structural model the access graph consumes.
 */
function decodePackage(pkg, { packageId, lfMinor }) {
  const diagnostics = [];
  const ctx = buildContext(pkg, diagnostics);
  const name = ctx.packageName;
  const version = ctx.packageVersion;

  const templates = [];
  const interfaces = [];
  const moduleNames = [];
  const modules = subs(pkg, S.Package.modules);

  for (const mod of modules) {
    const moduleName = ctx.dname(int(mod, S.Module.nameInternedDname));
    moduleNames.push(moduleName);

    for (const tpl of subs(mod, S.Module.templates)) {
      templates.push(decodeTemplate(tpl, moduleName, ctx));
    }
    for (const iface of subs(mod, S.Module.interfaces)) {
      interfaces.push(decodeInterface(iface, moduleName, ctx));
    }
  }

  if (templates.length === 0 && interfaces.length === 0) {
    diagnostics.push({
      severity: 'warning',
      code: 'dalf-empty',
      message:
        `Package ${name || '?'} decoded cleanly but declares no templates or interfaces. ` +
        `If that is unexpected, the package may be LF 1 or use a schema revision this decoder ` +
        `has not been checked against (checked: LF 2.${S.CHECKED_AGAINST_MINOR.join(', 2.')}).`,
    });
  }

  if (lfMinor && !S.CHECKED_AGAINST_MINOR.includes(lfMinor)) {
    diagnostics.push({
      severity: 'warning',
      code: 'lf-minor-unchecked',
      message:
        `Package is Daml-LF 2.${lfMinor}; this decoder's field numbers were verified against ` +
        `2.${S.CHECKED_AGAINST_MINOR.join(', 2.')}. Field numbers are additive within LF 2, so ` +
        `this usually decodes correctly, but treat surprising results with suspicion.`,
    });
  }

  return {
    module: moduleNames.length === 1 ? moduleNames[0] : null,
    modules: moduleNames,
    packageId,
    name,
    version,
    lfMinor,
    templates,
    interfaces,
    functions: [],
    referencedTemplates: [],
    referencedInterfaces: [],
    diagnostics,
  };
}

// ---------------------------------------------------------------------------
// Templates and interfaces
// ---------------------------------------------------------------------------

function decodeTemplate(tpl, moduleName, ctx) {
  const name = ctx.dname(int(tpl, S.DefTemplate.tyconInternedDname));
  const param = ctx.str(int(tpl, S.DefTemplate.paramInternedStr));

  const signatories = exprParties(sub(tpl, S.DefTemplate.signatories), ctx, {
    what: `${name} signatory`,
  });
  const observers = exprParties(sub(tpl, S.DefTemplate.observers), ctx, {
    what: `${name} observer`,
  });

  const choices = subs(tpl, S.DefTemplate.choices).map((c) =>
    decodeChoice(c, name, ctx, false, param)
  );

  // Contract key: the maintainer expression is a function from the key to
  // [Party], so its record projections name the maintaining fields.
  let key = null;
  const keyMsg = sub(tpl, S.DefTemplate.key);
  if (keyMsg) {
    const maintainers = exprParties(sub(keyMsg, S.DefKey.maintainers), ctx, {
      what: `${name} key maintainer`,
    });
    const keyType = typeName(sub(keyMsg, S.DefKey.type), ctx);
    key = {
      expr: keyType || '<key expression not rendered from compiled form>',
      type: keyType,
      parties: maintainers,
      maintainers,
      line: 0,
    };
    if (maintainers.length === 0) {
      ctx.diagnostics.push({
        severity: 'info',
        code: 'key-maintainer-unrecovered',
        message:
          `${name}: the contract key was found, but its maintainer expression yielded no field ` +
          `name from the compiled form. The source parser recovers these (\`maintainer key._1\`); ` +
          `prefer project mode when maintainer analysis matters.`,
      });
    }
  }

  // `interface instance` blocks, including the view body. The view expression
  // is a record construction whose fields map view field -> template
  // expression, which is what resolves a `(view this).admin` controller.
  const implementsList = [];
  const interfaceInstances = [];
  for (const impl of subs(tpl, S.DefTemplate.implements)) {
    const ifaceRef = typeConName(sub(impl, S.Implements.interface), ctx);
    if (!ifaceRef) continue;
    implementsList.push(ifaceRef.name);
    const body = sub(impl, S.Implements.body);
    const viewExpr = body ? sub(body, S.InterfaceInstanceBody.view) : undefined;
    interfaceInstances.push({
      interface: ifaceRef.name,
      forTemplate: name,
      viewType: null,
      viewBindings: viewExpr ? recordBindings(viewExpr, ctx) : {},
      nestedViewFields: [],
      line: 0,
    });
  }

  return {
    name,
    module: moduleName,
    param,
    fields: [],
    // In compiled code every stakeholder reference is a projection off the
    // template parameter, so the projected names ARE the party fields.
    partyFields: [...new Set([...signatories, ...observers])],
    signatories,
    observers,
    choices,
    implements: [...new Set(implementsList)],
    interfaceInstances,
    key,
    line: 0,
  };
}

function decodeInterface(iface, moduleName, ctx) {
  const name = ctx.dname(int(iface, S.DefInterface.tyconInternedDname));
  const methods = subs(iface, S.DefInterface.methods).map((m) =>
    ctx.str(int(m, S.InterfaceMethod.methodInternedName))
  );
  const ifaceParam = ctx.str(int(iface, S.DefInterface.paramInternedStr));
  const choices = subs(iface, S.DefInterface.choices).map((c) =>
    decodeChoice(c, name, ctx, true, ifaceParam)
  );
  const requires = subs(iface, S.DefInterface.requires)
    .map((r) => typeConName(r, ctx))
    .filter(Boolean)
    .map((r) => r.name);

  return {
    name,
    module: moduleName,
    viewtype: typeName(sub(iface, S.DefInterface.view), ctx) || null,
    methods,
    choices,
    requires,
    line: 0,
  };
}

function decodeChoice(choice, ownerName, ctx, onInterface = false, selfParam = null) {
  const name = ctx.str(int(choice, S.TemplateChoice.nameInternedStr));
  const consuming = bool(choice, S.TemplateChoice.consuming);

  const argBinder = sub(choice, S.TemplateChoice.argBinder);
  const argParam = argBinder ? ctx.str(int(argBinder, S.VarWithType.varInternedStr)) : null;

  const controllers = exprParties(sub(choice, S.TemplateChoice.controllers), ctx, {
    what: `${ownerName}.${name} controller`,
    // On an interface, stakeholders are reached through the view, so mark
    // param-rooted projections view-relative to match the source parser's
    // `view.x` form. Argument-rooted ones are tagged `#arg` instead.
    viewRelative: onInterface,
    selfParam,
    argParam,
  });

  const operations = [];
  collectOperations(sub(choice, S.TemplateChoice.update), ctx, operations, new Set());

  return {
    name,
    consuming,
    controllers,
    operations,
    refs: [],
    line: 0,
  };
}

// ---------------------------------------------------------------------------
// Expression walking
// ---------------------------------------------------------------------------

/**
 * Dereference the two kinds of indirection an expression can hide behind, so
 * walks see the real node:
 *
 *   * `Expr.interned_expr` - an index into Package.interned_exprs
 *   * `Expr.val`           - a reference to a top-level value, which is where
 *                            the compiler puts hoisted stakeholder expressions
 */
function deref(expr, ctx, seen = new Set()) {
  if (!expr) return undefined;

  if (has(expr, S.Expr.internedExpr)) {
    const idx = int(expr, S.Expr.internedExpr);
    const key = `e${idx}`;
    if (seen.has(key)) return undefined;
    seen.add(key);
    const target = ctx.internedExprs[idx];
    if (target) return deref(target, ctx, seen);
    ctx.diagnostics.push({
      severity: 'warning',
      code: 'interned-expr-missing',
      message: `Expression references interned expression ${idx}, which is not in the table.`,
    });
    return undefined;
  }

  const valRef = resolveValue(expr, ctx);
  if (valRef) {
    if (seen.has(valRef.key)) return undefined;
    seen.add(valRef.key);
    return deref(valRef.body, ctx, seen);
  }

  return expr;
}

/**
 * Resolve `Expr.val` (a ValueId) against the package's value table, following
 * the reference into an IMPORTED package when the ValueId carries one and the
 * context has a cross-package hook (readDarRaw wires it; decodeDalf does not).
 *
 * The returned `pkg` is the interning context the BODY must be read against:
 * a body that lives in daml-stdlib resolves its interned strings and interned
 * expressions in daml-stdlib's tables, not the referrer's.
 *
 * @returns {{key: string, name: string, body: Object, pkg: Object}|undefined}
 */
function resolveValue(expr, ctx) {
  const val = sub(expr, S.Expr.val);
  if (!val) return undefined;
  // Name indices resolve in the REFERRING package's tables; the resulting
  // strings are then looked up in the target package's value map.
  const name = ctx.dname(int(val, S.ValueId.nameInternedDname));
  if (!name || name.startsWith('<dname:')) return undefined;
  const moduleRef = sub(val, S.ValueId.module);
  const moduleName = moduleRef
    ? ctx.dname(int(moduleRef, S.ModuleId.moduleNameInternedDname))
    : null;
  const qualified = moduleName ? `${moduleName}:${name}` : null;

  // Which package does the reference point at?
  let externalPkgId = null;
  const pkgRef = moduleRef ? sub(moduleRef, S.ModuleId.packageId) : null;
  if (pkgRef) {
    if (has(pkgRef, S.SelfOrImportedPackageId.importedPackageIdInternedStr)) {
      externalPkgId = ctx.str(int(pkgRef, S.SelfOrImportedPackageId.importedPackageIdInternedStr));
    } else if (has(pkgRef, S.SelfOrImportedPackageId.packageImportId)) {
      const idx = int(pkgRef, S.SelfOrImportedPackageId.packageImportId);
      externalPkgId = ctx.importedPackages[idx] ?? null;
    }
    // `selfPackageId` (or no package ref at all) means this package.
  }

  if (externalPkgId && externalPkgId !== ctx.selfPackageId) {
    if (!ctx.getImportedPackage || !qualified) return undefined;
    const target = ctx.getImportedPackage(externalPkgId);
    if (!target) return undefined;
    const body = target.values.get(qualified);
    if (!body) return undefined;
    // No bare-name fallback across packages: a same-named local value must not
    // stand in for the imported one.
    return { key: `v${externalPkgId}:${qualified}`, name: qualified, body, pkg: target };
  }

  const body = (qualified && ctx.values.get(qualified)) || ctx.values.get(name);
  if (!body) return undefined;
  return {
    key: `v${ctx.selfPackageId || 'self'}:${qualified || name}`,
    name: qualified || name,
    body,
    pkg: ctx,
  };
}

/**
 * Collect the record-projection field names in an expression: the party fields
 * of a signatory / observer / controller / maintainer expression.
 *
 * A projection chain (`this.data.owner`) yields the OUTERMOST field joined to
 * the inner path, matching the source parser's `contractData.owner` form, so
 * the two frontends produce comparable party labels.
 */
function exprParties(expr, ctx, { what, viewRelative = false, selfParam, argParam } = {}) {
  const e = deref(expr, ctx);
  if (!e) return [];

  const found = [];
  let sawSignatoryRef = false;
  walkExpr(e, ctx, {
    recProj: (path, rootVar) => found.push({ path, rootVar }),
    signatoryRef: () => {
      sawSignatoryRef = true;
    },
  });

  // Label each projection by what it is rooted in, mirroring the source
  // parser so both frontends produce comparable party labels:
  //   rooted in the template/interface param -> a field (or `view.` field)
  //   rooted in the choice argument          -> a choice argument, not a field
  const parties = [];
  const seen = new Set();
  let unattributed = 0;
  for (const { path, rootVar } of found) {
    let label;
    if (argParam && rootVar === argParam) {
      label = `${path}#arg`;
    } else if (rootVar === selfParam) {
      label = viewRelative ? `view.${path}` : path;
    } else {
      // The chain bottoms out in a compiler-introduced let-binding (the
      // optimizer hoists `view this` into `let ds1 = ... in ds1.x`), so
      // whether this is a view field or a choice argument is not derivable
      // here. Emit the bare path rather than guessing a prefix.
      label = path;
      unattributed++;
    }
    if (seen.has(label)) continue;
    seen.add(label);
    parties.push(label);
  }

  if (unattributed > 0 && what) {
    ctx.diagnostics.push({
      severity: 'info',
      code: 'party-root-unattributed',
      message:
        `${what}: ${unattributed} projection path(s) are rooted in a compiler-introduced ` +
        `let-binding rather than the parameter or the choice argument, so they are reported as ` +
        `bare field paths without a \`view.\`/\`#arg\` attribution.`,
    });
  }

  // `choice Archive` and any `controller signatory this` compile to a
  // signatory reference with no projection of their own. That is not a failure
  // to resolve: the controllers ARE the stakeholders, so say so.
  if (parties.length === 0 && sawSignatoryRef) return ['<signatories>'];

  if (parties.length === 0 && what) {
    ctx.diagnostics.push({
      severity: 'info',
      code: 'unresolved-party-expr',
      message:
        `${what}: the compiled expression contains no record projection, so no party field name ` +
        `could be recovered (it is computed, e.g. by a helper call or a runtime list).`,
    });
  }
  return parties;
}

/**
 * The bindings of a record-construction expression: field name -> a readable
 * rendering of the bound expression. Used for `interface instance` view bodies.
 */
function recordBindings(expr, ctx) {
  const e = deref(expr, ctx);
  if (!e) return {};
  /** @type {Record<string,string>} */
  const out = {};
  // The view body is typically a lambda over `this` wrapping the record.
  const rec = findRecCon(e, ctx, 0);
  if (!rec) return out;
  for (const f of subs(rec, S.RecCon.fields)) {
    const field = ctx.str(int(f, S.FieldWithExpr.fieldInternedStr));
    const valueExpr = deref(sub(f, S.FieldWithExpr.expr), ctx);
    if (!valueExpr) continue;
    const projections = [];
    walkExpr(valueExpr, ctx, { recProj: (p) => projections.push(p) });
    // A view field bound to exactly one projection is a direct pass-through,
    // which is the case the access graph can resolve. Anything else is left
    // out rather than guessed at.
    if (projections.length === 1) out[field] = projections[0];
  }
  return out;
}

function findRecCon(expr, ctx, depth) {
  if (depth > 10) return undefined;
  // The view body is commonly a hoisted top-level value, so look through the
  // indirection before searching for the record construction.
  const e = deref(expr, ctx) || expr;
  if (e !== expr) {
    const viaRef = findRecCon(e, ctx, depth + 1);
    if (viaRef) return viaRef;
  }
  const rec = sub(expr, S.Expr.recCon);
  if (rec) return rec;
  for (const fn of [S.Expr.abs, S.Expr.tyAbs, S.Expr.let, S.Expr.tyApp]) {
    const inner = sub(expr, fn);
    if (!inner) continue;
    // body is field 2 for Abs/TyAbs/Block, field 1 for TyApp
    for (const bodyField of [2, 1]) {
      const body = deref(sub(inner, bodyField), ctx);
      if (!body) continue;
      const found = findRecCon(body, ctx, depth + 1);
      if (found) return found;
    }
  }
  return undefined;
}

/**
 * Walk an expression tree, reporting record projections.
 *
 * Descent is GENERIC (every length-delimited subfield is followed) because Expr
 * is a 40-case oneof and the access graph only cares about a couple of leaves.
 * To keep that from misreading unrelated bytes, a candidate is only accepted
 * when it has the right SHAPE: a RecProj must carry both a field index and a
 * record subexpression.
 */
function walkExpr(expr, ctx, visit, depth = 0, seen = new Set()) {
  if (!expr || depth > 60) return;

  if (visit.signatoryRef) {
    for (const fn of [S.Expr.signatoryInterface, S.Expr.observerInterface]) {
      if (has(expr, fn)) visit.signatoryRef();
    }
  }

  const proj = sub(expr, S.Expr.recProj);
  if (proj && has(proj, S.RecProj.fieldInternedStr) && has(proj, S.RecProj.record)) {
    const chain = projectionChain(proj, ctx, depth);
    if (chain) {
      if (visit.recProj) visit.recProj(chain.path, chain.rootVar);
      return;
    }
  }

  const valRef = resolveValue(expr, ctx);
  if (valRef && !seen.has(valRef.key)) {
    seen.add(valRef.key);
    walkExpr(valRef.body, ctx, visit, depth + 1, seen);
  }

  for (const [fieldNumber, values] of expr) {
    if (fieldNumber === S.Expr.internedExpr) {
      const idx = int(expr, S.Expr.internedExpr);
      if (seen.has(`e${idx}`)) continue;
      seen.add(`e${idx}`);
      walkExpr(ctx.internedExprs[idx], ctx, visit, depth + 1, seen);
      continue;
    }
    if (fieldNumber === S.Expr.val) continue; // handled above
    for (const v of values) {
      if (!(v instanceof Uint8Array) || v.length === 0) continue;
      let child;
      try {
        child = decodeMessage(v);
      } catch (_) {
        continue; // not a submessage: a string or opaque bytes
      }
      walkExpr(child, ctx, visit, depth + 1, seen);
    }
  }
}

/**
 * Flatten a RecProj chain into a dotted path plus the variable it is rooted in.
 *
 *   this.issuer                  -> {path: 'issuer',            rootVar: 'this'}
 *   this.contractData.owner      -> {path: 'contractData.owner', rootVar: 'this'}
 *   (view this).transfer.sender  -> {path: 'transfer.sender',    rootVar: 'this'}
 *   arg.newOwner                 -> {path: 'newOwner',           rootVar: 'arg'}
 *
 * The root matters: a projection off the choice argument is supplied by the
 * exercising party, not a field of the contract, and conflating the two was
 * the biggest false-positive source in the source parser too.
 */
function projectionChain(proj, ctx, depth) {
  const segments = [];
  let node = proj;
  for (let i = 0; i < 12 && node; i++) {
    if (!has(node, S.RecProj.fieldInternedStr)) return null;
    segments.unshift(ctx.str(int(node, S.RecProj.fieldInternedStr)));
    const record = deref(sub(node, S.RecProj.record), ctx);
    if (!record) return { path: segments.join('.'), rootVar: null };

    const next = sub(record, S.Expr.recProj);
    if (next && has(next, S.RecProj.fieldInternedStr)) {
      node = next;
      continue;
    }
    // Bottom of the chain. `view this` wraps the variable, so look through it.
    const rootVar = rootVariable(record, ctx, 0);
    return { path: segments.join('.'), rootVar };
  }
  return { path: segments.join('.'), rootVar: null };
}

/** The variable a (possibly wrapped) expression bottoms out in. */
function rootVariable(expr, ctx, depth) {
  if (!expr || depth > 6) return null;
  if (has(expr, S.Expr.varInternedStr)) return ctx.str(int(expr, S.Expr.varInternedStr));
  for (const fn of [
    S.Expr.viewInterface,
    S.Expr.toInterface,
    S.Expr.fromInterface,
    S.Expr.unsafeFromInterface,
  ]) {
    const inner = sub(expr, fn);
    if (!inner) continue;
    for (const f of [2, 3, 4]) {
      const e = deref(sub(inner, f), ctx);
      const v = e ? rootVariable(e, ctx, depth + 1) : null;
      if (v) return v;
    }
  }
  return null;
}

/**
 * Collect ledger operations from a choice body.
 *
 * Same validated generic descent as walkExpr: an `Update` candidate is only
 * accepted when one of its operation cases carries a TypeConId that resolves
 * to a real name, which makes a coincidental field-number match very unlikely.
 */
function collectOperations(expr, ctx, out, seen, depth = 0) {
  if (!expr || depth > 60) return;

  const update = sub(expr, S.Expr.update);
  if (update) {
    for (const [fieldNumber, spec] of Object.entries(S.UPDATE_OPS)) {
      const opMsg = sub(update, Number(fieldNumber));
      if (!opMsg) continue;
      const target = typeConName(sub(opMsg, spec.targetField), ctx);
      if (!target) continue;
      out.push({
        kind: spec.kind,
        target: target.name,
        inferred: true,
        ...(spec.byInterface ? { targetKind: 'interface' } : {}),
        ...(target.external ? { targetExternal: true, targetPackage: target.packageRef } : {}),
        ...(spec.choiceField && has(opMsg, spec.choiceField)
          ? { choice: ctx.str(int(opMsg, spec.choiceField)) }
          : {}),
        resolvedVia: 'daml-lf',
        line: 0,
      });
    }
  }

  const valRef = resolveValue(expr, ctx);
  if (valRef && !seen.has(valRef.key)) {
    seen.add(valRef.key);
    collectOperations(valRef.body, ctx, out, seen, depth + 1);
  }

  for (const [fieldNumber, values] of expr) {
    if (fieldNumber === S.Expr.internedExpr) {
      const idx = int(expr, S.Expr.internedExpr);
      if (seen.has(`e${idx}`)) continue;
      seen.add(`e${idx}`);
      collectOperations(ctx.internedExprs[idx], ctx, out, seen, depth + 1);
      continue;
    }
    if (fieldNumber === S.Expr.val) continue; // handled above
    for (const v of values) {
      if (!(v instanceof Uint8Array) || v.length === 0) continue;
      let child;
      try {
        child = decodeMessage(v);
      } catch (_) {
        continue;
      }
      collectOperations(child, ctx, out, seen, depth + 1);
    }
  }
}

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/**
 * Resolve a TypeConId to its bare name, and say whether it lives in this
 * package or an imported one.
 * @returns {{name: string, module: string|null, external: boolean, packageRef: string|null}|undefined}
 */
function typeConName(tycon, ctx) {
  if (!tycon) return undefined;
  if (!has(tycon, S.TypeConId.nameInternedDname) && !has(tycon, S.TypeConId.module)) return undefined;
  const name = ctx.dname(int(tycon, S.TypeConId.nameInternedDname));
  if (!name || name.startsWith('<dname:')) return undefined;

  const moduleRef = sub(tycon, S.TypeConId.module);
  let module = null;
  let external = false;
  let packageRef = null;
  if (moduleRef) {
    module = ctx.dname(int(moduleRef, S.ModuleId.moduleNameInternedDname));
    const pkgRef = sub(moduleRef, S.ModuleId.packageId);
    if (pkgRef) {
      if (has(pkgRef, S.SelfOrImportedPackageId.importedPackageIdInternedStr)) {
        external = true;
        packageRef = ctx.str(int(pkgRef, S.SelfOrImportedPackageId.importedPackageIdInternedStr));
      } else if (has(pkgRef, S.SelfOrImportedPackageId.packageImportId)) {
        external = true;
        const idx = int(pkgRef, S.SelfOrImportedPackageId.packageImportId);
        packageRef = ctx.importedPackages[idx] ?? `<import:${idx}>`;
      }
    }
  }
  return { name, module, external, packageRef };
}

// ---------------------------------------------------------------------------
// Field types
// ---------------------------------------------------------------------------

/**
 * BuiltinType -> the COARSE sort a property reasons about.
 *
 * Coarse on purpose. What a property needs to know is whether `>= 0` is a
 * question about the field at all, and everything this table does not
 * recognise stays `unknown` - which behaves as "no information", never as
 * "not numeric".
 *
 * `int` AND `numeric` ARE TWO SORTS, and the split is not cosmetic.
 *
 * Both are numbers and both carry the same obligations, so every consumer that
 * treats `numeric` as "this is a number" treats `int` the same way. What
 * differs is the SMT sort the symbol is declared at: `numeric` becomes `Real`,
 * `int` becomes `Int`, and an `Int`-sorted symbol carries INTEGRALITY - the
 * solver may not give it the value -1/10.
 *
 * The direction of that constraint is the thing to keep straight. Adding
 * integrality SHRINKS the model class, which is the opposite direction from
 * every other approximation in this pipeline (dropped guards, uninterpreted
 * functions, symbolic list elements all ENLARGE it). It is nevertheless sound,
 * and for one reason only: a Daml `Int` really is an integer, so no reachable
 * state is excluded. It is a faithful refinement of the model, not an
 * assumption about the code.
 *
 * The consequence is that a MIS-CLASSIFICATION here is unsound in the one
 * direction this pipeline must never fail: typing a `Decimal` field as `int`
 * would assert something false about the code and could make an unsat -- a
 * PROVED -- spurious. So `int` is answered from the DECLARED LF type and from
 * nothing else. Never from a field's name, never from its position, never from
 * a literal that happens to look integral. Where the declared type is not
 * available the field is `unknown` and the symbol keeps the `Real` treatment
 * it had before this split existed, which is the conservative side.
 *
 * BIGNUMERIC is deliberately absent. It is a number, but it is also a type the
 * translator does not arithmetically model, and admitting it here would create
 * obligations over terms the fragment cannot carry. `unknown` leaves such a
 * field exactly where it was before this table existed: judged on positional
 * evidence alone.
 */
const BT = S.ENUMS.BuiltinType;
const BUILTIN_SORT = new Map([
  [BT.NUMERIC, 'numeric'],
  [BT.INT64, 'int'],
  [BT.BOOL, 'bool'],
  [BT.TEXT, 'text'],
  [BT.PARTY, 'party'],
  [BT.DATE, 'time'],
  [BT.TIMESTAMP, 'time'],
  [BT.CONTRACT_ID, 'cid'],
]);

/**
 * The coarse sorts that make `>= 0` a question about a field: the two numeric
 * ones and nothing else.
 *
 * One place, because every consumer of the classification has to agree about
 * it: a consumer that checked for `numeric` alone would silently revert an
 * `Int` field to the unknown class the moment the split above happened, and an
 * unknown field is an unchecked obligation rather than a wrong answer - quiet,
 * and exactly the kind of quiet this pipeline is built to avoid.
 */
export const NUMERIC_SORTS = new Set(['numeric', 'int']);

/** Is this coarse sort one of the numeric ones (`numeric` or `int`)? */
export function isNumericSort(sort) {
  return NUMERIC_SORTS.has(sort);
}

/**
 * Classify a Type into `{sort, ref?}`.
 *
 * The three shapes that actually occur in a compiled field type:
 *
 *   * INTERNED. `Type.interned_type` is an index into `Package.interned_types`;
 *     most field types in a real package arrive this way, so not following the
 *     indirection would classify nearly everything as unknown.
 *   * APPLIED. `Numeric 10` is the NUMERIC builtin applied to its scale, and an
 *     `Optional Int64` is the OPTIONAL builtin applied to its element. LF
 *     writes an application either as `Type.Builtin` carrying `args`, or as a
 *     `Type.TApp` spine; in both the HEAD decides the sort, so the spine is
 *     walked to its head and the arguments are ignored. That is what keeps
 *     `Numeric 10` numeric and - just as importantly - keeps `Optional Numeric`
 *     UNKNOWN rather than numeric, because the IR models an Optional field as a
 *     `$some`/`$value` pair and the plain field path denotes neither.
 *   * NOMINAL. A `Type.Con` names a declared data type. It is returned as
 *     `record` together with the TypeConId it names, which is what lets a
 *     nested path (`this.terms.rate`) be followed one hop further. `record`
 *     covers variants and enums too; all three are non-numeric, and the descent
 *     step checks the definition's kind before it tries to enter one.
 *
 * Everything else - a type variable, a synonym, a forall, a struct, a nat - is
 * `unknown`. A type PARAMETER especially: its instantiation is not visible here,
 * and answering anything but "unknown" would be inventing a fact.
 *
 * @returns {{sort: string, ref?: object}}
 */
function classifyType(type, ctx, depth = 0) {
  if (!type || depth > 12) return { sort: 'unknown' };

  if (has(type, S.Type.internedType)) {
    const idx = int(type, S.Type.internedType);
    const target = ctx.internedTypes[idx];
    if (!target) return { sort: 'unknown' };
    return classifyType(target, ctx, depth + 1);
  }

  const builtin = sub(type, S.Type.builtin);
  if (builtin) {
    const bt = int(builtin, S.TypeBuiltin.builtin);
    if (bt === BT.OPTIONAL) {
      // `Type.Builtin` carries its arguments inline. An OPTIONAL with no
      // argument is not a field type (it is the unapplied constructor), and
      // its element is then unknown rather than assumed.
      const args = subs(builtin, S.TypeBuiltin.args);
      return optionalOf(args.length ? classifyType(args[0], ctx, depth + 1) : { sort: 'unknown' });
    }
    return { sort: BUILTIN_SORT.get(bt) || 'unknown' };
  }

  const con = sub(type, S.Type.con);
  if (con) {
    const ref = typeConName(sub(con, S.TypeCon.tycon), ctx);
    return ref ? { sort: 'record', ref } : { sort: 'unknown' };
  }

  const tapp = sub(type, S.Type.tapp);
  if (tapp) {
    const head = classifyType(sub(tapp, S.TypeApp.lhs), ctx, depth + 1);
    // `Optional T` written as a TApp spine: the HEAD classifies as an
    // unapplied Optional and the RIGHT-HAND side is the element. Every other
    // application still takes its sort from the head alone, which is what
    // keeps `Numeric 10` numeric.
    if (head.sort === 'optional' && head.elem && head.elem.sort === 'unknown') {
      return optionalOf(classifyType(sub(tapp, S.TypeApp.rhs), ctx, depth + 1));
    }
    return head;
  }

  return { sort: 'unknown' };
}

/**
 * The classification of an `Optional T`, carrying T's own classification.
 *
 * Kept as a distinct sort rather than folded into T's: the IR does not model
 * an Optional field as a value at all, it models it as the SYMBOL PAIR
 * `<path>.$some : Bool` / `<path>.$value : T` (see lfir.js: translateCase), so
 * the plain field path denotes neither and answering `T` here would tell a
 * property that a field it cannot read is a number.
 */
function optionalOf(elem) {
  return { sort: 'optional', elem: elem || { sort: 'unknown' } };
}

/**
 * Follow a projection PATH from a record type through nested record fields.
 *
 * Returns the coarse sort of the field the path ends at, or NULL when the path
 * cannot be followed to the end. Null is the whole point of the function: it
 * is returned for a field of a type declared in a package the archive does not
 * contain, for a step through something that is not a record, and for a field
 * name the record does not declare. In every one of those cases the caller
 * records nothing, so an unfollowable path costs coverage and never produces a
 * wrong sort.
 *
 * THE SYNTHETIC OPTIONAL SEGMENTS. The IR does not model an `Optional T` field
 * as a value; it models it as the symbol pair `<path>.$some : Bool` /
 * `<path>.$value : T` (lfir.js: translateCase), and those two segments are not
 * declared record fields. They used to fall off the end of this walk, which is
 * why `Optional Numeric` fields were indistinguishable from fields whose type
 * the archive could not read. They are now answered from the Optional's own
 * declaration:
 *
 *   `<path>`         ->  `optional:<T's sort>`, or null when T is unknown.
 *                        Deliberately NOT `<T's sort>`: the plain path denotes
 *                        neither half of the pair, and answering `numeric`
 *                        there would tell a property that an unreadable field
 *                        is a number.
 *   `<path>.$some`   ->  `bool`. A fact about the encoding, not about T, so it
 *                        is answered whatever T is.
 *   `<path>.$value`  ->  T's sort, and ONLY when T is NUMERIC (`numeric` or
 *                        `int`). A non-numeric or unknown T answers null: the
 *                        payload symbol is the one that reaches arithmetic
 *                        positions and seeds the sort inference, and the
 *                        numeric case is the one whose consequences have been
 *                        worked through. Nothing is lost by the restriction -
 *                        a property that needs to know the field is not a
 *                        number reads the `optional:` sort of the path itself.
 *
 *                        The ELEMENT SORT is carried through unchanged rather
 *                        than collapsed to `numeric`: an `Optional Int`'s
 *                        payload is an Int, and answering `numeric` here would
 *                        throw away the integrality of exactly the symbol that
 *                        reaches the arithmetic - which is where it is worth
 *                        something.
 *
 * Nothing is walked THROUGH `$value`: `<path>.$value.<field>` answers null
 * rather than descending into the payload's record, because the payload is a
 * value the walk has no declaration-level handle on beyond its own type.
 *
 * @param {Object} ctx     the interning context `start` is expressed against
 * @param {{module: string, name: string}} start  the record to begin at
 * @param {string[]} segments  field names, outermost first
 */
export function resolveFieldSort(ctx, start, segments) {
  if (!ctx || !start || !start.module || !start.name || !segments.length) return null;
  let cur = ctx;
  let ref = { module: start.module, name: start.name };

  for (let i = 0; i < segments.length; i++) {
    const entry = cur.dataTypes && cur.dataTypes.get(`${ref.module}:${ref.name}`);
    if (!entry || entry.kind !== 'record' || !entry.fields) return null;
    const field = entry.fields.get(segments[i]);
    if (!field) return null;

    if (field.sort === 'optional') {
      const elem = (field.elem && field.elem.sort) || 'unknown';
      const rest = segments.length - (i + 1);
      if (rest === 0) return elem === 'unknown' ? null : `optional:${elem}`;
      if (rest === 1 && segments[i + 1] === '$some') return 'bool';
      if (rest === 1 && segments[i + 1] === '$value') return isNumericSort(elem) ? elem : null;
      return null;
    }

    if (i === segments.length - 1) return field.sort === 'unknown' ? null : field.sort;
    // Not the last segment: the only thing we can step THROUGH is a record.
    if (field.sort !== 'record' || !field.ref || !field.ref.module) return null;
    if (field.ref.external) {
      // The nested record is declared in a dependency; its field types live in
      // that package's own table, against its own interning context.
      const next = cur.getImportedPackage ? cur.getImportedPackage(field.ref.packageRef) : null;
      if (!next) return null;
      cur = next;
    }
    ref = { module: field.ref.module, name: field.ref.name };
  }
  return null;
}

/**
 * The record a Type denotes, as the `{pkg, module, name}` a field walk starts
 * from - or null when the type is not a record this archive can read.
 *
 * Used to root a symbol's projection path: at the template's own record for
 * `this`, and at the choice argument's record for `arg`.
 */
function recordTypeRef(type, ctx) {
  const cls = classifyType(type, ctx);
  if (!cls || cls.sort !== 'record') return null;
  return resolveConRef(cls.ref, ctx);
}

/**
 * The record a TypeConId names, as a `{pkg, module, name}` - or null.
 *
 * Separate from recordTypeRef because a `create` addresses its target with a
 * bare TypeConId rather than with a Type, and the created record's own field
 * types are what say whether the field a create ASSIGNS is a number. That is a
 * different question from what the assigned VALUE is, and it is the one the
 * non-negativity property is actually about: a value the translation could not
 * read still lands in a field whose declared type is known.
 */
function recordRefOfTycon(tycon, ctx) {
  return resolveConRef(typeConName(tycon, ctx), ctx);
}

/**
 * The enum/variant a TypeConId names: `{pkg, module, name, kind, constructors,
 * sortName}`, or null.
 *
 * `sortName` IDENTIFIES the type the way lfir.js's `ufName` identifies a
 * function, and for the same reason: it becomes an SMT sort declared with a
 * fixed constructor list, and two different Daml types sharing one sort would
 * assert that their values are drawn from one set - an assumption, not a
 * relaxation, and assumptions can make an unsat spurious. The id of the
 * DECLARING package is therefore part of the name.
 */
function dataConRefOfTycon(tycon, ctx) {
  const ref = typeConName(tycon, ctx);
  if (!ref || !ref.module) return null;
  let target = ctx;
  if (ref.external) {
    target = ctx.getImportedPackage ? ctx.getImportedPackage(ref.packageRef) : null;
    if (!target) return null;
  }
  const entry = target.dataTypes && target.dataTypes.get(`${ref.module}:${ref.name}`);
  if (!entry || (entry.kind !== 'enum' && entry.kind !== 'variant')) return null;
  if (!Array.isArray(entry.constructors) || entry.constructors.length === 0) return null;
  const pid = String(target.selfPackageId || 'self').slice(0, 8);
  return {
    pkg: target,
    module: ref.module,
    name: ref.name,
    kind: entry.kind,
    constructors: entry.constructors.slice(),
    sortName: `${entry.kind} ${ref.module}:${ref.name}@${pid}`,
  };
}

/** Shared tail of the two above: hop to the declaring package, check the kind. */
function resolveConRef(ref, ctx) {
  if (!ref || !ref.module) return null;
  let target = ctx;
  if (ref.external) {
    target = ctx.getImportedPackage ? ctx.getImportedPackage(ref.packageRef) : null;
    if (!target) return null;
  }
  const entry = target.dataTypes && target.dataTypes.get(`${ref.module}:${ref.name}`);
  if (!entry || entry.kind !== 'record') return null;
  return { pkg: target, module: ref.module, name: ref.name };
}

/** A readable rendering of a Type, for view types and key types. */
function typeName(type, ctx, depth = 0) {
  if (!type || depth > 6) return null;
  if (has(type, S.Type.internedType)) {
    return typeName(ctx.internedTypes[int(type, S.Type.internedType)], ctx, depth + 1);
  }
  const con = sub(type, S.Type.con);
  if (con) {
    const ref = typeConName(sub(con, S.TypeCon.tycon), ctx);
    if (ref) {
      const args = subs(con, S.TypeCon.args)
        .map((a) => typeName(a, ctx, depth + 1))
        .filter(Boolean);
      return args.length ? `${ref.name} ${args.join(' ')}` : ref.name;
    }
  }
  return null;
}

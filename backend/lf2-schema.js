// backend/lf2-schema.js
//
// The schema surface the DALF decoder reads.
//
// There are NO field numbers in this file. Every number comes from
// `lf2-schema.generated.js`, which is produced by `npm run codegen` from the
// vendored official protos (see backend/proto/PROVENANCE.md). What lives here
// is only the two things a schema cannot tell you:
//
//   1. Aliases, mapping the names the decoder uses to fully qualified message
//      names. These resolve through `message()`, which throws on an unknown
//      name, so a wrong alias fails immediately and loudly - unlike a wrong
//      field number, which fails silently.
//   2. Semantics: which `Update` cases count as which access-graph operation,
//      and which LF minor versions the decoder has actually been checked on.
//      Those are decisions, not facts about the schema.
//
// The bug this structure exists to prevent was real. `Expr.RecProj` and
// `Expr.RecUpd` are near-identical messages whose `field_interned_str` sit in
// slots 4 and 2. Transcribing RecUpd's number for RecProj throws nothing: it
// just makes every signatory, observer and controller expression come back
// empty, so a package decodes "successfully" with no stakeholders at all.

import * as G from './lf2-schema.generated.js';

export { MESSAGES, ENUMS, PROVENANCE, message } from './lf2-schema.generated.js';

/**
 * LF 2 minor versions the decoder has been exercised against end to end.
 * A package outside this list still decodes (field numbers are additive within
 * LF 2) but is flagged, because "probably fine" is not the same as "checked".
 */
export const CHECKED_AGAINST_MINOR = ['1', '2', '3'];

// ---------------------------------------------------------------- envelope
export const Archive = G.message('Archive');
export const ArchivePayload = G.message('ArchivePayload');

// ----------------------------------------------------------------- package
export const Package = G.message('Package');
export const PackageMetadata = G.message('PackageMetadata');
export const PackageImports = G.message('PackageImports');
export const InternedDottedName = G.message('InternedDottedName');
export const Module = G.message('Module');

// ------------------------------------------------------------- definitions
export const DefValue = G.message('DefValue');
export const NameWithType = G.message('DefValue.NameWithType');
export const ValueId = G.message('ValueId');
export const DefTemplate = G.message('DefTemplate');
export const DefKey = G.message('DefTemplate.DefKey');
export const Implements = G.message('DefTemplate.Implements');
export const InterfaceInstanceBody = G.message('InterfaceInstanceBody');
export const InterfaceInstanceMethod = G.message('InterfaceInstanceBody.InterfaceInstanceMethod');
export const DefInterface = G.message('DefInterface');
export const InterfaceMethod = G.message('InterfaceMethod');
export const TemplateChoice = G.message('TemplateChoice');

// ------------------------------------------------------------------- names
export const TypeConId = G.message('TypeConId');
export const ModuleId = G.message('ModuleId');
export const SelfOrImportedPackageId = G.message('SelfOrImportedPackageId');

// --------------------------------------------------------------- source spans
export const Location = G.message('Location');
export const Range = G.message('Location.Range');

// ------------------------------------------------------------------- types
export const Type = G.message('Type');
export const TypeCon = G.message('Type.Con');

// ------------------------------------------------------------- expressions
export const Expr = G.message('Expr');
export const RecProj = G.message('Expr.RecProj');
export const RecUpd = G.message('Expr.RecUpd');
export const RecCon = G.message('Expr.RecCon');
export const StructProj = G.message('Expr.StructProj');
export const Cons = G.message('Expr.Cons');
export const FieldWithExpr = G.message('FieldWithExpr');
export const VarWithType = G.message('VarWithType');
export const Block = G.message('Block');
export const Case = G.message('Case');
export const CaseAlt = G.message('CaseAlt');
export const OptionalSomeAlt = G.message('CaseAlt.OptionalSome');
export const Binding = G.message('Binding');
export const BuiltinLit = G.message('BuiltinLit');
export const CallInterface = G.message('Expr.CallInterface');

// ------------------------------------------------------------------ update
export const Update = G.message('Update');

/**
 * Which `Update` oneof cases map to which access-graph operation kind, and
 * where each case names its target and choice.
 *
 * The case-to-kind mapping is a decision (an `ExerciseInterface` is reported as
 * an `exercise` against an interface). The FIELD NUMBERS are read out of the
 * generated schema, so an upstream renumbering, or a new `arg`/`guard` field,
 * cannot silently desynchronise this table - it throws instead.
 */
function updateOp(caseMessage, kind, { byInterface = false } = {}) {
  const m = G.message(caseMessage);
  const targetField = byInterface ? m.interface : m.template;
  if (targetField === undefined) {
    throw new Error(
      `lf2-schema: ${caseMessage} has no ${byInterface ? '`interface`' : '`template`'} field; ` +
        'the schema changed shape and UPDATE_OPS needs revisiting.'
    );
  }
  return {
    kind,
    targetField,
    ...(m.choiceInternedStr !== undefined ? { choiceField: m.choiceInternedStr } : {}),
    ...(byInterface ? { byInterface: true } : {}),
  };
}

export const UPDATE_OPS = {
  [Update.create]: updateOp('Update.Create', 'create'),
  [Update.createInterface]: updateOp('Update.CreateInterface', 'create', { byInterface: true }),
  [Update.exercise]: updateOp('Update.Exercise', 'exercise'),
  [Update.exerciseInterface]: updateOp('Update.ExerciseInterface', 'exercise', { byInterface: true }),
  [Update.exerciseByKey]: updateOp('Update.ExerciseByKey', 'exerciseByKey'),
  [Update.fetch]: updateOp('Update.Fetch', 'fetch'),
  [Update.fetchInterface]: updateOp('Update.FetchInterface', 'fetch', { byInterface: true }),
  [Update.fetchByKey]: updateOp('Update.RetrieveByKey', 'fetchByKey'),
  [Update.lookupByKey]: updateOp('Update.RetrieveByKey', 'lookupByKey'),
};

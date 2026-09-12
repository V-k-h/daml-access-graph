// backend/lf2-schema.generated.js
//
// GENERATED FILE - DO NOT EDIT.
// Regenerate with:  npm run codegen
//
// Source of truth: the vendored Daml-LF protobuf schemas.
//   repo:    github.com/digital-asset/daml
//   tag:     v3.4.11
//   path:    sdk/daml-lf/archive/src/protobuf/com/digitalasset/daml/lf/archive/
//   license: Apache-2.0
//
// See backend/proto/PROVENANCE.md for why these are generated rather than
// transcribed, and tests/codegen.test.js for the drift check.

export const PROVENANCE = {
  "repo": "github.com/digital-asset/daml",
  "tag": "v3.4.11",
  "path": "sdk/daml-lf/archive/src/protobuf/com/digitalasset/daml/lf/archive/",
  "license": "Apache-2.0"
};

/** Field numbers for every message, keyed by fully qualified name. */
export const MESSAGES = {
  "Archive": { "hashFunction": 1, "payload": 3, "hash": 4 },
  "ArchivePayload": { "damlLf1": 2, "minor": 3, "damlLf2": 4, "patch": 5 },
  "Binding": { "binder": 1, "bound": 2 },
  "Block": { "bindings": 1, "body": 2 },
  "BuiltinLit": { "int64": 1, "timestamp": 2, "numericInternedStr": 3, "textInternedStr": 4, "date": 5, "failureCategory": 6, "roundingMode": 1001 },
  "Case": { "scrut": 1, "alts": 2 },
  "CaseAlt": { "body": 1, "default": 2, "variant": 3, "builtinCon": 4, "nil": 5, "cons": 6, "optionalNone": 7, "optionalSome": 8, "enum": 9 },
  "CaseAlt.Cons": { "varHeadInternedStr": 1, "varTailInternedStr": 2 },
  "CaseAlt.Enum": { "con": 1, "constructorInternedStr": 2 },
  "CaseAlt.OptionalSome": { "varBodyInternedStr": 1 },
  "CaseAlt.Variant": { "con": 1, "variantInternedStr": 2, "binderInternedStr": 3 },
  "DefDataType": { "location": 1, "nameInternedDname": 2, "params": 3, "serializable": 4, "record": 5, "variant": 6, "enum": 7, "interface": 8 },
  "DefDataType.EnumConstructors": { "constructorsInternedStr": 2 },
  "DefDataType.Fields": { "fields": 1 },
  "DefException": { "nameInternedDname": 1, "location": 2, "message": 3 },
  "DefInterface": { "location": 1, "tyconInternedDname": 2, "methods": 3, "paramInternedStr": 4, "choices": 5, "view": 6, "requires": 7 },
  "DefTemplate": { "tyconInternedDname": 1, "paramInternedStr": 2, "precond": 3, "signatories": 4, "choices": 6, "observers": 7, "location": 8, "key": 9, "implements": 10 },
  "DefTemplate.DefKey": { "type": 1, "maintainers": 3, "keyExpr": 4 },
  "DefTemplate.Implements": { "interface": 1, "body": 2, "location": 3 },
  "DefTypeSyn": { "location": 1, "nameInternedDname": 2, "params": 3, "type": 4 },
  "DefValue": { "location": 1, "nameWithType": 2, "expr": 3 },
  "DefValue.NameWithType": { "nameInternedDname": 1, "type": 2 },
  "Expr": { "location": 1, "varInternedStr": 2, "val": 3, "builtin": 4, "builtinCon": 5, "builtinLit": 6, "recCon": 7, "recProj": 8, "recUpd": 9, "variantCon": 10, "enumCon": 11, "structCon": 12, "structProj": 13, "structUpd": 14, "app": 15, "tyApp": 16, "abs": 17, "tyAbs": 18, "case": 19, "let": 20, "nil": 21, "cons": 22, "update": 23, "optionalNone": 25, "optionalSome": 26, "toAny": 27, "fromAny": 28, "typeRep": 29, "toAnyException": 30, "fromAnyException": 31, "throw": 32, "toInterface": 33, "fromInterface": 34, "callInterface": 35, "signatoryInterface": 36, "observerInterface": 37, "viewInterface": 38, "unsafeFromInterface": 39, "interfaceTemplateTypeRep": 40, "toRequiredInterface": 41, "fromRequiredInterface": 42, "unsafeFromRequiredInterface": 43, "internedExpr": 44, "choiceController": 1001, "choiceObserver": 1002, "experimental": 9999 },
  "Expr.Abs": { "param": 1, "body": 2 },
  "Expr.App": { "fun": 1, "args": 2 },
  "Expr.CallInterface": { "interfaceType": 1, "methodInternedName": 2, "interfaceExpr": 3 },
  "Expr.ChoiceController": { "template": 1, "choiceInternedStr": 2, "contractExpr": 3, "choiceArgExpr": 4 },
  "Expr.ChoiceObserver": { "template": 1, "choiceInternedStr": 2, "contractExpr": 3, "choiceArgExpr": 4 },
  "Expr.Cons": { "type": 1, "front": 2, "tail": 3 },
  "Expr.EnumCon": { "tycon": 1, "enumConInternedStr": 2 },
  "Expr.Experimental": { "name": 1, "type": 2 },
  "Expr.FromAny": { "type": 1, "expr": 2 },
  "Expr.FromAnyException": { "type": 1, "expr": 2 },
  "Expr.FromInterface": { "interfaceType": 1, "templateType": 2, "interfaceExpr": 3 },
  "Expr.FromRequiredInterface": { "requiredInterface": 1, "requiringInterface": 2, "expr": 3 },
  "Expr.InterfaceTemplateTypeRep": { "interface": 1, "expr": 2 },
  "Expr.Nil": { "type": 1 },
  "Expr.ObserverInterface": { "interface": 1, "expr": 2 },
  "Expr.OptionalNone": { "type": 1 },
  "Expr.OptionalSome": { "type": 1, "value": 2 },
  "Expr.RecCon": { "tycon": 1, "fields": 2 },
  "Expr.RecProj": { "tycon": 1, "record": 3, "fieldInternedStr": 4 },
  "Expr.RecUpd": { "tycon": 1, "fieldInternedStr": 2, "record": 3, "update": 4 },
  "Expr.SignatoryInterface": { "interface": 1, "expr": 2 },
  "Expr.StructCon": { "fields": 1 },
  "Expr.StructProj": { "fieldInternedStr": 1, "struct": 2 },
  "Expr.StructUpd": { "fieldInternedStr": 1, "struct": 2, "update": 3 },
  "Expr.Throw": { "returnType": 1, "exceptionType": 2, "exceptionExpr": 3 },
  "Expr.ToAny": { "type": 1, "expr": 2 },
  "Expr.ToAnyException": { "type": 1, "expr": 2 },
  "Expr.ToInterface": { "interfaceType": 1, "templateType": 2, "templateExpr": 3 },
  "Expr.ToRequiredInterface": { "requiredInterface": 1, "requiringInterface": 2, "expr": 3 },
  "Expr.TyAbs": { "param": 1, "body": 2 },
  "Expr.TyApp": { "expr": 1, "types": 2 },
  "Expr.UnsafeFromInterface": { "interfaceType": 1, "templateType": 2, "contractIdExpr": 3, "interfaceExpr": 4 },
  "Expr.UnsafeFromRequiredInterface": { "requiredInterface": 1, "requiringInterface": 2, "contractIdExpr": 3, "interfaceExpr": 4 },
  "Expr.VariantCon": { "tycon": 1, "variantConInternedStr": 2, "variantArg": 3 },
  "Expr.ViewInterface": { "interface": 1, "expr": 2 },
  "FeatureFlags": { "forbidPartyLiterals": 1, "dontDivulgeContractIdsInCreateArguments": 2, "dontDiscloseNonConsumingChoicesToObservers": 3 },
  "FieldWithExpr": { "expr": 2, "fieldInternedStr": 3 },
  "FieldWithType": { "type": 2, "fieldInternedStr": 3 },
  "InterfaceInstanceBody": { "methods": 1, "view": 2 },
  "InterfaceInstanceBody.InterfaceInstanceMethod": { "methodInternedName": 1, "value": 2 },
  "InterfaceMethod": { "location": 1, "methodInternedName": 2, "type": 3 },
  "InternedDottedName": { "segmentsInternedStr": 1 },
  "Kind": { "star": 1, "arrow": 2, "nat": 3, "internedKind": 4 },
  "Kind.Arrow": { "params": 1, "result": 2 },
  "Location": { "module": 1, "range": 2 },
  "Location.Range": { "startLine": 1, "startCol": 2, "endLine": 3, "endCol": 4 },
  "Module": { "nameInternedDname": 1, "flags": 2, "synonyms": 3, "dataTypes": 4, "values": 5, "templates": 6, "exceptions": 7, "interfaces": 8 },
  "ModuleId": { "packageId": 1, "moduleNameInternedDname": 2 },
  "Package": { "modules": 1, "internedStrings": 2, "internedDottedNames": 3, "metadata": 4, "internedTypes": 5, "internedKinds": 6, "internedExprs": 7, "noImportedPackagesReason": 8, "packageImports": 9 },
  "PackageImports": { "importedPackages": 1 },
  "PackageMetadata": { "nameInternedStr": 1, "versionInternedStr": 2, "upgradedPackageId": 3 },
  "Pure": { "type": 1, "expr": 2 },
  "SelfOrImportedPackageId": { "selfPackageId": 1, "importedPackageIdInternedStr": 3, "packageImportId": 4 },
  "TemplateChoice": { "location": 1, "nameInternedStr": 2, "consuming": 3, "controllers": 4, "observers": 5, "argBinder": 6, "retType": 8, "update": 9, "selfBinderInternedStr": 10, "authorizers": 1001 },
  "Type": { "var": 1, "con": 2, "builtin": 3, "forall": 4, "struct": 5, "nat": 6, "syn": 7, "internedType": 8, "tapp": 9 },
  "Type.Builtin": { "builtin": 1, "args": 2 },
  "Type.Con": { "tycon": 1, "args": 2 },
  "Type.Forall": { "vars": 1, "body": 2 },
  "Type.Struct": { "fields": 1 },
  "Type.Syn": { "tysyn": 1, "args": 2 },
  "Type.TApp": { "lhs": 1, "rhs": 2 },
  "Type.Var": { "args": 2, "varInternedStr": 3 },
  "TypeConId": { "module": 1, "nameInternedDname": 2 },
  "TypeSynId": { "module": 1, "nameInternedDname": 2 },
  "TypeVarWithKind": { "kind": 2, "varInternedStr": 3 },
  "Unit": {  },
  "Update": { "pure": 1, "block": 2, "create": 3, "exercise": 4, "fetch": 5, "getTime": 6, "embedExpr": 7, "lookupByKey": 8, "fetchByKey": 9, "exerciseByKey": 10, "tryCatch": 11, "createInterface": 12, "exerciseInterface": 13, "fetchInterface": 14, "ledgerTimeLt": 15 },
  "Update.Create": { "template": 1, "expr": 2 },
  "Update.CreateInterface": { "interface": 1, "expr": 2 },
  "Update.EmbedExpr": { "type": 1, "body": 2 },
  "Update.Exercise": { "template": 1, "cid": 3, "arg": 5, "choiceInternedStr": 6 },
  "Update.ExerciseByKey": { "template": 1, "choiceInternedStr": 2, "key": 3, "arg": 4 },
  "Update.ExerciseInterface": { "interface": 1, "choiceInternedStr": 2, "cid": 3, "arg": 4, "guard": 5 },
  "Update.Fetch": { "template": 1, "cid": 2 },
  "Update.FetchInterface": { "interface": 1, "cid": 2 },
  "Update.RetrieveByKey": { "template": 1 },
  "Update.TryCatch": { "returnType": 1, "tryExpr": 2, "varInternedStr": 3, "catchExpr": 4 },
  "UpgradedPackageId": { "upgradedPackageIdInternedStr": 1 },
  "ValueId": { "module": 1, "nameInternedDname": 2 },
  "VarWithType": { "type": 2, "varInternedStr": 3 },
};

/** Enum values, keyed by fully qualified name. */
export const ENUMS = {
  "BuiltinCon": { "CON_UNIT": 0, "CON_FALSE": 1, "CON_TRUE": 2 },
  "BuiltinFunction": { "TRACE": 0, "ERROR": 1, "EQUAL": 2, "LESS_EQ": 3, "LESS": 4, "GREATER_EQ": 5, "GREATER": 6, "ADD_INT64": 7, "SUB_INT64": 8, "MUL_INT64": 9, "DIV_INT64": 10, "MOD_INT64": 11, "EXP_INT64": 12, "ADD_NUMERIC": 13, "SUB_NUMERIC": 14, "MUL_NUMERIC": 15, "DIV_NUMERIC": 16, "ROUND_NUMERIC": 17, "CAST_NUMERIC": 18, "SHIFT_NUMERIC": 19, "INT64_TO_NUMERIC": 20, "NUMERIC_TO_INT64": 21, "INT64_TO_TEXT": 22, "NUMERIC_TO_TEXT": 23, "TIMESTAMP_TO_TEXT": 25, "DATE_TO_TEXT": 26, "PARTY_TO_TEXT": 27, "TEXT_TO_PARTY": 28, "TEXT_TO_INT64": 29, "TEXT_TO_NUMERIC": 30, "CONTRACT_ID_TO_TEXT": 31, "SHA256_TEXT": 32, "EXPLODE_TEXT": 33, "APPEND_TEXT": 34, "IMPLODE_TEXT": 35, "CODE_POINTS_TO_TEXT": 36, "TEXT_TO_CODE_POINTS": 37, "DATE_TO_UNIX_DAYS": 38, "UNIX_DAYS_TO_DATE": 39, "TIMESTAMP_TO_UNIX_MICROSECONDS": 40, "UNIX_MICROSECONDS_TO_TIMESTAMP": 41, "COERCE_CONTRACT_ID": 42, "FOLDL": 43, "FOLDR": 44, "EQUAL_LIST": 45, "GENMAP_EMPTY": 52, "GENMAP_INSERT": 53, "GENMAP_LOOKUP": 54, "GENMAP_DELETE": 55, "GENMAP_KEYS": 56, "GENMAP_VALUES": 57, "GENMAP_SIZE": 58, "TEXTMAP_EMPTY": 60, "TEXTMAP_INSERT": 61, "TEXTMAP_LOOKUP": 62, "TEXTMAP_DELETE": 63, "TEXTMAP_TO_LIST": 64, "TEXTMAP_SIZE": 65, "ANY_EXCEPTION_MESSAGE": 59, "FAIL_WITH_STATUS": 66, "KECCAK256_TEXT": 67, "SECP256K1_BOOL": 68, "HEX_TO_TEXT": 69, "TEXT_TO_HEX": 70, "SHA256_HEX": 71, "SECP256K1_WITH_ECDSA_BOOL": 72, "SCALE_BIGNUMERIC": 2001, "PRECISION_BIGNUMERIC": 2002, "ADD_BIGNUMERIC": 2003, "SUB_BIGNUMERIC": 2004, "MUL_BIGNUMERIC": 2005, "DIV_BIGNUMERIC": 2006, "SHIFT_RIGHT_BIGNUMERIC": 2007, "BIGNUMERIC_TO_NUMERIC": 2008, "NUMERIC_TO_BIGNUMERIC": 2009, "BIGNUMERIC_TO_TEXT": 2010, "TYPE_REP_TYCON_NAME": 3011, "TEXT_TO_CONTRACT_ID": 4001, "SECP256K1_VALIDATE_KEY": 4002 },
  "BuiltinLit.FailureCategory": { "INVALID_INDEPENDENT_OF_SYSTEM_STATE": 0, "INVALID_GIVEN_CURRENT_SYSTEM_STATE_OTHER": 1 },
  "BuiltinLit.RoundingMode": { "UP": 0, "DOWN": 1, "CEILING": 2, "FLOOR": 3, "HALF_UP": 4, "HALF_DOWN": 5, "HALF_EVEN": 6, "UNNECESSARY": 7 },
  "BuiltinType": { "UNIT": 0, "BOOL": 1, "INT64": 2, "DATE": 3, "TIMESTAMP": 4, "NUMERIC": 5, "PARTY": 6, "TEXT": 7, "CONTRACT_ID": 8, "OPTIONAL": 9, "LIST": 10, "GENMAP": 11, "ANY": 13, "ANY_EXCEPTION": 14, "TYPE_REP": 15, "ARROW": 16, "UPDATE": 17, "FAILURE_CATEGORY": 18, "TEXTMAP": 19, "BIGNUMERIC": 1002, "ROUNDING_MODE": 1003 },
  "HashFunction": { "SHA256": 0 },
};

// Convenience named exports. A simple name is exported only when it is
// UNIQUE across the schemas; an ambiguous one is reachable through MESSAGES
// alone, so a decoder can never silently pick the wrong nesting.
export const Abs = MESSAGES["Expr.Abs"];
export const App = MESSAGES["Expr.App"];
export const Archive = MESSAGES["Archive"];
export const ArchivePayload = MESSAGES["ArchivePayload"];
export const Arrow = MESSAGES["Kind.Arrow"];
export const Binding = MESSAGES["Binding"];
export const Block = MESSAGES["Block"];
export const Builtin = MESSAGES["Type.Builtin"];
export const BuiltinLit = MESSAGES["BuiltinLit"];
export const CallInterface = MESSAGES["Expr.CallInterface"];
export const Case = MESSAGES["Case"];
export const CaseAlt = MESSAGES["CaseAlt"];
export const ChoiceController = MESSAGES["Expr.ChoiceController"];
export const ChoiceObserver = MESSAGES["Expr.ChoiceObserver"];
export const Con = MESSAGES["Type.Con"];
export const Create = MESSAGES["Update.Create"];
export const CreateInterface = MESSAGES["Update.CreateInterface"];
export const DefDataType = MESSAGES["DefDataType"];
export const DefException = MESSAGES["DefException"];
export const DefInterface = MESSAGES["DefInterface"];
export const DefKey = MESSAGES["DefTemplate.DefKey"];
export const DefTemplate = MESSAGES["DefTemplate"];
export const DefTypeSyn = MESSAGES["DefTypeSyn"];
export const DefValue = MESSAGES["DefValue"];
export const EmbedExpr = MESSAGES["Update.EmbedExpr"];
export const Enum = MESSAGES["CaseAlt.Enum"];
export const EnumCon = MESSAGES["Expr.EnumCon"];
export const EnumConstructors = MESSAGES["DefDataType.EnumConstructors"];
export const Exercise = MESSAGES["Update.Exercise"];
export const ExerciseByKey = MESSAGES["Update.ExerciseByKey"];
export const ExerciseInterface = MESSAGES["Update.ExerciseInterface"];
export const Experimental = MESSAGES["Expr.Experimental"];
export const Expr = MESSAGES["Expr"];
export const FeatureFlags = MESSAGES["FeatureFlags"];
export const Fetch = MESSAGES["Update.Fetch"];
export const FetchInterface = MESSAGES["Update.FetchInterface"];
export const FieldWithExpr = MESSAGES["FieldWithExpr"];
export const FieldWithType = MESSAGES["FieldWithType"];
export const Fields = MESSAGES["DefDataType.Fields"];
export const Forall = MESSAGES["Type.Forall"];
export const FromAny = MESSAGES["Expr.FromAny"];
export const FromAnyException = MESSAGES["Expr.FromAnyException"];
export const FromInterface = MESSAGES["Expr.FromInterface"];
export const FromRequiredInterface = MESSAGES["Expr.FromRequiredInterface"];
export const Implements = MESSAGES["DefTemplate.Implements"];
export const InterfaceInstanceBody = MESSAGES["InterfaceInstanceBody"];
export const InterfaceInstanceMethod = MESSAGES["InterfaceInstanceBody.InterfaceInstanceMethod"];
export const InterfaceMethod = MESSAGES["InterfaceMethod"];
export const InterfaceTemplateTypeRep = MESSAGES["Expr.InterfaceTemplateTypeRep"];
export const InternedDottedName = MESSAGES["InternedDottedName"];
export const Kind = MESSAGES["Kind"];
export const Location = MESSAGES["Location"];
export const Module = MESSAGES["Module"];
export const ModuleId = MESSAGES["ModuleId"];
export const NameWithType = MESSAGES["DefValue.NameWithType"];
export const Nil = MESSAGES["Expr.Nil"];
export const ObserverInterface = MESSAGES["Expr.ObserverInterface"];
export const OptionalNone = MESSAGES["Expr.OptionalNone"];
export const Package = MESSAGES["Package"];
export const PackageImports = MESSAGES["PackageImports"];
export const PackageMetadata = MESSAGES["PackageMetadata"];
export const Pure = MESSAGES["Pure"];
export const Range = MESSAGES["Location.Range"];
export const RecCon = MESSAGES["Expr.RecCon"];
export const RecProj = MESSAGES["Expr.RecProj"];
export const RecUpd = MESSAGES["Expr.RecUpd"];
export const RetrieveByKey = MESSAGES["Update.RetrieveByKey"];
export const SelfOrImportedPackageId = MESSAGES["SelfOrImportedPackageId"];
export const SignatoryInterface = MESSAGES["Expr.SignatoryInterface"];
export const Struct = MESSAGES["Type.Struct"];
export const StructCon = MESSAGES["Expr.StructCon"];
export const StructProj = MESSAGES["Expr.StructProj"];
export const StructUpd = MESSAGES["Expr.StructUpd"];
export const Syn = MESSAGES["Type.Syn"];
export const TApp = MESSAGES["Type.TApp"];
export const TemplateChoice = MESSAGES["TemplateChoice"];
export const Throw = MESSAGES["Expr.Throw"];
export const ToAny = MESSAGES["Expr.ToAny"];
export const ToAnyException = MESSAGES["Expr.ToAnyException"];
export const ToInterface = MESSAGES["Expr.ToInterface"];
export const ToRequiredInterface = MESSAGES["Expr.ToRequiredInterface"];
export const TryCatch = MESSAGES["Update.TryCatch"];
export const TyAbs = MESSAGES["Expr.TyAbs"];
export const TyApp = MESSAGES["Expr.TyApp"];
export const Type = MESSAGES["Type"];
export const TypeConId = MESSAGES["TypeConId"];
export const TypeSynId = MESSAGES["TypeSynId"];
export const TypeVarWithKind = MESSAGES["TypeVarWithKind"];
export const Unit = MESSAGES["Unit"];
export const UnsafeFromInterface = MESSAGES["Expr.UnsafeFromInterface"];
export const UnsafeFromRequiredInterface = MESSAGES["Expr.UnsafeFromRequiredInterface"];
export const Update = MESSAGES["Update"];
export const UpgradedPackageId = MESSAGES["UpgradedPackageId"];
export const ValueId = MESSAGES["ValueId"];
export const Var = MESSAGES["Type.Var"];
export const VarWithType = MESSAGES["VarWithType"];
export const Variant = MESSAGES["CaseAlt.Variant"];
export const VariantCon = MESSAGES["Expr.VariantCon"];
export const ViewInterface = MESSAGES["Expr.ViewInterface"];

// Ambiguous simple names, available via MESSAGES only:
//   Cons (Expr.Cons, CaseAlt.Cons)
//   OptionalSome (Expr.OptionalSome, CaseAlt.OptionalSome)

/** Look a message up by qualified name, failing loudly if absent. */
export function message(qualifiedName) {
  const m = MESSAGES[qualifiedName];
  if (!m) throw new Error(`lf2-schema: no such message: ${qualifiedName}`);
  return m;
}

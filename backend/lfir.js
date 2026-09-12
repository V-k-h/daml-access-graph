// backend/lfir.js
//
// Daml-LF expressions -> a small logical IR of GUARDED TRANSITIONS.
//
// This is the piece that closes the gap a hand-written symbolic model leaves
// open. Writing the model by hand establishes `M |= phi` for some model M, but
// leaves `[[C_daml]] = M` unproven and usually undocumented beyond a comment
// listing what was "elided". Deriving the model from the compiled package
// makes that correspondence hold by construction FOR THE FRAGMENT THE
// TRANSLATION COVERS, and the whole design here is about being unable to lie
// about where that fragment ends.
//
// Two rules make that work:
//
//   1. The translation is TOTAL. Every expression maps to a term; anything
//      outside the supported fragment becomes an explicit `unsupported` node
//      carrying a reason. There is no silent default and no elision.
//   2. A transition containing an `unsupported` node in a position the
//      property depends on is reported NOT MODELLABLE. It is never assumed to
//      be harmless, and it never quietly becomes `true`.
//
// So a proof from this pipeline reads: "for the fragment we translated, which
// is enumerated, the property holds". A choice we cannot translate shows up as
// a refusal in the report rather than as a pass.
//
// SEMANTIC CAVEAT, stated once and carried through to every result: Daml's
// `Decimal` is `Numeric 10`, a fixed-point type. This IR models numerics as
// exact rationals. That abstraction is SOUND for properties that do not depend
// on rounding (division-by-zero safety, sign, ordering) and UNSOUND for exact
// value equalities in the presence of rounding. Every rounding or truncating
// builtin is therefore recorded on the transition (`rounding`), and the SMT
// layer refuses conservation-style equalities on transitions that carry it.

// FRAGMENT NOTES beyond the arithmetic core:
//   * Value references are followed ACROSS PACKAGES (an ensure calling a
//     daml-stdlib helper reduces through the stdlib's actual compiled body);
//     readDarRaw wires the cross-package lookup, and an unresolvable
//     reference stays `unsupported`.
//   * Text is modelled at equality only (SMT String sort; see smt.js).
//   * Optional fields are modelled through CASE ANALYSIS as a
//     `<path>.$some : Bool` / `<path>.$value` symbol pair.
//   * `throw`/`error` become `abort` nodes, eliminated exactly where guard
//     semantics allow it (guardConjuncts) and refused everywhere else.
//   * Interface instances: each interface choice is emitted as a transition
//     against each implementing template, dispatching `call_interface`
//     through the instance's method bodies.

import { decodeMessage, sub, subs, one, many, int, has } from './protobuf.js';
import * as S from './lf2-schema.js';

// Builtin numbers come from the generated schema's enum table.
const BF = S.ENUMS.BuiltinFunction;
const BC = S.ENUMS.BuiltinCon;

/** Arithmetic and comparison builtins we can translate faithfully. */
const BINOP = new Map([
  [BF.ADD_INT64, '+'], [BF.SUB_INT64, '-'], [BF.MUL_INT64, '*'],
  [BF.ADD_NUMERIC, '+'], [BF.SUB_NUMERIC, '-'], [BF.MUL_NUMERIC, '*'],
  [BF.DIV_INT64, 'div'], [BF.DIV_NUMERIC, '/'],
  [BF.MOD_INT64, 'mod'],
  [BF.LESS, '<'], [BF.LESS_EQ, '<='], [BF.GREATER, '>'], [BF.GREATER_EQ, '>='],
  [BF.EQUAL, '='],
]);

/**
 * Builtins that round, truncate or change scale. Their presence does not stop
 * translation, but it is recorded, because the exact-rational abstraction stops
 * being sound for value equalities once one of them is on the path.
 *
 * INT64_TO_NUMERIC is deliberately NOT here, though its inverse is. The
 * conversion Int64 -> Numeric is EXACT: every Int64 maps to a rational with
 * no loss. Its only partiality is overflow, when the integer does not fit the
 * target scale, and overflow ABORTS the transaction rather than producing a
 * rounded value. An aborted transaction is not a reachable post-state, so
 * ignoring the overflow case shrinks the state space we quantify over, which
 * is sound for proving universal properties (the same direction as dropping
 * a guard; see the note in smt.js). Treating it as rounding cost real
 * verdicts: it is how `intToDecimal` builds the constant denominators that
 * every scaled division in a Canton perb calculation divides by, so one
 * misfiled builtin made all 104 division sites unadjudicable.
 *
 * NUMERIC_TO_INT64 stays: it truncates, and that is genuine value loss.
 */
const ROUNDING = new Set([
  BF.ROUND_NUMERIC, BF.CAST_NUMERIC, BF.SHIFT_NUMERIC,
  BF.NUMERIC_TO_INT64, BF.DIV_INT64, BF.MOD_INT64,
]);

/**
 * Builtins translated as the identity on the underlying rational value.
 * Exact conversions only: see the INT64_TO_NUMERIC argument above.
 */
const EXACT_CONVERSION = new Set([BF.INT64_TO_NUMERIC]);

const DIVISION = new Set([BF.DIV_NUMERIC, BF.DIV_INT64, BF.MOD_INT64]);

/**
 * Builtins that are the IDENTITY on the value they carry.
 *
 * COERCE_CONTRACT_ID changes only the phantom type of a contract id, never the
 * id, so `toInterfaceContractId cid` and `cid` denote the SAME contract.
 * Modelling it as the identity is exact, and it is what lets the archive loop
 * of a merge be recognised as archiving the very elements the sum ranges over
 * (see collectTraversal): the compiled loop archives
 * `toInterfaceContractId h`, not `h`.
 */
const IDENTITY_BUILTIN = new Set([BF.COERCE_CONTRACT_ID]);

/**
 * Text builtins with a SCALAR signature, modelled as uninterpreted functions.
 *
 * Daml Text manipulation has no counterpart in the arithmetic-plus-Strings
 * fragment the emitter speaks, but an operation whose arguments and result are
 * all scalars still has a signature the emitter can DECLARE. Replacing it by
 * an uninterpreted symbol of that signature keeps the surrounding guard
 * assertable instead of dropping it. The cost is asymmetric and spelled out in
 * smt.js: unsat still proves, sat may be an artifact.
 *
 * `arity` counts VALUE arguments from the end of the spine, the way BINOP
 * does, because scale and dictionary arguments sit in front. `argSorts` and
 * `sort` are read off the builtin's fixed LF type, so they are facts, not
 * guesses - and pinning them is what keeps two uses of the same symbol from
 * looking like two different signatures.
 *
 * Deliberately ABSENT: EXPLODE_TEXT ([Text]), IMPLODE_TEXT ([Text] -> Text),
 * TEXT_TO_CODE_POINTS ([Int]), CODE_POINTS_TO_TEXT, the GENMAP and TEXTMAP
 * families, and
 * TEXT_TO_INT64 / TEXT_TO_NUMERIC / TEXT_TO_PARTY. Each has a list, a map or
 * an Optional on one side, and the emitter's sort set is Bool/Real/Int/String
 * with nothing to declare such a symbol against. They stay `unsupported` with
 * that reason - and they are exactly what makes a whole enclosing predicate
 * eligible for abstraction instead (see textOpaqueUf).
 */
const TEXT_UF_BUILTIN = new Map([
  [BF.APPEND_TEXT, { arity: 2, argSorts: ['String', 'String'], sort: 'String' }],
  [BF.SHA256_TEXT, { arity: 1, argSorts: ['String'], sort: 'String' }],
  [BF.KECCAK256_TEXT, { arity: 1, argSorts: ['String'], sort: 'String' }],
  [BF.SHA256_HEX, { arity: 1, argSorts: ['String'], sort: 'String' }],
  [BF.HEX_TO_TEXT, { arity: 1, argSorts: ['String'], sort: 'String' }],
  [BF.TEXT_TO_HEX, { arity: 1, argSorts: ['String'], sort: 'String' }],
  [BF.INT64_TO_TEXT, { arity: 1, argSorts: ['Real'], sort: 'String' }],
  [BF.NUMERIC_TO_TEXT, { arity: 1, argSorts: ['Real'], sort: 'String' }],
  [BF.TIMESTAMP_TO_TEXT, { arity: 1, argSorts: ['Real'], sort: 'String' }],
  [BF.DATE_TO_TEXT, { arity: 1, argSorts: ['Real'], sort: 'String' }],
]);

/**
 * Text builtins whose presence in a refused translation identifies the
 * obstacle as A TEXT CHAIN, which is what makes an enclosing named function
 * eligible to be abstracted as a single uninterpreted symbol. Everything in
 * TEXT_UF_BUILTIN is here too, plus the list-valued ones that cannot be
 * abstracted on their own.
 */
const TEXT_OPAQUE_BUILTIN = new Set([
  ...TEXT_UF_BUILTIN.keys(),
  BF.EXPLODE_TEXT,
  BF.IMPLODE_TEXT,
  BF.TEXT_TO_CODE_POINTS,
  BF.CODE_POINTS_TO_TEXT,
  BF.TEXT_TO_INT64,
  BF.TEXT_TO_NUMERIC,
  BF.TEXT_TO_PARTY,
  BF.TEXT_TO_CONTRACT_ID,
  BF.CONTRACT_ID_TO_TEXT,
  BF.PARTY_TO_TEXT,
]);

/** Default list-length bound for fold/traversal unrolling (`--bound N`). */
export const DEFAULT_BOUND = 3;

/**
 * Compiled stdlib functions that traverse a list ELEMENTWISE, IN ORDER, and
 * WITHOUT changing its length, keyed by the fully qualified name of the
 * compiled value the application spine resolves to. The name is read out of
 * the DAR's own value table (resolveValue), not guessed from source.
 *
 * WHY THIS TABLE EXISTS. Element symbols are keyed to the LIST THEY RANGE
 * OVER (listNameOfExpr), and that is the whole reason a merge can be stated
 * correctly. A compiled merge fetches its inputs with
 * `tokens <- mapA fetch arg.holdings`, folds over `tokens`, and archives
 * `arg.holdings`. If `tokens` were named after itself, the fold would speak
 * about `tokens$i.amount` and the archive loop about `arg.holdings$i`, the
 * conservation goal would relate two unrelated families of free symbols, and
 * the solver would hand back a spurious counterexample. Because these
 * functions preserve length and index, element i of the result IS derived
 * from element i of the source, so naming both after the source is exact.
 *
 * `fn` and `list` are positions in the FLATTENED spine counted from the end,
 * because the number of dictionary arguments in front varies.
 *
 * The table is deliberately limited to shapes VERIFIED against compiled
 * packages (both entries below occur in canton-tokens.dar and were read out
 * of it). An unrecognised traversal is not guessed at: the list stays
 * unnameable and the dependent property refuses.
 */
const LIST_TRAVERSALS = new Map([
  ['DA.Internal.Prelude:mapA', { fn: -2, list: -1 }],
  ['DA.Foldable:mapA_', { fn: -2, list: -1 }],
]);

/**
 * The choice whose exercise is recognised as ARCHIVING its target.
 *
 * Only `Archive` qualifies, and the restriction is load-bearing rather than
 * lazy: conservation with archived inputs states
 * `sum(created) = this.amount + sum(archived)`. If a choice that does NOT
 * consume its target were counted as archived, that goal would excuse a
 * transition which mints the inputs' amounts into the created contract
 * without consuming them - a spurious PROVED. Every other exercise inside a
 * traversal therefore keeps the `consumesOthers` refusal.
 */
const ARCHIVING_CHOICE = 'Archive';

// --------------------------------------------------------------------- terms

export const T = {
  num: (v) => ({ k: 'num', v }),
  /** A Text literal. Rendered as an SMT-LIB String literal (see smt.js). */
  str: (v) => ({ k: 'str', v }),
  /**
   * A whole record in scope, not a scalar. The choice body is compiled as a
   * curried application of a hoisted worker to `this`, `self` and `arg`, so
   * the template record reaches the arithmetic through lambda parameters with
   * other names. Carrying the record's identity as a term is what lets a
   * projection off any of those aliases resolve back to `this.field`.
   */
  record: (root) => ({ k: 'record', root }),
  bool: (v) => ({ k: 'bool', v }),
  varRef: (name, sort) => ({ k: 'var', name, sort }),
  app: (op, args) => ({ k: 'app', op, args }),
  ite: (c, a, b) => ({ k: 'ite', c, a, b }),
  /**
   * An expression that ABORTS the transaction (`throw`, `error`). Unlike
   * `unsupported` this is a shape we understand exactly: on any successful
   * path it was not evaluated to completion. `guardConjuncts` uses that to
   * turn `if c then True else throw ...` into the assumption `c`; anywhere
   * an abort survives to a position we cannot eliminate, it degrades to
   * `unsupported` so it can never be asserted or proved over.
   */
  abort: (why) => ({ k: 'abort', why }),
  /**
   * An UNINTERPRETED APPLICATION: a named function symbol of fixed arity,
   * applied to translated arguments, with no definition attached.
   *
   * This is how an operation the fragment cannot express - Daml Text
   * manipulation, essentially - is kept in a guard instead of being dropped.
   * The soundness argument lives in smt.js's header and is asymmetric:
   * replacing a concrete function by an uninterpreted one ENLARGES the model
   * class, so an unsat still proves the property, while a sat may be an
   * artifact of an interpretation the real function never takes. Anything a
   * verdict is drawn from must therefore report which UFs it used.
   *
   * `name` must IDENTIFY the function (see ufName): two different Daml
   * functions sharing a symbol would be an assumption that they are equal,
   * and assumptions - unlike relaxations - can make an unsat spurious.
   *
   * `sort` is the result sort when the translation knows it (APPEND_TEXT is
   * String by signature) and null when it does not, in which case smt.js
   * infers it from the position the application is used in.
   */
  uf: (name, args, sort = null, argSorts = null) => ({ k: 'uf', name, args, sort, argSorts }),
  /**
   * A fold over a NAMED list, UNROLLED at every list length 0..bound.
   *
   * `unrolled[k]` is the term the fold denotes when the list has exactly k
   * elements, with element i standing for the record `<listName>$<i>`; the
   * archive-loop detector produces the same records, so the two agree by
   * construction rather than by coincidence.
   *
   * A fold node NEVER reaches the SMT emitter: a property instantiates it at
   * one k (instantiateFolds), emits one query per k, and the verdict prints
   * the bound. Uninstantiated it counts as unsupported everywhere, so a
   * property that does not know about folds drops it exactly as it dropped
   * the `builtin FOLDL is outside the fragment` node it replaces.
   */
  fold: (listName, op, unrolled) => ({ k: 'fold', listName, op, unrolled }),
  unsupported: (why, at) => ({ k: 'unsupported', why, at }),
};

/**
 * Does a term contain anything we could not translate? An un-eliminated
 * `abort` counts: it must never reach the SMT emitter as if it were a value.
 */
export function hasUnsupported(term) {
  if (!term || typeof term !== 'object') return false;
  if (term.k === 'unsupported' || term.k === 'abort') return true;
  // An UNINSTANTIATED fold is not a value: it denotes a different term at
  // every list length. Counting it as unsupported here is what keeps every
  // property that does not opt into bounded reasoning (division-safety, any
  // guard) behaving exactly as it did when a fold was a plain `unsupported`
  // node - it gets dropped or skipped, with the reason reported, never
  // asserted and never proved over.
  if (term.k === 'fold') return true;
  if (term.k === 'app' || term.k === 'uf') return term.args.some(hasUnsupported);
  if (term.k === 'ite') return [term.c, term.a, term.b].some(hasUnsupported);
  return false;
}

/** Collect every `unsupported` (or leftover abort) reason inside a term. */
export function unsupportedReasons(term, out = []) {
  if (!term || typeof term !== 'object') return out;
  if (term.k === 'unsupported') out.push(term);
  else if (term.k === 'abort') out.push({ k: 'unsupported', why: `abort (${term.why})` });
  else if (term.k === 'fold') {
    out.push({
      k: 'unsupported',
      why:
        `${term.op} over \`${term.listName}\` used where no list length is fixed; ` +
        `only a bounded property instantiates it`,
    });
  } else if (term.k === 'app' || term.k === 'uf') {
    term.args.forEach((a) => unsupportedReasons(a, out));
  } else if (term.k === 'ite') {
    [term.c, term.a, term.b].forEach((a) => unsupportedReasons(a, out));
  }
  return out;
}

/**
 * Replace every fold node by its unrolling at list length `k`.
 *
 * This is the ONLY way a fold becomes a term the emitter can render, and it
 * is what makes a bounded verdict mean something precise: the query the
 * solver saw is the transition's arithmetic for a list of exactly k elements.
 * A k beyond what the fold was unrolled to is a caller bug and degrades to an
 * explicit `unsupported` rather than to a silently shorter list.
 */
export function instantiateFolds(term, k) {
  if (!term || typeof term !== 'object') return term;
  if (term.k === 'fold') {
    const chosen = term.unrolled[k];
    if (chosen === undefined) {
      return T.unsupported(
        `${term.op} over \`${term.listName}\` was unrolled to ${term.unrolled.length - 1} ` +
          `element(s), which does not cover list length ${k}`,
        null
      );
    }
    return instantiateFolds(chosen, k);
  }
  if (term.k === 'app' || term.k === 'uf') {
    return { ...term, args: term.args.map((a) => instantiateFolds(a, k)) };
  }
  if (term.k === 'ite') {
    return {
      ...term,
      c: instantiateFolds(term.c, k),
      a: instantiateFolds(term.a, k),
      b: instantiateFolds(term.b, k),
    };
  }
  return term;
}

/** Names of the lists a term folds over, in encounter order. */
export function foldLists(term, out = new Set()) {
  if (!term || typeof term !== 'object') return out;
  if (term.k === 'fold') {
    out.add(term.listName);
    term.unrolled.forEach((u) => foldLists(u, out));
  } else if (term.k === 'app' || term.k === 'uf') {
    term.args.forEach((a) => foldLists(a, out));
  } else if (term.k === 'ite') {
    [term.c, term.a, term.b].forEach((a) => foldLists(a, out));
  }
  return out;
}

/**
 * Decompose a translated `ensure` (or other Bool guard) into CONJUNCTS that
 * hold on every successful path, dropping nothing silently.
 *
 * Two rewrites, both exact for guard semantics (a guard either evaluates to
 * True or the transaction does not happen - an abort and a False are the same
 * outcome):
 *
 *   ite(c, a, False|abort)  ->  c  AND  a        (the compiled form of &&,
 *                                                 and of `if c then a else throw`)
 *   ite(c, False|abort, b)  ->  (not c)  AND  b
 *
 * Splitting matters for soundness bookkeeping: a guard that is only PARTLY
 * translatable must not be asserted whole, but its independently translatable
 * conjuncts are each implied by the full guard, so keeping those and dropping
 * the rest (with the drop reported) stays sound for proving universals.
 * Any abort that survives outside those positions is degraded to
 * `unsupported`, so downstream checks drop that conjunct rather than assert it.
 */
export function guardConjuncts(term) {
  const out = [];
  const isFail = (t) => t && ((t.k === 'bool' && t.v === false) || t.k === 'abort');
  const walk = (t) => {
    if (!t || typeof t !== 'object') return;
    if (t.k === 'bool' && t.v === true) return; // trivially true: no conjunct
    if (t.k === 'app' && t.op === 'and') {
      t.args.forEach(walk);
      return;
    }
    if (t.k === 'ite') {
      if (isFail(t.b)) {
        walk(t.c);
        walk(t.a);
        return;
      }
      if (isFail(t.a)) {
        walk(T.app('not', [t.c]));
        walk(t.b);
        return;
      }
    }
    out.push(scrubAborts(t));
  };
  walk(term);
  return out;
}

/** Replace any abort that guardConjuncts could not eliminate. */
function scrubAborts(t) {
  if (!t || typeof t !== 'object') return t;
  if (t.k === 'abort') {
    return T.unsupported(`abort (${t.why}) in a guard position the translation cannot eliminate`, null);
  }
  if (t.k === 'app' || t.k === 'uf') return { ...t, args: t.args.map(scrubAborts) };
  if (t.k === 'ite') return { ...t, c: scrubAborts(t.c), a: scrubAborts(t.a), b: scrubAborts(t.b) };
  return t;
}

/** Every division denominator appearing in a term, for division-safety. */
export function divisors(term, out = []) {
  if (!term || typeof term !== 'object') return out;
  if (term.k === 'app') {
    if ((term.op === '/' || term.op === 'div' || term.op === 'mod') && term.args.length === 2) {
      out.push(term.args[1]);
    }
    term.args.forEach((a) => divisors(a, out));
  } else if (term.k === 'uf') {
    term.args.forEach((a) => divisors(a, out));
  } else if (term.k === 'ite') {
    [term.c, term.a, term.b].forEach((a) => divisors(a, out));
  } else if (term.k === 'fold') {
    term.unrolled.forEach((u) => divisors(u, out));
  }
  return out;
}

// ----------------------------------------------------------------- translate

/**
 * Translation context for one choice.
 *
 * `env` maps an LF variable name to a term, which is how `let` bindings and
 * lambda parameters are resolved without substituting into the protobuf.
 */
function makeCtx(pkg, { selfParam, argParam, label, dispatch = null, bound = DEFAULT_BOUND }) {
  const env = new Map();
  if (selfParam) env.set(selfParam, T.record('this'));
  if (argParam) env.set(argParam, T.record('arg'));
  return {
    /**
     * The interning context of the expression CURRENTLY being read. Following
     * a value reference into an imported package (daml-stdlib arithmetic, an
     * interface declared in a sibling package) swaps this for the callee's
     * context and restores it afterwards, because interned string/expression
     * indices only mean anything against their own package's tables.
     */
    pkg,
    /**
     * Interface-instance dispatch, set only when translating an interface
     * choice against one implementing template:
     * `{ methods: Map<name, {expr, pkg}> }` - a `call_interface` on `this`
     * resolves to that template's method body. Null for template choices.
     */
    dispatch,
    selfParam,
    argParam,
    label,
    env,
    /**
     * Variable name -> the RAW protobuf expression it was bound to.
     *
     * The term env is enough for arithmetic, but not for records: the compiler
     * constructs a created contract's record at the CALL SITE and passes it
     * into the hoisted worker, whose body then just says `create @T v`. By the
     * time recordFields sees `v`, a term-only environment has already reduced
     * the construction to `unsupported`. Keeping the raw expression lets the
     * field extractor peel the RecCon/RecUpd it was actually given.
     */
    rawEnv: new Map(),
    /** symbolic inputs discovered during translation */
    params: new Map(),
    rounding: [],
    divisions: [],
    /**
     * Fresh records standing for the elements of a list a higher-order
     * builtin ranges over. Surfaced on the transition so a verdict can state
     * that it holds for an arbitrary element rather than a known one.
     */
    symbolicElements: [],
    elementCount: 0,
    /** Effects consuming contracts other than `this` (see collectEffects). */
    consumesOthers: [],
    /**
     * Contracts consumed by a loop whose list WE CAN NAME: `{listName, effect}`
     * meaning "every element of listName is archived". Unlike consumesOthers
     * these do not refuse the conservation property - they change its
     * statement, and the amounts they contribute are the very symbols a fold
     * over the same list produces.
     */
    archivedInputs: [],
    /**
     * Effects inside a traversal that the per-element modelling cannot carry
     * (a create per element, say). Recorded separately because they make the
     * TOTAL over created contracts unstateable, which is a refusal, not a
     * mere translation gap.
     */
    unmodelledLoopEffects: [],
    /** Set while walking a traversal body: the element the parameter denotes. */
    loopElement: null,
    /** List length bound for fold and traversal unrolling. */
    bound,
    /** Element records introduced by fold unrolling: {listName, index}. */
    listElements: [],
    /** Nesting guard: a fold inside a fold's step is not unrolled. */
    foldDepth: 0,
    /** `{fold, index}` while a fold step is being reduced; null otherwise. */
    foldContext: null,
    /** Work cap, so a fold-dense choice cannot blow the translation up. */
    foldBudget: 64,
    /**
     * Every refusal raised while translating expressions, in order:
     * `{kind, builtin?, cascade}`. A refusal is CASCADE when its own cause was
     * an already-`unsupported` sub-term, so it says nothing new about why the
     * expression left the fragment. The list is what decides whether a failed
     * application may be abstracted as an uninterpreted function: eligibility
     * requires the ORIGINAL obstacles to be text builtins and nothing else,
     * and that question is only answerable from the refusals raised underneath
     * (see textOpaqueUf). Append-only, so a slice taken between two marks is
     * exactly the refusals raised inside that subtree.
     */
    refusals: [],
    /** Uninterpreted symbols introduced, with why: surfaced on the transition. */
    uninterpreted: [],
    depth: 0,
  };
}

/** Run `f` with ctx.pkg temporarily switched to `pkg`. */
function withPkg(ctx, pkg, f) {
  const prev = ctx.pkg;
  ctx.pkg = pkg || prev;
  try {
    return f();
  } finally {
    ctx.pkg = prev;
  }
}

/**
 * Record a refusal and return the `unsupported` node for it.
 *
 * Every refusal raised while translating an EXPRESSION goes through here, so
 * that an enclosing application can ask what actually stopped the translation
 * rather than guessing from the reason string. `cascade` marks a refusal whose
 * cause was already an `unsupported` sub-term - a case whose scrutinee is
 * opaque, an application whose head is opaque - because such a refusal carries
 * no independent information about the obstacle.
 */
function refuse(ctx, kind, why, { builtin = null, cascade = false } = {}) {
  if (ctx.refusals) ctx.refusals.push({ kind, builtin, cascade });
  return T.unsupported(why, ctx.label);
}

/**
 * The symbol an uninterpreted application of a compiled value is named by.
 *
 * The PACKAGE ID is part of the name and that is load-bearing: two distinct
 * functions sharing a symbol would assert that they are equal, and an
 * assumption - unlike the relaxation a UF otherwise is - can make an unsat
 * spurious. Sharing a symbol is only correct when it really is the same
 * compiled value, which is what a package-qualified name says.
 */
function ufName(qualified, pkgCtx) {
  const pid = pkgCtx && pkgCtx.selfPackageId;
  return pid ? `${qualified}@${String(pid).slice(0, 8)}` : qualified;
}

/** Register (or reuse) a symbolic input for a projection path. */
function symbol(ctx, root, path, sort) {
  const name = `${root}.${path}`;
  if (!ctx.params.has(name)) ctx.params.set(name, { name, root, path, sort });
  return T.varRef(name, sort);
}

/**
 * Translate one LF expression into an IR term.
 *
 * Unhandled shapes become `unsupported` rather than throwing, so a single
 * exotic sub-expression degrades one choice's report instead of aborting the
 * whole run.
 */
export function translateExpr(expr, ctx) {
  if (!expr) return T.unsupported('empty expression', ctx.label);
  if (ctx.depth > 120) {
    return refuse(ctx, 'depth', 'expression nested deeper than the translator follows');
  }
  ctx.depth++;
  try {
    return translateInner(expr, ctx);
  } finally {
    ctx.depth--;
  }
}

function translateInner(expr, ctx) {
  const pkg = ctx.pkg;

  // interned expression -> follow the indirection
  if (has(expr, S.Expr.internedExpr)) {
    const idx = int(expr, S.Expr.internedExpr);
    const target = pkg.internedExprs[idx];
    if (!target) return refuse(ctx, 'expr', `interned expression ${idx} missing`);
    return translateExpr(target, ctx);
  }

  // a hoisted top-level value -> follow it, into its own package if imported
  const valRef = pkg.resolveValue(expr);
  if (valRef) {
    if (ctx.env.has(valRef.key)) return ctx.env.get(valRef.key);
    // guard against recursion: a recursive value is outside the fragment
    ctx.env.set(valRef.key, T.unsupported(`recursive value ${valRef.name}`, ctx.label));
    const prevPkg = ctx.pkg;
    ctx.pkg = valRef.pkg || prevPkg;
    let t;
    try {
      t = translateExpr(valRef.body, ctx);
    } finally {
      ctx.pkg = prevPkg;
    }
    ctx.env.set(valRef.key, t);
    return t;
  }

  // variable
  if (has(expr, S.Expr.varInternedStr)) {
    const name = pkg.str(int(expr, S.Expr.varInternedStr));
    if (ctx.env.has(name)) return ctx.env.get(name);
    return refuse(ctx, 'unbound', `unbound variable \`${name}\``);
  }

  // literals
  const lit = sub(expr, S.Expr.builtinLit);
  if (lit) {
    if (has(lit, S.BuiltinLit.int64)) return T.num(String(int(lit, S.BuiltinLit.int64)));
    if (has(lit, S.BuiltinLit.numericInternedStr)) {
      return T.num(pkg.str(int(lit, S.BuiltinLit.numericInternedStr)));
    }
    if (has(lit, S.BuiltinLit.textInternedStr)) {
      return T.str(pkg.str(int(lit, S.BuiltinLit.textInternedStr)));
    }
    return refuse(ctx, 'literal', 'literal of a type the translation does not model');
  }
  if (has(expr, S.Expr.builtinCon)) {
    const c = int(expr, S.Expr.builtinCon);
    if (c === BC.CON_TRUE) return T.bool(true);
    if (c === BC.CON_FALSE) return T.bool(false);
    return refuse(ctx, 'literal', 'unit value');
  }

  // record projection. The base is translated rather than pattern-matched on a
  // name, so `this.amount`, `worker_param.amount` and a let-bound alias all
  // resolve to the same symbol as long as the base evaluates to a record.
  const proj = sub(expr, S.Expr.recProj);
  if (proj && has(proj, S.RecProj.fieldInternedStr) && has(proj, S.RecProj.record)) {
    const segments = [];
    let node = proj;
    for (let i = 0; i < 16 && node; i++) {
      if (!has(node, S.RecProj.fieldInternedStr)) break;
      segments.unshift(pkg.str(int(node, S.RecProj.fieldInternedStr)));
      const record = deref(sub(node, S.RecProj.record), ctx);
      const next = record ? sub(record, S.Expr.recProj) : null;
      if (next && has(next, S.RecProj.fieldInternedStr)) {
        node = next;
        continue;
      }
      const base = record ? translateExpr(record, ctx) : null;
      if (base && base.k === 'record') return symbol(ctx, base.root, segments.join('.'), 'Real');
      // The base may itself be a projection that was let-bound earlier
      // (`let ds = this.contractData in ... ds.investorId ...`): its term is a
      // registered symbol carrying root+path, so extend that path.
      if (base && base.k === 'var' && ctx.params.has(base.name)) {
        const p = ctx.params.get(base.name);
        return symbol(ctx, p.root, `${p.path}.${segments.join('.')}`, 'Real');
      }
      if (base && base.k === 'unsupported') return base;
      return refuse(ctx, 'projection', `projection off a value that is not a known record`, {
        cascade: false,
      });
    }
    return refuse(ctx, 'projection', 'record projection we could not follow');
  }

  // application of a builtin
  const app = sub(expr, S.Expr.app);
  if (app) return translateApp(app, ctx);

  // type application is transparent for our purposes
  const tyApp = sub(expr, S.Expr.tyApp);
  if (tyApp) return translateExpr(deref(sub(tyApp, 1), ctx), ctx);

  // let bindings
  const block = sub(expr, S.Expr.let);
  if (block) {
    const saved = [];
    for (const binding of subs(block, S.Block.bindings)) {
      const binder = sub(binding, S.Binding.binder);
      const name = binder ? pkg.str(int(binder, S.VarWithType.varInternedStr)) : null;
      const bound = deref(sub(binding, S.Binding.bound), ctx);
      const boundTerm = translateExpr(bound, ctx);
      if (name) {
        saved.push([
          name,
          ctx.env.has(name) ? ctx.env.get(name) : undefined,
          ctx.rawEnv.has(name) ? ctx.rawEnv.get(name) : undefined,
        ]);
        ctx.env.set(name, boundTerm);
        // The RAW expression matters as much as the term: the compiler turns
        // a guard's failure branches into join points (`let fail = \_ -> False
        // in ... fail ()`), and a term-only binding leaves the later
        // APPLICATION of `fail` with nothing to reduce. Keeping the expression
        // lets betaReduce step through it.
        if (bound) ctx.rawEnv.set(name, { expr: bound, pkg: ctx.pkg, kind: 'let' });
        else ctx.rawEnv.delete(name);
      }
    }
    const body = translateExpr(deref(sub(block, S.Block.body), ctx), ctx);
    restore(saved, ctx);
    return body;
  }

  // case: only a two-way Bool scrutinee is in the fragment, as an ite
  const cse = sub(expr, S.Expr.case);
  if (cse) return translateCase(cse, ctx);

  // An UNAPPLIED lambda: the function argument of a higher-order builtin
  // (foldl, map, filter). Its parameters are not bound by any application, so
  // leaving them unbound made every expression inside unreachable - which is
  // how a whole concentration calculation reduced to `unbound variable
  // \`entry\``.
  //
  // Instead each parameter becomes a FRESH SYMBOLIC ELEMENT record, so a
  // projection inside the body resolves to `elem$N.field`. For a property
  // that is universally quantified over the list elements - division safety
  // being the case that matters - proving it of an unconstrained element IS
  // the statement "for every element", because the symbol is free in the
  // query and the solver quantifies over all its values.
  //
  // This does NOT model the fold's aggregate: FOLDL itself is still outside
  // BINOP, so a summed value stays `unsupported` and any property depending
  // on it is refused. The elements are recorded on the context so a verdict
  // that relied on one can say so.
  for (const fn of [S.Expr.abs, S.Expr.tyAbs]) {
    const inner = sub(expr, fn);
    if (!inner) continue;
    if (fn === S.Expr.tyAbs) return translateExpr(deref(sub(inner, 2), ctx), ctx);

    const params = subs(inner, 1);
    const saved = [];
    for (const param of params) {
      const name = pkg.str(int(param, S.VarWithType.varInternedStr));
      const root = `elem$${ctx.elementCount}`;
      ctx.elementCount += 1;
      ctx.symbolicElements.push({ param: name, root, at: ctx.label });
      saved.push([name, ctx.env.has(name) ? ctx.env.get(name) : undefined]);
      ctx.env.set(name, T.record(root));
    }
    try {
      return translateExpr(deref(sub(inner, 2), ctx), ctx);
    } finally {
      restore(saved, ctx);
    }
  }

  // throw / abort: understood exactly, eliminated by guardConjuncts when it
  // sits in an ensure-style position, refused everywhere else.
  if (has(expr, S.Expr.throw)) return T.abort('throw');

  // call_interface: resolvable only when translating against a concrete
  // interface instance (ctx.dispatch); see extractTransitions.
  const ci = sub(expr, S.Expr.callInterface);
  if (ci) {
    const mname = ctx.pkg.str(int(ci, S.CallInterface.methodInternedName));
    const impl = ctx.dispatch && ctx.dispatch.methods.get(mname);
    if (!impl) {
      return refuse(
        ctx,
        'interface',
        `interface method \`${mname}\` call with no implementation in scope`
      );
    }
    const recv = translateExpr(deref(sub(ci, S.CallInterface.interfaceExpr), ctx), ctx);
    if (!(recv && recv.k === 'record' && recv.root === 'this')) {
      return refuse(
        ctx,
        'interface',
        `interface method \`${mname}\` called on a value other than this contract`
      );
    }
    const prevPkg = ctx.pkg;
    ctx.pkg = impl.pkg || prevPkg;
    try {
      return translateExpr(impl.expr, ctx);
    } finally {
      ctx.pkg = prevPkg;
    }
  }

  // A list VALUE. The emitter's sorts are Bool/Real/Int/String, with nothing
  // to declare a list against, so a list cannot be a term - but saying so
  // precisely matters: a list of Text is what EXPLODE_TEXT produces, and a
  // refusal of this kind inside an otherwise text-only body is part of that
  // chain rather than an independent gap (see textOpaqueUf).
  if (has(expr, S.Expr.nil) || has(expr, S.Expr.cons)) {
    return refuse(
      ctx,
      'list',
      'a list value, which has no sort in the emitter (Bool/Real/Int/String only)'
    );
  }

  // A typeclass method, projected off its dictionary. Resolving the
  // dictionary to the compiled instance is exact; see resolveStructField.
  const spMsg = sub(expr, S.Expr.structProj);
  if (spMsg) {
    const field = structFieldName(spMsg, ctx);
    const found = field ? resolveStructField(sub(spMsg, S.StructProj.struct), field, ctx) : null;
    if (found) {
      const prevPkg = ctx.pkg;
      ctx.pkg = found.pkg || prevPkg;
      try {
        return translateExpr(found.expr, ctx);
      } finally {
        ctx.pkg = prevPkg;
        found.restore();
      }
    }
    return refuse(
      ctx,
      'dictionary',
      `\`${field || '?'}\` projected off a value the translation could not reduce to a ` +
        `typeclass dictionary, so the instance it selects is unknown`
    );
  }

  if (has(expr, S.Expr.optionalSome) || has(expr, S.Expr.optionalNone)) {
    return refuse(
      ctx,
      'expr',
      'Optional constructor (only Optional CASE ANALYSIS on contract/argument fields is modelled)'
    );
  }

  return refuse(ctx, 'expr', 'expression form outside the translated fragment');
}

/**
 * Step through type application/abstraction layers to the value underneath.
 * A monomorphised builtin arrives as `tyApp(tyAbs(tyApp(builtin)))`; the type
 * layers carry no value and are transparent for translation.
 */
function unwrapTypeLayers(fun, ctx) {
  for (let i = 0; fun && i < 12; i++) {
    if (has(fun, S.Expr.internedExpr)) {
      fun = deref(fun, ctx);
      continue;
    }
    const ta = sub(fun, S.Expr.tyApp);
    if (ta) {
      fun = deref(sub(ta, 1), ctx);
      continue;
    }
    const tb = sub(fun, S.Expr.tyAbs);
    if (tb) {
      fun = deref(sub(tb, 2), ctx);
      continue;
    }
    break;
  }
  return fun;
}

function translateApp(app, ctx) {
  // Flatten the application spine - `app(app(f, a), b)` becomes `f [a, b]` -
  // stepping through type layers between segments, so a builtin wrapped as
  // `tyApp(tyAbs(tyApp(builtin)))` under a curried application is found.
  let fun = deref(sub(app, 1), ctx);
  let rawArgs = many(app, 2).filter((v) => v instanceof Uint8Array);
  for (let i = 0; i < 16 && fun; i++) {
    const peeled = unwrapTypeLayers(fun, ctx);
    const innerApp = peeled ? sub(peeled, S.Expr.app) : null;
    if (!innerApp) {
      fun = peeled;
      break;
    }
    rawArgs = [...many(innerApp, 2).filter((v) => v instanceof Uint8Array), ...rawArgs];
    fun = deref(sub(innerApp, 1), ctx);
  }

  const builtin = fun && has(fun, S.Expr.builtin) ? int(fun, S.Expr.builtin) : null;
  if (builtin === null) {
    // Not a builtin. Beta reduce: the compiler hoists choice bodies into
    // top-level workers and applies them to `this` / `self` / `arg`, so
    // without this step every projection inside the body is unreachable.
    //
    // If that leaves an untranslatable term AND the only thing in the way was
    // a Daml Text chain, the application is abstracted as ONE uninterpreted
    // symbol (textOpaqueUf) instead of being refused.
    //
    // The abstraction is attempted at the INNERMOST identifiable function,
    // not the outermost, and that is deliberate. `isNonBlankText value` is
    // `isNotEmpty (trim value)`: abstracting `trim` alone leaves the
    // comparison `isNotEmpty` compiles to - an equality against "" - intact
    // and visible to the solver, whereas one opaque predicate over the whole
    // chain would throw that structure away. Abstracting the smallest opaque
    // piece keeps the most interpreted structure, which is the more precise
    // choice as well as the cheaper one.
    const mark = ctx.refusals.length;
    let out;
    const reduced = betaReduce(fun, rawArgs, ctx);
    if (reduced) {
      if (reduced.term) {
        out = reduced.term;
        reduced.restore();
      } else {
        try {
          out = translateExpr(reduced.body, ctx);
        } finally {
          reduced.restore();
        }
      }
    } else {
      out = refuse(ctx, 'inline', 'application of a function the translation cannot inline', {
        cascade: headIsOpaque(fun, ctx),
      });
    }
    if (!hasUnsupported(out)) return out;
    return textOpaqueUf(fun, rawArgs, ctx, ctx.refusals.slice(mark), out) || out;
  }

  return translateBuiltinApp(
    builtin,
    rawArgs.map((b) => ({ bytes: b, pkg: ctx.pkg })),
    ctx
  );
}

/**
 * Refusal kinds that DISQUALIFY an application from being abstracted as an
 * uninterpreted function, because each names an obstacle that is not a text
 * chain and would be silently papered over by a UF:
 *
 *   fold        a quantifier over a user list - abstracting it would hide
 *               the list, not a text operation
 *   apply       a function the term-applier could not reduce: unidentified
 *   dictionary  a typeclass dictionary that did not resolve, so WHICH
 *               function is being called is unknown (see ufName)
 *   interface   an interface method with no implementation in scope
 *   depth       the translator gave up, which says nothing about the shape
 *   projection  a projection off a record the translation lost track of
 *
 * The kinds NOT listed here - case, inline, expr, list, literal, unbound -
 * are the shapes a text chain actually produces once EXPLODE_TEXT has turned
 * the text into a list nothing downstream can name.
 */
const UF_BLOCKING_REFUSAL = new Set([
  'fold',
  'apply',
  'dictionary',
  'interface',
  'depth',
  'projection',
]);

/** Does a term contain an un-eliminated `abort`? */
function containsAbort(t) {
  if (!t || typeof t !== 'object') return false;
  if (t.k === 'abort') return true;
  if (t.k === 'app' || t.k === 'uf') return t.args.some(containsAbort);
  if (t.k === 'ite') return [t.c, t.a, t.b].some(containsAbort);
  if (t.k === 'fold') return t.unrolled.some(containsAbort);
  return false;
}

/** Is the head of this application a variable already known to be opaque? */
function headIsOpaque(fun, ctx) {
  if (!fun || !has(fun, S.Expr.varInternedStr)) return false;
  const bound = ctx.env.get(ctx.pkg.str(int(fun, S.Expr.varInternedStr)));
  return !!(bound && bound.k === 'unsupported');
}

/**
 * Abstract a failed application as ONE uninterpreted symbol, when - and only
 * when - the reason it failed is a Daml Text chain.
 *
 * This is the top-down half of the UF story. `isNonBlankText value` is
 * `isNotEmpty (trim value)`, and `trim` bottoms out in EXPLODE_TEXT /
 * IMPLODE_TEXT, whose list-shaped signatures the emitter has no sort for. The
 * bottom-up route therefore cannot recover the chain; abstracting the named
 * predicate as a single symbol over its (translatable) arguments can.
 *
 * FOUR CONDITIONS, all of which are about being able to justify the symbol
 * rather than about making the numbers look better:
 *
 *   1. Every refusal raised underneath is either a TEXT builtin or a CASCADE
 *      of one. A fold, a ledger effect, an unresolved dictionary or a
 *      non-text builtin means the obstacle has NOT been identified as text,
 *      and an unidentified obstacle is not a modelling choice - it stays
 *      `unsupported`, exactly as before.
 *   2. At least one text builtin was actually refused, so the abstraction has
 *      a stated cause and is not a blanket fallback.
 *   3. The head resolves to a COMPILED VALUE with a qualified name, which is
 *      what gives the symbol an identity (see ufName). A function reached
 *      through an unresolved variable or dictionary has no such identity, and
 *      giving two different functions one symbol would be an assumption, not
 *      a relaxation.
 *   4. Every value argument translates cleanly to a scalar. A dirty argument
 *      is NOT dropped: an argument that is a typeclass dictionary selects
 *      WHICH function this is, and dropping it would merge distinct functions
 *      under one symbol; a record or list argument has no sort to declare the
 *      parameter against.
 *
 * An argument that is itself an opaque text expression
 * (`validateAssetTokenId (scopedTokenIdPrefix id)`) has already become its own
 * symbol by the time it is translated here, so it counts as clean.
 *
 * @returns {Object|null} a `uf` term, or null to leave the refusal standing
 */
function textOpaqueUf(fun, rawArgs, ctx, trace, translated) {
  // An expression that ABORTS is not opaque - it is understood exactly, and
  // `guardConjuncts` turns `if c then True else error "..."` into the
  // assumption `c`. Replacing the abort by an uninterpreted value would throw
  // that away and, worse, would treat an aborting branch as a reachable
  // post-state. Error paths format their messages with text builtins, so
  // without this check `GHC.Err:error` itself came out as a UF.
  if (containsAbort(translated)) return null;

  const textBuiltins = new Set();
  const otherKinds = new Set();
  for (const r of trace) {
    if (r.kind === 'builtin') {
      // a builtin refusal is either a text one (the stated cause) or a
      // disqualifying one; there is no third case
      if (r.builtin !== null && TEXT_OPAQUE_BUILTIN.has(r.builtin)) {
        textBuiltins.add(builtinName(r.builtin));
        continue;
      }
      return null;
    }
    if (UF_BLOCKING_REFUSAL.has(r.kind)) return null; // condition 1
    otherKinds.add(r.kind);
  }
  if (textBuiltins.size === 0) return null; // condition 2

  const vr = fun ? ctx.pkg.resolveValue(fun) : null;
  if (!vr || !vr.name) return null; // condition 3

  // condition 4: every value argument, translated on its own
  const argTerms = [];
  for (const raw of rawArgs) {
    const tagged = raw instanceof Uint8Array ? { bytes: raw, pkg: ctx.pkg } : raw;
    const expr = decodeExpr(tagged.bytes);
    if (!expr) return null;
    const term = withPkg(ctx, tagged.pkg, () => translateExpr(expr, ctx));
    if (!term || hasUnsupported(term) || term.k === 'record') return null; // condition 4
    argTerms.push(term);
  }
  if (argTerms.length === 0) return null;

  const name = ufName(vr.name, vr.pkg);
  // The inventory is complete on purpose: the stated cause (which text
  // builtins) AND what else was refused underneath, so a reader can judge the
  // abstraction rather than take it on trust.
  const why =
    `\`${vr.name}\` is modelled as an uninterpreted function of ${argTerms.length} ` +
    `argument(s): its compiled body bottoms out in ${[...textBuiltins].sort().join(', ')}, ` +
    `which the translated fragment cannot express` +
    (otherKinds.size
      ? `; the rest of its body refused only as ${[...otherKinds].sort().join(', ')}, the ` +
        `shapes a text chain makes (list construction and matching over the exploded text)`
      : '');
  ctx.uninterpreted.push({ name, why });
  // Result sort left to the emitter: the position the application is used in
  // decides it, and a symbol used at two different sorts is a conflict there.
  return T.uf(name, argTerms, null, null);
}

function translateCase(cse, ctx) {
  const scrutExpr = deref(sub(cse, 1), ctx);
  const alts = subs(cse, 2);
  if (alts.length !== 2) {
    return refuse(ctx, 'case', `case with ${alts.length} alternatives`);
  }

  const noneAlt = alts.find((a) => has(a, S.CaseAlt.optionalNone));
  const someAlt = alts.find((a) => has(a, S.CaseAlt.optionalSome));
  // A `_ ->` catch-all standing in for whichever Optional shape is not spelled
  // out. The compiled Eq instance for Optional writes exactly this shape
  // (`case x of None -> ...; _ -> ...`), so refusing a case that names only
  // ONE of the two constructors made every `field /= None` guard untranslatable.
  const defaultAlt = alts.find((a) => has(a, S.CaseAlt.default));

  // A case whose scrutinee is a LITERAL Optional constructor is decided
  // statically, exactly: `case None of None -> a; _ -> b` IS `a`. This is not
  // an abstraction, it is evaluation, and it is what the compiled
  // `x /= None` reduces to once the Eq dictionary has been resolved - the
  // instance body compares `x` against the constant `None`.
  if (noneAlt || someAlt) {
    const decided = decideOptionalConstructor(scrutExpr, { noneAlt, someAlt, defaultAlt }, ctx);
    if (decided) return decided;
  }

  const scrut = translateExpr(scrutExpr, ctx);

  // Optional None/Some over a contract or argument field: modelled as a pair
  // of symbols, `<path>.$some : Bool` and `<path>.$value`. Exact: the value
  // symbol is only reachable under the `$some` branch of the ite, so its
  // value when `$some` is false never matters. Only fields (registered
  // symbols) are modelled this way; an Optional produced by computation is
  // outside the fragment and refused below.
  //
  // Either constructor may be replaced by the `_ ->` catch-all: a default
  // branch binds nothing, so the Some side simply cannot name the payload,
  // which costs nothing for a guard that only asks whether the field is set.
  if ((noneAlt || someAlt) && (noneAlt || defaultAlt) && (someAlt || defaultAlt)) {
    if (!(scrut.k === 'var' && ctx.params.has(scrut.name))) {
      if (scrut.k === 'unsupported') return scrut;
      return refuse(ctx, 'case', 'Optional case over a value that is not a contract/argument field');
    }
    const p = ctx.params.get(scrut.name);
    const present = symbol(ctx, p.root, `${p.path}.$some`, 'Bool');
    const value = symbol(ctx, p.root, `${p.path}.$value`, 'Real');
    let someBody;
    if (someAlt) {
      const someMsg = sub(someAlt, S.CaseAlt.optionalSome);
      const binder = ctx.pkg.str(int(someMsg, S.OptionalSomeAlt.varBodyInternedStr));
      const prev = ctx.env.has(binder) ? ctx.env.get(binder) : undefined;
      ctx.env.set(binder, value);
      try {
        someBody = translateExpr(deref(sub(someAlt, S.CaseAlt.body), ctx), ctx);
      } finally {
        if (prev === undefined) ctx.env.delete(binder);
        else ctx.env.set(binder, prev);
      }
    } else {
      someBody = translateExpr(deref(sub(defaultAlt, S.CaseAlt.body), ctx), ctx);
    }
    const noneBody = translateExpr(
      deref(sub(noneAlt || defaultAlt, S.CaseAlt.body), ctx),
      ctx
    );
    return T.ite(present, someBody, noneBody);
  }

  let whenTrue = null;
  let whenFalse = null;
  for (const alt of alts) {
    const body = deref(sub(alt, S.CaseAlt.body), ctx);
    if (has(alt, S.CaseAlt.builtinCon)) {
      const con = int(alt, S.CaseAlt.builtinCon);
      if (con === BC.CON_TRUE) whenTrue = body;
      else if (con === BC.CON_FALSE) whenFalse = body;
    } else if (has(alt, S.CaseAlt.default)) {
      if (whenTrue === null) whenTrue = body;
      else whenFalse = body;
    }
  }
  if (!whenTrue || !whenFalse) {
    // A case whose SCRUTINEE is already opaque tells us nothing new: whatever
    // made the scrutinee opaque is the real obstacle, so the refusal cascades.
    return refuse(ctx, 'case', 'case on something other than a two-way Bool', {
      cascade: scrut.k === 'unsupported',
    });
  }

  return T.ite(scrut, translateExpr(whenTrue, ctx), translateExpr(whenFalse, ctx));
}

/**
 * Decide a `case` whose SCRUTINEE is a literal Optional constructor.
 *
 * `case None of None -> a; _ -> b` is `a`; `case (Some e) of Some x -> f x;
 * _ -> b` is `f e`. Both are plain evaluation, not abstraction: the compiler
 * emits exactly these when an Eq instance for Optional is applied to the
 * constant `None`, which is how `contractData.businessDate /= None` reaches
 * the translator. Returns null when the scrutinee is not a constructor, or
 * when the matching alternative is absent (which would be an ill-typed case).
 */
function decideOptionalConstructor(scrutExpr, { noneAlt, someAlt, defaultAlt }, ctx) {
  const con = optionalConstructorOf(scrutExpr, ctx);
  if (!con) return null;
  if (!con.some) {
    const alt = noneAlt || defaultAlt;
    if (!alt) return null;
    return translateExpr(deref(sub(alt, S.CaseAlt.body), ctx), ctx);
  }
  if (!someAlt) {
    if (!defaultAlt) return null;
    return translateExpr(deref(sub(defaultAlt, S.CaseAlt.body), ctx), ctx);
  }
  // The payload expression belongs to the package the constructor was found
  // in, which is not necessarily the package the case lives in.
  const payload = withPkg(ctx, con.pkg, () => translateExpr(deref(con.value, ctx), ctx));
  const someMsg = sub(someAlt, S.CaseAlt.optionalSome);
  const binder = ctx.pkg.str(int(someMsg, S.OptionalSomeAlt.varBodyInternedStr));
  const prev = ctx.env.has(binder) ? ctx.env.get(binder) : undefined;
  ctx.env.set(binder, payload);
  try {
    return translateExpr(deref(sub(someAlt, S.CaseAlt.body), ctx), ctx);
  } finally {
    if (prev === undefined) ctx.env.delete(binder);
    else ctx.env.set(binder, prev);
  }
}

/**
 * Is this expression a literal Optional CONSTRUCTOR, once aliases are chased?
 *
 * The compiled Eq instance for Optional compares its two arguments by nested
 * case analysis, and the argument carrying the constant `None` arrives as a
 * lambda PARAMETER - so the constructor is only visible through the raw
 * expression the parameter was bound to. Do-block binders are excluded: they
 * hold the result of an action, not the action's expression.
 *
 * @returns {{some: false} | {some: true, value: Object, pkg: Object} | null}
 */
function optionalConstructorOf(expr, ctx, depth = 0) {
  if (!expr || depth > 16) return null;
  const e = deref(expr, ctx);
  if (!e) return null;
  if (has(e, S.Expr.optionalNone)) return { some: false };
  const someMsg = sub(e, S.Expr.optionalSome);
  if (someMsg) {
    return { some: true, value: sub(someMsg, S.OptionalSomeExpr.value), pkg: ctx.pkg };
  }
  const ta = sub(e, S.Expr.tyApp);
  if (ta) return optionalConstructorOf(sub(ta, 1), ctx, depth + 1);
  const tb = sub(e, S.Expr.tyAbs);
  if (tb) return optionalConstructorOf(sub(tb, 2), ctx, depth + 1);
  if (has(e, S.Expr.varInternedStr)) {
    const name = ctx.pkg.str(int(e, S.Expr.varInternedStr));
    const entry = ctx.rawEnv.get(name);
    if (!entry || !entry.expr || entry.kind === 'do') return null;
    ctx.rawEnv.delete(name); // no self-reference loops
    try {
      return withPkg(ctx, entry.pkg, () => optionalConstructorOf(entry.expr, ctx, depth + 1));
    } finally {
      ctx.rawEnv.set(name, entry);
    }
  }
  const vr = ctx.pkg.resolveValue(e);
  if (vr) {
    ctx.optChasing = ctx.optChasing || new Set();
    if (ctx.optChasing.has(vr.key)) return null;
    ctx.optChasing.add(vr.key);
    try {
      return withPkg(ctx, vr.pkg, () => optionalConstructorOf(vr.body, ctx, depth + 1));
    } finally {
      ctx.optChasing.delete(vr.key);
    }
  }
  return null;
}

/**
 * Reduce a STRUCT expression to the struct construction it denotes and select
 * one field, returning `{expr, pkg, restore}` (or null).
 *
 * WHY THIS EXISTS. Daml compiles every typeclass method call to a projection
 * off a dictionary struct: `x == y` is `(structProj m_== $dEq) x y`, and the
 * dictionary arrives as a lambda parameter, a hoisted value, or a dictionary
 * FUNCTION applied to sub-dictionaries (`$fEqOptional $dEqTime`). Left
 * unresolved, every such call died as "application of a function the
 * translation cannot inline", which is how `contractData.businessDate /= None`
 * - an ordinary Optional comparison - left the fragment.
 *
 * Resolving the projection is EXACT, not an abstraction: the dictionary is a
 * closed record of method implementations in the compiled package, and this
 * picks out the very implementation the call site would have run. Anything it
 * cannot reduce to a struct construction returns null, and the caller reports
 * a refusal with the method name.
 *
 * Bindings introduced on the way (a dictionary function's parameters) stay in
 * place until `restore()` runs, so the returned expression's free variables
 * are still bound when the caller translates it - the same discipline
 * betaReduce uses.
 */
function resolveStructField(structExpr, field, ctx, depth = 0) {
  if (!structExpr || depth > 24) return null;
  const e = deref(structExpr, ctx);
  if (!e) return null;
  const nothing = () => {};

  const con = sub(e, S.Expr.structCon);
  if (con) {
    for (const f of subs(con, S.StructCon.fields)) {
      if (ctx.pkg.str(int(f, S.FieldWithExpr.fieldInternedStr)) !== field) continue;
      return { expr: sub(f, S.FieldWithExpr.expr), pkg: ctx.pkg, restore: nothing };
    }
    return null;
  }

  // a hoisted dictionary value, in its own package
  const vr = ctx.pkg.resolveValue(e);
  if (vr) {
    ctx.structing = ctx.structing || new Set();
    if (ctx.structing.has(vr.key)) return null; // recursive dictionary
    ctx.structing.add(vr.key);
    const prevPkg = ctx.pkg;
    ctx.pkg = vr.pkg || prevPkg;
    const inner = resolveStructField(vr.body, field, ctx, depth + 1);
    ctx.pkg = prevPkg;
    if (!inner) {
      ctx.structing.delete(vr.key);
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        ctx.structing.delete(vr.key);
      },
    };
  }

  const ta = sub(e, S.Expr.tyApp);
  if (ta) return resolveStructField(sub(ta, 1), field, ctx, depth + 1);
  const tb = sub(e, S.Expr.tyAbs);
  if (tb) return resolveStructField(sub(tb, 2), field, ctx, depth + 1);

  // the dictionary is a parameter: it was bound to the CALLER's expression
  if (has(e, S.Expr.varInternedStr)) {
    const name = ctx.pkg.str(int(e, S.Expr.varInternedStr));
    const entry = ctx.rawEnv.get(name);
    if (!entry || !entry.expr) return null;
    ctx.rawEnv.delete(name); // no self-reference loops
    const prevPkg = ctx.pkg;
    ctx.pkg = entry.pkg || prevPkg;
    const inner = resolveStructField(entry.expr, field, ctx, depth + 1);
    ctx.pkg = prevPkg;
    if (!inner) {
      ctx.rawEnv.set(name, entry);
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        ctx.rawEnv.set(name, entry);
      },
    };
  }

  // a dictionary FUNCTION applied to sub-dictionaries: reduce it, then look
  // for the field in what it returns
  const app = sub(e, S.Expr.app);
  if (app) {
    const rawArgs = many(app, 2)
      .filter((v) => v instanceof Uint8Array)
      .map((b) => ({ bytes: b, pkg: ctx.pkg }));
    const reduced = betaReduce(deref(sub(app, 1), ctx), rawArgs, ctx, depth + 1);
    if (!reduced || !reduced.body) {
      if (reduced) reduced.restore();
      return null;
    }
    const inner = resolveStructField(reduced.body, field, ctx, depth + 1);
    if (!inner) {
      reduced.restore();
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        reduced.restore();
      },
    };
  }

  const block = sub(e, S.Expr.let);
  if (block) {
    const saved = bindBlock(block, ctx);
    const inner = resolveStructField(sub(block, S.Block.body), field, ctx, depth + 1);
    if (!inner) {
      restore(saved, ctx);
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        restore(saved, ctx);
      },
    };
  }

  return null;
}

/** The method name a struct projection selects, for reporting. */
function structFieldName(spMsg, ctx) {
  return has(spMsg, S.StructProj.fieldInternedStr)
    ? ctx.pkg.str(int(spMsg, S.StructProj.fieldInternedStr))
    : null;
}

/**
 * Beta reduce `App(fun, args)` when `fun` is (or resolves to) a lambda.
 *
 * This is a small call-by-name reducer over the compiled shapes that occur in
 * practice, and it is TOTAL in the same sense as the translator: any shape it
 * does not cover makes it return null, and the caller falls back to an
 * explicit refusal (or, in effect collection, to a generic descent).
 *
 *   * value references are followed into their OWN package: an ensure calling
 *     `GHC.Num:$c-` reduces through daml-prim's actual definition, not a
 *     transcription of it. `ctx.pkg` is swapped for the duration.
 *   * arguments are tagged `{bytes, pkg}` with the package whose tables they
 *     must be read against, because an application collected in one package
 *     can bind parameters of a lambda that lives in another.
 *   * type abstraction/application layers are transparent.
 *   * a `let` between lambdas is bound and stepped through.
 *   * OVER-application recurses: `(\x -> \y -> e) a b` binds both.
 *   * a fully applied builtin reduces to a TERM (`{term}` instead of
 *     `{body}`), since a builtin has no expression body to return.
 *   * `call_interface` on `this` dispatches to the implementing template's
 *     method body when translating an interface instance (ctx.dispatch).
 *
 * @param {Object} fun  decoded Expr
 * @param {Array<Uint8Array|{bytes: Uint8Array, pkg: Object}>} rawArgs
 * @returns {{body?: Object, term?: Object, restore: () => void}|null}
 */
function betaReduce(fun, rawArgs, ctx, depth = 0) {
  if (!fun || depth > 48) return null;
  // Normalize arguments to tagged form; untagged bytes come from the caller's
  // current package.
  const args = rawArgs.map((a) =>
    a instanceof Uint8Array ? { bytes: a, pkg: ctx.pkg } : a
  );

  if (has(fun, S.Expr.internedExpr)) {
    return betaReduce(deref(fun, ctx), args, ctx, depth + 1);
  }

  // follow a hoisted value to its definition, in its own package
  const valRef = ctx.pkg.resolveValue(fun);
  if (valRef) {
    if (ctx.inlining && ctx.inlining.has(valRef.key)) return null; // recursive
    ctx.inlining = ctx.inlining || new Set();
    ctx.inlining.add(valRef.key);
    const prevPkg = ctx.pkg;
    ctx.pkg = valRef.pkg || prevPkg;
    const inner = betaReduce(deref(valRef.body, ctx), args, ctx, depth + 1);
    if (!inner) {
      ctx.pkg = prevPkg;
      ctx.inlining.delete(valRef.key);
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        ctx.pkg = prevPkg;
        ctx.inlining.delete(valRef.key);
      },
    };
  }

  // type layers contribute no value binding
  const tyAbs = sub(fun, S.Expr.tyAbs);
  if (tyAbs) return betaReduce(deref(sub(tyAbs, 2), ctx), args, ctx, depth + 1);
  const tyApp = sub(fun, S.Expr.tyApp);
  if (tyApp) return betaReduce(deref(sub(tyApp, 1), ctx), args, ctx, depth + 1);

  // a nested application: flatten, tagging the inner args with this package
  const innerApp = sub(fun, S.Expr.app);
  if (innerApp) {
    const innerArgs = many(innerApp, 2)
      .filter((v) => v instanceof Uint8Array)
      .map((b) => ({ bytes: b, pkg: ctx.pkg }));
    return betaReduce(deref(sub(innerApp, 1), ctx), [...innerArgs, ...args], ctx, depth + 1);
  }

  // a let wrapping the function: bind it, reduce the body underneath
  const block = sub(fun, S.Expr.let);
  if (block) {
    const saved = bindBlock(block, ctx);
    const inner = betaReduce(deref(sub(block, S.Block.body), ctx), args, ctx, depth + 1);
    if (!inner) {
      restore(saved, ctx);
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        restore(saved, ctx);
      },
    };
  }

  // interface method dispatch against the instance under translation
  const ci = sub(fun, S.Expr.callInterface);
  if (ci && ctx.dispatch) {
    const mname = ctx.pkg.str(int(ci, S.CallInterface.methodInternedName));
    const impl = ctx.dispatch.methods.get(mname);
    if (!impl) return null;
    const recv = translateExpr(deref(sub(ci, S.CallInterface.interfaceExpr), ctx), ctx);
    if (!(recv && recv.k === 'record' && recv.root === 'this')) return null;
    const prevPkg = ctx.pkg;
    ctx.pkg = impl.pkg || prevPkg;
    const inner = betaReduce(deref(impl.expr, ctx), args, ctx, depth + 1);
    if (!inner) {
      ctx.pkg = prevPkg;
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        ctx.pkg = prevPkg;
      },
    };
  }

  // A VARIABLE at the head of the spine, bound to a function by a `let` or by
  // an enclosing application. The term environment holds that function's
  // VALUE, which for a function is meaningless, so reduction has to go through
  // the expression it was bound to. Do-block binders are excluded: they hold
  // the result of an action, not an inlinable function.
  if (has(fun, S.Expr.varInternedStr)) {
    const vname = ctx.pkg.str(int(fun, S.Expr.varInternedStr));
    const entry = ctx.rawEnv.get(vname);
    if (!entry || !entry.expr || entry.kind === 'do') return null;
    ctx.rawEnv.delete(vname); // no self-reference loops
    const prevPkg = ctx.pkg;
    ctx.pkg = entry.pkg || prevPkg;
    const inner = betaReduce(deref(entry.expr, ctx), args, ctx, depth + 1);
    ctx.pkg = prevPkg;
    if (!inner) {
      ctx.rawEnv.set(vname, entry);
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        ctx.rawEnv.set(vname, entry);
      },
    };
  }

  // a typeclass method at the head of the spine: resolve the dictionary, then
  // reduce the instance's implementation against the arguments
  const spHead = sub(fun, S.Expr.structProj);
  if (spHead) {
    const field = structFieldName(spHead, ctx);
    const found = field ? resolveStructField(sub(spHead, S.StructProj.struct), field, ctx) : null;
    if (!found) return null;
    const prevPkg = ctx.pkg;
    ctx.pkg = found.pkg || prevPkg;
    const inner = betaReduce(deref(found.expr, ctx), args, ctx, depth + 1);
    if (!inner) {
      ctx.pkg = prevPkg;
      found.restore();
      return null;
    }
    return {
      ...inner,
      restore: () => {
        inner.restore();
        ctx.pkg = prevPkg;
        found.restore();
      },
    };
  }

  // a builtin at the bottom of the spine: reduce to a term
  if (has(fun, S.Expr.builtin)) {
    const term = translateBuiltinApp(int(fun, S.Expr.builtin), args, ctx);
    return { term, restore: () => {} };
  }

  const abs = sub(fun, S.Expr.abs);
  if (!abs) return null;

  const params = subs(abs, 1);
  const saved = [];
  const savedRaw = [];
  params.forEach((param, i) => {
    const name = ctx.pkg.str(int(param, S.VarWithType.varInternedStr));
    const arg = args[i];
    let term;
    let argExpr = null;
    let argPkg = ctx.pkg;
    if (arg) {
      argPkg = arg.pkg;
      try {
        argExpr = decodeMessage(arg.bytes);
      } catch (_) {
        argExpr = null;
      }
      if (argExpr) {
        // the argument expression belongs to the CALLER's package
        const prev = ctx.pkg;
        ctx.pkg = argPkg;
        try {
          term = translateExpr(argExpr, ctx);
        } finally {
          ctx.pkg = prev;
        }
      } else {
        term = T.unsupported('unreadable argument', ctx.label);
      }
    } else {
      term = T.unsupported(`parameter \`${name}\` applied to nothing`, ctx.label);
    }
    saved.push([name, ctx.env.has(name) ? ctx.env.get(name) : undefined]);
    savedRaw.push([name, ctx.rawEnv.has(name) ? ctx.rawEnv.get(name) : undefined]);
    ctx.env.set(name, term);
    if (argExpr) ctx.rawEnv.set(name, { expr: argExpr, pkg: argPkg, kind: 'param' });
    else ctx.rawEnv.delete(name);
  });

  const restoreHere = () => {
    restore(saved, ctx);
    for (const [name, prev] of savedRaw.reverse()) {
      if (prev === undefined) ctx.rawEnv.delete(name);
      else ctx.rawEnv.set(name, prev);
    }
  };

  const body = deref(sub(abs, 2), ctx);
  const rest = args.slice(params.length);
  if (rest.length === 0) return { body, restore: restoreHere };

  // over-application: the lambda's result is itself applied to the rest
  const inner = betaReduce(body, rest, ctx, depth + 1);
  if (!inner) {
    restoreHere();
    return null;
  }
  return {
    ...inner,
    restore: () => {
      inner.restore();
      restoreHere();
    },
  };
}

/**
 * A fully applied builtin, reduced directly to a term. Shared by translateApp
 * (builtin at the head of an application) and betaReduce (builtin uncovered
 * after inlining, e.g. `GHC.Num:$c-` reducing to SUB_NUMERIC).
 *
 * @param {number} builtin
 * @param {Array<{bytes: Uint8Array, pkg: Object}>} args tagged arguments
 */
function translateBuiltinApp(builtin, args, ctx) {
  if (builtin === BF.ERROR) return T.abort('call to error');
  // A fold is not a scalar operation: it becomes a node carrying one term per
  // list length, which a bounded property instantiates. See translateFold.
  if (builtin === BF.FOLDL || builtin === BF.FOLDR) return translateFold(builtin, args, ctx);
  if (ROUNDING.has(builtin)) ctx.rounding.push(builtinName(builtin));

  const translateArg = (a) => {
    const expr = decodeExpr(a.bytes);
    if (!expr) return T.unsupported('unreadable argument', ctx.label);
    const prev = ctx.pkg;
    ctx.pkg = a.pkg || prev;
    try {
      return translateExpr(expr, ctx);
    } finally {
      ctx.pkg = prev;
    }
  };

  // An exact conversion is the identity on the rational value: translate the
  // single value argument and pass it through. Like the numeric binops, it
  // carries scale/dictionary arguments ahead of the value, so take the last.
  if (EXACT_CONVERSION.has(builtin)) {
    const converted = args.length ? translateArg(args[args.length - 1]) : null;
    if (!converted) {
      return refuse(ctx, 'builtin', `${builtinName(builtin)} applied to no value`, { builtin });
    }
    return converted;
  }

  // COERCE_CONTRACT_ID is the identity on the contract id it carries (only the
  // phantom type changes), so `toInterfaceContractId cid` denotes the same
  // contract as `cid`. Modelling it as the identity is exact, and it is what
  // lets an archive loop be matched against the element it archives.
  if (IDENTITY_BUILTIN.has(builtin)) {
    if (!args.length) {
      return refuse(ctx, 'builtin', `${builtinName(builtin)} applied to no value`, { builtin });
    }
    return translateArg(args[args.length - 1]);
  }

  // A text builtin with a scalar signature becomes an UNINTERPRETED
  // application rather than a refusal, provided every value argument is
  // itself translatable. A dirty argument is not dropped: dropping it would
  // merge applications at different arguments under one symbol, which asserts
  // an equality nobody established.
  const uf = TEXT_UF_BUILTIN.get(builtin);
  if (uf) {
    const vals = args.slice(-uf.arity).map(translateArg);
    if (vals.length === uf.arity && !vals.some(hasUnsupported)) {
      const name = `builtin:${builtinName(builtin)}`;
      ctx.uninterpreted.push({
        name,
        why: `${builtinName(builtin)} has no counterpart in the translated fragment`,
      });
      return T.uf(name, vals, uf.sort, uf.argSorts);
    }
    return refuse(
      ctx,
      'builtin',
      `builtin ${builtinName(builtin)} applied to an argument outside the fragment, so it ` +
        `cannot be modelled as an uninterpreted function of that argument`,
      { builtin, cascade: true }
    );
  }

  const op = BINOP.get(builtin);
  if (!op) {
    return refuse(ctx, 'builtin', textlessBuiltinReason(builtin), { builtin });
  }

  const terms = args.map(translateArg);
  // Numeric builtins carry dictionary/scale arguments ahead of the two values.
  const valueArgs = terms.slice(-2);
  if (valueArgs.length !== 2) {
    return refuse(ctx, 'builtin', `builtin ${builtinName(builtin)} applied to ${terms.length} arguments`, {
      builtin,
    });
  }
  const term = T.app(op, valueArgs);
  if (DIVISION.has(builtin)) {
    // A denominator discovered while unrolling a fold step is an obligation
    // about ONE element of a bounded instantiation, not about the whole list.
    // Tagging it here is what lets division-safety say PROVED-BOUNDED instead
    // of overclaiming a PROVED that never looked past element bound-1.
    ctx.divisions.push({ term, denominator: valueArgs[1], ...(ctx.foldContext || {}) });
  }
  return term;
}

// ------------------------------------------------------------------ helpers

function decodeExpr(bytes) {
  try {
    return decodeMessage(bytes);
  } catch (_) {
    return null;
  }
}

function deref(expr, ctx) {
  if (!expr) return expr;
  if (has(expr, S.Expr.internedExpr)) {
    const idx = int(expr, S.Expr.internedExpr);
    return ctx.pkg.internedExprs[idx] || expr;
  }
  return expr;
}

function projectionPath(proj, ctx) {
  const segments = [];
  let node = proj;
  for (let i = 0; i < 12 && node; i++) {
    if (!has(node, S.RecProj.fieldInternedStr)) return null;
    segments.unshift(ctx.pkg.str(int(node, S.RecProj.fieldInternedStr)));
    const record = deref(sub(node, S.RecProj.record), ctx);
    if (!record) return null;
    const next = sub(record, S.Expr.recProj);
    if (next && has(next, S.RecProj.fieldInternedStr)) {
      node = next;
      continue;
    }
    if (has(record, S.Expr.varInternedStr)) {
      return { root: ctx.pkg.str(int(record, S.Expr.varInternedStr)), path: segments.join('.') };
    }
    return null;
  }
  return null;
}

// ------------------------------------------------- naming the lists we fold

/**
 * The canonical name of a record-projection expression, WITHOUT registering a
 * symbol for it (unlike the projection case in translateInner, which is about
 * scalars). `arg.holdings` off the choice argument, `this.contractData.buckets`
 * off the template record, and a projection off an already-registered symbol
 * all resolve to the path a list element can be numbered against.
 */
function projectionName(expr, ctx) {
  const proj = sub(expr, S.Expr.recProj);
  if (!proj) return null;
  const segments = [];
  let node = proj;
  for (let i = 0; i < 16 && node; i++) {
    if (!has(node, S.RecProj.fieldInternedStr)) return null;
    segments.unshift(ctx.pkg.str(int(node, S.RecProj.fieldInternedStr)));
    const record = deref(sub(node, S.RecProj.record), ctx);
    if (!record) return null;
    const next = sub(record, S.Expr.recProj);
    if (next && has(next, S.RecProj.fieldInternedStr)) {
      node = next;
      continue;
    }
    if (!has(record, S.Expr.varInternedStr)) return null;
    const bound = ctx.env.get(ctx.pkg.str(int(record, S.Expr.varInternedStr)));
    if (bound && bound.k === 'record') return `${bound.root}.${segments.join('.')}`;
    if (bound && bound.k === 'var' && ctx.params.has(bound.name)) {
      const pth = ctx.params.get(bound.name);
      return `${pth.root}.${pth.path}.${segments.join('.')}`;
    }
    return null;
  }
  return null;
}

/**
 * Flatten an application spine to `{name, args}`, where `name` is the fully
 * qualified name of the compiled value at the head (or null) and `args` are
 * the value arguments in order, each tagged with the package its bytes must be
 * read against.
 *
 * Following value references matters: the compiler wraps a partially applied
 * stdlib function in a per-module shim (`$$sc_TransferableRecToken_23`, whose
 * body is `mapA <dict>`), so the head is only visible after the shim is
 * resolved, and the shim's own arguments belong to the shim's package.
 */
function flattenSpine(expr, ctx, depth = 0) {
  if (!expr || depth > 32) return null;
  const e = deref(expr, ctx);
  if (!e) return null;

  const app = sub(e, S.Expr.app);
  if (app) {
    const here = many(app, 2)
      .filter((b) => b instanceof Uint8Array)
      .map((b) => ({ bytes: b, pkg: ctx.pkg }));
    const inner = flattenSpine(sub(app, 1), ctx, depth + 1);
    if (!inner) return null;
    return { name: inner.name, args: [...inner.args, ...here] };
  }
  const ta = sub(e, S.Expr.tyApp);
  if (ta) return flattenSpine(sub(ta, 1), ctx, depth + 1);
  const tb = sub(e, S.Expr.tyAbs);
  if (tb) return flattenSpine(sub(tb, 2), ctx, depth + 1);

  const vr = ctx.pkg.resolveValue(e);
  if (vr) {
    const inner = withPkg(ctx, vr.pkg, () => flattenSpine(vr.body, ctx, depth + 1));
    if (inner && inner.name) return inner;
    return { name: vr.name, args: [] };
  }
  return { name: null, args: [] };
}

/**
 * Recognise `mapA f xs` / `mapA_ f xs` and friends (LIST_TRAVERSALS), giving
 * back the function and the list as tagged raw arguments.
 */
function matchTraversal(expr, ctx) {
  const spine = flattenSpine(expr, ctx);
  if (!spine || !spine.name) return null;
  const shape = LIST_TRAVERSALS.get(spine.name);
  if (!shape) return null;
  const n = spine.args.length;
  const fn = spine.args[n + shape.fn];
  const list = spine.args[n + shape.list];
  if (!fn || !list) return null;
  return { name: spine.name, fn, list };
}

/**
 * The canonical name of a LIST-valued expression, or null when there is none.
 *
 * Refusing to name a list is the honest outcome: element symbols are keyed to
 * the name, so inventing one would break the identity between a fold's
 * elements and an archive loop's elements, which is the only thing that makes
 * merge conservation a true statement rather than a comparison of two
 * unrelated symbol families.
 *
 * Three ways to a name, and nothing else:
 *   * a projection path (`arg.holdings`);
 *   * a variable, chased through the expression it was bound to (a do-block
 *     binder holds the RESULT of its action, which for a traversal is the
 *     mapped list);
 *   * an index-preserving traversal, named after its SOURCE list.
 */
function listNameOfExpr(expr, ctx, depth = 0) {
  if (!expr || depth > 12) return null;
  const e = deref(expr, ctx);
  if (!e) return null;

  const direct = projectionName(e, ctx);
  if (direct) return direct;

  if (has(e, S.Expr.varInternedStr)) {
    const name = ctx.pkg.str(int(e, S.Expr.varInternedStr));
    const entry = ctx.rawEnv.get(name);
    if (!entry || !entry.expr) return null;
    // guard against a binding that refers to itself
    ctx.rawEnv.delete(name);
    try {
      return withPkg(ctx, entry.pkg, () => listNameOfExpr(entry.expr, ctx, depth + 1));
    } finally {
      ctx.rawEnv.set(name, entry);
    }
  }

  const ta = sub(e, S.Expr.tyApp);
  if (ta) return listNameOfExpr(sub(ta, 1), ctx, depth + 1);
  const tb = sub(e, S.Expr.tyAbs);
  if (tb) return listNameOfExpr(sub(tb, 2), ctx, depth + 1);

  const tr = matchTraversal(e, ctx);
  if (tr) {
    return withPkg(ctx, tr.list.pkg, () =>
      listNameOfExpr(decodeExpr(tr.list.bytes), ctx, depth + 1)
    );
  }
  return null;
}

// ------------------------------------------------------------ folds, unrolled

/**
 * Apply a compiled function to IR TERMS, rather than to raw argument
 * expressions the way betaReduce does.
 *
 * The fold unroller needs exactly this: the accumulator at step i is a term it
 * built, and the element is a symbolic record it named - neither exists as an
 * expression in the package, so there is nothing to hand betaReduce. The rest
 * is the same small reducer (value references followed into their own package,
 * type layers and lets stepped through, a partial application contributing its
 * own arguments ahead of the terms), and it is TOTAL in the same sense:
 * anything it cannot reduce becomes an explicit `unsupported`.
 *
 * `onBody`, when given, is called with the fully applied body INSTEAD of
 * translating it, with the parameter bindings and the package still in place.
 * That is how the archive-loop walker gets to run collectEffects under the
 * traversal's parameter binding.
 */
function applyToTerms(fn, terms, ctx, depth = 0, onBody = null) {
  if (!fn) return refuse(ctx, 'apply', 'function applied to terms is missing');
  if (depth > 32) {
    return refuse(ctx, 'apply', 'function nested deeper than the term-applier follows');
  }
  const e = deref(fn, ctx);
  if (!e) return refuse(ctx, 'apply', 'function applied to terms is missing');

  const vr = ctx.pkg.resolveValue(e);
  if (vr) {
    ctx.inlining = ctx.inlining || new Set();
    if (ctx.inlining.has(vr.key)) {
      return refuse(ctx, 'apply', `recursive value ${vr.name} applied to terms`);
    }
    ctx.inlining.add(vr.key);
    try {
      return withPkg(ctx, vr.pkg, () => applyToTerms(vr.body, terms, ctx, depth + 1, onBody));
    } finally {
      ctx.inlining.delete(vr.key);
    }
  }

  const tb = sub(e, S.Expr.tyAbs);
  if (tb) return applyToTerms(sub(tb, 2), terms, ctx, depth + 1, onBody);
  const ta = sub(e, S.Expr.tyApp);
  if (ta) return applyToTerms(sub(ta, 1), terms, ctx, depth + 1, onBody);

  const block = sub(e, S.Expr.let);
  if (block) {
    const saved = bindBlock(block, ctx);
    try {
      return applyToTerms(sub(block, S.Block.body), terms, ctx, depth + 1, onBody);
    } finally {
      restore(saved, ctx);
    }
  }

  const app = sub(e, S.Expr.app);
  if (app) {
    // a partial application in front of the lambda: its arguments are
    // translated here (in their own package) and go ahead of the terms
    const pre = many(app, 2)
      .filter((b) => b instanceof Uint8Array)
      .map((b) => translateExpr(decodeExpr(b), ctx));
    return applyToTerms(sub(app, 1), [...pre, ...terms], ctx, depth + 1, onBody);
  }

  const abs = sub(e, S.Expr.abs);
  if (!abs) {
    if (has(e, S.Expr.builtin)) {
      return refuse(
        ctx,
        'apply',
        `builtin ${builtinName(int(e, S.Expr.builtin))} used where a lambda was expected`
      );
    }
    return refuse(
      ctx,
      'apply',
      'function applied to terms is not a lambda the translation can reduce'
    );
  }

  const params = subs(abs, 1);
  const saved = [];
  const savedRaw = [];
  params.forEach((param, i) => {
    const name = ctx.pkg.str(int(param, S.VarWithType.varInternedStr));
    saved.push([name, ctx.env.has(name) ? ctx.env.get(name) : undefined]);
    savedRaw.push([name, ctx.rawEnv.has(name) ? ctx.rawEnv.get(name) : undefined]);
    ctx.env.set(
      name,
      i < terms.length
        ? terms[i]
        : T.unsupported(`parameter \`${name}\` applied to nothing`, ctx.label)
    );
    // a term-bound parameter has no raw expression behind it; a stale one
    // would let recordFields chase the WRONG record
    ctx.rawEnv.delete(name);
  });
  const undo = () => {
    restore(saved, ctx);
    for (const [name, prev] of savedRaw.reverse()) {
      if (prev === undefined) ctx.rawEnv.delete(name);
      else ctx.rawEnv.set(name, prev);
    }
  };
  try {
    const body = deref(sub(abs, 2), ctx);
    const rest = terms.slice(params.length);
    if (rest.length) return applyToTerms(body, rest, ctx, depth + 1, onBody);
    return onBody ? onBody(body) : translateExpr(body, ctx);
  } finally {
    undo();
  }
}

/**
 * FOLDL / FOLDR over a NAMED list, unrolled at every list length 0..bound.
 *
 * The fold is instantiated at k = 0..bound and the step function is applied k
 * times, threading the accumulator; element i is the record
 * `<listName>$<i>`, so a projection inside the step yields
 * `arg.holdings$0.amount` and the archive-loop detector, keying off the same
 * list, yields the same symbol. That identity is the point of the whole
 * exercise: model the archived contracts as unrelated symbols and merge
 * conservation degenerates into `this + sum(A) = this + sum(B)`, which is
 * satisfiable, and the report says DISPROVED about a transition that is
 * perfectly correct.
 *
 * A bounded result is NOT a proof about arbitrary lists, and the verdict says
 * so out loud (see verify.js: PROVED-BOUNDED).
 *
 * Refusals, all explicit:
 *   * a list with no canonical name (elements could not be shared);
 *   * a fold inside another fold's step (the unroller does not nest);
 *   * the per-choice unrolling budget;
 *   * a step body that leaves the fragment - the unrolled term carries the
 *     `unsupported` node and the property refuses with its reason.
 */
function translateFold(builtin, args, ctx) {
  const op = builtin === BF.FOLDL ? 'foldl' : 'foldr';
  if (args.length < 3) {
    return refuse(
      ctx,
      'fold',
      `${builtinName(builtin)} applied to ${args.length} argument(s); only a fully applied ` +
        `fold is unrolled`,
      { builtin }
    );
  }
  const [fnArg, initArg, listArg] = args.slice(-3);
  const listName = withPkg(ctx, listArg.pkg, () =>
    listNameOfExpr(decodeExpr(listArg.bytes), ctx)
  );
  if (!listName) {
    return refuse(
      ctx,
      'fold',
      `${builtinName(builtin)} over a list with no canonical name: its elements cannot be ` +
        `identified with the contracts the choice archives, and inventing names for them ` +
        `would relate unrelated symbols`,
      { builtin }
    );
  }
  if (ctx.foldDepth > 0) {
    return refuse(
      ctx,
      'fold',
      `${builtinName(builtin)} over \`${listName}\` inside another fold's step; the unroller ` +
        `does not nest`,
      { builtin }
    );
  }
  if (ctx.foldBudget <= 0) {
    return refuse(
      ctx,
      'fold',
      `fold unrolling budget exhausted on this choice before ${builtinName(builtin)} over ` +
        `\`${listName}\``,
      { builtin }
    );
  }
  ctx.foldBudget -= 1;

  const init = withPkg(ctx, initArg.pkg, () => translateExpr(decodeExpr(initArg.bytes), ctx));
  const element = (i) => {
    ctx.listElements.push({ listName, index: i });
    return T.record(`${listName}$${i}`);
  };
  const step = (terms, index) => {
    const savedFoldContext = ctx.foldContext;
    ctx.foldContext = { fold: listName, index };
    try {
      return withPkg(ctx, fnArg.pkg, () => applyToTerms(decodeExpr(fnArg.bytes), terms, ctx));
    } finally {
      ctx.foldContext = savedFoldContext;
    }
  };

  const unrolled = [init];
  ctx.foldDepth += 1;
  try {
    if (op === 'foldl') {
      // foldl f z [e0..e(k-1)] = f (... (f z e0) ...) e(k-1): each prefix is
      // the previous one extended, so k applications give every k at once.
      let acc = init;
      for (let i = 0; i < ctx.bound; i++) {
        acc = step([acc, element(i)], i);
        unrolled.push(acc);
      }
    } else {
      // foldr f z [e0..e(k-1)] = f e0 (f e1 (... (f e(k-1) z))): the innermost
      // application depends on k, so each length is built from the right.
      for (let k = 1; k <= ctx.bound; k++) {
        let acc = init;
        for (let i = k - 1; i >= 0; i--) acc = step([element(i), acc], i);
        unrolled.push(acc);
      }
    }
  } finally {
    ctx.foldDepth -= 1;
  }
  return T.fold(listName, op, unrolled);
}

/**
 * Why a builtin outside BINOP is not modelled, said precisely.
 *
 * The text builtins get their own sentence because "outside the fragment" is
 * not the whole story for them: they are outside it because one side of their
 * signature is a list, a map or an Optional, and the emitter's sort set
 * (Bool/Real/Int/String) has nothing to declare such a symbol against. That
 * distinction is what tells a reader whether a better translation is possible
 * and what it would take.
 */
function textlessBuiltinReason(builtin) {
  if (TEXT_OPAQUE_BUILTIN.has(builtin)) {
    return (
      `builtin ${builtinName(builtin)} has a list, map or Optional on one side of its ` +
      `signature, so there is no sort to declare an uninterpreted symbol against; only a ` +
      `NAMED enclosing function over scalars can be abstracted instead`
    );
  }
  return `builtin ${builtinName(builtin)} is outside the fragment`;
}

function builtinName(n) {
  for (const [k, v] of Object.entries(BF)) if (v === n) return k;
  return `builtin#${n}`;
}

export { BF, BINOP, ROUNDING, EXACT_CONVERSION, DIVISION, makeCtx, symbol };

// ---------------------------------------------------------------------------
// Transitions
// ---------------------------------------------------------------------------

/**
 * @typedef {Object} Transition
 * @property {string} module
 * @property {string} template
 * @property {string} choice
 * @property {boolean} consuming
 * @property {Term[]} guards        preconditions that hold on this path
 * @property {Array<{template: string, fields: Record<string, Term>, path: Term[]}>} creates
 * @property {Array<{denominator: Term, path: Term[]}>} divisions
 * @property {string[]} rounding    rounding/truncating builtins seen on the path
 * @property {Array<{name: string, why: string}>} uninterpreted  symbols the
 *   translation abstracted as uninterpreted functions, with the stated reason.
 *   A verdict drawn from a query mentioning one of these is sound for PROVED
 *   and only SUGGESTIVE for DISPROVED; see smt.js.
 * @property {Array<{listName: string, effect: string}>} archivedInputs
 *   contracts the choice consumes BESIDES `this`, identified as "every element
 *   of listName". Their amounts are the same `<listName>$<i>.amount` symbols a
 *   fold over the same list produces, which is what lets merge conservation be
 *   stated instead of refused.
 * @property {Array<{why: string}>} unmodelledLoopEffects  effects inside a
 *   traversal that per-element modelling cannot carry; a refusal, not a gap.
 * @property {Array<{listName: string, index: number}>} listElements
 * @property {number} bound          list length the folds were unrolled to
 * @property {Array<{why: string}>} unsupported
 */

/**
 * Extract one guarded transition per choice from a raw-decoded package.
 *
 * The `ensure` clause becomes a guard on every path, because Daml evaluates it
 * before the choice body and aborts the transaction if it fails. Branches
 * inside the body contribute their own path conditions, so an `if c then abort
 * else e` narrows the successful path to `not c` rather than being dropped.
 *
 * @param {{ctx: Object, modules: Array}} raw  from dalf.readDarRaw
 * @param {{bound?: number}} [options]  list-length bound for fold and
 *   traversal unrolling (verify.js `--bound N`, default DEFAULT_BOUND). It is
 *   fixed at EXTRACTION time because unrolling a fold means reducing its step
 *   function inside the translation context, which does not outlive this call.
 * @returns {Transition[]}
 */
export function extractTransitions(raw, options = {}) {
  const bound =
    Number.isInteger(options.bound) && options.bound >= 0 ? options.bound : DEFAULT_BOUND;
  const out = [];
  for (const mod of raw.modules) {
    for (const tpl of mod.templates) {
      const template = raw.ctx.dname(int(tpl, S.DefTemplate.tyconInternedDname));
      const selfParam = raw.ctx.str(int(tpl, S.DefTemplate.paramInternedStr));
      const tplLocation = readLocation(tpl, S.DefTemplate.location, raw.ctx);

      // `ensure` holds on every successful path through every choice, and it
      // also held when THIS contract was created, so it is a valid assumption
      // for interface choices exercised on it too. It is decomposed into
      // conjuncts so a partly untranslatable ensure still contributes its
      // translatable parts (see guardConjuncts for why that is sound).
      const precondCtx = makeCtx(raw.ctx, {
        selfParam,
        argParam: null,
        label: `${template}.ensure`,
        bound,
      });
      const precondExpr = sub(tpl, S.DefTemplate.precond);
      const precond = precondExpr ? translateExpr(precondExpr, precondCtx) : null;
      const ensureGuards = precond ? guardConjuncts(precond) : [];

      for (const choiceMsg of subs(tpl, S.DefTemplate.choices)) {
        const choice = raw.ctx.str(int(choiceMsg, S.TemplateChoice.nameInternedStr));
        const argBinder = sub(choiceMsg, S.TemplateChoice.argBinder);
        const argParam = argBinder
          ? raw.ctx.str(int(argBinder, S.VarWithType.varInternedStr))
          : null;

        const ctx = makeCtx(raw.ctx, { selfParam, argParam, label: `${template}.${choice}`, bound });
        // carry the precondition's discovered symbols into this choice
        for (const [k, v] of precondCtx.params) ctx.params.set(k, v);
        // ...and the abstractions it made: the ensure guards travel onto every
        // choice, so the reasons behind their uninterpreted symbols have to
        // travel with them or a verdict would name a symbol it cannot explain.
        ctx.uninterpreted.push(...precondCtx.uninterpreted);

        const creates = [];
        const unsupported = [];
        const update = sub(choiceMsg, S.TemplateChoice.update);
        collectEffects(update, ctx, [], creates, unsupported);

        if (ctx.sawOpaqueApp) {
          unsupported.push({
            why: 'the body applies functions the translation does not model, so effects may be missing',
          });
        }

        out.push({
          module: mod.name,
          template,
          choice,
          consuming: !!int(choiceMsg, S.TemplateChoice.consuming, 0),
          selfParam,
          argParam,
          params: [...ctx.params.values()],
          guards: [...ensureGuards],
          creates,
          divisions: ctx.divisions.map((d) => ({
            denominator: d.denominator,
            ...(d.fold ? { fold: d.fold, index: d.index } : {}),
          })),
          rounding: [...new Set(ctx.rounding)],
          uninterpreted: dedupeUninterpreted(ctx.uninterpreted),
          symbolicElements: ctx.symbolicElements.slice(),
          consumesOthers: ctx.consumesOthers.slice(),
          archivedInputs: dedupeArchived(ctx.archivedInputs),
          unmodelledLoopEffects: ctx.unmodelledLoopEffects.slice(),
          listElements: dedupeElements(ctx.listElements),
          bound,
          unsupported,
          location: readLocation(choiceMsg, S.TemplateChoice.location, raw.ctx) || tplLocation,
        });
      }

      // Interface instances: each interface CHOICE, exercised against this
      // implementing template, is a transition whose body is the instance
      // METHOD the choice's update dispatches to via call_interface.
      for (const implMsg of subs(tpl, S.DefTemplate.implements)) {
        interfaceInstanceTransitions({
          raw,
          mod,
          template,
          selfParam,
          implMsg,
          ensureGuards,
          precondCtx,
          tplLocation,
          bound,
          out,
        });
      }
    }
  }
  return out;
}

/** Source span of a definition, or null. LF stores 0-based lines; 1-based out. */
function readLocation(msg, field, pkg) {
  if (!msg) return null;
  const loc = sub(msg, field);
  if (!loc) return null;
  const range = sub(loc, S.Location.range);
  if (!range) return null;
  const out = {
    startLine: int(range, S.Range.startLine) + 1,
    endLine: int(range, S.Range.endLine) + 1,
  };
  const modRef = sub(loc, S.Location.module);
  if (modRef && has(modRef, S.ModuleId.moduleNameInternedDname)) {
    out.module = pkg.dname(int(modRef, S.ModuleId.moduleNameInternedDname));
  }
  return out;
}

/**
 * Find the DefInterface an `implements` block points at: in this package's
 * modules, or in the dependency package the TypeConId names (readDarRaw
 * exposes those; a bare decodeDalfRaw does not, and that absence is reported
 * rather than skipped).
 */
function resolveInterfaceDef(implMsg, raw) {
  const ifc = sub(implMsg, S.Implements.interface);
  if (!ifc) return { error: 'interface instance carries no interface reference' };
  const name = raw.ctx.dname(int(ifc, S.TypeConId.nameInternedDname));
  const moduleRef = sub(ifc, S.TypeConId.module);
  const moduleName = moduleRef
    ? raw.ctx.dname(int(moduleRef, S.ModuleId.moduleNameInternedDname))
    : null;

  let pkgId = null;
  const pkgRef = moduleRef ? sub(moduleRef, S.ModuleId.packageId) : null;
  if (pkgRef) {
    if (has(pkgRef, S.SelfOrImportedPackageId.importedPackageIdInternedStr)) {
      pkgId = raw.ctx.str(int(pkgRef, S.SelfOrImportedPackageId.importedPackageIdInternedStr));
    } else if (has(pkgRef, S.SelfOrImportedPackageId.packageImportId)) {
      pkgId = raw.ctx.importedPackages[int(pkgRef, S.SelfOrImportedPackageId.packageImportId)] ?? null;
    }
  }

  let owner = raw;
  if (pkgId && pkgId !== raw.ctx.selfPackageId) {
    owner = raw.getPackage ? raw.getPackage(pkgId) : null;
    if (!owner) {
      return {
        name,
        error: `interface ${name} is declared in package ${pkgId.slice(0, 12)}..., which this reader cannot resolve`,
      };
    }
  }
  for (const mod of owner.modules) {
    if (moduleName && mod.name !== moduleName) continue;
    for (const iface of mod.interfaces) {
      if (owner.ctx.dname(int(iface, S.DefInterface.tyconInternedDname)) === name) {
        return { name, iface, pkg: owner.ctx };
      }
    }
  }
  return { name, error: `interface ${name} was not found in its declaring package` };
}

/** Emit one transition per interface choice for one `interface instance`. */
function interfaceInstanceTransitions({
  raw,
  mod,
  template,
  selfParam,
  implMsg,
  ensureGuards,
  precondCtx,
  tplLocation,
  bound,
  out,
}) {
  const resolved = resolveInterfaceDef(implMsg, raw);
  const implLocation = readLocation(implMsg, S.Implements.location, raw.ctx) || tplLocation;

  // The instance's method bodies live in THIS package regardless of where the
  // interface is declared.
  const methods = new Map();
  const body = sub(implMsg, S.Implements.body);
  if (body) {
    for (const m of subs(body, S.InterfaceInstanceBody.methods)) {
      methods.set(raw.ctx.str(int(m, S.InterfaceInstanceMethod.methodInternedName)), {
        expr: sub(m, S.InterfaceInstanceMethod.value),
        pkg: raw.ctx,
      });
    }
  }

  if (resolved.error) {
    // Reported, never skipped: the instance exists, its choices do not appear,
    // and this row says why.
    out.push({
      module: mod.name,
      template,
      choice: '*',
      via: resolved.name || '<unknown interface>',
      consuming: false,
      selfParam,
      argParam: null,
      params: [],
      guards: [],
      creates: [],
      divisions: [],
      rounding: [],
      uninterpreted: [],
      archivedInputs: [],
      unmodelledLoopEffects: [],
      listElements: [],
      bound,
      unsupported: [{ why: resolved.error }],
      location: implLocation,
    });
    return;
  }

  const ifacePkg = resolved.pkg;
  const ifaceParam = ifacePkg.str(int(resolved.iface, S.DefInterface.paramInternedStr));

  for (const choiceMsg of subs(resolved.iface, S.DefInterface.choices)) {
    const choice = ifacePkg.str(int(choiceMsg, S.TemplateChoice.nameInternedStr));
    const argBinder = sub(choiceMsg, S.TemplateChoice.argBinder);
    const argParam = argBinder
      ? ifacePkg.str(int(argBinder, S.VarWithType.varInternedStr))
      : null;
    const selfBinder = has(choiceMsg, S.TemplateChoice.selfBinderInternedStr)
      ? ifacePkg.str(int(choiceMsg, S.TemplateChoice.selfBinderInternedStr))
      : null;

    const label = `${template}.${choice} (via ${resolved.name})`;
    // The choice's update expression lives in the interface's package: that is
    // the starting interning context. The interface parameter denotes the
    // contract the choice runs on - for THIS instance, the template record.
    const ctx = makeCtx(ifacePkg, {
      selfParam: ifaceParam,
      argParam,
      label,
      dispatch: { methods },
      bound,
    });
    // The template's own parameter names the same record once dispatch enters
    // the implementing package's method bodies.
    if (selfParam && !ctx.env.has(selfParam)) ctx.env.set(selfParam, T.record('this'));
    if (selfBinder && !ctx.env.has(selfBinder)) {
      ctx.env.set(selfBinder, T.unsupported('the exercised contract id `self`', label));
    }
    for (const [k, v] of precondCtx.params) ctx.params.set(k, v);
    ctx.uninterpreted.push(...precondCtx.uninterpreted);

    const creates = [];
    const unsupported = [];
    collectEffects(sub(choiceMsg, S.TemplateChoice.update), ctx, [], creates, unsupported);
    if (ctx.sawOpaqueApp) {
      unsupported.push({
        why: 'the body applies functions the translation does not model, so effects may be missing',
      });
    }

    out.push({
      module: mod.name,
      template,
      choice,
      via: resolved.name,
      consuming: !!int(choiceMsg, S.TemplateChoice.consuming, 0),
      selfParam,
      argParam,
      params: [...ctx.params.values()],
      guards: [...ensureGuards],
      creates,
      divisions: ctx.divisions.map((d) => ({
        denominator: d.denominator,
        ...(d.fold ? { fold: d.fold, index: d.index } : {}),
      })),
      rounding: [...new Set(ctx.rounding)],
      uninterpreted: dedupeUninterpreted(ctx.uninterpreted),
      symbolicElements: ctx.symbolicElements.slice(),
      consumesOthers: ctx.consumesOthers.slice(),
      archivedInputs: dedupeArchived(ctx.archivedInputs),
      unmodelledLoopEffects: ctx.unmodelledLoopEffects.slice(),
      listElements: dedupeElements(ctx.listElements),
      bound,
      unsupported,
      location: implLocation,
    });
  }
}

/**
 * One entry per (list, effect): an archive loop is walked once and stands for
 * every element, so repeating it would suggest a count the walk never made.
 */
function dedupeArchived(entries) {
  const seen = new Map();
  for (const e of entries || []) seen.set(`${e.listName}\u0000${e.effect}`, e);
  return [...seen.values()];
}

/**
 * One entry per uninterpreted symbol, keyed by name: the same abstraction
 * reached twice is one modelling decision, not two.
 */
function dedupeUninterpreted(entries) {
  const seen = new Map();
  for (const e of entries || []) if (!seen.has(e.name)) seen.set(e.name, e);
  return [...seen.values()];
}

/** One entry per (list, index) element record introduced by fold unrolling. */
function dedupeElements(entries) {
  const seen = new Map();
  for (const e of entries || []) seen.set(`${e.listName}\u0000${e.index}`, e);
  return [...seen.values()];
}

/**
 * Walk the monadic body of a choice, collecting `create`s and the path
 * conditions under which they happen.
 *
 * Anything that is not a shape we model is pushed onto `unsupported` with the
 * reason. It is never skipped silently: a choice whose body we only partly
 * understand must not be reported as verified.
 */
function collectEffects(expr, ctx, path, creates, unsupported, depth = 0) {
  if (!expr) return;
  if (depth > 80) {
    unsupported.push({ why: 'choice body nested deeper than the walker follows' });
    return;
  }

  // follow interned expressions and hoisted values
  if (has(expr, S.Expr.internedExpr)) {
    const target = ctx.pkg.internedExprs[int(expr, S.Expr.internedExpr)];
    if (!target) {
      unsupported.push({ why: 'interned expression missing from the table' });
      return;
    }
    return collectEffects(target, ctx, path, creates, unsupported, depth + 1);
  }
  const valRef = ctx.pkg.resolveValue(expr);
  if (valRef) {
    if (ctx.seenValues && ctx.seenValues.has(valRef.key)) {
      unsupported.push({ why: `recursive value ${valRef.name}` });
      return;
    }
    ctx.seenValues = ctx.seenValues || new Set();
    ctx.seenValues.add(valRef.key);
    const prevPkg = ctx.pkg;
    ctx.pkg = valRef.pkg || prevPkg;
    try {
      collectEffects(valRef.body, ctx, path, creates, unsupported, depth + 1);
    } finally {
      ctx.pkg = prevPkg;
      ctx.seenValues.delete(valRef.key);
    }
    return;
  }

  // A variable can carry an update built elsewhere (`let act = create ...` or
  // a worker parameter bound to an action at the call site); running it here
  // means the effects live behind the binding, so chase it. Do-block binders
  // are excluded: they hold the RESULT of an action already collected at its
  // bind site, and re-descending would double-count the effect.
  if (has(expr, S.Expr.varInternedStr)) {
    const name = ctx.pkg.str(int(expr, S.Expr.varInternedStr));
    const entry = ctx.rawEnv.get(name);
    if (entry && entry.expr && entry.kind !== 'do') {
      const prevPkg = ctx.pkg;
      ctx.pkg = entry.pkg || prevPkg;
      ctx.rawEnv.delete(name); // no self-reference loops
      try {
        collectEffects(entry.expr, ctx, path, creates, unsupported, depth + 1);
      } finally {
        ctx.rawEnv.set(name, entry);
        ctx.pkg = prevPkg;
      }
    }
    return;
  }

  // lambdas are transparent here
  for (const fn of [S.Expr.abs, S.Expr.tyAbs, S.Expr.tyApp]) {
    const inner = sub(expr, fn);
    if (inner) {
      const body = sub(inner, fn === S.Expr.tyApp ? 1 : 2);
      return collectEffects(body, ctx, path, creates, unsupported, depth + 1);
    }
  }

  // a branch contributes a path condition to each side
  const cse = sub(expr, S.Expr.case);
  if (cse) {
    const scrut = translateExpr(sub(cse, 1), ctx);
    const alts = subs(cse, 2);
    if (alts.length !== 2 || scrut.k === 'unsupported') {
      unsupported.push({ why: 'branch on a value outside the translated fragment' });
      // still descend, so creates below are not missed, but with no refinement
      for (const alt of alts) {
        collectEffects(sub(alt, S.CaseAlt.body), ctx, path, creates, unsupported, depth + 1);
      }
      return;
    }
    for (const alt of alts) {
      const body = sub(alt, S.CaseAlt.body);
      let cond = null;
      if (has(alt, S.CaseAlt.builtinCon)) {
        const con = int(alt, S.CaseAlt.builtinCon);
        cond = con === BC.CON_TRUE ? scrut : T.app('not', [scrut]);
      }
      collectEffects(body, ctx, cond ? [...path, cond] : path, creates, unsupported, depth + 1);
    }
    return;
  }

  // let bindings: bind the name, then walk the body
  const letBlock = sub(expr, S.Expr.let);
  if (letBlock) {
    const saved = bindBlock(letBlock, ctx);
    collectEffects(sub(letBlock, S.Block.body), ctx, path, creates, unsupported, depth + 1);
    restore(saved, ctx);
    return;
  }

  const update = sub(expr, S.Expr.update);
  if (!update) {
    // A choice body compiles to `App(Abs([this, self, arg], body), args)`, so
    // the effects sit under an application. Descend into the function and each
    // argument rather than treating the whole body as opaque.
    const app = sub(expr, S.Expr.app);
    if (app) {
      const before = creates.length + unsupported.length;

      // A traversal over a list WE CAN NAME is walked with its parameter bound
      // to an element of that list, so a consuming effect inside it is
      // recorded as archiving the elements of THAT list - the same symbols a
      // fold over the same list produces. Tried before beta reduction, which
      // would inline the traversal into an opaque dictionary application and
      // lose the connection to the list.
      if (collectTraversal(expr, ctx, path, creates, unsupported, depth)) return;

      // Beta reduce first: the choice body is a hoisted worker applied to
      // `this` / `self` / `arg`, so without this the creates are unreachable.
      const rawArgs = many(app, 2).filter((v) => v instanceof Uint8Array);
      const reduced = betaReduce(deref(sub(app, 1), ctx), rawArgs, ctx);
      if (reduced) {
        try {
          // A builtin reduced to a term is pure arithmetic: no ledger effect.
          if (!reduced.term) {
            collectEffects(reduced.body, ctx, path, creates, unsupported, depth + 1);
          }
        } finally {
          reduced.restore();
        }
        return;
      }

      const fun = sub(app, 1);
      if (fun) collectEffects(fun, ctx, path, creates, unsupported, depth + 1);
      for (const argBytes of many(app, 2)) {
        if (!(argBytes instanceof Uint8Array)) continue;
        let argExpr;
        try {
          argExpr = decodeMessage(argBytes);
        } catch (_) {
          continue;
        }
        collectEffects(argExpr, ctx, path, creates, unsupported, depth + 1);
      }
      // Most applications carry type and dictionary arguments and perform no
      // ledger action, so a per-site complaint would drown the report. Record
      // the fact once per choice instead, and only when nothing was recovered.
      if (creates.length + unsupported.length === before) ctx.sawOpaqueApp = true;
    }
    return;
  }

  // pure / get_time: no ledger effect
  if (has(update, S.Update.pure) || has(update, S.Update.getTime)) return;

  // do-block
  const block = sub(update, S.Update.block);
  if (block) {
    const saved = bindBlock(block, ctx, (bound) =>
      collectEffects(bound, ctx, path, creates, unsupported, depth + 1)
    );
    collectEffects(sub(block, S.Block.body), ctx, path, creates, unsupported, depth + 1);
    restore(saved, ctx);
    return;
  }

  // create: the shape we are here for
  const create = sub(update, S.Update.create);
  if (create) {
    const target = createTargetName(sub(create, 1), ctx);
    const { base, fields } = recordFields(sub(create, 2), ctx, unsupported);
    creates.push({ template: target || '<unknown>', base, fields, path: [...path] });
    return;
  }

  // any other ledger effect: named, not silently dropped
  //
  // `consumesOthers` is tracked separately from the general unsupported list
  // because it changes WHICH PROPERTY is true, not just how much of the body
  // we saw. A choice that exercises or archives contracts besides `this` (a
  // merge consuming its inputs) does not satisfy `sum(created) = this.amount`
  // at all; the correct statement adds the consumed contracts' amounts. Left
  // undistinguished, such a choice gets a spurious DISPROVED against a
  // property nobody claimed. Conservation therefore refuses it outright (see
  // smt.js) rather than answering the wrong question.
  const CONSUMING_EFFECTS = new Set([
    S.Update.exercise,
    S.Update.exerciseInterface,
    S.Update.exerciseByKey,
  ]);
  for (const [field, label] of [
    [S.Update.exercise, 'exercise'],
    [S.Update.exerciseInterface, 'exercise (interface)'],
    [S.Update.exerciseByKey, 'exerciseByKey'],
    [S.Update.createInterface, 'create (interface)'],
    [S.Update.fetch, 'fetch'],
    [S.Update.fetchByKey, 'fetchByKey'],
    [S.Update.lookupByKey, 'lookupByKey'],
    [S.Update.tryCatch, 'try/catch'],
    [S.Update.embedExpr, 'embedded expression'],
  ]) {
    if (has(update, field)) {
      unsupported.push({ why: `${label} in the choice body is outside the modelled fragment` });
      if (CONSUMING_EFFECTS.has(field) && ctx.consumesOthers) {
        // Inside a traversal over a named list, an `Archive` exercise ON THE
        // ELEMENT is an archived input we can state; anything else keeps the
        // refusal. See ARCHIVING_CHOICE for why the choice name is checked
        // rather than assumed.
        const archived = archivedElement(update, field, ctx);
        if (archived) ctx.archivedInputs.push({ listName: archived.listName, effect: label });
        else ctx.consumesOthers.push({ effect: label });
      }
      return;
    }
  }
  unsupported.push({ why: 'unrecognised ledger effect' });
}

/**
 * Walk a list traversal (`mapA f xs`, `mapA_ f xs`) whose list has a canonical
 * name, with `f`'s parameter bound to an ELEMENT of that list.
 *
 * This is the archived-input half of the merge story. The compiled archive
 * loop is `mapA_ (\cid -> exercise Archive (toInterfaceContractId cid))
 * arg.holdings`; walked this way, the exercised contract id reduces to the
 * element record `arg.holdings$*`, so the effect is recorded as "every element
 * of arg.holdings is archived" rather than as an unidentified consuming
 * effect. The amounts it contributes are then the same `arg.holdings$i.amount`
 * symbols the fold over the same list produced.
 *
 * The element is a single marker rather than one record per index: the
 * traversal applies f to EVERY element, so what the walk establishes is
 * uniform in i, and the property expands it to indices 0..k-1 at each bound.
 *
 * Returns false (and changes nothing) when the shape is not a recognised
 * traversal, when its list cannot be named, or when the function cannot be
 * applied - in every one of those cases the caller falls back to the existing
 * descent, which ends in the `consumesOthers` refusal.
 *
 * A create inside the loop is NOT modelled: there would be one per element,
 * and no total over the created contracts could be stated. That is recorded
 * as a refusal (`unmodelledLoopEffects`), never dropped.
 */
function collectTraversal(expr, ctx, path, creates, unsupported, depth) {
  if (!ctx.archivedInputs) return false;
  if (ctx.loopElement) return false; // one element family at a time
  const tr = matchTraversal(expr, ctx);
  if (!tr) return false;
  const listName = withPkg(ctx, tr.list.pkg, () =>
    listNameOfExpr(decodeExpr(tr.list.bytes), ctx)
  );
  if (!listName) return false;
  const fnExpr = decodeExpr(tr.fn.bytes);
  if (!fnExpr) return false;

  // `$*` rather than an index: the walk establishes what happens to an
  // ARBITRARY element, uniformly in i. Recorded as a symbolic element so a
  // verdict that leaned on arithmetic inside the loop discloses the
  // quantification, exactly as it does for an unapplied lambda's parameters.
  const marker = `${listName}$*`;
  ctx.symbolicElements.push({ param: `an element of ${listName}`, root: marker, at: ctx.label });
  const loopCreates = [];
  const loopUnsupported = [];
  let entered = false;
  const savedLoop = ctx.loopElement;
  ctx.loopElement = { listName, marker };
  try {
    withPkg(ctx, tr.fn.pkg, () =>
      applyToTerms(fnExpr, [T.record(marker)], ctx, 0, (body) => {
        entered = true;
        collectEffects(body, ctx, path, loopCreates, loopUnsupported, depth + 1);
        return T.bool(true);
      })
    );
  } finally {
    ctx.loopElement = savedLoop;
  }
  if (!entered) return false;

  for (const u of loopUnsupported) unsupported.push(u);
  if (loopCreates.length) {
    const why =
      `${loopCreates.length} create(s) inside a traversal over \`${listName}\`: one create ` +
      `PER ELEMENT is not modelled, so no total over the created contracts can be stated`;
    ctx.unmodelledLoopEffects.push({ why });
    unsupported.push({ why });
  }
  return true;
}

/**
 * Is this consuming effect the archival of the element the enclosing traversal
 * is walking? Returns `{listName}` when it is, null otherwise.
 *
 * Both halves are checked, because assuming either would be unsound:
 *   * the exercised contract id must reduce to the loop's element (an exercise
 *     on some other, fixed contract inside a loop archives one contract, not
 *     one per element);
 *   * the choice must be `Archive` (a nonconsuming choice archives nothing,
 *     and counting it as archived would license minting the inputs' amounts
 *     into the created contract - see ARCHIVING_CHOICE).
 */
function archivedElement(update, field, ctx) {
  if (!ctx.loopElement) return null;
  const caseMsg = sub(update, field);
  if (!caseMsg) return null;
  const spec = S.UPDATE_OPS[field];
  const choiceField = spec && spec.choiceField;
  if (choiceField === undefined || !has(caseMsg, choiceField)) return null;
  if (ctx.pkg.str(int(caseMsg, choiceField)) !== ARCHIVING_CHOICE) return null;
  // exerciseByKey names its target by key, not by contract id, so there is
  // nothing to match the loop element against: it stays an unidentified
  // consuming effect.
  const CID_MESSAGE = {
    [S.Update.exercise]: 'Update.Exercise',
    [S.Update.exerciseInterface]: 'Update.ExerciseInterface',
  };
  if (!CID_MESSAGE[field]) return null;
  const cidField = S.message(CID_MESSAGE[field]).cid;
  if (cidField === undefined || !has(caseMsg, cidField)) return null;
  const cid = translateExpr(sub(caseMsg, cidField), ctx);
  if (!(cid && cid.k === 'record' && cid.root === ctx.loopElement.marker)) return null;
  return { listName: ctx.loopElement.listName };
}

/**
 * Bind a Block's binders into ctx.env (+ rawEnv), returning saved shadows.
 *
 * `onBound` is passed only for MONADIC blocks (a do-block's `x <- act`), where
 * the bound expression is an action to collect effects from and the binder
 * holds its result. Without it the block is a plain `let`, where the binder
 * holds the expression's value itself. rawEnv entries carry that distinction
 * (`kind`) plus the package their expression must be read against.
 */
function bindBlock(block, ctx, onBound) {
  const saved = [];
  for (const binding of subs(block, S.Block.bindings)) {
    const binder = sub(binding, S.Binding.binder);
    const name = binder ? ctx.pkg.str(int(binder, S.VarWithType.varInternedStr)) : null;
    const bound = sub(binding, S.Binding.bound);
    if (onBound && bound) onBound(bound);
    if (!name) continue;
    saved.push([
      name,
      ctx.env.has(name) ? ctx.env.get(name) : undefined,
      ctx.rawEnv.has(name) ? ctx.rawEnv.get(name) : undefined,
    ]);
    // The result of a bound update is a contract id or similar: opaque, but
    // named, so a later reference resolves to something honest.
    const term = bound ? translateExpr(bound, ctx) : T.unsupported('empty binding', ctx.label);
    ctx.env.set(name, term);
    if (bound) ctx.rawEnv.set(name, { expr: bound, pkg: ctx.pkg, kind: onBound ? 'do' : 'let' });
    else ctx.rawEnv.delete(name);
  }
  return saved;
}

function restore(saved, ctx) {
  for (const entry of saved.reverse()) {
    const [name, prev, prevRaw] = entry;
    if (prev === undefined) ctx.env.delete(name);
    else ctx.env.set(name, prev);
    if (entry.length > 2) {
      if (prevRaw === undefined) ctx.rawEnv.delete(name);
      else ctx.rawEnv.set(name, prevRaw);
    }
  }
}

function createTargetName(tycon, ctx) {
  if (!tycon) return null;
  const idx = int(tycon, S.TypeConId.nameInternedDname);
  const name = ctx.pkg.dname(idx);
  return name && !name.startsWith('<dname:') ? name : null;
}

/**
 * Field-by-field translation of the record a `create` is given.
 *
 * Two shapes matter, and the second is the common one in Daml:
 *
 *   create Foo with a = x, b = y     ->  RecCon, every field written out
 *   create this with amount = newAmt ->  RecUpd over the template parameter,
 *                                        one override, everything else
 *                                        inherited from `this`
 *
 * For the RecUpd form the result carries `base: 'this'`, which lets a property
 * treat an un-overridden field as equal to the pre-state field rather than as
 * unknown. Reading that shape as "not a literal record" would have made every
 * split/merge choice unanalysable.
 *
 * @returns {{base: string|null, fields: Record<string, Term>}}
 */
function recordFields(expr, ctx, unsupported, depth = 0) {
  /** @type {Record<string, Term>} */
  const fields = {};
  if (depth > 12) {
    unsupported.push({ why: 'record chased through too many bindings' });
    return { base: null, fields };
  }
  let node = deref(expr, ctx);

  // Peel a chain of record updates, innermost last.
  for (let i = 0; i < 32 && node; i++) {
    const upd = sub(node, S.Expr.recUpd);
    if (!upd) break;
    const name = ctx.pkg.str(int(upd, S.RecUpd.fieldInternedStr));
    // An outer update wins over an inner one for the same field.
    if (!(name in fields)) fields[name] = translateExpr(sub(upd, S.RecUpd.update), ctx);
    node = deref(sub(upd, S.RecUpd.record), ctx);
  }

  if (node && has(node, S.Expr.varInternedStr)) {
    const root = ctx.pkg.str(int(node, S.Expr.varInternedStr));
    const bound = ctx.env.get(root);
    // The variable IS the template record: un-overridden fields inherit.
    if (bound && bound.k === 'record' && bound.root === 'this') return { base: 'this', fields };
    if (bound && bound.k === 'record' && bound.root === 'arg') return { base: 'arg', fields };
    // Otherwise chase the RAW expression the variable was bound to: this is
    // the call-site record construction the compiler moved out of the worker.
    // The bound expression is read against the package it was collected in.
    if (ctx.rawEnv.has(root)) {
      const entry = ctx.rawEnv.get(root);
      const prevPkg = ctx.pkg;
      ctx.pkg = entry.pkg || prevPkg;
      let inner;
      try {
        inner = recordFields(entry.expr, ctx, unsupported, depth + 1);
      } finally {
        ctx.pkg = prevPkg;
      }
      // overrides applied on the way down win over the inner record's fields
      return { base: inner.base, fields: { ...inner.fields, ...fields } };
    }
    unsupported.push({ why: `create from record variable \`${root}\` with no known binding` });
    return { base: null, fields };
  }

  const rec = node ? sub(node, S.Expr.recCon) : null;
  if (rec) {
    for (const f of subs(rec, S.RecCon.fields)) {
      const name = ctx.pkg.str(int(f, S.FieldWithExpr.fieldInternedStr));
      if (!(name in fields)) fields[name] = translateExpr(sub(f, S.FieldWithExpr.expr), ctx);
    }
    return { base: null, fields };
  }

  unsupported.push({ why: 'create argument is neither a record construction nor an update of `this`' });
  return { base: null, fields };
}

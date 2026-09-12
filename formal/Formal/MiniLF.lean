/-
  Formal/MiniLF.lean

  MiniLF: a faithful fragment of Daml-LF expressions, formalized as an
  intrinsically sorted inductive type. This is the SOURCE side of the
  translation arrow that backend/lfir.js implements in JavaScript; the Lean
  translation (Formal/Translate.lean) mirrors that code, and
  Formal/TranslateCorrect.lean proves it semantics-preserving. Together they
  move the machine-checked boundary one arrow left: from "the IR transition
  conserves" to "the MiniLF transition conserves".

  WHAT MiniLF COVERS, case by case against backend/lfir.js translateInner
  (the happy path: the cases that produce a supported term rather than
  `unsupported`). Line references are to the shapes handled, not literal
  line numbers, since the file evolves.

    lfir.js translateInner case          MiniLF constructor      notes
    -----------------------------------  ----------------------  --------------
    builtinLit int64 /                   num (v : Rat)           the JS carries the
      numericInternedStr -> T.num(str)                           literal's decimal
                                                                 string; Lean carries
                                                                 the rational that
                                                                 string denotes. The
                                                                 string->Rat reading is
                                                                 the same trusted paper
                                                                 arrow already noted for
                                                                 Term.num in Term.lean.
    builtinCon CON_TRUE / CON_FALSE      boolLit (v : Bool)      T.bool(v).
      -> T.bool(v)
    recProj chain whose base translates  proj (root) (path)      symbol(ctx, root, path,
      to T.record(root)                                          'Real') registers and
      -> symbol(...) = T.varRef(         Root := this | arg      returns the IR variable
         `${root}.${path}`, 'Real')                              named root ++ "." ++
                                                                 path. `this` is the
                                                                 template parameter,
                                                                 `arg` the choice
                                                                 argument (makeCtx binds
                                                                 selfParam/argParam to
                                                                 T.record('this'/'arg')).
                                                                 lfir.js always registers
                                                                 projections at sort
                                                                 'Real', so proj is
                                                                 Real-sorted here. The
                                                                 dotted multi-segment
                                                                 path (segments joined
                                                                 with ".") is carried as
                                                                 one String; the
                                                                 path-extension case in
                                                                 translateInner (a
                                                                 projection off an
                                                                 already-registered
                                                                 symbol) produces the
                                                                 same symbol a single
                                                                 longer proj denotes,
                                                                 so MiniLF models the
                                                                 RESULT of that
                                                                 mechanism, not the
                                                                 mechanism.
    translateApp/translateBuiltinApp     addN, subN, mulN, divN  BINOP rows: ADD_* '+',
      with a BINOP builtin, applied to                           SUB_* '-', MUL_* '*',
      its two value arguments                                    DIV_NUMERIC '/'.
      (valueArgs = terms.slice(-2):      lt, le, gt, ge          LESS '<', LESS_EQ '<=',
      dictionary/scale arguments ahead                           GREATER '>',
      of the two values are dropped                              GREATER_EQ '>='.
      by the JS; MiniLF constructors     eqN                     EQUAL '=' at the Real
      are binary, i.e. they model the                            sort (the Bool instance
      post-slice application)                                    of the polymorphic '='
                                                                 is NOT in MiniLF; see
                                                                 exclusions).
    T.app('not', [c])                    notB                    lfir.js has no NOT
                                                                 builtin in BINOP; its
                                                                 'not' nodes are built by
                                                                 guardConjuncts when it
                                                                 decomposes
                                                                 ite(c, False|abort, b)
                                                                 into (not c) and b.
                                                                 MiniLF includes boolean
                                                                 negation so guards of
                                                                 that shape are
                                                                 expressible at the
                                                                 source level.
    translateCase, exactly two           ite (c) (a b)           the two-alternative Bool
      alternatives resolving to                                  case (CON_TRUE /
      CON_TRUE/CON_FALSE (or default)                            CON_FALSE / default) is
      -> T.ite(scrut, whenTrue,                                  the compiled form of
         whenFalse)                                              if-then-else AND of the
                                                                 short-circuit operators
                                                                 (&&, || compile to a
                                                                 Bool case), so Bool-
                                                                 sorted ite is how
                                                                 conjunction reaches this
                                                                 fragment. Indexed by s:
                                                                 branches at either sort,
                                                                 like Term.ite.
    let block (S.Expr.let): each         letE (name) (bound)     lfir.js translates the
      binding's bound expression is        (body)                bound expression FIRST,
      translated, then bound in                                  binds the resulting TERM
      ctx.env; the body is translated                            in ctx.env, translates
      under the extended env; the env                            the body, then restores.
      is restored afterwards                                     That is translation-time
                                                                 substitution, mirrored
                                                                 exactly by
                                                                 Formal/Translate.lean.
                                                                 A multi-binding Block is
                                                                 sequential (each bound
                                                                 sees the previous
                                                                 binders), which is
                                                                 nested letE.
    varInternedStr with a ctx.env hit    varL (name) (s)         reference to a let-bound
      -> the bound term                                          (or, in JS, parameter-
                                                                 bound) name. lfir.js
                                                                 returns `unsupported`
                                                                 for an UNBOUND name;
                                                                 MiniLF keeps varL total
                                                                 by giving translation
                                                                 and evaluation default
                                                                 environments, and the
                                                                 correctness theorem
                                                                 carries an agreement
                                                                 hypothesis instead (see
                                                                 TranslateCorrect.lean).

  DELIBERATELY EXCLUDED from MiniLF (each is either eliminated by lfir.js
  BEFORE this fragment is reached, or refused by the property layer, or an
  explicitly untranslated residue - see formal/Correspondence.md for the
  consolidated list):

    * Lambdas / beta reduction (S.Expr.abs, betaReduce, unwrapTypeLayers,
      over-application, cross-package value inlining). The compiler hoists
      choice bodies into workers applied to this/self/arg; lfir.js inlines
      those applications ON THE JS SIDE before any shape MiniLF models is
      reached. MiniLF is the post-inlining fragment; the inliner itself
      remains untrusted JS.
    * Records as first-class values (T.record, ctx.rawEnv, recordFields).
      T.record is an intermediate device of the translator: it is always
      projected away (becoming a proj symbol) before terms reach guards or
      amounts, and termToSmt throws on a surviving one. MiniLF bakes the
      device's OUTCOME into proj's root.
    * Rounding builtins (ROUND_NUMERIC, CAST_NUMERIC, SHIFT_NUMERIC,
      NUMERIC_TO_INT64, INT64_TO_NUMERIC). Translation records them in
      `rounding` and amountConservation REFUSES the property, so no
      conservation VC ever contains one; modelling them exactly would need a
      Numeric-10 fixed-point theory (stated future work).
    * DIV_INT64 / MOD_INT64 ('div' / 'mod'). Members of the rounding set,
      refused the same way; Term.divE/.modE exist on the IR side only so the
      IR covers its full operator list.
    * Text literals and Text equality (T.str). Sound at equality via SMT
      String, but a third sort would widen every statement here for a case
      the conservation fragment does not exercise; left with the JS layer.
    * The Bool instance of the polymorphic EQUAL ('=' at Bool, Term.eqB).
      Not produced by the numeric fragment; Daml Bool equality compiles to
      case analysis, which ite covers.
    * Optional case analysis (the $some/$value symbol pair), abort/throw and
      the guardConjuncts ensure-decomposition, interface dispatch
      (call_interface), and everything translateInner maps to
      `unsupported`. These stay on the untrusted-JS side of the boundary
      and are enumerated as residue in formal/Correspondence.md.

  Intrinsic sorting: like Term, MiniLF is indexed by Srt, so ill-sorted
  source expressions are unrepresentable and both evaluation
  (Formal/MiniLFEval.lean) and translation (Formal/Translate.lean) are total
  functions with no Option plumbing. The JS justification is the same as for
  Term: Daml-LF is a typed language and damlc emits well-typed packages, so
  the happy-path fragment only meets well-sorted shapes; anything else
  degrades to `unsupported`, which this type deliberately cannot represent.
-/
import Formal.Term

namespace Formal

open Std.Internal (Rat)

/--
  The root a projected field lives on: the template record (`this`, bound by
  makeCtx from the template's selfParam) or the choice-argument record
  (`arg`, bound from the choice's argParam). These are the only two roots
  lfir.js's makeCtx ever seeds, so the only two a happy-path projection can
  resolve to.
-/
inductive Root where
  | this : Root
  | arg  : Root
deriving DecidableEq, Repr

/-- The symbol-name prefix for a root: exactly the string lfir.js uses. -/
def Root.name : Root -> String
  | .this => "this"
  | .arg  => "arg"

/--
  MiniLF expressions, indexed by sort. Constructor-by-constructor
  correspondence with backend/lfir.js translateInner is documented in the
  header of this file.
-/
inductive MiniLF : Srt -> Type where
  -- literals
  | num     (v : Rat)  : MiniLF .real
  | boolLit (v : Bool) : MiniLF .bool
  -- projection of a Real-valued field path off `this` or `arg`
  -- (lfir.js `symbol`: always registered at sort 'Real')
  | proj (root : Root) (path : String) : MiniLF .real
  -- numeric builtins (BINOP: ADD/SUB/MUL/DIV_NUMERIC and the INT64 variants
  -- of the first three)
  | addN (a b : MiniLF .real) : MiniLF .real
  | subN (a b : MiniLF .real) : MiniLF .real
  | mulN (a b : MiniLF .real) : MiniLF .real
  | divN (a b : MiniLF .real) : MiniLF .real
  -- comparison builtins (LESS, LESS_EQ, GREATER, GREATER_EQ) and numeric
  -- equality (EQUAL at Real)
  | lt  (a b : MiniLF .real) : MiniLF .bool
  | le  (a b : MiniLF .real) : MiniLF .bool
  | gt  (a b : MiniLF .real) : MiniLF .bool
  | ge  (a b : MiniLF .real) : MiniLF .bool
  | eqN (a b : MiniLF .real) : MiniLF .bool
  -- boolean negation (the 'not' node guardConjuncts builds)
  | notB (a : MiniLF .bool) : MiniLF .bool
  -- two-alternative Bool case (translateCase), at either result sort
  | ite (c : MiniLF .bool) (a b : MiniLF s) : MiniLF s
  -- let-binding of a numeric or bool expression (S.Expr.let), and reference
  -- to a bound name (varInternedStr resolved through ctx.env)
  | letE {bs s : Srt} (name : String) (bound : MiniLF bs) (body : MiniLF s) : MiniLF s
  | varL (name : String) (s : Srt) : MiniLF s

end Formal

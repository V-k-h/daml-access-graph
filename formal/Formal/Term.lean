/-
  Formal/Term.lean

  The guarded-transition IR term language, as an indexed inductive type.

  CORRESPONDENCE with backend/lfir.js (the `T` constructors), field by field:

    JS constructor            Lean constructor        notes
    ------------------------  ----------------------  -------------------------------
    T.num(v)                  Term.num (v : Rat)      JS carries the decimal string
                                                      ("0.0000000000"); Lean carries
                                                      the exact rational that string
                                                      denotes. "d+.d*" with k digits
                                                      after the point denotes
                                                      mkRat mantissa (10^k). The
                                                      string->rational reading is a
                                                      trusted (paper) arrow; no code
                                                      crosses it.
    T.bool(v)                 Term.boolLit (v)        renamed to avoid clashing with
                                                      the sort constructor Srt.bool.
    T.varRef(name, sort)      Term.var name s         sort 'Real' ~ Srt.real,
                                                      'Bool' ~ Srt.bool.
    T.app('+',  [a, b])       Term.add a b            JS app is n-ary; an n-ary
    T.app('-',  [a, b])       Term.sub a b            (+ a b c ...) corresponds to a
    T.app('*',  [a, b])       Term.mul a b            fold of the binary form. All
    T.app('/',  [a, b])       Term.divR a b           these operators are associative
    T.app('div',[a, b])       Term.divE a b           in SMT-LIB, so the fold denotes
    T.app('mod',[a, b])       Term.modE a b           the same value. See VCGen for
    T.app('<',  [a, b])       Term.lt a b             the one place the pipeline
    T.app('<=', [a, b])       Term.le a b             builds n-ary nodes.
    T.app('>',  [a, b])       Term.gt a b
    T.app('>=', [a, b])       Term.ge a b
    T.app('=',  [a, b])       Term.eqR a b            '=' is polymorphic in the JS IR
                              Term.eqB a b            (see inferSorts in smt.js); the
                                                      indexed type splits it by sort.
    T.app('not',[a])          Term.notT a
    T.app('and',[a, b])       Term.andT a b           n-ary in JS: fold, as for '+'.
    T.app('or', [a, b])       Term.orT a b
    T.ite(c, a, b)            Term.ite c a b

  DELIBERATELY ABSENT constructors, and the trust boundary they mark:

    T.unsupported(why, at) has NO Lean counterpart. This type models only the
    SUPPORTED fragment. The JS side guarantees by construction that no term
    reaching the SMT emitter contains an unsupported node: termToSmt in
    backend/smt.js THROWS on one, and every property builder
    (amountConservation, divisionSafety, usableGuards) filters or refuses
    first. The theorem proved in Formal/Soundness.lean therefore covers
    exactly the terms expressible in this type. The claim that a given
    Daml-LF expression translates to a given term of this type is the
    UNTRUSTED arrow of the pipeline: it is exercised by the JS test suite,
    not machine-checked here. Formalizing Daml-LF semantics and proving the
    translator correct is stated future work, not something this development
    claims.

    T.record(root) also has NO counterpart: it is an intermediate device of
    the translator (aliasing `this` through curried worker parameters) and is
    always projected away before terms reach guards, amounts, or the emitter
    (termToSmt throws on it as a bug, not a report).

  Sorts: SMT-LIB Real is modelled as core Rat (Std.Internal.Rat), Bool as
  Bool. See Formal/Eval.lean for why Rat (with total division, x/0 = 0) does
  not weaken the theorem, and formal/Correspondence.md for the full argument
  relating Rat to SMT-LIB Real on the fragment the pipeline emits.
-/
import Std.Internal.Rat

namespace Formal

open Std.Internal (Rat)

/-- The two sorts of the IR: SMT-LIB 'Real' and 'Bool'. -/
inductive Srt where
  | real : Srt
  | bool : Srt
deriving DecidableEq, Repr

/--
  IR terms, indexed by sort. The index makes ill-sorted terms (which the JS
  side rejects dynamically via inferSorts in backend/smt.js) unrepresentable,
  and makes evaluation total: no Option, no sort errors.
-/
inductive Term : Srt -> Type where
  -- literals
  | num     (v : Rat)  : Term .real
  | boolLit (v : Bool) : Term .bool
  -- variables: a name at a sort. inferSorts rejects a name used at both
  -- sorts; here the two uses simply read different components of the
  -- environment (see Env in Formal/Eval.lean), which is harmless because the
  -- JS side never emits such a query at all.
  | var (name : String) (s : Srt) : Term s
  -- arithmetic (SMT-LIB Real ops)
  | add  (a b : Term .real) : Term .real
  | sub  (a b : Term .real) : Term .real
  | mul  (a b : Term .real) : Term .real
  | divR (a b : Term .real) : Term .real  -- '/'   (real division)
  | divE (a b : Term .real) : Term .real  -- 'div' (euclidean int division)
  | modE (a b : Term .real) : Term .real  -- 'mod' (euclidean int remainder)
  -- comparisons
  | lt  (a b : Term .real) : Term .bool
  | le  (a b : Term .real) : Term .bool
  | gt  (a b : Term .real) : Term .bool
  | ge  (a b : Term .real) : Term .bool
  | eqR (a b : Term .real) : Term .bool
  | eqB (a b : Term .bool) : Term .bool
  -- boolean connectives
  | notT (a : Term .bool)   : Term .bool
  | andT (a b : Term .bool) : Term .bool
  | orT  (a b : Term .bool) : Term .bool
  -- if-then-else, at either sort (mirrors T.ite)
  | ite (c : Term .bool) (a b : Term s) : Term s

end Formal

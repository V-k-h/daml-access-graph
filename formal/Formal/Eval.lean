/-
  Formal/Eval.lean

  Environments and TOTAL evaluation of IR terms.

  Because Term is indexed by sort (Formal/Term.lean), evaluation needs no
  Option: a Term .real always evaluates to a Rat and a Term .bool to a Bool.
  This is the "typed-by-construction" design; the dynamic sort checking the
  JS pipeline performs (inferSorts in backend/smt.js, which rejects sort
  conflicts) is what justifies modelling only well-sorted terms.

  NUMERIC CARRIER: SMT-LIB Real is modelled as core Rat (Std.Internal.Rat),
  with Lean's total-division convention x / 0 = 0 (Rat.div is mul by inv,
  and Rat.inv 0 = 0). Why this does not weaken the theorem:

    * SMT-LIB leaves (/ x 0) UNDERSPECIFIED: division is a total function
      whose value at 0 is not constrained. cvc5 therefore reports `unsat`
      only when the asserted formulas are unsatisfiable under EVERY total
      interpretation of division at 0. The convention x / 0 = 0 is one such
      interpretation, so a cvc5 `unsat` verdict entails validity of the VC
      under the semantics defined here. That is exactly the direction the
      soundness theorem consumes (valid VC implies conservation); nothing
      about x / 0 = 0 lets a false property be "proved".

    * Independently, the JS pipeline never relies on any value of x / 0:
      the separate `division-safety` property (backend/smt.js) proves each
      denominator nonzero under the guards, and conservation results are
      reported alongside it. The convention here mirrors, not extends, what
      the SMT layer already assumes.

  A further honest caveat, stated once: Rat equality in this file is the
  DecidableEq of Std.Internal.Rat, which is structural equality on the
  normalized (num, den) representation. Every Rat built by the public API
  (mkRat, the arithmetic ops, literals) is normalized, and on normalized
  values structural equality coincides with equality of rationals. The
  soundness proof in Formal/Soundness.lean does not depend on this: it never
  unfolds any Rat operation, so the theorem holds for ANY interpretation of
  the arithmetic symbols (a reviewer can check that replacing Rat by an
  arbitrary carrier with the same operations leaves every proof intact).
  The Rat instantiation matters only for the paper correspondence to
  SMT-LIB Real, argued in formal/Correspondence.md.

  WHAT IS NOT MODELLED: Daml Numeric 10 fixed-point rounding. The pipeline
  refuses conservation on transitions whose path uses rounding builtins
  (see `rounding` in backend/lfir.js and the refusal in amountConservation,
  backend/smt.js), so terms reaching a conservation VC are rounding-free and
  the exact-rational abstraction is faithful for them.
-/
import Formal.Term

namespace Formal

open Std.Internal (Rat mkRat)

/--
  Floor of a rational, as an integer. Defined from first principles because
  we only rely on: for a NORMALIZED q (den > 0), q.num.ediv q.den is the
  floor of q. (Core's Std.Internal.Rat.floor is not used.)
-/
def ratFloor (q : Rat) : Int :=
  q.num.ediv (Int.ofNat q.den)

/--
  Semantics of the IR op 'div': SMT-LIB integer euclidean division,
  totalized. For integer-valued x, y with y /= 0 this agrees with SMT-LIB
  (div x y): the quotient q with x = y * q + r and 0 <= r < |y|.
  At y = 0 SMT-LIB leaves div unconstrained; we pick 0 (same argument as for
  '/' above: cvc5 `unsat` covers every total extension, including this one).

  NOTE ON REACH: 'div' and 'mod' arise only from DIV_INT64 / MOD_INT64,
  which backend/lfir.js records in the transition's `rounding` set, and
  amountConservation REFUSES transitions carrying rounding. So these two
  operators never occur in an amount-conservation VC the pipeline actually
  emits; they are included so the Lean term language covers the full
  operator list of the IR.
-/
def smtDiv (x y : Rat) : Rat :=
  if y = 0 then 0
  else if 0 < y then mkRat (ratFloor (x / y)) 1
  else mkRat (-(ratFloor (x / (-y)))) 1

/-- Semantics of the IR op 'mod': the remainder matching smtDiv
    (x = y * (div x y) + (mod x y)); at y = 0 it degenerates to x. -/
def smtMod (x y : Rat) : Rat :=
  x - y * smtDiv x y

/--
  An environment: one value for every Real-sorted name and one for every
  Bool-sorted name. Two separate maps is the simple design; a name used at
  both sorts reads independent components, which the JS side anyway rejects
  (inferSorts conflict), so no emitted query distinguishes the designs.
-/
structure Env where
  realVar : String -> Rat
  boolVar : String -> Bool

/-- Denotation of a sort. Reducible so dependent matches in eval typecheck. -/
@[reducible] def Srt.denote : Srt -> Type
  | .real => Rat
  | .bool => Bool

/-- Look a name up at a sort. -/
def Env.get (env : Env) : (s : Srt) -> String -> s.denote
  | .real => env.realVar
  | .bool => env.boolVar

/--
  TOTAL evaluation. This is the Lean counterpart of the SEMANTICS that
  backend/smt.js assigns to terms by emitting SMT-LIB: each case is the
  standard reading of the operator it mirrors. (> and >= are evaluated as
  flipped < and <=, which is their SMT-LIB meaning.)
-/
def eval (env : Env) : {s : Srt} -> Term s -> s.denote
  | _, .num v      => v
  | _, .boolLit v  => v
  | _, .var n s    => env.get s n
  | _, .add a b    => eval env a + eval env b
  | _, .sub a b    => eval env a - eval env b
  | _, .mul a b    => eval env a * eval env b
  | _, .divR a b   => eval env a / eval env b        -- total: x / 0 = 0
  | _, .divE a b   => smtDiv (eval env a) (eval env b)
  | _, .modE a b   => smtMod (eval env a) (eval env b)
  | _, .lt a b     => decide (eval env a < eval env b)
  | _, .le a b     => decide (eval env a <= eval env b)
  | _, .gt a b     => decide (eval env b < eval env a)
  | _, .ge a b     => decide (eval env b <= eval env a)
  | _, .eqR a b    => decide (eval env a = eval env b)
  | _, .eqB a b    => eval env a == eval env b
  | _, .notT a     => !(eval env a)
  | _, .andT a b   => eval env a && eval env b
  | _, .orT a b    => eval env a || eval env b
  | _, .ite c a b  => cond (eval env c) (eval env a) (eval env b)

-- Definitional simp lemmas for the cases the proofs use. Each is `rfl`;
-- they exist so proofs do not depend on the shape of the compiled match.
@[simp] theorem eval_num  (env : Env) (v : Rat) :
    eval env (.num v) = v := rfl
@[simp] theorem eval_add  (env : Env) (a b : Term .real) :
    eval env (.add a b) = eval env a + eval env b := rfl
@[simp] theorem eval_eqR  (env : Env) (a b : Term .real) :
    eval env (.eqR a b) = decide (eval env a = eval env b) := rfl
@[simp] theorem eval_notT (env : Env) (a : Term .bool) :
    eval env (.notT a) = !(eval env a) := rfl
@[simp] theorem eval_andT (env : Env) (a b : Term .bool) :
    eval env (.andT a b) = (eval env a && eval env b) := rfl

end Formal

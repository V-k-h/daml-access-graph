/-
  Formal/VCGen.lean

  The verification-condition generator, mirroring backend/smt.js#buildQuery
  composed with backend/smt.js#amountConservation.

  buildQuery does not emit one formula: it asserts each guard g1 .. gn
  separately, asserts (not goal), and checks satisfiability. `unsat` of the
  set {g1, ..., gn, not goal} is equivalent to VALIDITY of the single
  formula
      (not (and g1 (and g2 (... (and gn (not goal))))))
  and that single formula is what vcgen builds. STRUCTURAL DIFFERENCES from
  the JS emission, all denotation-preserving:

    1. JS asserts guards separately; vcgen conjoins them (right fold).
    2. JS builds the created-amount sum as ONE n-ary node
       (+ a1 a2 ... an) for n >= 2 and as a1 alone for n = 1 (see
       amountConservation); sumT folds binary .add with the same n = 1
       special case. SMT-LIB (+ a b c) abbreviates the same left/right
       associated sum, so the denotations agree.
    3. The goal (= sum this.amount) is Term.eqR, the Real instance of the
       polymorphic JS '='.
-/
import Formal.Term
import Formal.Eval
import Formal.Transition

namespace Formal

/-- Term-level sum of the created amounts; shape documented above. -/
def sumT : List (Term .real) -> Term .real
  | []        => .num 0
  | [a]       => a
  | a :: rest => .add a (sumT rest)

/-- Conjoin guards onto a tail formula: g1 && (g2 && (... && tail)). -/
def conjT : List (Term .bool) -> Term .bool -> Term .bool
  | [],      tail => tail
  | g :: gs, tail => .andT g (conjT gs tail)

/--
  The single VC formula for amount conservation:
      (not (and guards... (not (= (sum createdAmounts) thisAmount))))
  Its validity (eval = true in every environment) is what a cvc5 `unsat`
  verdict on the buildQuery script establishes.
-/
def vcgen (t : Transition) : Term .bool :=
  .notT (conjT t.guards (.notT (.eqR (sumT t.createdAmounts) t.thisAmount)))

end Formal

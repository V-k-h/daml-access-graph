/-
  Formal/Transition.lean

  Guarded transitions and the amount-conservation property.

  CORRESPONDENCE with the JS pipeline: a JS transition is
    { guards, creates: [{fields: {amount, ...}}], consuming, rounding, ... }.
  The Lean structure keeps exactly what the amount-conservation VC consumes
  AFTER the applicability filtering that backend/smt.js#amountConservation
  performs:

    guards         ~ the USABLE guards (usableGuards drops any guard
                     containing an unsupported node; the drop is justified by
                     drop_guard_sound / drop_guards_sound in Soundness.lean).
    createdAmounts ~ one Term .real per create: c.fields.amount, or
                     `var "this.amount" .real` when a `create this with ...`
                     inherits it. amountConservation refuses the property if
                     any create lacks an amount or the amount is unsupported.
    thisAmount     ~ the archived contract's amount. The JS side always uses
                     the variable `this.amount`; the Lean field permits any
                     Term .real, which only generalizes the statement.

  NOT modelled here, because the JS side refuses BEFORE building the VC
  (so no theorem about them is claimed):
    consuming      - nonconsuming choices are `applicable: false`;
    rounding       - transitions whose path rounds are refused (the
                     exact-rational abstraction would be unsound for exact
                     equalities there);
    creates = []   - refused ("pure archive"). The Lean definitions are
                     total anyway: an empty createdAmounts sums to 0.
-/
import Formal.Term
import Formal.Eval

namespace Formal

open Std.Internal (Rat)

/-- A guarded transition, restricted to what the conservation VC consumes. -/
structure Transition where
  guards         : List (Term .bool)
  createdAmounts : List (Term .real)
  thisAmount     : Term .real

/--
  Sum of a list of rationals, with the same shape as the term-level sum the
  JS pipeline builds (see sumT in Formal/VCGen.lean): a singleton list is its
  element, a longer list folds binary +, and the empty list (which the JS
  side refuses) is 0.
-/
def sumR : List Rat -> Rat
  | []        => 0
  | [a]       => a
  | a :: rest => a + sumR rest

/--
  AMOUNT CONSERVATION, the semantic property (backend/smt.js):
  for every environment in which all guards hold, the sum of the created
  amounts equals the archived contract's amount.

  This is the meaning of "the consuming choice preserves the amount field in
  total" ONCE the untrusted translation has produced the transition; it says
  nothing about Daml-LF evaluation itself (future work, see
  formal/Correspondence.md).
-/
def Conserves (t : Transition) : Prop :=
  forall env : Env,
    (forall g, g ∈ t.guards -> eval env g = true) ->
    sumR (t.createdAmounts.map (eval env)) = eval env t.thisAmount

end Formal

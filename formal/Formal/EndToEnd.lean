/-
  Formal/EndToEnd.lean

  THE HEADLINE: composing translation correctness with VC soundness moves
  the machine-checked boundary one arrow left. Before this file, a valid VC
  implied conservation OF THE IR TRANSITION (Formal/Soundness.lean); the
  claim that the IR transition means what the source says was untrusted
  JavaScript. After it, for transitions whose guards and amounts lie in the
  MiniLF fragment, a valid VC implies conservation stated in the SOURCE
  FRAGMENT'S OWN SEMANTICS (evalLF over MiniLF expressions):

      minilf_vcgen_sound :
        (forall env, eval env (vcgen (translateTransition t)) = true) ->
        ConservesLF t

  What remains untrusted is enumerated in formal/Correspondence.md: the JS
  reduction that brings a compiled choice INTO the MiniLF fragment
  (beta-reduction/inlining, record chasing, ensure-conjunct decomposition,
  interface dispatch, protobuf reading), and the solver.

  A MiniLF transition mirrors what backend/smt.js#amountConservation
  consumes, one arrow earlier:

    guardsLF     ~ the usable guards, as source expressions (ensure
                   conjuncts and path conditions that translated cleanly);
    createdLF    ~ per create, the `amount` field's source expression; for
                   `create this with ...` inheriting the amount, that
                   expression is proj this "amount" - which translates to
                   exactly the `var "this.amount"` the JS inserts;
    thisAmountLF ~ the archived contract's amount, proj this "amount" in
                   the JS pipeline; any MiniLF .real only generalizes.

  Top-level expressions are evaluated under the canonical initial
  let-environment (LEnv.ofEnv env): lfir.js starts each choice with ctx.env
  holding only the this/arg record aliases, which MiniLF bakes into proj,
  so no real let-binding is in scope at the top of a guard or amount.
-/
import Formal.Term
import Formal.Eval
import Formal.Transition
import Formal.VCGen
import Formal.Soundness
import Formal.MiniLF
import Formal.MiniLFEval
import Formal.Translate
import Formal.TranslateCorrect

namespace Formal

/-- Evaluation of a TOP-LEVEL MiniLF expression: symbol environment env,
    canonical initial let-environment. -/
def evalLF0 (env : Env) {s : Srt} (e : MiniLF s) : s.denote :=
  evalLF env (LEnv.ofEnv env) e

/-- A guarded transition with guards and amounts as SOURCE-FRAGMENT
    expressions (one arrow left of Formal.Transition). -/
structure TransitionLF where
  guards         : List (MiniLF .bool)
  createdAmounts : List (MiniLF .real)
  thisAmount     : MiniLF .real

/-- Amount conservation, stated entirely in MiniLF semantics: in every
    symbol environment where all source guards hold, the source-level sum
    of created amounts equals the source-level archived amount. -/
def ConservesLF (t : TransitionLF) : Prop :=
  forall env : Env,
    (forall g, g ∈ t.guards -> evalLF0 env g = true) ->
    sumR (t.createdAmounts.map (evalLF0 env)) = evalLF0 env t.thisAmount

/-- Translate a MiniLF transition to an IR transition, expression by
    expression (each against TEnv.init, as lfir.js starts each choice). -/
def translateTransition (t : TransitionLF) : Transition :=
  { guards         := t.guards.map (translate TEnv.init),
    createdAmounts := t.createdAmounts.map (translate TEnv.init),
    thisAmount     := translate TEnv.init t.thisAmount }

/-- Mapping IR evaluation over translated expressions is mapping MiniLF
    evaluation over the sources. -/
theorem map_eval_translate (env : Env) :
    (l : List (MiniLF .real)) ->
    (l.map (translate TEnv.init)).map (eval env) = l.map (evalLF0 env)
  | [] => rfl
  | a :: rest => by
      have ih := map_eval_translate env rest
      simp only [List.map_cons, ih]
      rw [translate_correct_init env a]
      rfl

/--
  END-TO-END SOUNDNESS (the headline): if the VC generated FROM THE
  TRANSLATED IR TRANSITION is valid - which is what a cvc5 `unsat` on the
  emitted script establishes, per the trusted-solver arrow - then the
  MiniLF transition conserves amounts IN THE SOURCE SEMANTICS.

  Proof: vcgen_sound gives conservation of the IR transition; preservation
  (translate_correct_init) transports each guard, each created amount, and
  the archived amount between the two semantics.
-/
theorem minilf_vcgen_sound (t : TransitionLF) :
    (forall env : Env, eval env (vcgen (translateTransition t)) = true) ->
    ConservesLF t := by
  intro hvalid env hguards
  have hcons : Conserves (translateTransition t) := vcgen_sound _ hvalid
  have hg : forall g', g' ∈ (translateTransition t).guards -> eval env g' = true := by
    intro g' hg'
    have ⟨g, hgmem, hgeq⟩ := List.mem_map.mp hg'
    subst hgeq
    rw [translate_correct_init env g]
    exact hguards g hgmem
  have hsum := hcons env hg
  rw [show (translateTransition t).createdAmounts
        = t.createdAmounts.map (translate TEnv.init) from rfl,
      map_eval_translate env t.createdAmounts,
      show (translateTransition t).thisAmount
        = translate TEnv.init t.thisAmount from rfl,
      translate_correct_init env t.thisAmount] at hsum
  exact hsum

/--
  COMPLETENESS of the composition, for parity with vcgen_iff: source-level
  conservation makes the generated VC valid. (About vcgen and the
  translation only - the solver may still time out on a valid VC.)
-/
theorem minilf_vcgen_complete (t : TransitionLF) :
    ConservesLF t ->
    forall env : Env, eval env (vcgen (translateTransition t)) = true := by
  intro hcons
  apply vcgen_complete
  intro env hguards
  have hlf : forall g, g ∈ t.guards -> evalLF0 env g = true := by
    intro g hgmem
    have := hguards (translate TEnv.init g)
      (List.mem_map.mpr ⟨g, hgmem, rfl⟩)
    rw [translate_correct_init env g] at this
    exact this
  have hsum := hcons env hlf
  rw [show (translateTransition t).createdAmounts
        = t.createdAmounts.map (translate TEnv.init) from rfl,
      map_eval_translate env t.createdAmounts,
      show (translateTransition t).thisAmount
        = translate TEnv.init t.thisAmount from rfl,
      translate_correct_init env t.thisAmount]
  exact hsum

/-- The two directions packaged: for MiniLF transitions, validity of the VC
    over the TRANSLATED transition IS source-level conservation. -/
theorem minilf_vcgen_iff (t : TransitionLF) :
    (forall env : Env, eval env (vcgen (translateTransition t)) = true) <->
    ConservesLF t :=
  ⟨minilf_vcgen_sound t, minilf_vcgen_complete t⟩

-- Axiom audit for the new main results. Verified output of the #print
-- axioms commands below (lake build, Lean 4.15.0):
--
--   'Formal.translate_correct' depends on axioms: [propext, Quot.sound]
--   'Formal.translate_correct_init' depends on axioms: [propext, Quot.sound]
--   'Formal.minilf_vcgen_sound' depends on axioms: [propext, Quot.sound]
--   'Formal.minilf_vcgen_iff' depends on axioms: [propext, Quot.sound]
--
-- propext and Quot.sound are Lean kernel axioms (Quot.sound arrives via
-- funext in core simp lemmas, as for vcgen_sound). No sorry, no
-- Classical.choice (the decidability instances used - Rat order/equality,
-- String equality - are all constructive), no user axioms.
#print axioms translate_correct
#print axioms translate_correct_init
#print axioms minilf_vcgen_sound
#print axioms minilf_vcgen_iff

end Formal

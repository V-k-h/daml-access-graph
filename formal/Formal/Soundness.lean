/-
  Formal/Soundness.lean

  THE theorem of this development: validity of the generated VC implies the
  conservation property, and (completeness for this fragment) conversely.
  Plus the guard-dropping monotonicity lemma that backend/smt.js relies on.

  WHAT IS PROVED: properties of the VC layer only - the formula vcgen builds
  means the property Conserves, under the Lean semantics `eval` of the IR.

  WHAT IS NOT PROVED (and not claimed): that the Daml-LF program denotes the
  Transition (untrusted translator, tested in JS), that cvc5's `unsat` is
  correct (trusted solver), or anything about Daml-LF/Numeric-10 semantics
  (stated future work). See formal/Correspondence.md.
-/
import Formal.Term
import Formal.Eval
import Formal.Transition
import Formal.VCGen

namespace Formal

/-- Boolean scaffolding: !(a && !b) is the boolean implication a -> b. -/
theorem not_and_not_eq_true (a b : Bool) :
    ((!(a && !b)) = true) <-> (a = true -> b = true) := by
  cases a <;> cases b <;> simp

/-- Evaluating the term-level sum is summing the evaluations. -/
theorem eval_sumT (env : Env) :
    (l : List (Term .real)) -> eval env (sumT l) = sumR (l.map (eval env))
  | []             => by simp [sumT, sumR]
  | [a]            => by simp [sumT, sumR]
  | a :: b :: rest => by
      have ih := eval_sumT env (b :: rest)
      simp [sumT, sumR, ih]

/-- Evaluating the conjoined guards is the boolean `all` of the guards. -/
theorem eval_conjT (env : Env) :
    (gs : List (Term .bool)) -> (tail : Term .bool) ->
    eval env (conjT gs tail) = (gs.all (fun g => eval env g) && eval env tail)
  | [],      tail => by simp [conjT]
  | g :: gs, tail => by
      have ih := eval_conjT env gs tail
      simp [conjT, ih, Bool.and_assoc]

/--
  Pointwise characterization of the VC: at one environment, the VC evaluates
  to true exactly when "all guards true implies the sums agree" at that
  environment.
-/
theorem eval_vcgen_iff (env : Env) (t : Transition) :
    eval env (vcgen t) = true <->
      (t.guards.all (fun g => eval env g) = true ->
        sumR (t.createdAmounts.map (eval env)) = eval env t.thisAmount) := by
  rw [vcgen, eval_notT, eval_conjT, eval_notT, eval_eqR, eval_sumT,
      not_and_not_eq_true]
  simp

/--
  SOUNDNESS (the direction the pipeline uses): if the VC is valid - true in
  EVERY environment, which is what cvc5's `unsat` on the buildQuery script
  establishes for the SMT-LIB reading of the same formula - then the
  transition conserves amounts.
-/
theorem vcgen_sound (t : Transition) :
    (forall env : Env, eval env (vcgen t) = true) -> Conserves t := by
  intro hvalid env hguards
  exact (eval_vcgen_iff env t).mp (hvalid env)
    (List.all_eq_true.mpr fun g hg => hguards g hg)

/--
  COMPLETENESS for this fragment: the VC is literally the property, so the
  converse holds as well. (This is a statement about vcgen, not about the
  solver: cvc5 may still time out on a valid VC.)
-/
theorem vcgen_complete (t : Transition) :
    Conserves t -> forall env : Env, eval env (vcgen t) = true := by
  intro hcons env
  exact (eval_vcgen_iff env t).mpr fun hall =>
    hcons env fun g hg => List.all_eq_true.mp hall g hg

/-- The two directions packaged as an iff: validity of the VC IS the property. -/
theorem vcgen_iff (t : Transition) :
    (forall env : Env, eval env (vcgen t) = true) <-> Conserves t :=
  ⟨vcgen_sound t, vcgen_complete t⟩

/--
  GUARD DROPPING, general form. If every guard the VC actually used appears
  among the transition's full guards, then conservation proved from the used
  guards implies conservation under the full guards: fewer assumptions make
  the proved statement STRONGER. This is exactly the shape of
  backend/smt.js#usableGuards: `used` is the filtered list (unsupported
  guards dropped), `full` is the transition's real guard list.
-/
theorem drop_guards_sound (used full : List (Term .bool))
    (amounts : List (Term .real)) (thisAmount : Term .real)
    (hsub : forall g, g ∈ used -> g ∈ full) :
    Conserves ⟨used, amounts, thisAmount⟩ ->
    Conserves ⟨full, amounts, thisAmount⟩ := by
  intro h env hfull
  exact h env fun g hg => hfull g (hsub g hg)

/--
  GUARD DROPPING, single-guard form, stated the way the pipeline uses it:
  if the property was proved with guard g DROPPED from the assumptions, it
  holds under the full guard list g :: gs. (Soundness note at the top of
  backend/smt.js: dropping an assumption can only make a universal property
  harder to prove, never easier, so a PROVED verdict survives untranslated
  guards.)
-/
theorem drop_guard_sound (g : Term .bool) (gs : List (Term .bool))
    (amounts : List (Term .real)) (thisAmount : Term .real) :
    Conserves ⟨gs, amounts, thisAmount⟩ ->
    Conserves ⟨g :: gs, amounts, thisAmount⟩ :=
  drop_guards_sound gs (g :: gs) amounts thisAmount
    (fun _ hx => List.mem_cons_of_mem g hx)

/-- The same, in `{t with ...}` form. -/
theorem drop_guard_sound' (t : Transition) (g : Term .bool)
    (gs : List (Term .bool)) :
    Conserves {t with guards := gs} -> Conserves {t with guards := g :: gs} :=
  drop_guard_sound g gs t.createdAmounts t.thisAmount

/--
  END-TO-END shape of a pipeline run with dropped guards: cvc5 proves the VC
  built from the USABLE guards valid; the property then holds for the
  transition with its FULL guard list.
-/
theorem vcgen_dropped_guards_sound (used full : List (Term .bool))
    (amounts : List (Term .real)) (thisAmount : Term .real)
    (hsub : forall g, g ∈ used -> g ∈ full)
    (hvalid : forall env : Env,
      eval env (vcgen ⟨used, amounts, thisAmount⟩) = true) :
    Conserves ⟨full, amounts, thisAmount⟩ :=
  drop_guards_sound used full amounts thisAmount hsub
    (vcgen_sound ⟨used, amounts, thisAmount⟩ hvalid)

-- Axiom audit for the main results. Verified output of the four commands
-- below (lake build, Lean 4.15.0):
--
--   'Formal.vcgen_sound' depends on axioms: [propext, Quot.sound]
--   'Formal.vcgen_iff' depends on axioms: [propext, Quot.sound]
--   'Formal.drop_guard_sound' depends on axioms: [propext]
--   'Formal.vcgen_dropped_guards_sound' depends on axioms: [propext, Quot.sound]
--
-- propext and Quot.sound are Lean kernel axioms (Quot.sound arrives via
-- funext inside core List/Bool simp lemmas). No sorry, no Classical.choice,
-- no user axioms.
#print axioms vcgen_sound
#print axioms vcgen_iff
#print axioms drop_guard_sound
#print axioms vcgen_dropped_guards_sound

end Formal

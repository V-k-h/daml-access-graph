/-
  Formal/Division.lean

  PART B: the OTHER shipped property, DIVISION SAFETY, given the same
  treatment as amount conservation - a semantic statement, a VC generator
  mirroring backend/smt.js, a soundness theorem, and the guard-drop
  monotonicity lemma the pipeline relies on. Both shipped properties now
  rest on a machine-checked theorem rather than one of them.

  CORRESPONDENCE with backend/smt.js#divisionSafety:

    transition.divisions   ~ `denominators`, one Term .real per division
                             recovered on the path (lfir.js pushes
                             {denominator, ...} for every DIV builtin it
                             translates).
    usableGuards(t)        ~ `guards`, the guards that translated cleanly.
    the goal               ~ (and (not (= d1 0)) ... (not (= dn 0))), with
                             the JS special case `goal.args.length === 1 ?
                             goal.args[0] : goal` mirrored by conjAllT's
                             singleton case.
    buildQuery             ~ as for conservation: asserting the guards and
                             the negated goal and getting `unsat` is
                             validity of the single formula vcgenDiv builds.

  PER-DENOMINATOR ADJUDICATION. backend/smt.js splits the denominators into
  `checkable` (inside the translated fragment) and `skipped`, and proves
  only the conjunction over `checkable`, reporting `coverage`. The theorem
  below is stated over whatever denominator list the VC was built from, so
  a valid VC over `checkable` yields exactly `DivisionSafe` for the
  CHECKABLE denominators and says nothing about the skipped ones -
  `divsafe_denominators_mono` records the only direction that holds
  (safety for a superset implies safety for a subset). The report layer's
  refusal to print a bare PROVED when `coverage.skipped` is nonempty is the
  practical reading of that gap.

  NOT MODELLED here, because the JS refuses or qualifies before the VC
  exists: denominators recovered from unrolled fold steps (the verdict is
  `bounded`, not PROVED - nothing is claimed about element indices beyond
  the bound), and transitions all of whose denominators are unsupported
  (`applicable: false`).
-/
import Formal.Term
import Formal.Eval
import Formal.Transition
import Formal.VCGen
import Formal.Soundness

namespace Formal

open Std.Internal (Rat)

/-- A transition, restricted to what the division-safety VC consumes. -/
structure DivTransition where
  guards       : List (Term .bool)
  denominators : List (Term .real)

/--
  DIVISION SAFETY, the semantic property: in every environment where all
  guards hold, no denominator on the transition is zero.
-/
def DivisionSafe (d : DivTransition) : Prop :=
  forall env : Env,
    (forall g, g ∈ d.guards -> eval env g = true) ->
    forall t, t ∈ d.denominators -> eval env t ≠ 0

/-- The per-denominator obligation: (not (= d 0)). -/
def nonzeroT (t : Term .real) : Term .bool :=
  .notT (.eqR t (.num 0))

/--
  Conjunction of the obligations, with the same shape the JS emits: one
  obligation alone is emitted bare, several are conjoined. The empty list
  (which backend/smt.js refuses - `applicable: false` when nothing is
  checkable) is totalized to `true`.
-/
def conjAllT : List (Term .bool) -> Term .bool
  | []        => .boolLit true
  | [a]       => a
  | a :: rest => .andT a (conjAllT rest)

/--
  The single VC formula for division safety:
      (not (and guards... (not (and (not (= d1 0)) ... (not (= dn 0))))))
  Its validity is what a cvc5 `unsat` on the buildQuery script establishes.
-/
def vcgenDiv (d : DivTransition) : Term .bool :=
  .notT (conjT d.guards (.notT (conjAllT (d.denominators.map nonzeroT))))

theorem eval_nonzeroT (env : Env) (t : Term .real) :
    eval env (nonzeroT t) = true <-> eval env t ≠ 0 := by
  simp [nonzeroT]

theorem eval_conjAllT (env : Env) :
    (l : List (Term .bool)) ->
    eval env (conjAllT l) = l.all (fun t => eval env t)
  | []             => rfl
  | [a]            => by simp [conjAllT]
  | a :: b :: rest => by
      have ih := eval_conjAllT env (b :: rest)
      simp [conjAllT, ih]

/-- The conjunction of obligations is true exactly when no denominator is
    zero. -/
theorem eval_obligations (env : Env) (dens : List (Term .real)) :
    eval env (conjAllT (dens.map nonzeroT)) = true <->
      (forall t, t ∈ dens -> eval env t ≠ 0) := by
  rw [eval_conjAllT]
  constructor
  · intro h t ht
    have := List.all_eq_true.mp h (nonzeroT t) (List.mem_map.mpr ⟨t, ht, rfl⟩)
    exact (eval_nonzeroT env t).mp this
  · intro h
    refine List.all_eq_true.mpr ?_
    intro x hx
    have ⟨t, ht, hxt⟩ := List.mem_map.mp hx
    subst hxt
    exact (eval_nonzeroT env t).mpr (h t ht)

/-- Pointwise characterization: at one environment, the VC is true exactly
    when "all guards true implies every denominator nonzero" there. -/
theorem eval_vcgenDiv_iff (env : Env) (d : DivTransition) :
    eval env (vcgenDiv d) = true <->
      (d.guards.all (fun g => eval env g) = true ->
        forall t, t ∈ d.denominators -> eval env t ≠ 0) := by
  rw [vcgenDiv, eval_notT, eval_conjT, eval_notT, not_and_not_eq_true]
  constructor
  · intro h hall
    exact (eval_obligations env d.denominators).mp (h hall)
  · intro h hall
    exact (eval_obligations env d.denominators).mpr (h hall)

/--
  SOUNDNESS, the same shape as `Formal.vcgen_sound`: if the VC is valid -
  true in EVERY environment, which is what cvc5's `unsat` on the
  buildQuery script establishes for the SMT-LIB reading of the same
  formula - then no division on the transition can divide by zero under
  its guards.
-/
theorem vcgenDiv_sound (d : DivTransition) :
    (forall env : Env, eval env (vcgenDiv d) = true) -> DivisionSafe d := by
  intro hvalid env hguards
  exact (eval_vcgenDiv_iff env d).mp (hvalid env)
    (List.all_eq_true.mpr fun g hg => hguards g hg)

/-- COMPLETENESS for this fragment: the VC is literally the property. (A
    statement about vcgenDiv, not about the solver, which may time out.) -/
theorem vcgenDiv_complete (d : DivTransition) :
    DivisionSafe d -> forall env : Env, eval env (vcgenDiv d) = true := by
  intro hsafe env
  exact (eval_vcgenDiv_iff env d).mpr fun hall =>
    hsafe env fun g hg => List.all_eq_true.mp hall g hg

/-- The two directions packaged: validity of the VC IS the property. -/
theorem vcgenDiv_iff (d : DivTransition) :
    (forall env : Env, eval env (vcgenDiv d) = true) <-> DivisionSafe d :=
  ⟨vcgenDiv_sound d, vcgenDiv_complete d⟩

/--
  GUARD DROPPING, general form, exactly as for conservation
  (`drop_guards_sound`): safety proved from the USABLE guards holds under
  the transition's full guard list, because dropping an assumption only
  strengthens a universally quantified statement. This is the soundness
  note at the top of backend/smt.js, now covering the second property too.
-/
theorem divsafe_drop_guards_sound (used full : List (Term .bool))
    (dens : List (Term .real))
    (hsub : forall g, g ∈ used -> g ∈ full) :
    DivisionSafe ⟨used, dens⟩ -> DivisionSafe ⟨full, dens⟩ := by
  intro h env hfull
  exact h env fun g hg => hfull g (hsub g hg)

/-- Single-guard form, the way the pipeline uses it. -/
theorem divsafe_drop_guard_sound (g : Term .bool) (gs : List (Term .bool))
    (dens : List (Term .real)) :
    DivisionSafe ⟨gs, dens⟩ -> DivisionSafe ⟨g :: gs, dens⟩ :=
  divsafe_drop_guards_sound gs (g :: gs) dens
    (fun _ hx => List.mem_cons_of_mem g hx)

/--
  DENOMINATOR COVERAGE, the honest direction: safety for a set of
  denominators gives safety for any SUBSET of them. It does not give
  safety for denominators the VC never mentioned - which is exactly why
  backend/smt.js carries `coverage.skipped` to the report instead of
  printing a bare PROVED.
-/
theorem divsafe_denominators_mono (guards : List (Term .bool))
    (sub full : List (Term .real))
    (hsub : forall t, t ∈ sub -> t ∈ full) :
    DivisionSafe ⟨guards, full⟩ -> DivisionSafe ⟨guards, sub⟩ := by
  intro h env hg t ht
  exact h env hg t (hsub t ht)

/--
  END-TO-END shape of a division-safety run with dropped guards: cvc5
  proves the VC built from the USABLE guards valid; the property then holds
  for the transition with its FULL guard list.
-/
theorem vcgenDiv_dropped_guards_sound (used full : List (Term .bool))
    (dens : List (Term .real))
    (hsub : forall g, g ∈ used -> g ∈ full)
    (hvalid : forall env : Env, eval env (vcgenDiv ⟨used, dens⟩) = true) :
    DivisionSafe ⟨full, dens⟩ :=
  divsafe_drop_guards_sound used full dens hsub
    (vcgenDiv_sound ⟨used, dens⟩ hvalid)

-- Axiom audit for the main results of this file. Verified output of the
-- #print axioms commands below (lake build, Lean 4.15.0):
--
--   'Formal.vcgenDiv_sound' depends on axioms: [propext, Quot.sound]
--   'Formal.vcgenDiv_iff' depends on axioms: [propext, Quot.sound]
--   'Formal.divsafe_drop_guard_sound' depends on axioms: [propext]
--   'Formal.vcgenDiv_dropped_guards_sound' depends on axioms: [propext, Quot.sound]
--
-- propext and Quot.sound are Lean kernel axioms. No sorry, no
-- Classical.choice, no user axioms - the same audit the conservation
-- development records in Formal/Soundness.lean.
#print axioms vcgenDiv_sound
#print axioms vcgenDiv_iff
#print axioms divsafe_drop_guard_sound
#print axioms vcgenDiv_dropped_guards_sound

end Formal

/-
  Formal/Model.lean

  CARRIER-GENERIC SEMANTICS of the IR, and the algebraic laws the ledger
  layer (Formal/Ledger.lean) needs from the numeric carrier.

  WHY THIS FILE EXISTS. Formal/Eval.lean interprets the IR sort 'Real' as
  core `Std.Internal.Rat`, and already notes (see its header) that no proof
  in this development unfolds a single Rat operation, so every theorem holds
  for any carrier with the same operations. Per-transition soundness needs
  nothing more. The LEDGER induction does: to say "the total of a numeric
  field over the active contracts is unchanged" one has to re-associate a
  sum, because a step replaces ONE contract by a LIST of created ones, and
  the state's total is a sum over a list.

  That re-association is NOT available for `Std.Internal.Rat`, and the
  reason is worth stating precisely, because it is a property of the
  REPRESENTATION and not of the rationals:

    * `Std.Internal.Rat` is a bare structure `(num : Int, den : Nat)` with
      no reducedness invariant, and a PRIVATE constructor. `Rat.add` (core)
      computes with gcds in a way that is correct only when its arguments
      are already reduced.
    * Addition is therefore NOT associative on the type: with the
      representations a = (-4)/2, b = (-4)/2, c = (-4)/4 one gets
      (a + b) + c = (-20)/4 and a + (b + c) = (-5)/1. Both DENOTE -5, but
      they are different elements of the structure, and Lean's `=` on Rat
      is equality of the representation. (Verified by mirroring core's
      `Rat.add` outside Lean and searching small representations:
      associativity fails on unreduced inputs, commutativity and the unit
      laws hold on all inputs.)
    * On reduced representations associativity does hold - `Rat.add`
      returns reduced results there and the reduced form is unique - but
      proving that is a correctness theory for `Std.Internal.Rat` which
      core does not provide (the module exports no algebraic lemma at all,
      only definitions) and which this development does not attempt. Nor
      can the values be assumed reduced: an environment is an arbitrary
      total map `String -> Rat`.

  So `forall a b c : Rat, a + b + c = a + (b + c)` is not a theorem we can
  have, and ASSUMING it would be assuming something FALSE - every theorem
  taking it as a hypothesis would be vacuous. That is the trap this file
  exists to avoid.

  WHAT IS DONE INSTEAD. The IR semantics is re-given over an arbitrary
  model of the sort 'Real' (`RealModel`: a carrier plus the operations the
  IR uses), and:

    1. `evalM_rat` proves the generic semantics INSTANTIATED AT Rat is
       literally the shipped `Formal.eval` - the generic layer is a
       strict generalization of Eval.lean, not a different semantics;
    2. `vcgenM_sound` re-proves VC soundness for every model, and
       `vcgen_sound_via_model` derives the shipped `vcgen_sound` from it,
       so nothing is lost by working generically;
    3. `AddLaws M` states the three facts about the carrier's addition that
       the ledger induction consumes (associativity, commutativity, unit).
       SMT-LIB Real satisfies them - they are theorems about the rationals,
       which is what cvc5 reasons over - so requiring them adds NO
       assumption about the pipeline; they fail only for the Lean-side
       REPRESENTATION `Std.Internal.Rat`, and only because equality there
       is representational.
    4. `intLaws` exhibits a model satisfying `AddLaws`, so no theorem with
       an `AddLaws` hypothesis is vacuous. (`intModel` is a witness of
       satisfiability only: Int is not a faithful model of SMT-LIB Real,
       since its division is not the Real one. It is used for nothing
       else.)

  HONEST SUMMARY of the resulting claim shape. A cvc5 `unsat` verdict says
  the VC is valid under EVERY interpretation of the SMT-LIB script - in
  particular under any `RealModel` faithful to SMT-LIB Real, all of which
  satisfy `AddLaws`. The ledger theorems consume validity in exactly that
  form. Reading a cvc5 verdict as validity in a given model is the same
  trusted-solver arrow the per-transition theorems already rely on (see
  formal/Correspondence.md); this file does not widen it, it only makes
  explicit which properties of the carrier the induction uses.
-/
import Formal.Term
import Formal.Eval
import Formal.Transition
import Formal.VCGen
import Formal.Soundness

namespace Formal

open Std.Internal (Rat)

/--
  A model of the IR sort 'Real': a carrier, a reading of the numeric
  literals the IR carries, and one operation per IR operator. The Bool sort
  is always Lean `Bool` (the IR's boolean connectives are the standard ones
  and nothing in the development varies them), so comparisons return `Bool`
  directly and no decidability instance is needed anywhere - which also
  keeps `Classical.choice` out of the axiom audit.
-/
structure RealModel where
  R     : Type
  ofRat : Rat -> R
  add   : R -> R -> R
  sub   : R -> R -> R
  mul   : R -> R -> R
  divR  : R -> R -> R
  divE  : R -> R -> R
  modE  : R -> R -> R
  ltb   : R -> R -> Bool
  leb   : R -> R -> Bool
  eqb   : R -> R -> Bool

/-- An environment for a model: as `Formal.Env`, one total map per sort. -/
structure ModelEnv (M : RealModel) where
  realVar : String -> M.R
  boolVar : String -> Bool

/-- Denotation of a sort in a model. -/
@[reducible] def Srt.denoteM (M : RealModel) : Srt -> Type
  | .real => M.R
  | .bool => Bool

/-- Look a name up at a sort. -/
def ModelEnv.get {M : RealModel} (env : ModelEnv M) :
    (s : Srt) -> String -> Srt.denoteM M s
  | .real => env.realVar
  | .bool => env.boolVar

/-- Total evaluation in a model; case for case, `Formal.eval` with the
    operations taken from `M`. -/
def evalM (M : RealModel) (env : ModelEnv M) :
    {s : Srt} -> Term s -> Srt.denoteM M s
  | _, .num v      => M.ofRat v
  | _, .boolLit v  => v
  | _, .var n s    => env.get s n
  | _, .add a b    => M.add (evalM M env a) (evalM M env b)
  | _, .sub a b    => M.sub (evalM M env a) (evalM M env b)
  | _, .mul a b    => M.mul (evalM M env a) (evalM M env b)
  | _, .divR a b   => M.divR (evalM M env a) (evalM M env b)
  | _, .divE a b   => M.divE (evalM M env a) (evalM M env b)
  | _, .modE a b   => M.modE (evalM M env a) (evalM M env b)
  | _, .lt a b     => M.ltb (evalM M env a) (evalM M env b)
  | _, .le a b     => M.leb (evalM M env a) (evalM M env b)
  | _, .gt a b     => M.ltb (evalM M env b) (evalM M env a)
  | _, .ge a b     => M.leb (evalM M env b) (evalM M env a)
  | _, .eqR a b    => M.eqb (evalM M env a) (evalM M env b)
  | _, .eqB a b    => evalM M env a == evalM M env b
  | _, .notT a     => !(evalM M env a)
  | _, .andT a b   => evalM M env a && evalM M env b
  | _, .orT a b    => evalM M env a || evalM M env b
  | _, .ite c a b  => cond (evalM M env c) (evalM M env a) (evalM M env b)

@[simp] theorem evalM_num (M : RealModel) (env : ModelEnv M) (v : Rat) :
    evalM M env (.num v) = M.ofRat v := rfl
@[simp] theorem evalM_add (M : RealModel) (env : ModelEnv M) (a b : Term .real) :
    evalM M env (.add a b) = M.add (evalM M env a) (evalM M env b) := rfl
@[simp] theorem evalM_eqR (M : RealModel) (env : ModelEnv M) (a b : Term .real) :
    evalM M env (.eqR a b) = M.eqb (evalM M env a) (evalM M env b) := rfl
@[simp] theorem evalM_notT (M : RealModel) (env : ModelEnv M) (a : Term .bool) :
    evalM M env (.notT a) = !(evalM M env a) := rfl
@[simp] theorem evalM_andT (M : RealModel) (env : ModelEnv M) (a b : Term .bool) :
    evalM M env (.andT a b) = (evalM M env a && evalM M env b) := rfl

-- ---------------------------------------------------------------------------
-- The shipped semantics is one instance
-- ---------------------------------------------------------------------------

/-- The model Formal/Eval.lean fixes: core `Rat` with its total division. -/
@[reducible] def ratModel : RealModel where
  R     := Rat
  ofRat := id
  add   := (· + ·)
  sub   := (· - ·)
  mul   := (· * ·)
  divR  := (· / ·)
  divE  := smtDiv
  modE  := smtMod
  ltb   := fun a b => decide (a < b)
  leb   := fun a b => decide (a <= b)
  eqb   := fun a b => decide (a = b)

/-- An `Env` read as a `ratModel` environment. -/
def Env.toModel (env : Env) : ModelEnv ratModel :=
  ⟨env.realVar, env.boolVar⟩

/-- A `ratModel` environment read as an `Env`. The two structures have the
    same fields, so both round trips are definitional. -/
def ModelEnv.toEnv (env : ModelEnv ratModel) : Env :=
  ⟨env.realVar, env.boolVar⟩

/--
  THE BRIDGE: the generic semantics at `ratModel` IS `Formal.eval`. So
  Formal/Model.lean generalizes Formal/Eval.lean rather than replacing it,
  and every generic theorem below specializes to a statement about the
  shipped semantics.
-/
theorem evalM_rat (env : Env) :
    {s : Srt} -> (t : Term s) -> evalM ratModel env.toModel t = eval env t
  | _, .num _     => rfl
  | _, .boolLit _ => rfl
  | _, .var _ s   => by cases s <;> rfl
  | _, .add a b   => by
      show evalM ratModel env.toModel a + evalM ratModel env.toModel b
         = eval env a + eval env b
      rw [evalM_rat env a, evalM_rat env b]
  | _, .sub a b   => by
      show evalM ratModel env.toModel a - evalM ratModel env.toModel b
         = eval env a - eval env b
      rw [evalM_rat env a, evalM_rat env b]
  | _, .mul a b   => by
      show evalM ratModel env.toModel a * evalM ratModel env.toModel b
         = eval env a * eval env b
      rw [evalM_rat env a, evalM_rat env b]
  | _, .divR a b  => by
      show evalM ratModel env.toModel a / evalM ratModel env.toModel b
         = eval env a / eval env b
      rw [evalM_rat env a, evalM_rat env b]
  | _, .divE a b  => by
      show smtDiv (evalM ratModel env.toModel a) (evalM ratModel env.toModel b)
         = smtDiv (eval env a) (eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .modE a b  => by
      show smtMod (evalM ratModel env.toModel a) (evalM ratModel env.toModel b)
         = smtMod (eval env a) (eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .lt a b    => by
      show decide (evalM ratModel env.toModel a < evalM ratModel env.toModel b)
         = decide (eval env a < eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .le a b    => by
      show decide (evalM ratModel env.toModel a <= evalM ratModel env.toModel b)
         = decide (eval env a <= eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .gt a b    => by
      show decide (evalM ratModel env.toModel b < evalM ratModel env.toModel a)
         = decide (eval env b < eval env a)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .ge a b    => by
      show decide (evalM ratModel env.toModel b <= evalM ratModel env.toModel a)
         = decide (eval env b <= eval env a)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .eqR a b   => by
      show decide (evalM ratModel env.toModel a = evalM ratModel env.toModel b)
         = decide (eval env a = eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .eqB a b   => by
      show (evalM ratModel env.toModel a == evalM ratModel env.toModel b)
         = (eval env a == eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .notT a    => congrArg (fun b => !b) (evalM_rat env a)
  | _, .andT a b  => by
      show (evalM ratModel env.toModel a && evalM ratModel env.toModel b)
         = (eval env a && eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .orT a b   => by
      show (evalM ratModel env.toModel a || evalM ratModel env.toModel b)
         = (eval env a || eval env b)
      rw [evalM_rat env a, evalM_rat env b]
  | _, .ite c a b => by
      show cond (evalM ratModel env.toModel c)
             (evalM ratModel env.toModel a) (evalM ratModel env.toModel b)
         = cond (eval env c) (eval env a) (eval env b)
      rw [evalM_rat env c, evalM_rat env a, evalM_rat env b]

/-- The same bridge, stated from the model side. `env.toEnv.toModel` is
    `env` definitionally (both structures have the same two fields), so
    this is `evalM_rat` with no work. -/
theorem evalM_rat' {s : Srt} (env : ModelEnv ratModel) (t : Term s) :
    evalM ratModel env t = eval env.toEnv t :=
  evalM_rat env.toEnv t

-- ---------------------------------------------------------------------------
-- Conservation and VC soundness, in an arbitrary model
-- ---------------------------------------------------------------------------

/-- `Formal.sumR`, in a model: same shape, same n = 1 special case. -/
def sumM (M : RealModel) : List M.R -> M.R
  | []        => M.ofRat 0
  | [a]       => a
  | a :: rest => M.add a (sumM M rest)

/-- `Formal.Conserves`, in a model. -/
def ConservesM (M : RealModel) (t : Transition) : Prop :=
  forall env : ModelEnv M,
    (forall g, g ∈ t.guards -> evalM M env g = true) ->
    sumM M (t.createdAmounts.map (evalM M env)) = evalM M env t.thisAmount

theorem evalM_sumT (M : RealModel) (env : ModelEnv M) :
    (l : List (Term .real)) ->
    evalM M env (sumT l) = sumM M (l.map (evalM M env))
  | []             => by simp [sumT, sumM]
  | [a]            => by simp [sumT, sumM]
  | a :: b :: rest => by
      have ih := evalM_sumT M env (b :: rest)
      simp [sumT, sumM, ih]

theorem evalM_conjT (M : RealModel) (env : ModelEnv M) :
    (gs : List (Term .bool)) -> (tail : Term .bool) ->
    evalM M env (conjT gs tail)
      = (gs.all (fun g => evalM M env g) && evalM M env tail)
  | [],      tail => by simp [conjT]
  | g :: gs, tail => by
      have ih := evalM_conjT M env gs tail
      simp [conjT, ih, Bool.and_assoc]

/-- Pointwise characterization of the VC in a model. Note the one place the
    model's `eqb` matters: the goal is an equality TEST, so the model must
    decide equality of its carrier the way the solver does. Any faithful
    model of SMT-LIB Real does (`=` is interpreted equality there). -/
theorem evalM_vcgen_iff (M : RealModel) (env : ModelEnv M) (t : Transition)
    (heq : forall a b : M.R, M.eqb a b = true <-> a = b) :
    evalM M env (vcgen t) = true <->
      (t.guards.all (fun g => evalM M env g) = true ->
        sumM M (t.createdAmounts.map (evalM M env)) = evalM M env t.thisAmount) := by
  rw [vcgen, evalM_notT, evalM_conjT, evalM_notT, evalM_eqR, evalM_sumT]
  rw [not_and_not_eq_true]
  constructor
  · intro h hall
    exact (heq _ _).mp (h hall)
  · intro h hall
    exact (heq _ _).mpr (h hall)

/--
  SOUNDNESS in an arbitrary model: the same theorem as
  `Formal.vcgen_sound`, with the carrier abstracted. The proof is the same
  proof; nothing about Rat was ever used.
-/
theorem vcgenM_sound (M : RealModel) (t : Transition)
    (heq : forall a b : M.R, M.eqb a b = true <-> a = b) :
    (forall env : ModelEnv M, evalM M env (vcgen t) = true) -> ConservesM M t := by
  intro hvalid env hguards
  exact (evalM_vcgen_iff M env t heq).mp (hvalid env)
    (List.all_eq_true.mpr fun g hg => hguards g hg)

/-- Completeness in an arbitrary model, for parity with `vcgen_iff`. -/
theorem vcgenM_complete (M : RealModel) (t : Transition)
    (heq : forall a b : M.R, M.eqb a b = true <-> a = b) :
    ConservesM M t -> forall env : ModelEnv M, evalM M env (vcgen t) = true := by
  intro hcons env
  exact (evalM_vcgen_iff M env t heq).mpr fun hall =>
    hcons env fun g hg => List.all_eq_true.mp hall g hg

/-- `ratModel` decides equality by `decide`, so it satisfies the side
    condition of the two theorems above. -/
theorem ratModel_eqb (a b : Rat) : ratModel.eqb a b = true <-> a = b := by
  constructor
  · intro h; exact of_decide_eq_true h
  · intro h; exact decide_eq_true h

theorem sumM_rat : (l : List Rat) -> sumM ratModel l = sumR l
  | []             => rfl
  | [_]            => rfl
  | a :: b :: rest => by
      have ih := sumM_rat (b :: rest)
      show ratModel.add a (sumM ratModel (b :: rest)) = a + sumR (b :: rest)
      rw [ih]

/-- Conservation in `ratModel` IS conservation as Formal/Transition.lean
    states it. -/
theorem conservesM_rat (t : Transition) : ConservesM ratModel t <-> Conserves t := by
  constructor
  · intro h env hg
    have := h env.toModel (by
      intro g hgm
      rw [evalM_rat env g]
      exact hg g hgm)
    rw [sumM_rat, evalM_rat env t.thisAmount] at this
    rw [show t.createdAmounts.map (evalM ratModel env.toModel)
          = t.createdAmounts.map (eval env) from
        List.map_congr_left (fun a _ => evalM_rat env a)] at this
    exact this
  · intro h env hg
    have := h env.toEnv (by
      intro g hgm
      rw [← evalM_rat' env g]
      exact hg g hgm)
    rw [show t.createdAmounts.map (evalM ratModel env)
          = t.createdAmounts.map (eval env.toEnv) from
        List.map_congr_left (fun a _ => evalM_rat' env a),
        sumM_rat, evalM_rat' env t.thisAmount]
    exact this

/--
  The shipped `Formal.vcgen_sound`, re-derived through the generic layer.
  This is the check that nothing was smuggled in by going generic: the
  model machinery proves exactly the theorem Formal/Soundness.lean proves
  directly.
-/
theorem vcgen_sound_via_model (t : Transition) :
    (forall env : Env, eval env (vcgen t) = true) -> Conserves t := by
  intro hvalid
  refine (conservesM_rat t).mp (vcgenM_sound ratModel t ratModel_eqb ?_)
  intro env
  rw [evalM_rat' env (vcgen t)]
  exact hvalid env.toEnv

-- ---------------------------------------------------------------------------
-- The algebraic laws the ledger induction needs
-- ---------------------------------------------------------------------------

/--
  The carrier's addition is a commutative monoid with `ofRat 0` as unit.

  These are theorems about the rationals (hence about SMT-LIB Real, hence
  about anything cvc5 proves), and they are NOT provable for `ratModel`:
  see the header of this file for the counterexample and the reason
  (representational equality on an unreduced-tolerant structure). They are
  satisfiable - `intLaws` below exhibits a model - so no theorem carrying
  this hypothesis is vacuous.
-/
structure AddLaws (M : RealModel) : Prop where
  add_assoc : forall a b c : M.R, M.add (M.add a b) c = M.add a (M.add b c)
  add_comm  : forall a b : M.R, M.add a b = M.add b a
  zero_add  : forall a : M.R, M.add (M.ofRat 0) a = a

theorem AddLaws.add_zero {M : RealModel} (L : AddLaws M) (a : M.R) :
    M.add a (M.ofRat 0) = a := by
  rw [L.add_comm]; exact L.zero_add a

/-- With the unit law, the n = 1 special case of `sumM` disappears: a cons
    is always an addition. -/
theorem sumM_cons {M : RealModel} (L : AddLaws M) (a : M.R) :
    (l : List M.R) -> sumM M (a :: l) = M.add a (sumM M l)
  | []     => (L.add_zero a).symm
  | _ :: _ => rfl

/-- Sums split along concatenation. This is the ONLY place associativity is
    used, and the whole reason `AddLaws` exists. -/
theorem sumM_append {M : RealModel} (L : AddLaws M) :
    (l1 l2 : List M.R) -> sumM M (l1 ++ l2) = M.add (sumM M l1) (sumM M l2)
  | [],      l2 => by
      show sumM M l2 = M.add (M.ofRat 0) (sumM M l2)
      rw [L.zero_add]
  | a :: l1, l2 => by
      have ih := sumM_append L l1 l2
      rw [List.cons_append, sumM_cons L, ih, sumM_cons L a l1, L.add_assoc]

-- ---------------------------------------------------------------------------
-- A witness that `AddLaws` is satisfiable
-- ---------------------------------------------------------------------------

/--
  Integers with their arithmetic. This is NOT proposed as a model of
  SMT-LIB Real (its division is integer division, and `ofRat` throws away
  the denominator); it exists only to exhibit an `AddLaws` model, which is
  what rules out a vacuous reading of every theorem below that takes
  `AddLaws` as a hypothesis.
-/
@[reducible] def intModel : RealModel where
  R     := Int
  ofRat := fun q => q.num
  add   := (· + ·)
  sub   := (· - ·)
  mul   := (· * ·)
  divR  := (· / ·)
  divE  := (· / ·)
  modE  := (· % ·)
  ltb   := fun a b => decide (a < b)
  leb   := fun a b => decide (a <= b)
  eqb   := fun a b => decide (a = b)

theorem intLaws : AddLaws intModel where
  add_assoc a b c := Int.add_assoc a b c
  add_comm  a b   := Int.add_comm a b
  zero_add  a     := Int.zero_add a

-- Axiom audit for the results this file adds. Verified output of the
-- #print axioms commands below (lake build, Lean 4.15.0):
--
--   'Formal.evalM_rat' depends on axioms: [propext]
--   'Formal.vcgenM_sound' depends on axioms: [propext, Quot.sound]
--   'Formal.vcgen_sound_via_model' depends on axioms: [propext, Quot.sound]
--   'Formal.sumM_append' does not depend on any axioms
--   'Formal.intLaws' depends on axioms: [propext]
--
-- propext and Quot.sound are Lean kernel axioms (Quot.sound arrives via
-- funext inside core List/Bool simp lemmas). No sorry, no
-- Classical.choice, no user axioms. In particular `AddLaws` is a
-- STRUCTURE used as a hypothesis, not an axiom: nothing in this
-- development asserts it, and `intLaws` proves it is inhabited.
#print axioms evalM_rat
#print axioms vcgenM_sound
#print axioms vcgen_sound_via_model
#print axioms sumM_append
#print axioms intLaws

end Formal

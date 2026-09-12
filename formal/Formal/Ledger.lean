/-
  Formal/Ledger.lean

  PART A: a ledger-state abstraction, a step relation, reachability, the
  induction principle that lifts a per-transition property to every
  reachable state, and the worked instantiation that composes it with VC
  soundness so that "the VC of every transition is valid" implies a GLOBAL
  invariant.

  ---------------------------------------------------------------------------
  THE STATE ABSTRACTION, AND WHY IT HAS EXACTLY THESE PARTS
  ---------------------------------------------------------------------------

  A state is a LIST OF ACTIVE CONTRACTS, each carrying a template name and a
  valuation of its numeric fields:

      Contract M := { template : String, fields : String -> M.R }
      LedgerState M := List (Contract M)

  Justified field by field against what backend/lfir.js actually extracts
  (see the `Transition` typedef there: creates with per-field terms,
  archivedInputs, consuming flags):

    * ACTIVITY = membership in the list. `lfir.js` sees creates and
      archivals and nothing else about contract lifetime; a contract is
      either currently active or not. No contract ids, no parties, no
      observers, no keys, no time: the extractor records none of them in
      the positions any property reads, so modelling them would be
      modelling what the pipeline cannot observe.
    * TEMPLATE NAME: `creates` carries `template`, and choices are
      extracted per template, so "which template" is observable. It earns
      its place in the model: `no_template_reachable` below is an invariant
      that could not even be stated without it.
    * NUMERIC FIELD VALUATION `String -> M.R`: `creates[i].fields` is a map
      from field name to an IR term, so the pipeline observes a whole
      record of numeric fields, not just `amount`. A total map is the same
      design Env uses; fields the create did not mention read `ofRat 0`,
      which is a MODELLING CHOICE, not an observation (see
      `CreateSpec.instantiate`). It is consistent with the term side -
      `CreateSpec.fieldTerm` defaults to the literal 0 in the same case -
      so the two never disagree; and the pipeline refuses conservation for
      a create with no `amount` field anyway
      (backend/smt.js: "create of X has no amount field"), so no verdict is
      ever transported through that case.
    * ORDER is not observable. A list, not a multiset, because core Lean
      has no multiset and pulling one in would cost more than it buys; the
      step relation consumes a contract at an ARBITRARY position
      (`pre ++ c :: post`), so position carries no meaning, and
      `totalAmount_swap` shows the invariant we instantiate is insensitive
      to it.

  WHAT IS DELIBERATELY NOT MODELLED (and so: what the theorems say nothing
  about):

    * NONCONSUMING choices. Every `LedgerTransition` archives its `this`
      contract. A nonconsuming choice that creates contracts adds supply
      and does not conserve; backend/smt.js reports such choices as
      `applicable: false` for amount-conservation, so there is no verdict
      to lift. The consequence for reading the global theorem is stated in
      the side conditions below: a ledger whose choices include a
      nonconsuming create simply has steps this relation does not contain.
    * MULTI-ARCHIVE transitions (`archivedInputs` in lfir.js: "the choice
      archives every element of arg.holdings"). The pipeline models those
      with a bounded unrolling and the symbols `L$i.amount`; the ledger
      model cannot say WHICH active contracts those symbols denote, so
      relating them would be invention. Transitions with archivedInputs are
      out of the modelled set.
    * Transaction structure (exercise trees, sub-transactions, rollbacks),
      contract keys, authorization, and time. None is observable in the IR.

  ---------------------------------------------------------------------------
  WHAT THE INDUCTION PRINCIPLE IS AND IS NOT
  ---------------------------------------------------------------------------

  `invariant_reachable` is the ordinary induction on a reflexive-transitive
  closure. It is stated once, generically, so any per-step lemma lifts to
  every reachable state. It is a theorem ABOUT THE MODEL IN THIS FILE. That
  the transitions backend/lfir.js extracts are in correspondence with the
  steps a real Daml ledger (Canton) can take is NOT proved anywhere and is
  not claimed: it is the untrusted residue enumerated in
  formal/Correspondence.md, plus the abstraction chosen here.

  The arithmetic carrier is abstract (Formal/Model.lean) because the
  conservation invariant re-associates sums, which core's representational
  `Std.Internal.Rat` does not support; see that file's header for the
  counterexample and why assuming it would be assuming a falsehood.
-/
import Formal.Term
import Formal.Eval
import Formal.Transition
import Formal.VCGen
import Formal.Soundness
import Formal.Model

namespace Formal

-- ---------------------------------------------------------------------------
-- States
-- ---------------------------------------------------------------------------

/-- One active contract: its template, and a valuation of its numeric
    fields. See the header for why these two components and no others. -/
structure Contract (M : RealModel) where
  template : String
  fields   : String -> M.R

/-- A ledger state: the active contract set, as a list (order carries no
    meaning; see `totalAmount_swap`). -/
abbrev LedgerState (M : RealModel) := List (Contract M)

-- ---------------------------------------------------------------------------
-- Transitions at the ledger level
-- ---------------------------------------------------------------------------

/--
  One `create` as backend/lfir.js records it: a template name and the
  numeric field expressions (`creates[i].fields`, a map from field name to
  IR term).
-/
structure CreateSpec where
  template : String
  fields   : List (String × Term .real)

/--
  A guarded transition at the ledger level: the IR transition of
  Formal/Transition.lean, plus the two things the ledger needs and the VC
  does not - which template the archived contract has, and the whole field
  record of each create rather than only its `amount` term.

  `thisAmount` is the term denoting the archived contract's tracked field;
  backend/smt.js always uses the symbol `this.amount`, and the Lean field
  permits any term, which only generalizes.
-/
structure LedgerTransition where
  template   : String
  guards     : List (Term .bool)
  creates    : List CreateSpec
  thisAmount : Term .real

/-- The term for one created contract's field `f`: the create's own
    expression for it, or the literal 0 if the create does not mention the
    field (a modelling choice, matched exactly by `instantiate` below). -/
def CreateSpec.fieldTerm (c : CreateSpec) (f : String) : Term .real :=
  (c.fields.lookup f).getD (.num 0)

/-- The contract a create produces in environment `env`. -/
def CreateSpec.instantiate (M : RealModel) (env : ModelEnv M) (c : CreateSpec) :
    Contract M :=
  { template := c.template,
    fields   := fun n =>
      match c.fields.lookup n with
      | some t => evalM M env t
      | none   => M.ofRat 0 }

/-- Term side and contract side agree on every field, including the
    defaulted one. -/
theorem CreateSpec.eval_fieldTerm (M : RealModel) (env : ModelEnv M)
    (c : CreateSpec) (f : String) :
    evalM M env (c.fieldTerm f) = (c.instantiate M env).fields f := by
  show evalM M env ((c.fields.lookup f).getD (.num 0))
     = (match c.fields.lookup f with
        | some t => evalM M env t
        | none   => M.ofRat 0)
  cases h : c.fields.lookup f <;> simp [h]

/--
  The IR transition a ledger transition generates a VC for, tracking field
  `f`: exactly what backend/smt.js#amountConservation builds (the guards,
  one amount term per create, and `this`'s amount as the goal's right-hand
  side).
-/
def LedgerTransition.toTransition (lt : LedgerTransition) (f : String) : Transition :=
  { guards         := lt.guards,
    createdAmounts := lt.creates.map (fun c => c.fieldTerm f),
    thisAmount     := lt.thisAmount }

-- ---------------------------------------------------------------------------
-- Steps
-- ---------------------------------------------------------------------------

/--
  ONE STEP: some transition of `ts` is exercised on some active contract.

  Reading the constructor, with the side conditions called out because they
  are the whole content of the model:

    * `ht`      - only transitions from `ts` run. A ledger that can also
                  run a choice outside `ts` has steps this relation does
                  not contain, and the theorems below say nothing about it.
    * `env`     - the environment in which this exercise happened: the
                  choice argument, the archived contract's fields, and
                  every other symbol the transition mentions. It is
                  existentially chosen per step, which is what makes the
                  invariant a statement about ALL executions.
    * `htpl`    - the choice was exercised on a contract of the
                  transition's own template.
    * `hthis`   - THE LINK CONDITION: in that environment, the term the
                  transition uses for the archived contract's tracked field
                  denotes that contract's actual field value. The pipeline
                  cannot check this (it is the meaning of the symbol
                  `this.amount`, not a fact about the formula), so it is an
                  assumption of the ledger model, stated here and repeated
                  in the theorem's side conditions. A fuller model would
                  demand agreement on EVERY field of the archived contract;
                  the weaker form is what the proof consumes.
    * `hg`      - the guards hold, which is what "this choice could be
                  exercised" means (`ensure` plus path conditions).

  The archived contract is at an arbitrary position and the created ones
  take its place; nothing depends on the position (see `totalAmount_swap`).
-/
inductive Step (M : RealModel) (f : String) (ts : List LedgerTransition) :
    LedgerState M -> LedgerState M -> Prop where
  | exec (lt : LedgerTransition) (ht : lt ∈ ts) (env : ModelEnv M)
      (pre post : LedgerState M) (c : Contract M)
      (htpl : c.template = lt.template)
      (hthis : evalM M env lt.thisAmount = c.fields f)
      (hg : forall g, g ∈ lt.guards -> evalM M env g = true) :
      Step M f ts (pre ++ c :: post)
        (pre ++ (lt.creates.map (CreateSpec.instantiate M env) ++ post))

/-- Reachability: the reflexive-transitive closure of a step relation,
    from an initial state. Generic in the relation so the induction
    principle below is reusable for any step relation, not only `Step`. -/
inductive Reachable {M : RealModel} (R : LedgerState M -> LedgerState M -> Prop)
    (S0 : LedgerState M) : LedgerState M -> Prop where
  | refl : Reachable R S0 S0
  | tail {S S' : LedgerState M} : Reachable R S0 S -> R S S' -> Reachable R S0 S'

/--
  THE INDUCTION PRINCIPLE. An invariant that holds initially and is
  preserved by every step holds in every reachable state. This is what
  lifts the per-transition theorems of Formal/Soundness.lean to a
  statement about all executions.
-/
theorem invariant_reachable {M : RealModel}
    (R : LedgerState M -> LedgerState M -> Prop) (I : LedgerState M -> Prop)
    (S0 : LedgerState M) (hinit : I S0)
    (hstep : forall S S', I S -> R S S' -> I S') :
    forall S, Reachable R S0 S -> I S := by
  intro S hreach
  induction hreach with
  | refl => exact hinit
  | tail _ hstep' ih => exact hstep _ _ ih hstep'

/-- The same, specialized to the ledger step relation - the shape the task
    of this file is stated in. -/
theorem invariant_reachable_step {M : RealModel} (f : String)
    (ts : List LedgerTransition) (I : LedgerState M -> Prop)
    (S0 : LedgerState M) (hinit : I S0)
    (hstep : forall S S', I S -> Step M f ts S S' -> I S') :
    forall S, Reachable (Step M f ts) S0 S -> I S :=
  invariant_reachable (Step M f ts) I S0 hinit hstep

-- ---------------------------------------------------------------------------
-- Worked instantiation 1: total of a numeric field is constant
-- ---------------------------------------------------------------------------

/-- The total of field `f` over the active contracts. -/
def totalAmount (M : RealModel) (f : String) (S : LedgerState M) : M.R :=
  sumM M (S.map (fun c => c.fields f))

theorem totalAmount_append {M : RealModel} (L : AddLaws M) (f : String)
    (S1 S2 : LedgerState M) :
    totalAmount M f (S1 ++ S2)
      = M.add (totalAmount M f S1) (totalAmount M f S2) := by
  show sumM M ((S1 ++ S2).map (fun c => c.fields f)) = _
  rw [List.map_append, sumM_append L]
  rfl

theorem totalAmount_cons {M : RealModel} (L : AddLaws M) (f : String)
    (c : Contract M) (S : LedgerState M) :
    totalAmount M f (c :: S) = M.add (c.fields f) (totalAmount M f S) := by
  show sumM M ((c :: S).map (fun x => x.fields f)) = _
  rw [List.map_cons, sumM_cons L]
  rfl

/-- Order is immaterial to the invariant: swapping two active contracts
    leaves the total alone. This is the promised justification for using a
    list where a multiset is meant. -/
theorem totalAmount_swap {M : RealModel} (L : AddLaws M) (f : String)
    (a b : Contract M) (S : LedgerState M) :
    totalAmount M f (a :: b :: S) = totalAmount M f (b :: a :: S) := by
  rw [totalAmount_cons L, totalAmount_cons L, totalAmount_cons L,
      totalAmount_cons L, ← L.add_assoc, ← L.add_assoc, L.add_comm (a.fields f)]

/-- The created contracts' field values are the evaluations of the created
    field TERMS - the list the conservation VC talks about. -/
theorem map_fields_instantiate {M : RealModel} (env : ModelEnv M) (f : String) :
    (creates : List CreateSpec) ->
    (creates.map (CreateSpec.instantiate M env)).map (fun c => c.fields f)
      = (creates.map (fun c => c.fieldTerm f)).map (evalM M env)
  | []            => rfl
  | c :: rest => by
      have ih := map_fields_instantiate env f rest
      simp only [List.map_cons, ih, CreateSpec.eval_fieldTerm]

/--
  ONE STEP PRESERVES THE TOTAL, given that the transition executed
  conserves. This is the per-transition-to-per-step bridge; everything
  global follows from it by `invariant_reachable`.
-/
theorem step_preserves_total {M : RealModel} (L : AddLaws M) (f : String)
    (ts : List LedgerTransition)
    (hcons : forall lt, lt ∈ ts -> ConservesM M (lt.toTransition f))
    {S S' : LedgerState M} (h : Step M f ts S S') :
    totalAmount M f S' = totalAmount M f S := by
  cases h with
  | exec lt ht env pre post c _htpl hthis hg =>
      have hc : sumM M
            ((lt.creates.map (fun x => x.fieldTerm f)).map (evalM M env))
          = evalM M env lt.thisAmount :=
        hcons lt ht env hg
      rw [totalAmount_append L, totalAmount_append L, totalAmount_append L,
          totalAmount_cons L]
      have hcreated : totalAmount M f (lt.creates.map (CreateSpec.instantiate M env))
          = c.fields f := by
        show sumM M ((lt.creates.map (CreateSpec.instantiate M env)).map
            (fun x => x.fields f)) = c.fields f
        rw [map_fields_instantiate env f lt.creates, hc, hthis]
      rw [hcreated]

/--
  THE COMPOSITION, and the point of the whole file: if the pipeline's VC is
  valid for every transition of `ts`, then the total of field `f` over the
  active contracts is the same in every reachable state as it was
  initially.

  SIDE CONDITIONS, stated plainly - the theorem is only as good as these:

    1. `hvc` - for each transition of `ts`, the conservation VC that
       backend/smt.js builds for it is valid IN THE MODEL `M`. A cvc5
       `unsat` on the emitted script is the pipeline's evidence for this;
       reading that verdict as validity in a model is the trusted-solver
       arrow of formal/Correspondence.md, unchanged by this file.
    2. `heq` - `M` decides equality of its carrier as the solver does
       (`M.eqb a b = true` iff `a = b`). True in any faithful model of
       SMT-LIB Real.
    3. `L : AddLaws M` - `M`'s addition is a commutative monoid. True of
       SMT-LIB Real. NOT true of core `Std.Internal.Rat` as a
       REPRESENTATION, which is why this development is generic in `M`;
       see the header of Formal/Model.lean.
    4. Every step is an exercise of a transition of `ts` on a contract of
       that transition's template, whose guards hold, and in an environment
       where the transition's `thisAmount` term denotes the archived
       contract's actual field value (the link condition `hthis` of
       `Step.exec`). Steps outside this - choices not in `ts`, nonconsuming
       choices, transitions that archive contracts besides `this` - are not
       in the relation, and the conclusion says nothing about ledgers that
       can take them.
    5. The correspondence between this abstract ledger and a real Daml
       ledger is not proved: see the header, and
       formal/Correspondence.md.
-/
theorem conservation_global {M : RealModel} (L : AddLaws M) (f : String)
    (ts : List LedgerTransition) (S0 : LedgerState M)
    (heq : forall a b : M.R, M.eqb a b = true <-> a = b)
    (hvc : forall lt, lt ∈ ts ->
      forall env : ModelEnv M, evalM M env (vcgen (lt.toTransition f)) = true) :
    forall S, Reachable (Step M f ts) S0 S ->
      totalAmount M f S = totalAmount M f S0 := by
  have hcons : forall lt, lt ∈ ts -> ConservesM M (lt.toTransition f) := by
    intro lt hlt
    exact vcgenM_sound M (lt.toTransition f) heq (hvc lt hlt)
  refine invariant_reachable_step f ts
    (fun S => totalAmount M f S = totalAmount M f S0) S0 rfl ?_
  intro S S' hI hstep
  rw [step_preserves_total L f ts hcons hstep]
  exact hI

-- ---------------------------------------------------------------------------
-- Worked instantiation 2: a template-level invariant
-- ---------------------------------------------------------------------------

/--
  A second, arithmetic-free instantiation, to show the induction principle
  is reusable and to justify carrying template names in the state: if no
  transition of `ts` creates template `X` and no contract of template `X`
  is active initially, then none ever is.

  This is the shape an invariant like "no contract is both active and
  cancelled" takes in this model: a property of the active set, preserved
  by every step.
-/
theorem no_template_reachable {M : RealModel} (f : String)
    (ts : List LedgerTransition) (S0 : LedgerState M) (X : String)
    (hinit : forall c, c ∈ S0 -> c.template ≠ X)
    (hcreates : forall lt, lt ∈ ts -> forall cs, cs ∈ lt.creates -> cs.template ≠ X) :
    forall S, Reachable (Step M f ts) S0 S -> forall c, c ∈ S -> c.template ≠ X := by
  refine invariant_reachable_step f ts
    (fun S => forall c, c ∈ S -> c.template ≠ X) S0 hinit ?_
  intro S S' hI hstep
  cases hstep with
  | exec lt ht env pre post c _htpl _hthis _hg =>
      intro d hd
      rcases List.mem_append.mp hd with hpre | hrest
      · exact hI d (List.mem_append.mpr (Or.inl hpre))
      · rcases List.mem_append.mp hrest with hcre | hpost
        · rcases List.mem_map.mp hcre with ⟨cs, hcs, heqd⟩
          subst heqd
          exact hcreates lt ht cs hcs
        · exact hI d (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem c hpost)))

-- ---------------------------------------------------------------------------
-- Sanity: the composition is not vacuous
-- ---------------------------------------------------------------------------

/-
  Every hypothesis of `conservation_global` is satisfiable together, shown
  by instantiating the whole chain on a concrete transition. This is a
  WITNESS, not a claim about any real Daml package: `intModel` is the
  `AddLaws` witness of Formal/Model.lean (not a faithful model of SMT-LIB
  Real), and the transition below is written here, not extracted from a
  DAR. Its only job is to rule out the reading "the theorem holds because
  its hypotheses cannot all be met".
-/

/-- A split: archives `this` and creates two pieces, of amounts `arg.x` and
    `this.amount - arg.x`. -/
def splitTransition : LedgerTransition :=
  { template   := "Splitter",
    guards     := [],
    creates    :=
      [ { template := "Piece", fields := [("amount", .var "arg.x" .real)] },
        { template := "Piece",
          fields := [("amount", .sub (.var "this.amount" .real) (.var "arg.x" .real))] } ],
    thisAmount := .var "this.amount" .real }

theorem splitTransition_conserves :
    ConservesM intModel (splitTransition.toTransition "amount") := by
  intro env _
  show env.realVar "arg.x" + (env.realVar "this.amount" - env.realVar "arg.x")
     = env.realVar "this.amount"
  rw [Int.add_comm, Int.sub_add_cancel]

theorem intModel_eqb (a b : Int) : intModel.eqb a b = true <-> a = b := by
  simp

/-- The global invariant, end to end, for a ledger whose only choice is the
    split: in every reachable state the total `amount` is what it was
    initially. -/
theorem split_conservation_global (S0 : LedgerState intModel) :
    forall S, Reachable (Step intModel "amount" [splitTransition]) S0 S ->
      totalAmount intModel "amount" S = totalAmount intModel "amount" S0 :=
  conservation_global intLaws "amount" [splitTransition] S0 intModel_eqb
    (by
      intro lt hlt env
      have : lt = splitTransition := by
        simpa using hlt
      subst this
      exact vcgenM_complete intModel _ intModel_eqb splitTransition_conserves env)

-- Axiom audit for the main results of this file. Verified output of the
-- #print axioms commands below (lake build, Lean 4.15.0):
--
--   'Formal.invariant_reachable' does not depend on any axioms
--   'Formal.step_preserves_total' depends on axioms: [propext]
--   'Formal.conservation_global' depends on axioms: [propext, Quot.sound]
--   'Formal.no_template_reachable' depends on axioms: [propext, Quot.sound]
--   'Formal.split_conservation_global' depends on axioms: [propext, Quot.sound]
--
-- propext and Quot.sound are Lean kernel axioms. No sorry, no
-- Classical.choice, no user axioms. `AddLaws` is a HYPOTHESIS of the
-- theorems that need it, never an axiom of the development.
#print axioms invariant_reachable
#print axioms step_preserves_total
#print axioms conservation_global
#print axioms no_template_reachable
#print axioms split_conservation_global

end Formal

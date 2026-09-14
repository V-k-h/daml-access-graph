# Correspondence and trust boundaries

> For the definitions and theorems themselves, stated in mathematics, see
> [`SPECIFICATION.md`](SPECIFICATION.md). This document is the trust audit:
> which arrows are machine-checked, which are tested, and which are trusted.

This document states, arrow by arrow, what in the pipeline

    DAR -> protobuf -> IR (guarded transitions) -> SMT-LIB -> cvc5 verdict

is machine-checked, what is tested, and what is trusted, and - since the
ledger layer was added - what one verdict per transition does and does not
say about a whole execution. The machine-checked part is the Lean development
in this directory (`lake build`, core Lean 4 only, no mathlib, no sorry;
axioms of the main theorems: `propext` and `Quot.sound`, both Lean kernel
axioms, and no user axioms anywhere: the algebraic laws the ledger layer needs
are hypotheses of the theorems that use them, not assertions).

Files: `Term`/`Eval` (IR and its semantics), `Transition`/`VCGen`/`Soundness`
(amount conservation), `Division` (division safety), `MiniLF*`/`Translate*`/
`EndToEnd` (the source-fragment arrow), `Model` (carrier-generic semantics and
the algebraic laws), `Ledger` (ledger states, steps, reachability, and the
induction principle).

## The arrows

| Arrow | Artifact | Status |
|---|---|---|
| Daml source -> DAR (compiled LF) | `damlc` | **Trusted.** The compiler is the root of trust for what the package means. Formalizing Daml-LF semantics and verifying compilation is out of scope and stated future work. |
| DAR -> protobuf messages | `backend/protobuf.js` (reader), zip/DALF extraction | **Tested** (JS test suite). A misread here produces a wrong IR, which the theorem cannot detect: the theorem starts at the IR. |
| protobuf -> IR guarded transitions | `backend/lfir.js` (translator) | **Machine-checked for the MiniLF fragment** (`Formal.translate_correct`), **tested elsewhere.** Lean models the post-inlining expression fragment (`Formal/MiniLF.lean`), gives it its own semantics (`evalLF`), mirrors the JS translation (`Formal/Translate.lean`), and proves `eval env (translate e) = evalLF env e`. Outside that fragment the claim "this LF expression denotes this IR term" remains untrusted JS; the residue is enumerated below. Hardened by design throughout: translation is total, anything outside the fragment becomes an explicit `unsupported` node, and the property builders refuse transitions whose relevant positions contain one. |
| IR -> SMT-LIB script | `backend/smt.js` (`buildQuery`, `termToSmt`) mirrored by `Formal.vcgen` and `Formal.vcgenDiv` | **Machine-checked at the VC level for BOTH shipped properties** (see below), **tested at the syntax level**. Amount conservation: validity of the VC formula implies the property, and conversely (`Formal.vcgen_iff`), plus guard-drop monotonicity (`Formal.drop_guard_sound`, `Formal.drop_guards_sound`, `Formal.vcgen_dropped_guards_sound`). Division safety: the same three results (`Formal.vcgenDiv_iff`, `Formal.divsafe_drop_guard_sound`, `Formal.vcgenDiv_dropped_guards_sound`), plus `Formal.divsafe_denominators_mono` for the per-denominator coverage split. What Lean does NOT check: that the printed SMT-LIB text is the term (printer is trivial and tested), nor `inferSorts` (the indexed Lean type makes ill-sorted terms unrepresentable instead). |
| SMT-LIB script -> unsat/sat | `cvc5` | **Trusted.** An `unsat` verdict is taken to mean the asserted set {guards, not goal} has no model, i.e. the single VC formula is valid. (cvc5 can emit proofs; checking them is future work.) |
| unsat -> "property PROVED" report | report layer | **Machine-checked meaning:** `Formal.vcgen_sound` says a valid conservation VC entails `Conserves`; `Formal.vcgenDiv_sound` says a valid division-safety VC entails `DivisionSafe`; the `..._dropped_guards_sound` pair says both survive dropped guards. The report's English sentence is backed by these theorems given the trusted/tested arrows above. |
| one transition -> every reachable ledger state | `Formal/Ledger.lean` | **Machine-checked INSIDE THE LEAN LEDGER MODEL** (`Formal.invariant_reachable`, `Formal.step_preserves_total`, `Formal.conservation_global`, `Formal.no_template_reachable`). A property proved of each transition in isolation is lifted to an invariant of every state reachable from an initial state. **What is NOT checked:** that the transitions `lfir.js` extracts are the steps a real Daml (Canton) ledger can take. That correspondence is the untrusted residue already enumerated below, plus the ledger abstraction itself (its own list, below). |

## The MiniLF fragment: what moved, and what did not

`Formal/EndToEnd.lean` composes translation correctness with VC soundness:

    minilf_vcgen_sound : (forall env, eval env (vcgen (translateTransition t)) = true)
                         -> ConservesLF t

`ConservesLF` is stated entirely in **source-fragment semantics** (`evalLF`
over MiniLF expressions), not in IR semantics. So for a transition whose
expressions lie in MiniLF, a cvc5 `unsat` now entails a property about the
MiniLF-level meaning of the choice, with the LF-to-IR step no longer taken on
trust. `minilf_vcgen_iff` gives the converse for the same fragment.

This is one arrow, not the whole chain. MiniLF is the fragment `lfir.js`
reaches on its happy path AFTER its own JS-side work; that work is what
remains untrusted.

### Untrusted residue of `lfir.js` (enumerated, not glossed)

Everything below happens in JavaScript before or around the fragment the Lean
theorem covers. A bug in any of it can still produce a proof about the wrong
formula, and no theorem here would notice:

1. **Cross-package beta reduction and inlining** - `betaReduce`, type-layer
   unwrapping, over-application, following `ValueId` references into
   dependency DALFs and swapping the interning context per package. MiniLF is
   the POST-inlining fragment; the inliner is the largest untrusted component.
2. **Record chasing** - `ctx.rawEnv`, `recordFields`, `RecUpd` peeling to a
   call-site `RecCon`. MiniLF bakes only the OUTCOME (a `proj` root) into its
   syntax; how the translator decided that outcome is untrusted.
3. **`ensure` conjunct decomposition** - `guardConjuncts`, the
   `ite(c, a, False|abort) -> c AND a` rewrite, and per-conjunct dropping.
   The DROP is covered by `vcgen_dropped_guards_sound`; the DECOMPOSITION is
   not.
4. **Interface dispatch** - resolving `interface instance` method bodies,
   `call_interface`, matching interface choices to instance methods.
5. **Effect collection** - `collectEffects` deciding which `create`s a choice
   performs, and the path conditions attached to them. The theorem takes the
   transition's create list as given; that the list is complete and correct
   for the compiled choice is untrusted. This is why `amountConservation`
   attaches a note when the body had untranslated parts: effects beyond the
   recovered creates may exist.
6. **Symbol naming** - that `proj this "amount"` and the JS `symbol()` produce
   the same string `this.amount`. Lean fixes a naming convention; that the JS
   agrees with it is convention, checked by tests, not by proof.
7. **Sort inference** - `inferSorts`. The indexed Lean types make ill-sorted
   terms unrepresentable rather than proving the JS inference correct.
8. Everything listed as deliberately excluded in `Formal/MiniLF.lean`:
   rounding builtins, `div`/`mod`, Text and the String sort, Bool equality,
   Optional case analysis, abort/throw.

## Division safety (the second shipped property)

`Formal/Division.lean` gives `division-safety` the same treatment amount
conservation already had, so both properties the pipeline ships now rest on a
checked theorem rather than one of them:

    DivisionSafe d : forall env, (all guards hold) -> every denominator is nonzero
    vcgenDiv d     = not (guards... && not ((not (d1 = 0)) && ... && (not (dn = 0))))

- `vcgenDiv_sound` : validity of that formula in every environment implies
  `DivisionSafe`. `vcgenDiv_iff` adds the converse (completeness of the
  generator, not of the solver).
- `vcgenDiv_dropped_guards_sound` : proved from the USABLE guards, the property
  holds under the transition's full guard list - the same monotonicity note
  that backend/smt.js relies on for conservation.
- `divsafe_denominators_mono` : safety for a set of denominators gives safety
  for a SUBSET, and nothing for denominators the VC never mentioned. This is
  the honest reading of the per-denominator `coverage` split in
  `divisionSafety`: proving the `checkable` ones says nothing about the
  `skipped` ones, which is why the report never prints a bare PROVED when
  `coverage.skipped` is nonempty.

Not modelled (the JS refuses or qualifies before a VC exists): denominators
recovered from unrolled fold steps (the verdict is `bounded`, and nothing is
claimed beyond the bound), and transitions where nothing is checkable.

## Ledger-state induction: from one transition to every reachable state

Every theorem above is about ONE transition in isolation. `Formal/Ledger.lean`
adds the induction principle that lifts such theorems to all executions, and
the composition that makes it do work:

    invariant_reachable  : I S0 -> (forall S S', I S -> R S S' -> I S')
                           -> forall S, Reachable R S0 S -> I S

    conservation_global  : (every transition of `ts` has a valid VC)
                           -> forall S, Reachable (Step M f ts) S0 S
                              -> totalAmount M f S = totalAmount M f S0

The chain is: `vcgenM_sound` turns VC validity into `ConservesM` per
transition; `step_preserves_total` turns `ConservesM` into "this step does not
change the total"; `invariant_reachable` turns that into a statement about
every reachable state. `no_template_reachable` is a second, arithmetic-free
instantiation (no contract of a template nothing creates is ever active),
present to show the principle is reusable and that template names in the state
earn their place.

### The state abstraction, against what the pipeline observes

A state is a LIST OF ACTIVE CONTRACTS, each a template name plus a valuation of
its numeric fields, because that is what `backend/lfir.js` extracts and no
more: `creates[i].template`, `creates[i].fields` (field name -> IR term),
archival of `this` under the `consuming` flag. Activity is membership. No
contract ids, parties, observers, keys, or time are modelled, because the
extractor records none of them in any position a property reads. Order is not
observable; a list is used because core Lean has no multiset, the step relation
consumes a contract at an arbitrary position, and `totalAmount_swap` shows the
invariant is insensitive to order.

Fields a create does not mention read `ofRat 0` in the model. That is a
modelling choice, not an observation - it is matched exactly on the term side
(`CreateSpec.fieldTerm` defaults to the literal `0`), and `amountConservation`
refuses a create with no `amount` field anyway, so no verdict is transported
through that case.

### Side conditions of `conservation_global`, stated plainly

1. The VC of every transition in `ts` is valid in the model reasoned in. A cvc5
   `unsat` is the pipeline's evidence; reading a verdict as validity is the
   trusted-solver arrow above, unchanged.
2. The model decides carrier equality as the solver does (`M.eqb a b = true`
   iff `a = b`).
3. The carrier's addition is a commutative monoid (`AddLaws M`) - true of
   SMT-LIB Real, not true of the Lean REPRESENTATION `Std.Internal.Rat`; see
   the next section.
4. Every step is an exercise of a transition of `ts`, on a contract of that
   transition's template, whose guards hold, in an environment where the
   transition's `thisAmount` term denotes THAT contract's actual field value
   (the link condition). The pipeline cannot check this last part: it is the
   meaning of the symbol `this.amount`, not a fact about the formula.
5. Only single-archive, consuming transitions are in the relation.
   Nonconsuming choices (which `amountConservation` reports as
   `applicable: false`) and transitions with `archivedInputs` (where the model
   cannot say which active contracts the `L$i.amount` symbols denote) are
   outside it.

### What the induction theorem does NOT give you

It is a theorem about the abstract ledger model defined in
`Formal/Ledger.lean`. It does not say that the transitions the pipeline
extracts correspond to the steps a real Daml ledger takes. That claim is
exactly the untrusted residue enumerated above for `lfir.js` - inlining,
record chasing, `ensure` decomposition, interface dispatch, effect collection,
symbol naming, sort inference, and the excluded builtins - PLUS the ledger
abstraction itself:

9. **The ledger model.** That "the active contract set is a multiset of
   (template, numeric field valuation)" is an adequate abstraction of a Canton
   ledger; that a transaction is one such step rather than a tree of them
   (sub-transactions, rollbacks, nonconsuming exercises inside a consuming
   one); that `collectEffects` recovered ALL the creates and archivals of the
   choice (a missed create is a step the model does not contain); and the link
   condition in 4 above. None of this is proved, and no theorem here would
   notice if it were false.

A one-line summary of the value: BEFORE, a PROVED verdict meant "this one
transition conserves". AFTER, the same verdict set means "no execution of this
package's checked choices changes the total" - inside the model, and subject to
the five side conditions.

## What the Lean theorems say, exactly

For a transition `t` with usable guards `used` (subset of the full guards
`full`), created amounts `as`, and archived amount `a`:

    vcgen t = not (used_1 && ... && used_n && not (sum as = a))

- `vcgen_sound` : if `eval env (vcgen t) = true` for EVERY environment,
  then in every environment where all of `t`'s guards hold, the sum of the
  evaluated created amounts equals the evaluated archived amount
  (`Conserves t`).
- `vcgen_iff` : the converse also holds; the VC is literally the property
  (completeness of vcgen for this fragment - not of the solver, which may
  time out).
- `vcgen_dropped_guards_sound` : validity of the VC built from `used` alone
  implies `Conserves` for the transition with the FULL guard list. This is
  the load-bearing soundness note at the top of `backend/smt.js`: dropping
  an assumption only strengthens what was proved. Direction check: the
  fewer-guards VC quantifies over MORE environments (a superset of the
  reachable states), so its validity is the stronger statement, and the
  property under more guards follows. What is lost is completeness only: a
  property that holds because of a dropped `ensure` will come back
  DISPROVED with a spurious counterexample, never wrongly PROVED.

Environments in Lean are total maps `String -> Rat` and `String -> Bool`
(one per sort), matching the SMT declaration of every free symbol as an
uninterpreted constant of sort Real or Bool: a first-order model of the
buildQuery script is exactly such a pair of maps.

## The division convention (the subtle part)

Lean semantics: `/` on `Rat` is total with `x / 0 = 0` (core
`Std.Internal.Rat`: division is multiplication by `inv`, and `inv 0 = 0`).
SMT-LIB semantics: `/` on Real is UNDERSPECIFIED at 0 - the standard says
models may interpret `(/ x 0)` as any value; cvc5 concretely treats
division as a total function unconstrained at 0.

Why the two agree where it matters, in the only direction the pipeline
uses:

1. cvc5 answers `unsat` only if {guards, not goal} has no model under ANY
   total interpretation of division at 0. The interpretation `x / 0 = 0` is
   one of them. Therefore `unsat` implies the VC formula is true in every
   environment UNDER THE LEAN SEMANTICS TOO, which is precisely the
   hypothesis `forall env, eval env (vcgen t) = true` of `vcgen_sound`.
   The convention can only make the Lean hypothesis EASIER to satisfy than
   "true under all interpretations"; it is implied by unsat, never assumed
   by it.

2. The reverse direction (Lean-valid but cvc5 says `sat`) can happen only
   when the counterexample forces a division by zero and exploits a value
   of `x / 0` other than 0. That costs completeness, not soundness: the
   pipeline reports DISPROVED/counterexample, never a wrong PROVED. And the
   pipeline separately runs `division-safety` (backend/smt.js), which
   proves every denominator nonzero under the guards; on transitions where
   that property is PROVED, no reachable environment divides by zero and
   the two semantics coincide outright.

3. The IR ops `div` and `mod` (from `DIV_INT64` / `MOD_INT64`) are modelled
   in Lean as euclidean division/remainder totalized with divisor 0 mapped
   to 0 (`Formal.smtDiv`, `Formal.smtMod`) - the same argument applies. In
   addition these builtins are members of the translator's `rounding` set,
   and `amountConservation` REFUSES transitions that round, so they never
   occur in a conservation VC the pipeline actually emits.

Caveat stated honestly: point 1 is a PAPER argument about cvc5 and the
SMT-LIB standard, not a Lean theorem. The machine-checked statement starts
at "the VC is valid under `Formal.eval`". Bridging "cvc5 said unsat" to
that hypothesis is exactly the trusted-solver arrow of the table, with the
division caveat above as its finest print. A second paper-level remark: the
soundness proof never unfolds any `Rat` arithmetic, so the theorem is
insensitive to the numeric carrier (it holds verbatim with Rat replaced by
the reals); `Rat` matters only for making `eval` computable in Lean.

## The numeric carrier, and why the ledger layer is generic in it

The per-transition theorems never unfold a single `Rat` operation, so they hold
for any carrier with the same operations; that was already noted above as a
paper remark. `Formal/Model.lean` now makes it a machine-checked statement:
the IR semantics is re-given over an arbitrary `RealModel`, `evalM_rat` proves
the instance at `Std.Internal.Rat` IS the shipped `Formal.eval`, and
`vcgen_sound_via_model` re-derives the shipped soundness theorem through the
generic layer. Nothing is weakened by working generically.

The ledger layer NEEDS the generality, for a reason worth stating exactly,
because it is a fact about the representation and not about the rationals:

- A step replaces one contract by a LIST of created ones, so preserving a sum
  over the active set requires re-associating that sum.
- `Std.Internal.Rat` is a bare `(num : Int, den : Nat)` structure with no
  reducedness invariant and a private constructor, and core's `Rat.add`
  computes with gcds in a way that is correct only on already-reduced
  arguments. Addition is therefore NOT associative on the type: taking the
  representations (-4)/2, (-4)/2 and (-4)/4 gives ((a+b)+c) = (-20)/4 and
  (a+(b+c)) = (-5)/1. Both denote -5, but Lean's `=` on `Rat` is equality of
  the representation. (Checked by mirroring core's `Rat.add` outside Lean and
  searching small representations: associativity fails on unreduced inputs;
  commutativity and the unit laws hold on all inputs, and `0 + a = a` is
  provable in Lean directly.)
- On reduced representations associativity does hold, but proving that is a
  correctness theory for `Std.Internal.Rat` that core does not provide (the
  module exports definitions and no algebraic lemmas at all) and that this
  development does not attempt. The values cannot be assumed reduced either:
  an environment is an arbitrary total map `String -> Rat`.

So `forall a b c : Rat, a + b + c = a + (b + c)` is not a theorem, and ASSUMING
it would be assuming a falsehood, which would make every theorem depending on
it vacuous. Instead the three laws are a hypothesis `AddLaws M` on the model.
They are theorems about the rationals - hence about SMT-LIB Real, which is what
cvc5 reasons over - so they add no assumption about the pipeline, and
`Formal.intLaws` exhibits a model satisfying them, which rules out a vacuous
reading. `Formal.split_conservation_global` instantiates the entire chain on a
concrete two-create transition, as a witness that the hypotheses of
`conservation_global` are jointly satisfiable.

A reviewer should scrutinize exactly this point: the global conservation
theorem is stated for models whose addition is a commutative monoid, and the
computable `ratModel` used elsewhere in the development is not one of them at
the level of representations. What bridges them is the solver arrow: an `unsat`
verdict is validity under every interpretation of the script, including the
models the ledger theorem quantifies over.

## Rounding (why Numeric 10 is out of scope here)

Daml `Decimal` is `Numeric 10`, a fixed-point type. The IR models numbers
as exact rationals, which is sound for order/sign/nonzero facts and unsound
for exact value equalities on paths that round. The translator records
every rounding builtin on the transition, and `amountConservation` refuses
to state the property when the set is nonempty. Consequently the Lean
theorem only ever meets rounding-free transitions, where exact rationals
are a faithful model of Numeric arithmetic (addition, subtraction,
multiplication by integral literals, and comparisons on scale-10 values are
exact). Formalizing Numeric 10 itself is future work, not claimed.

## Future work (explicitly NOT claimed by this development)

- Daml-LF operational semantics in Lean and a verified translator
  (discharging the `lfir.js` arrow).
- A verified SMT-LIB printer/parser (discharging the `termToSmt` arrow).
- Checking cvc5 proof objects instead of trusting verdicts.
- A Numeric 10 fixed-point model to lift the rounding refusal.
- A verified rational carrier (reduced-by-construction, with the commutative
  monoid laws proved) so the ledger theorems could be instantiated at the
  computable semantics instead of at an abstract model.
- Ledger steps for the cases currently outside the model: multi-archive
  (`archivedInputs`) transitions, nonconsuming choices, and transaction trees
  rather than flat steps.

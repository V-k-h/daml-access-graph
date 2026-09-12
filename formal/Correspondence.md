# Correspondence and trust boundaries

This document states, arrow by arrow, what in the pipeline

    DAR -> protobuf -> IR (guarded transitions) -> SMT-LIB -> cvc5 verdict

is machine-checked, what is tested, and what is trusted. The machine-checked
part is the Lean development in this directory (`lake build`, core Lean 4
only, no mathlib, no sorry; axioms of the main theorems: `propext` and
`Quot.sound`, both Lean kernel axioms).

## The arrows

| Arrow | Artifact | Status |
|---|---|---|
| Daml source -> DAR (compiled LF) | `damlc` | **Trusted.** The compiler is the root of trust for what the package means. Formalizing Daml-LF semantics and verifying compilation is out of scope and stated future work. |
| DAR -> protobuf messages | `backend/protobuf.js` (reader), zip/DALF extraction | **Tested** (JS test suite). A misread here produces a wrong IR, which the theorem cannot detect: the theorem starts at the IR. |
| protobuf -> IR guarded transitions | `backend/lfir.js` (translator) | **Machine-checked for the MiniLF fragment** (`Formal.translate_correct`), **tested elsewhere.** Lean models the post-inlining expression fragment (`Formal/MiniLF.lean`), gives it its own semantics (`evalLF`), mirrors the JS translation (`Formal/Translate.lean`), and proves `eval env (translate e) = evalLF env e`. Outside that fragment the claim "this LF expression denotes this IR term" remains untrusted JS; the residue is enumerated below. Hardened by design throughout: translation is total, anything outside the fragment becomes an explicit `unsupported` node, and the property builders refuse transitions whose relevant positions contain one. |
| IR -> SMT-LIB script | `backend/smt.js` (`buildQuery`, `termToSmt`) mirrored by `Formal.vcgen` | **Machine-checked at the VC level** (see below), **tested at the syntax level**. Lean proves: validity of the VC formula implies the conservation property, and conversely (`Formal.vcgen_iff`), plus guard-drop monotonicity (`Formal.drop_guard_sound`, `Formal.drop_guards_sound`, `Formal.vcgen_dropped_guards_sound`). What Lean does NOT check: that the printed SMT-LIB text is the term (printer is trivial and tested), nor `inferSorts` (the indexed Lean type makes ill-sorted terms unrepresentable instead). |
| SMT-LIB script -> unsat/sat | `cvc5` | **Trusted.** An `unsat` verdict is taken to mean the asserted set {guards, not goal} has no model, i.e. the single VC formula is valid. (cvc5 can emit proofs; checking them is future work.) |
| unsat -> "property PROVED" report | report layer | **Machine-checked meaning:** `Formal.vcgen_sound` says a valid VC entails `Conserves`; `Formal.vcgen_dropped_guards_sound` says this survives dropped guards. The report's English sentence is backed by these theorems given the trusted/tested arrows above. |

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

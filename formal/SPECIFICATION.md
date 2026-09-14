# Mathematical specification

This document states, in mathematics, what the verification pipeline computes
and what its verdicts mean. It is the formal companion to
[`Correspondence.md`](Correspondence.md), which covers the same ground as an
arrow-by-arrow trust audit. Read this one for the definitions and theorems;
read that one to find out which arrows are machine-checked and which are
merely tested.

Every definition below has a counterpart in `formal/Formal/*.lean` and in
`backend/*.js`, and the names are given so a reader can jump to either. Where
the two differ, the difference is stated rather than smoothed over.

## 1. The problem

A Daml package compiles to Daml-LF, a typed intermediate language. We want
statements of the form "no choice in this package can create a contract with a
negative balance" to be *proved*, not sampled by tests.

The obstacle is the **correspondence gap**. Writing a symbolic model by hand
next to the code and verifying the model proves things about the model; whether
the model matches the contract stays an unproven comment. Formally, a
hand-written development establishes

$$M \models \varphi$$

for a hand-built model $M$, and leaves $[\![C]\!] = M$ unproven, where
$[\![C]\!]$ denotes the meaning of the actual compiled contract $C$.

This pipeline instead derives the model from the compiled artifact, so the
correspondence holds by construction for the fragment it translates, and every
edge of that fragment is machine-reported rather than elided.

## 2. The pipeline

$$
\text{DAR}
\;\xrightarrow{\;\text{readDarRaw}\;}\;
\text{LF}
\;\xrightarrow{\;\mathcal{T}\;}\;
\mathcal{I}
\;\xrightarrow{\;\mathrm{VCGen}\;}\;
\text{SMT-LIB}
\;\xrightarrow{\;\text{cvc5}\;}\;
\{\mathsf{unsat}, \mathsf{sat}, \mathsf{unknown}\}
$$

with $\mathcal{T}$ the translator (`backend/lfir.js`) and $\mathcal{I}$ the
space of guarded transitions. The central claim, proved in Lean for the
fragment described in section 8, is

$$\boxed{\;\models \mathrm{VCGen}(P, \varphi) \;\Longrightarrow\; P \models \varphi\;}$$

where $\models \psi$ means $\psi$ evaluates to true in every environment.

## 3. Syntax

Sorts, `Formal/Term.lean`:

$$s \;::=\; \mathbb{R} \;\mid\; \mathbb{B}$$

Terms are indexed by sort, $t : \mathrm{Term}\, s$. Making the index part of
the type means ill-sorted terms cannot be written down, so evaluation is total:
no `Option`, no sort errors. The JS side achieves the same by rejecting
ill-sorted queries dynamically in `inferSorts`.

$$
\begin{aligned}
t^{\mathbb{R}} \;::=\;& q \;\mid\; x^{\mathbb{R}}
  \;\mid\; t_1 + t_2 \;\mid\; t_1 - t_2 \;\mid\; t_1 \cdot t_2 \\
  &\mid\; t_1 / t_2 \;\mid\; t_1 \mathbin{\mathrm{div}} t_2 \;\mid\; t_1 \bmod t_2 \\[4pt]
t^{\mathbb{B}} \;::=\;& b \;\mid\; x^{\mathbb{B}}
  \;\mid\; t_1 < t_2 \;\mid\; t_1 \le t_2 \;\mid\; t_1 > t_2 \;\mid\; t_1 \ge t_2 \\
  &\mid\; t_1 =_{\mathbb{R}} t_2 \;\mid\; t_1 =_{\mathbb{B}} t_2
  \;\mid\; \neg t \;\mid\; t_1 \wedge t_2 \;\mid\; t_1 \vee t_2
\end{aligned}
$$

with $q \in \mathbb{Q}$ and $b \in \{\text{true}, \text{false}\}$.

The numeric carrier is $\mathbb{Q}$, exact rationals, not floating point.
Daml's `Numeric 10` is modelled as exact $\mathbb{R}$. This is sound for
ordering, sign and division-safety, and unsound for exact equalities on paths
that round, which is why transitions carrying rounding builtins are refused
for equality properties rather than proved wrongly (section 11).

## 4. Semantics

An environment is a pair of total maps, `Formal/Eval.lean`:

$$\rho \;=\; (\rho_{\mathbb{R}}, \rho_{\mathbb{B}}), \qquad
\rho_{\mathbb{R}} : \mathrm{Name} \to \mathbb{Q}, \qquad
\rho_{\mathbb{B}} : \mathrm{Name} \to \mathbb{B}$$

Evaluation $[\![\cdot]\!]_\rho$ (Lean: `eval`) is defined by structural
recursion, homomorphically on every operator:

$$
[\![q]\!]_\rho = q, \qquad
[\![x^s]\!]_\rho = \rho_s(x), \qquad
[\![t_1 + t_2]\!]_\rho = [\![t_1]\!]_\rho + [\![t_2]\!]_\rho,
$$

and so on. Totality matters: it is what lets every later theorem be stated
without side conditions about undefined terms.

Division is total, with $t/0 = 0$ by convention, following SMT-LIB. This is
discussed in `Correspondence.md` section "The division convention"; the short
version is that the convention is harmless precisely because division safety
is proved as a separate obligation rather than assumed.

## 5. Guarded transitions

A transition, `Formal/Transition.lean`, is what remains of a Daml choice after
translation:

$$\tau \;=\; \langle G, A, a_{\text{this}} \rangle$$

- $G$, a finite list of guards, $g_i : \mathrm{Term}\,\mathbb{B}$
- $A$, the created amounts, $a_j : \mathrm{Term}\,\mathbb{R}$, one per create
- $a_{\text{this}}$, the archived contract's amount

$G$ holds the *usable* guards: `usableGuards` in `backend/smt.js` drops any
guard containing an unsupported node, and that drop is justified by
`drop_guards_sound` (section 7).

For division safety the transition carries a denominator list instead,
`Formal/Division.lean`:

$$\delta \;=\; \langle G, D \rangle, \qquad D = [d_1, \ldots, d_m]$$

## 6. The properties

Summation follows the term shape the emitter builds, with $\sum$ of the empty
list equal to $0$ and of a singleton equal to its element:

$$\Sigma([\,]) = 0, \qquad \Sigma([a]) = a, \qquad \Sigma(a :: r) = a + \Sigma(r)$$

**Amount conservation** (`Conserves`, `Formal/Transition.lean`):

$$
\mathrm{Conserves}(\tau) \;\equiv\;
\forall \rho.\;
\Bigl( \forall g \in G.\; [\![g]\!]_\rho = \text{true} \Bigr)
\;\Longrightarrow\;
\Sigma\bigl( [\![a]\!]_\rho : a \in A \bigr) = [\![a_{\text{this}}]\!]_\rho
$$

**Division safety** (`DivisionSafe`, `Formal/Division.lean`):

$$
\mathrm{DivisionSafe}(\delta) \;\equiv\;
\forall \rho.\;
\Bigl( \forall g \in G.\; [\![g]\!]_\rho = \text{true} \Bigr)
\;\Longrightarrow\;
\forall d \in D.\; [\![d]\!]_\rho \neq 0
$$

Both are universally quantified over environments, which is what makes a
positive verdict a proof rather than the absence of a found counterexample.

## 7. Verification conditions

The solver is asked for satisfiability of the set
$\{g_1, \ldots, g_n, \neg\,\mathrm{goal}\}$. An $\mathsf{unsat}$ answer is
equivalent to validity of a single formula, and that formula is what
$\mathrm{VCGen}$ builds. Writing $\bigwedge(G, \text{tail})$ for the right
fold $g_1 \wedge (g_2 \wedge (\cdots \wedge \text{tail}))$:

$$
\mathrm{VCGen}(\tau) \;=\;
\neg\, \Bigl( \textstyle\bigwedge \bigl(G,\; \neg\, (\Sigma(A) =_{\mathbb{R}} a_{\text{this}}) \bigr) \Bigr)
$$

$$
\mathrm{VCGen}_{\div}(\delta) \;=\;
\neg\, \Bigl( \textstyle\bigwedge \bigl(G,\; \neg \textstyle\bigwedge_{d \in D} (d \neq 0) \bigr) \Bigr)
$$

**The main theorems**, `Formal/Soundness.lean` and `Formal/Division.lean`:

$$
\begin{aligned}
\texttt{vcgen\_sound} &: \; (\forall \rho.\, [\![\mathrm{VCGen}(\tau)]\!]_\rho = \text{true}) \;\Rightarrow\; \mathrm{Conserves}(\tau) \\
\texttt{vcgen\_complete} &: \; \mathrm{Conserves}(\tau) \;\Rightarrow\; (\forall \rho.\, [\![\mathrm{VCGen}(\tau)]\!]_\rho = \text{true}) \\
\texttt{vcgen\_iff} &: \; (\forall \rho.\, [\![\mathrm{VCGen}(\tau)]\!]_\rho = \text{true}) \;\Longleftrightarrow\; \mathrm{Conserves}(\tau)
\end{aligned}
$$

with `vcgenDiv_sound`, `vcgenDiv_complete`, `vcgenDiv_iff` the same three for
division safety. Completeness here is a statement about $\mathrm{VCGen}$, not
about the solver: cvc5 may still time out on a valid VC.

**Guard dropping.** If the guards actually used are a sublist of the real ones,
$U \subseteq F$, then

$$
\texttt{drop\_guards\_sound} : \;
\mathrm{Conserves}(\langle U, A, a_{\text{this}} \rangle)
\;\Longrightarrow\;
\mathrm{Conserves}(\langle F, A, a_{\text{this}} \rangle)
$$

Fewer assumptions make the proved statement stronger. This is the formal
content of "dropping an untranslatable guard is sound for a proof": the
property is established over a superset of the reachable states. What it costs
is completeness, which is why a DISPROVED whose counterexample might be
excluded by a dropped guard says so in the report.
`divsafe_denominators_mono` plays the corresponding role for the
per-denominator coverage split that yields PROVED-PARTIAL.

## 8. Closing part of the correspondence gap

Sections 3 to 7 prove things about the IR. They say nothing about whether the
IR faithfully represents the LF the compiler emitted. That arrow is closed for
a fragment.

`Formal/MiniLF.lean` defines a sort-indexed fragment of post-inlining LF with
its own semantics $[\![\cdot]\!]^{\mathrm{LF}}$ (`evalLF`), including
projections and let-binding through a binding environment.
`Formal/Translate.lean` mirrors the JS translation as a function
$\mathcal{T}$, and `Formal/TranslateCorrect.lean` proves it correct:

$$
\texttt{translate\_correct} : \;
\mathrm{Agrees}(\rho, \Gamma_T, \Gamma_L)
\;\Longrightarrow\;
[\![\mathcal{T}_{\Gamma_T}(e)]\!]_\rho = [\![e]\!]^{\mathrm{LF}}_{\rho, \Gamma_L}
$$

where $\mathrm{Agrees}$ relates the translator's binding environment to the
source semantics' one. Composing with section 7 gives the end-to-end statement
in `Formal/EndToEnd.lean`:

$$
\texttt{minilf\_vcgen\_sound} : \;
\bigl( \forall \rho.\, [\![\mathrm{VCGen}(\mathcal{T}(t))]\!]_\rho = \text{true} \bigr)
\;\Longrightarrow\;
\mathrm{ConservesLF}(t)
$$

The conclusion $\mathrm{ConservesLF}$ is stated purely in source-fragment
semantics. For transitions inside MiniLF, a cvc5 $\mathsf{unsat}$ is a proof
about the *source expression*, not merely about the IR.

Outside MiniLF the claim "this LF expression denotes this IR term" is
untrusted JS. The residue is enumerated, not glossed, in `Correspondence.md`.

## 9. From one transition to every reachable state

A per-transition property is not yet a statement about a ledger.
`Formal/Ledger.lean` supplies the lifting. Let $\mathcal{S}$ be a ledger state
(a multiset of active contracts), $\mathrm{Step}$ the relation induced by a
transition list $ts$, and $\mathrm{Reachable}$ its reflexive transitive
closure. Writing $\mathrm{total}_f(\mathcal{S})$ for the sum of field $f$ over
active contracts:

$$
\texttt{conservation\_global} : \;
\bigl( \forall lt \in ts.\; \models \mathrm{VCGen}(lt) \bigr)
\;\Longrightarrow\;
\forall \mathcal{S}.\; \mathrm{Reachable}(\mathcal{S}_0, \mathcal{S})
\;\Rightarrow\;
\mathrm{total}_f(\mathcal{S}) = \mathrm{total}_f(\mathcal{S}_0)
$$

Proved by induction over reachability from `invariant_reachable` and
`step_preserves_total`. `no_template_reachable` gives the corresponding
template-level invariant.

This layer is generic in the numeric carrier: `Formal/Model.lean` abstracts
$\mathbb{Q}$ to any `RealModel`, and the algebraic laws the induction needs
(`AddLaws`) are **hypotheses of the theorems that use them**, not axioms. The
development declares no user axioms; `#print axioms` on the main theorems
reports only `propext` and `Quot.sound`, both Lean kernel axioms.

What this does **not** give you is that the transitions `lfir.js` extracts are
the steps a real Canton ledger can take. That correspondence is the untrusted
residue of section 8 plus the ledger abstraction itself.

## 10. Verdicts

The verdict vocabulary in `backend/verify.js` is deliberately asymmetric,
because $\mathsf{unsat}$ and $\mathsf{sat}$ carry very different weight.

| Verdict | Solver | Meaning |
|---|---|---|
| `PROVED` | $\mathsf{unsat}$ | No counterexample exists in the model. A theorem, modulo section 11. |
| `PROVED-BOUNDED` | $\mathsf{unsat}$ | As above, for lists up to the stated unrolling bound only. |
| `PROVED-PARTIAL` | $\mathsf{unsat}$ | As above, for a stated subset of the obligations, with the rest reported. |
| `DISPROVED` | $\mathsf{sat}$ | A concrete counterexample, printed. May be an artifact: see below. |
| `NOT-MODELLABLE` | not run | Refused, with a machine-generated reason. |
| `NOT-APPLICABLE` | not run | The property says nothing here (for example conservation of a choice that creates nothing). |
| `SOLVER-UNKNOWN` | $\mathsf{unknown}$ | No claim. |

**The asymmetry.** $\mathsf{unsat}$ proves. $\mathsf{sat}$ may be spurious,
for two reasons that the report always discloses:

1. A **dropped guard** may have excluded the counterexample.
2. An **uninterpreted function** may have been given an interpretation the real
   function never takes. Every verdict resting on one names it; a DISPROVED
   adds an explicit artifact caveat, and a PROVED must not depend on one in a
   way that would weaken it.

This is why a DISPROVED is a *finding to triage* rather than a bug report.

## 11. What is not proved

Stated plainly, because a specification that hides its limits is worse than
none.

- **`damlc` is trusted.** Daml source to DAR is outside the development. The
  compiler is the root of trust for what the package means.
- **cvc5 is trusted.** An $\mathsf{unsat}$ is taken at its word. Proof
  certificate checking is future work.
- **The protobuf reader is tested, not verified.** A misread produces a wrong
  IR, and the theorems start at the IR, so they cannot detect it.
- **`lfir.js` is verified only on MiniLF.** It is the trust root of this
  pipeline exactly as `damlc` is the trust root of the ledger.
- **Numeric 10 is exact $\mathbb{R}$.** Sound for sign, order and division
  safety; unsound for exact equalities on rounding paths, which are therefore
  refused rather than proved.
- **The Int sort is not in the Lean development.** `backend/*.js` distinguishes
  Daml `Int` from `Numeric` and emits SMT `Int` with integrality (commit
  `92942a3`), but Lean's `Srt` is still $\{\mathbb{R}, \mathbb{B}\}$. Every
  theorem above is stated over the two-sort fragment. Extending `Srt`, `eval`
  and `translate` to three sorts is open work. Note the direction of risk:
  integrality *shrinks* the model class, so a wrong Int classification could in
  principle yield a false PROVED. The JS side mitigates this by deriving
  Int-ness only from the compiled `DefDataType`, never from inference, but that
  argument is currently a code invariant and a test, not a theorem.

## 12. Where to look

| Concept | Lean | JavaScript |
|---|---|---|
| Sorts, terms | `Formal/Term.lean` | `backend/lfir.js` (`T`) |
| Semantics | `Formal/Eval.lean` | `backend/ir-eval.js` |
| Transitions | `Formal/Transition.lean` | `backend/lfir.js` (`extractTransitions`) |
| VC generation | `Formal/VCGen.lean` | `backend/smt.js` (`buildQuery`) |
| Soundness | `Formal/Soundness.lean` | (the claim the report makes) |
| Division safety | `Formal/Division.lean` | `backend/smt.js` (`divisionSafety`) |
| Source fragment | `Formal/MiniLF*.lean`, `Translate*.lean` | `backend/lfir.js` |
| Ledger induction | `Formal/Ledger.lean`, `Model.lean` | (no counterpart: this layer is Lean only) |

Build the development with `lake build` in `formal/`. It uses core Lean 4
only, no mathlib, and contains no `sorry`.

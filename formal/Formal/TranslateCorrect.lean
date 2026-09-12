/-
  Formal/TranslateCorrect.lean

  SEMANTIC PRESERVATION of the MiniLF -> IR translation: evaluating the
  translated term (under the IR semantics of Formal/Eval.lean) gives the
  same value as evaluating the source expression (under the MiniLF
  semantics of Formal/MiniLFEval.lean), in the same symbol environment.

  THE ONE SIDE CONDITION, and why it is the honest minimum: translation
  resolves let-bound names through a translation environment TEnv (of
  already-translated terms - the ctx.env mechanism of lfir.js), while
  evaluation resolves them through a value environment LEnv. The theorem
  needs those two views of the SAME binding structure to agree wherever a
  name is read, and nothing else. `Agrees env tenv lenv` states exactly
  that: at every name and sort, evaluating the term TEnv holds gives the
  value LEnv holds. It is:

    * preserved by the paired extension a letE performs on both sides
      (agrees_set), with the extension values related by the induction
      hypothesis for the bound expression - this is the whole content of
      the letE case;
    * trivially true (definitionally, per name) for the canonical initial
      pair TEnv.init / LEnv.ofEnv env, where a free name maps on both sides
      to "the symbol of that name": eval env (var n s) = env.get s n =
      (LEnv.ofEnv env).get s n. Hence the unconditional corollary
      translate_correct_init, which is what Formal/EndToEnd.lean consumes.

  WHAT IS DELIBERATELY NOT A HYPOTHESIS: closedness. Happy-path expressions
  are closed at the let level (lfir.js turns an unbound name into
  `unsupported`, and the property layer refuses those), so on the
  expressions the pipeline produces the initial environments are never
  consulted; but the theorem does not need to know that, because
  translate_correct_init holds for ALL expressions - open ones simply have
  their free names read the same symbol on both sides. One consequence a
  reviewer should note: under TEnv.init, a free let-variable named
  "this.amount" would alias the projection symbol of the same name. That
  cannot arise from lfir.js output (LF variable names never contain '.';
  the happy path has no unbound variables at all), and for closed
  expressions the aliasing is unobservable; it is a property of the chosen
  default only, not of the translation.
-/
import Formal.Term
import Formal.Eval
import Formal.MiniLF
import Formal.MiniLFEval
import Formal.Translate

namespace Formal

/--
  Agreement between a translation environment and a let-value environment,
  at a fixed symbol environment: every name, at either sort, evaluates
  (through TEnv) to the value LEnv assigns it.
-/
def Agrees (env : Env) (tenv : TEnv) (lenv : LEnv) : Prop :=
  (forall n, eval env (tenv.realT n) = lenv.realL n) /\
  (forall n, eval env (tenv.boolT n) = lenv.boolL n)

/--
  Agreement is preserved by binding the same name on both sides, to a term
  and a value that evaluate alike. This is the letE step: lfir.js extends
  ctx.env with the translated bound term; evaluation extends the value
  environment with the bound expression's value.
-/
theorem agrees_set {env : Env} {tenv : TEnv} {lenv : LEnv}
    (h : Agrees env tenv lenv) {s : Srt} (n : String)
    {tm : Term s} {v : s.denote} (hv : eval env tm = v) :
    Agrees env (tenv.set n tm) (lenv.set n v) := by
  cases s with
  | real =>
      refine ⟨fun m => ?_, h.2⟩
      show eval env (if m = n then tm else tenv.realT m)
         = (if m = n then v else lenv.realL m)
      by_cases hm : m = n
      · simp [hm, hv]
      · simp [hm, h.1 m]
  | bool =>
      refine ⟨h.1, fun m => ?_⟩
      show eval env (if m = n then tm else tenv.boolT m)
         = (if m = n then v else lenv.boolL m)
      by_cases hm : m = n
      · simp [hm, hv]
      · simp [hm, h.2 m]

/--
  PRESERVATION. For every MiniLF expression, in every symbol environment,
  and for every agreeing pair of let-environments: the IR evaluation of the
  translation equals the MiniLF evaluation of the source.

  Proof: structural induction. Literals and projections are definitional
  (for proj, both sides read env.realVar at the SAME string, because
  translate emits exactly the `${root}.${path}` name evalLF reads - the
  format is fixed once, in projName). Operators are congruence. letE
  re-establishes agreement via agrees_set, with the bound expression's own
  induction hypothesis as the evaluation fact. varL IS the agreement
  hypothesis.
-/
theorem translate_correct (env : Env) :
    {s : Srt} -> (e : MiniLF s) -> (tenv : TEnv) -> (lenv : LEnv) ->
    Agrees env tenv lenv ->
    eval env (translate tenv e) = evalLF env lenv e
  | _, .num _, _, _, _ => rfl
  | _, .boolLit _, _, _, _ => rfl
  | _, .proj _ _, _, _, _ => rfl
  | _, .addN a b, tenv, lenv, h => by
      show eval env (translate tenv a) + eval env (translate tenv b)
         = evalLF env lenv a + evalLF env lenv b
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .subN a b, tenv, lenv, h => by
      show eval env (translate tenv a) - eval env (translate tenv b)
         = evalLF env lenv a - evalLF env lenv b
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .mulN a b, tenv, lenv, h => by
      show eval env (translate tenv a) * eval env (translate tenv b)
         = evalLF env lenv a * evalLF env lenv b
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .divN a b, tenv, lenv, h => by
      show eval env (translate tenv a) / eval env (translate tenv b)
         = evalLF env lenv a / evalLF env lenv b
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .lt a b, tenv, lenv, h => by
      show decide (eval env (translate tenv a) < eval env (translate tenv b))
         = decide (evalLF env lenv a < evalLF env lenv b)
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .le a b, tenv, lenv, h => by
      show decide (eval env (translate tenv a) <= eval env (translate tenv b))
         = decide (evalLF env lenv a <= evalLF env lenv b)
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .gt a b, tenv, lenv, h => by
      show decide (eval env (translate tenv b) < eval env (translate tenv a))
         = decide (evalLF env lenv b < evalLF env lenv a)
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .ge a b, tenv, lenv, h => by
      show decide (eval env (translate tenv b) <= eval env (translate tenv a))
         = decide (evalLF env lenv b <= evalLF env lenv a)
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .eqN a b, tenv, lenv, h => by
      show decide (eval env (translate tenv a) = eval env (translate tenv b))
         = decide (evalLF env lenv a = evalLF env lenv b)
      rw [translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  -- Congruence rather than `rw`: both sides are definitionally `!` applied to
  -- the two evaluations, and rewriting under the equation compiler's motive
  -- left a goal `rfl` could not discharge.
  | _, .notB a, tenv, lenv, h =>
      congrArg (fun b => !b) (translate_correct env a tenv lenv h)
  | _, .ite c a b, tenv, lenv, h => by
      show cond (eval env (translate tenv c))
             (eval env (translate tenv a)) (eval env (translate tenv b))
         = cond (evalLF env lenv c) (evalLF env lenv a) (evalLF env lenv b)
      rw [translate_correct env c tenv lenv h,
          translate_correct env a tenv lenv h, translate_correct env b tenv lenv h]
  | _, .letE n bound body, tenv, lenv, h =>
      translate_correct env body (tenv.set n (translate tenv bound))
        (lenv.set n (evalLF env lenv bound))
        (agrees_set h n (translate_correct env bound tenv lenv h))
  | _, .varL n s, tenv, lenv, h => by
      cases s with
      | real => exact h.1 n
      | bool => exact h.2 n

/-- The canonical initial pair agrees, definitionally: a free name reads
    the symbol of that name on both sides. -/
theorem agrees_init (env : Env) : Agrees env TEnv.init (LEnv.ofEnv env) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/--
  CLOSED/DEFAULT-ENVIRONMENT COROLLARY, with no side condition: under the
  canonical initial environments, translation preserves evaluation
  outright. This is the form Formal/EndToEnd.lean composes with
  vcgen_sound; top-level guard and amount expressions are translated
  against TEnv.init exactly as lfir.js starts each choice with a ctx.env
  containing only the this/arg record aliases (which MiniLF bakes into
  proj, so the Lean initial let-env is empty of real bindings).
-/
theorem translate_correct_init (env : Env) {s : Srt} (e : MiniLF s) :
    eval env (translate TEnv.init e) = evalLF env (LEnv.ofEnv env) e :=
  translate_correct env e TEnv.init (LEnv.ofEnv env) (agrees_init env)

-- Axiom audit: see the #print axioms commands and their recorded output at
-- the bottom of Formal/EndToEnd.lean.

end Formal

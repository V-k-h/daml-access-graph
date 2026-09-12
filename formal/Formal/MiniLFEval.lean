/-
  Formal/MiniLFEval.lean

  TOTAL evaluation of MiniLF expressions, against the SAME Env used by
  Formal/Eval.lean for IR terms, plus a let-environment for bound names.

  Two environments, deliberately separate:

    * Env (from Formal/Eval.lean) interprets the SYMBOLIC INPUTS: the fields
      of the template record and of the choice argument. `proj root path`
      reads env.realVar (root.name ++ "." ++ path) - the SAME total map, at
      the SAME string, that the translated IR variable reads, because
      lfir.js's `symbol(ctx, root, path, sort)` names the variable with the
      template literal `${root}.${path}`, i.e. root, then ".", then the
      dot-joined field path. The Lean concatenation Root.name r ++ "." ++ p
      reproduces that format exactly; preservation of the projection case is
      then definitional.

    * LEnv interprets LET-BOUND NAMES (ctx.env on the JS side). It is a pair
      of TOTAL functions, one per sort, mirroring the two-map design of Env:
      total functions make evaluation total with no Option and make the
      update/lookup lemmas one-line case splits, which keeps the
      TranslateCorrect induction clean (the alternative, an association list
      with a default, adds a lookup relation for no benefit here).

  Free let-variables therefore read a default from LEnv rather than being
  errors. lfir.js maps an unbound name to `unsupported` (which the property
  layer refuses), so happy-path expressions never actually consult the
  default; the correctness theorem handles this honestly with an agreement
  hypothesis between LEnv and the translation environment
  (Formal/TranslateCorrect.lean) rather than by a closedness side condition.
-/
import Formal.Term
import Formal.Eval
import Formal.MiniLF

namespace Formal

open Std.Internal (Rat)

/-- Let-environment: one total map per sort, like Env. -/
structure LEnv where
  realL : String -> Rat
  boolL : String -> Bool

/-- Look a let-bound name up at a sort. -/
def LEnv.get (l : LEnv) : (s : Srt) -> String -> s.denote
  | .real => l.realL
  | .bool => l.boolL

/-- Bind a name at a sort (functional update; later bindings shadow). -/
def LEnv.set (l : LEnv) : {s : Srt} -> String -> s.denote -> LEnv
  | .real, n, v => { l with realL := fun m => if m = n then v else l.realL m }
  | .bool, n, v => { l with boolL := fun m => if m = n then v else l.boolL m }

/--
  The canonical let-environment derived from a symbol environment: a free
  let-variable reads the symbol of the same name at the same sort. This is
  the default the end-to-end statement uses; on closed expressions (every
  varL under its letE, which is all the happy path produces) it is never
  consulted. See TranslateCorrect.lean for why this default makes the
  env-agreement hypothesis hold definitionally.
-/
def LEnv.ofEnv (env : Env) : LEnv :=
  { realL := env.realVar, boolL := env.boolVar }

/-- The exact symbol-name format of lfir.js `symbol`: `${root}.${path}`. -/
def projName (r : Root) (path : String) : String :=
  r.name ++ "." ++ path

/--
  TOTAL evaluation of MiniLF. Each case is the standard Daml-LF reading of
  the construct it models, under the same numeric abstraction as the IR
  (exact rationals; sound here because rounding builtins are excluded from
  MiniLF and refused upstream - see MiniLF.lean):

    * literals denote themselves;
    * a projection reads the field's symbol from Env (fields of the archived
      contract and of the choice argument are the transition's inputs);
    * ADD/SUB/MUL_NUMERIC and DIV_NUMERIC are exact rational +, -, *, /,
      with Lean's total-division convention x / 0 = 0 - the same convention,
      justified the same way, as Term.divR in Formal/Eval.lean (Daml's
      DIV_NUMERIC throws on 0, and the pipeline's division-safety property
      separately proves denominators nonzero; conservation never relies on a
      value of x / 0);
    * comparisons and equality are the rational order/equality;
    * ite is Bool case analysis (cond);
    * letE evaluates the bound expression in the CURRENT environments and
      the body under the extended let-environment (call-by-value; sound for
      this pure, total fragment where call-by-name coincides);
    * varL reads the let-environment.
-/
def evalLF (env : Env) : LEnv -> {s : Srt} -> MiniLF s -> s.denote
  | _,    _, .num v            => v
  | _,    _, .boolLit v        => v
  | _,    _, .proj r p         => env.realVar (projName r p)
  | lenv, _, .addN a b         => evalLF env lenv a + evalLF env lenv b
  | lenv, _, .subN a b         => evalLF env lenv a - evalLF env lenv b
  | lenv, _, .mulN a b         => evalLF env lenv a * evalLF env lenv b
  | lenv, _, .divN a b         => evalLF env lenv a / evalLF env lenv b
  | lenv, _, .lt a b           => decide (evalLF env lenv a < evalLF env lenv b)
  | lenv, _, .le a b           => decide (evalLF env lenv a <= evalLF env lenv b)
  | lenv, _, .gt a b           => decide (evalLF env lenv b < evalLF env lenv a)
  | lenv, _, .ge a b           => decide (evalLF env lenv b <= evalLF env lenv a)
  | lenv, _, .eqN a b          => decide (evalLF env lenv a = evalLF env lenv b)
  | lenv, _, .notB a           => !(evalLF env lenv a)
  | lenv, _, .ite c a b        => cond (evalLF env lenv c) (evalLF env lenv a) (evalLF env lenv b)
  | lenv, _, .letE n bound body =>
      evalLF env (lenv.set n (evalLF env lenv bound)) body
  | lenv, _, .varL n s         => lenv.get s n

end Formal

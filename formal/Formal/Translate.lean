/-
  Formal/Translate.lean

  The MiniLF -> IR translation, structurally mirroring backend/lfir.js
  translateInner on the fragment MiniLF covers. Case by case:

    MiniLF            lfir.js action                        IR term
    ----------------  ------------------------------------  ----------------
    num v             T.num(literal string)                 Term.num v
    boolLit v         T.bool(v)                             Term.boolLit v
    proj r p          symbol(ctx, root, path, 'Real')       Term.var
                        = T.varRef(`${root}.${path}`,         (projName r p)
                          'Real')                             .real
    addN/subN/mulN    T.app('+'|'-'|'*', [a, b])            .add/.sub/.mul
    divN              T.app('/', [a, b])  (DIV_NUMERIC)     .divR
    lt/le/gt/ge       T.app('<'|'<='|'>'|'>=', [a, b])      .lt/.le/.gt/.ge
    eqN               T.app('=', [a, b])  (Real instance)   .eqR
    notB              T.app('not', [a])                     .notT
    ite c a b         T.ite(c', a', b')                     .ite
    letE n bound body ctx.env.set(n, translate(bound));     translate body
                        translate body; restore               under tenv
                                                              extended at n
    varL n s          ctx.env.get(n)                        tenv.get s n

  LET HANDLING - the design decision a reviewer should look at first.
  lfir.js does NOT emit a let construct into the IR (the IR has none): it
  resolves lets at TRANSLATION TIME, by translating the bound expression
  once and binding the resulting TERM in ctx.env; a later variable
  reference returns that term. That is substitution performed during
  translation (each occurrence of the variable becomes a copy of the bound
  term). The Lean translation mirrors it exactly: `translate` takes a
  translation environment TEnv mapping names to ALREADY-TRANSLATED terms,
  extends it at a letE, and reads it at a varL. Consequences worth noting:

    * duplication is semantic-free: the bound term is pure (this fragment
      has no effects), so evaluating a copy at each occurrence equals
      evaluating once and sharing - which is exactly what the preservation
      proof shows against evalLF's call-by-value letE;
    * shadowing: functional update of TEnv = ctx.env.set with save/restore,
      because translation of the body happens entirely under the extended
      env and nothing outside the letE can observe it;
    * unbound names: lfir.js returns `unsupported`; here TEnv is total and
      an unbound varL reads the default. TEnv.init defaults name n at sort
      s to the IR variable `var n s` - the translation is total, and the
      correctness theorem's agreement hypothesis (TranslateCorrect.lean)
      pins down what the default must denote.
-/
import Formal.Term
import Formal.Eval
import Formal.MiniLF
import Formal.MiniLFEval

namespace Formal

/-- Translation environment: a name's ALREADY-TRANSLATED term, per sort
    (the Lean counterpart of ctx.env in backend/lfir.js). -/
structure TEnv where
  realT : String -> Term .real
  boolT : String -> Term .bool

/-- Look a name up at a sort. -/
def TEnv.get (t : TEnv) : (s : Srt) -> String -> Term s
  | .real => t.realT
  | .bool => t.boolT

/-- Bind a name to a translated term (ctx.env.set with restore-on-exit,
    expressed functionally). -/
def TEnv.set (t : TEnv) : {s : Srt} -> String -> Term s -> TEnv
  | .real, n, tm => { t with realT := fun m => if m = n then tm else t.realT m }
  | .bool, n, tm => { t with boolT := fun m => if m = n then tm else t.boolT m }

/--
  The canonical initial translation environment: a free name maps to the IR
  variable of the same name and sort. Happy-path expressions are closed at
  the let level (lfir.js turns a genuinely unbound name into `unsupported`,
  which the property layer refuses), so this default is never consulted for
  them; it is chosen because it agrees with LEnv.ofEnv definitionally
  (see TranslateCorrect.lean).
-/
def TEnv.init : TEnv :=
  { realT := fun n => .var n .real, boolT := fun n => .var n .bool }

/-- The translation. Total and structural; see the table above. -/
def translate (tenv : TEnv) : {s : Srt} -> MiniLF s -> Term s
  | _, .num v            => .num v
  | _, .boolLit v        => .boolLit v
  | _, .proj r p         => .var (projName r p) .real
  | _, .addN a b         => .add (translate tenv a) (translate tenv b)
  | _, .subN a b         => .sub (translate tenv a) (translate tenv b)
  | _, .mulN a b         => .mul (translate tenv a) (translate tenv b)
  | _, .divN a b         => .divR (translate tenv a) (translate tenv b)
  | _, .lt a b           => .lt (translate tenv a) (translate tenv b)
  | _, .le a b           => .le (translate tenv a) (translate tenv b)
  | _, .gt a b           => .gt (translate tenv a) (translate tenv b)
  | _, .ge a b           => .ge (translate tenv a) (translate tenv b)
  | _, .eqN a b          => .eqR (translate tenv a) (translate tenv b)
  | _, .notB a           => .notT (translate tenv a)
  | _, .ite c a b        => .ite (translate tenv c) (translate tenv a) (translate tenv b)
  | _, .letE n bound body => translate (tenv.set n (translate tenv bound)) body
  | _, .varL n s         => tenv.get s n

end Formal

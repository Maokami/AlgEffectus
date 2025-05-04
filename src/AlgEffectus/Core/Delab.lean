import Lean
import Lean.PrettyPrinter
import AlgEffectus.Core.Syntax
import AlgEffectus.Core.Parser
import AlgEffectus.Core.Elab

namespace AlgEffectus.Core
namespace Delab

open Lean PrettyPrinter.Delaborator SubExpr Expr Elab Parser

/-!  Coercions: `effVal` / `effComp` syntax → ordinary `term` syntax.

     Lean’s delaborator framework expects each `@[delab]` function to return
     `TSyntax `term`.  Our pretty‑printer often builds `TSyntax \`effVal`
     or `TSyntax \`effComp`.  The following coercions let the type‑checker
     treat them as ordinary terms. -/
instance : Coe (TSyntax `effVal) (TSyntax `term) where
  coe := fun stx => ⟨stx.raw⟩

instance : Coe (TSyntax `effComp) (TSyntax `term) where
  coe := fun stx => ⟨stx.raw⟩

/-- Helper: convert a `String` into an `ident` token. -/
private def mkIdentFromStr (s : String) : TSyntax `ident :=
  Lean.mkIdent (Name.mkSimple s)

-- =========================================================
-- 1. `Value` delaborators
-- =========================================================

@[delab Value.varV] def delabValueVar : Delab := do
  let e ← getExpr
  let args := getAppArgs e
  guard (args.size == 1)
  let Expr.lit (.strVal n) := args[0]! | failure
  let identStx : TSyntax `effVal := ⟨mkIdentFromStr n⟩
  `(effVal| $(identStx))

@[delab Value.ttV] def delabValueTrue  : Delab := `(effVal| true)
@[delab Value.ffV] def delabValueFalse : Delab := `(effVal| false)

@[delab Value.funV] def delabValueFun : Delab := do
  let e ← getExpr
  let #[Expr.lit (.strVal x), body] := getAppArgs e | failure
  let bodyTerm ← PrettyPrinter.delab body
  let bodyStx : TSyntax `effComp := ⟨bodyTerm.raw⟩
  `(effVal| fun $(mkIdentFromStr x) ↦ $bodyStx)

@[delab Value.handV] def delabValueHand : Delab := do
  let e ← getExpr
  let #[h] := getAppArgs e | failure
  PrettyPrinter.delab h

-- =========================================================
-- 2. helper utilities for handler delaboration
-- =========================================================

/-- Extract the two data arguments from a `Prod.mk` application,
    ignoring the first two (type) arguments. -/
private def unpackProd (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (.const ``Prod.mk _) _) _) a) b => some (a, b)
  | _ => none

/-- Unpack the nested triple encoding produced in `Elab.lean` for
    an operation clause. Returns `(opName, argName, kName, bodyExpr)`. -/
private def unpackOpTuple (e : Expr) : Option (String × String × String × Expr) := do
  let (opExpr, rest₁) ← unpackProd e
  let (argExpr,  rest₂) ← unpackProd rest₁
  let (kExpr, body) ← unpackProd rest₂
  let Expr.lit (.strVal op)  := opExpr  | none
  let Expr.lit (.strVal arg)   :=  argExpr  | none
  let Expr.lit (.strVal k) := kExpr | none
  pure (op, arg, k, body)

/-- Recursively collect the head elements of a `List.cons` chain. -/
private partial def collectList (e : Expr) : Array Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (.const ``List.cons _) _) hd) tl =>
      #[hd] ++ collectList tl
  | Expr.app (.const ``List.nil _) _ => #[]
  | _ => #[]

-- =========================================================
-- 3. `Handler` delaborator
-- =========================================================

@[delab Handler.mk] def delabHandler : Delab := do
  let e ← getExpr
  let #[Expr.lit (.strVal rb), retBody, opClausesExpr] := getAppArgs e | failure
  let retBodyTerm ← PrettyPrinter.delab retBody
  let retBodyStx : TSyntax `effComp := ⟨retBodyTerm.raw⟩
  let rbIdent := mkIdentFromStr rb
  let opTuples := collectList opClausesExpr
  let clauseStxs ← opTuples.mapM fun t => do
    let some (op, arg, k, body) := unpackOpTuple t | failure
    let opId  := mkIdentFromStr op
    let argId := mkIdentFromStr arg
    let kId   := mkIdentFromStr k
    let bodyTerm ← PrettyPrinter.delab body
    let bodyStx : TSyntax `effComp := ⟨bodyTerm.raw⟩
    `(opClause| $opId ( $argId ; $kId ) ↦ $bodyStx)
  `(effVal| handler { return $rbIdent ↦ $retBodyStx$[ , $clauseStxs]* })

-- =========================================================
-- 4. `Computation` delaborators
-- =========================================================

@[delab Computation.retC] def delabCompRet : Delab := do
  let e ← getExpr
  let #[v] := getAppArgs e | failure
  let vTerm ← PrettyPrinter.delab v
  let vStx : TSyntax `effVal := ⟨vTerm.raw⟩
  `(effComp| return $vStx)

  -- `(Computation.retC $vStx)

@[delab Computation.callC] def delabCompCall : Delab := do
  let e ← getExpr
  let #[Expr.lit (.strVal op), arg, Expr.lit (.strVal k), body] := getAppArgs e | failure
  let argTerm  ← PrettyPrinter.delab arg
  let argStx   : TSyntax `effVal := ⟨argTerm.raw⟩
  let bodyTerm ← PrettyPrinter.delab body
  let bodyStx : TSyntax `effComp := ⟨bodyTerm.raw⟩
  let opLit := mkIdentFromStr op
  let kLit  := mkIdentFromStr k
  `(effComp| call $opLit ($argStx; $kLit. $bodyStx))
  --`(Computation.callC $opLit $argStx $kLit $bodyStx)

@[delab Computation.seqC] def delabCompSeq : Delab := do
  -- Extract components from `Computation.seqC x c₁ c₂`
  let e ← getExpr
  let #[Expr.lit (.strVal x), c₁, c₂] := getAppArgs e | failure
  -- Recursively delaborate the two sub‑computations
  let c₁Term ← PrettyPrinter.delab c₁
  let c₁Stx : TSyntax `effComp := ⟨c₁Term.raw⟩
  let c₂Term ← PrettyPrinter.delab c₂
  let c₂Stx : TSyntax `effComp := ⟨c₂Term.raw⟩
  -- Build concrete DSL syntax:  do x ← c₁ in c₂
  `(effComp| do $(mkIdentFromStr x) ← $c₁Stx in $c₂Stx)

@[delab Computation.ifC] def delabCompIf : Delab := do
  let e ← getExpr
  let #[cond, tBranch, eBranch] := getAppArgs e | failure
  let condTerm ← PrettyPrinter.delab cond
  let condStx : TSyntax `effVal := ⟨condTerm.raw⟩
  let tTerm    ← PrettyPrinter.delab tBranch
  let tStx : TSyntax `effComp := ⟨tTerm.raw⟩
  let eTerm    ← PrettyPrinter.delab eBranch
  let eStx : TSyntax `effComp := ⟨eTerm.raw⟩
  -- Build concrete DSL syntax:  if cond then tBranch else eBranch
  `(effComp| if $condStx then $tStx else $eStx)

@[delab Computation.appC] def delabCompApp : Delab := do
  let e ← getExpr
  let #[f, a] := getAppArgs e | failure
  -- Delaborate function and argument into `effVal` syntax
  let fTerm ← PrettyPrinter.delab f
  let aTerm ← PrettyPrinter.delab a
  let fStx : TSyntax `effVal := ⟨fTerm.raw⟩
  let aStx : TSyntax `effVal := ⟨aTerm.raw⟩
  let raw   : Syntax := mkNode ``effApp #[fStx, aStx]
  let comp : TSyntax `effComp := ⟨raw⟩
  pure comp

@[delab Computation.withC] def delabCompWith : Delab := do
  let e ← getExpr
  let #[h, c] := getAppArgs e | failure
  let hTerm ← PrettyPrinter.delab h
  let hStx : TSyntax `effVal := ⟨hTerm.raw⟩
  let cTerm ← PrettyPrinter.delab c
  let cStx : TSyntax `effComp := ⟨cTerm.raw⟩
  `(effComp| with $hStx handle $cStx)

@[delab AlgEffectus.Core.Computation] def topLevelEff : Delab := do
  let e ← getExpr
  let innerTerm ← PrettyPrinter.delab e
  let innerStx : TSyntax `effComp := ⟨innerTerm.raw⟩
  `(eff $innerStx)


#eval eff return x

#eval (Computation.seqC (.str .anonymous "y")
          (Computation.retC (Value.ttV))
          (Computation.retC (Value.varV (.str .anonymous "y"))))

def exampleComp₂ : Computation :=
  Computation.seqC (.str .anonymous "y")
    (Computation.retC (Value.ttV))
    (Computation.retC (Value.varV (.str .anonymous "y")))

end Delab
end AlgEffectus.Core

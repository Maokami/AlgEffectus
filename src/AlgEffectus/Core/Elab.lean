import Lean
import AlgEffectus.Core.Syntax
import AlgEffectus.Core.Parser

/-!
-----------------------------------------------------
# Elaborator Definition
-----------------------------------------------------
-/
namespace AlgEffectus.Core
namespace Elab

open Lean Lean.Elab AlgEffectus.Core.Parser

private def getIdentName (n : TSyntax `ident) : Expr :=
  let nameStr := n.getId.toString
  Expr.lit (Literal.strVal nameStr)

private def mkOpTuple (opName argName kName bodyExpr : Expr) : Expr := by
  -- basic constants
  let strTy  := mkConst ``String
  let compTy := mkConst ``Computation
  let prodTy := mkConst ``Prod [.zero, .zero]
  let prodMk := mkConst ``Prod.mk  [.zero, .zero]

  -- k × body : String × Computation
  let pair3 := mkApp4 prodMk strTy compTy kName bodyExpr
  -- arg × (k × body) : String × (String × Computation)
  let pair2Ty := mkApp2 prodTy strTy compTy
  let pair2   := mkApp4 prodMk strTy pair2Ty argName pair3
  -- op × (arg × (k × body))
  let pair1Ty := mkApp2 prodTy strTy pair2Ty
  exact mkApp4 prodMk strTy pair1Ty opName pair2


/-! Elaborators: Map Syntax to AST -/
mutual

partial def elabValInternal : TSyntax `effVal → TermElabM Expr
| `(effVal| $n:ident) =>
   pure (mkApp (mkConst ``Value.varV) (getIdentName n))
| `(effVal| true) => pure (mkConst ``Value.ttV)
| `(effVal| false) => pure (mkConst ``Value.ffV)
| `(effVal| fun $x:ident ↦ $c) => do
    let body ← elabCompInternal c
    pure (mkApp2 (mkConst ``Value.funV) (getIdentName x) body)
| `(effVal|
    handler { return $xRet:ident ↦ $retC:effComp
      $[ , $opArr:ident ( $argArr:ident ; $kArr:ident ) ↦ $bodyArr:effComp ]*
    }) => do
  let retBinderExpr := getIdentName xRet
  let retBodyExpr   ← elabCompInternal retC

  -- basic type aliases used throughout the tuple construction
  let strTy  := mkConst ``String
  let compTy := mkConst ``Computation
  let prodTy := mkConst ``Prod [.zero, .zero]   -- Prod type constructor

  -- nested product types
  let tyPair3 := mkApp2 prodTy strTy compTy     -- String × Computation
  let tyPair2 := mkApp2 prodTy strTy tyPair3      -- String × (String × Computation)
  let tupTy   := mkApp2 prodTy strTy tyPair2      -- final 3‑tuple type
  let mut tupExprs : Array Expr := #[]
  for i in [:opArr.size] do
    let opSyntax   := opArr[i]!
    let argSyntax  := argArr[i]!
    let kSyntax    := kArr[i]!
    let bodySyntax := bodyArr[i]!

    let opNameExpr  := getIdentName opSyntax
    let argNameExpr := getIdentName argSyntax
    let kNameExpr   := getIdentName kSyntax
    let bodyExpr    ← elabCompInternal bodySyntax

    -- build (op, arg, k, body) tuple with helper
    let tuple := mkOpTuple opNameExpr argNameExpr kNameExpr bodyExpr
    tupExprs := tupExprs.push tuple


  let nilCtor    := mkConst ``List.nil  [.zero] -- ∀ {α}, List α
  let consCtor   := mkConst ``List.cons [.zero] -- ∀ {α}, α → List α → List α
  let nilExpr    := mkApp nilCtor tupTy         -- : List tupTy

  let listExpr :=
    tupExprs.foldr
      (fun hd tl => mkApp3 consCtor tupTy hd tl)
      nilExpr

  let handlerStruct :=
    mkApp3 (mkConst ``Handler.mk)
           retBinderExpr retBodyExpr listExpr
  let handlerExpr := mkApp (mkConst ``Value.handV) handlerStruct
  pure handlerExpr
| _ => throwUnsupportedSyntax

partial def elabCompInternal : TSyntax `effComp → TermElabM Expr
| `(effComp| $v:effVal) | `(effComp| return $v:effVal) => do
  let v' ← elabValInternal v
  pure (mkApp (mkConst ``Computation.retC) v')
| `(effComp| call $op:ident ($arg:effVal; $k:ident. $c:effComp)) => do
  let arg' ← elabValInternal arg
  let c' ← elabCompInternal c
  pure (mkApp4 (mkConst ``Computation.callC) (getIdentName op) arg' (getIdentName k) c')
| `(effComp| do $x:ident ← $c₁:effComp in $c₂:effComp) => do
  let c₁' ← elabCompInternal c₁
  let c₂' ← elabCompInternal c₂
  pure (mkApp3 (mkConst ``Computation.seqC) (getIdentName x) c₁' c₂')
| `(effComp| if $cond:effVal then $c₁:effComp else $c₂:effComp) => do
  let cond' ← elabValInternal cond
  let c₁' ← elabCompInternal c₁
  let c₂' ← elabCompInternal c₂
  pure (mkApp3 (mkConst ``Computation.ifC) cond' c₁' c₂')
| `(effComp| with $h:effVal handle $c:effComp) => do
  let h' ← elabValInternal h
  let c' ← elabCompInternal c
  pure (mkApp2 (mkConst ``Computation.withC) h' c')
| `(effComp| $f:effVal @ $arg:effVal) => do
  -- throwIllFormedSyntax
  let f' ← elabValInternal f
  let arg' ← elabValInternal arg
  pure (mkApp2 (mkConst ``Computation.appC) f' arg')
| `(effComp| ($c:effComp)) => do
  let c' ← elabCompInternal c
  pure c'
| _ => throwUnsupportedSyntax
end

@[term_elab Parser.algEffParser]
def elabEff : Term.TermElab := fun stx _ => do
  let `(eff $c:effComp) := stx | throwUnsupportedSyntax
  elabCompInternal c

@[term_elab Parser.algEffBlockParser]
def elabEffBlock : Term.TermElab := fun stx _ => do
  let `(eff { $c:effComp }) := stx | throwUnsupportedSyntax
  elabCompInternal c

/-- `eff_program foo := <computation>` expands to
`def foo : AlgEffectus.Core.Computation := eff <computation>` -/
syntax (name := effProgramCmd) "eff_program " ident " := " effComp : command

macro_rules
| `(eff_program $nm:ident := $c:effComp) =>
  `(def $nm : AlgEffectus.Core.Computation := eff $c)

-- test
example := eff return true
example := eff x
example := eff true @ x
example := eff (x)
example := eff fun x ↦ return x
example := eff handler { return x ↦ false }

example := eff {
  handler { return x ↦ return x, op1(x; k) ↦ return x }
}

example := eff
  with handler { return x ↦ return x, op(x; k) ↦ return x } handle
    do x ← return true in
    do y ← call op(x; v. return v) in
    return x

eff_program demo :=
  do x ← return true in
  return x

eff_program demo2 :=
  with handler { return x ↦ return x,
                 op1(x; k) ↦ return x,
                 op2(x; k) ↦ k @ x } handle
    do x ← return true in
    do y ← call op2(a; v. return v) in
    return x

#eval demo2

end Elab
end AlgEffectus.Core

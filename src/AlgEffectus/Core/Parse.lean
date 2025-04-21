import Lean

import AlgEffectus.Core.Syntax -- Import the core syntax definitions

-- Draft: This file is a work in progress and may not be fully functional yet.

/-!
-----------------------------------------------------
# Parser Definition
-----------------------------------------------------
-/
namespace Parser

-- open Lean Parser PrettyPrinter Delaborator SubExpr Meta Elab
open Lean Elab Parser
open AlgEffectus.Core

-- Declare syntax categories for values and computations
declare_syntax_cat effVal
declare_syntax_cat effComp

-- Define the syntax for values
syntax ident : effVal
syntax "true" : effVal
syntax "false" : effVal
syntax:25 "fun " ident " ↦ " effComp : effVal
syntax "handler " "{" "return " ident " ↦ " effComp ("," ident "("ident ";" ident ")" " ↦ " effComp )* "}" : effVal
syntax:1025 "(" effVal ")" : effVal

-- Define the syntax for computations
syntax:max "return " effVal : effComp -- `return` has high precedence within its scope
syntax:65 "call " ident "(" effVal "; " ident ". " effComp ")" : effComp
syntax:40   "do " ident " ← " effComp " in " effComp : effComp
syntax:45   "if " effVal " then " effComp " else " effComp : effComp
syntax:1024  effVal:1024 effVal:(1024+1) : effComp -- Application (Value followed by atomic value)
syntax:35 "with " effVal " handle " effComp : effComp
syntax:max "(" effComp ")" : effComp

-- Bridge syntax categories to the main 'term' category for elaboration
syntax (name := effValParser) "eff " effVal : term
syntax (name := effCompParser) "eff " effComp : term

-- helper function to get the name of ident
def getIdentName (n : TSyntax `ident) : Expr :=
  let nameStr := n.getId.toString
  Expr.lit (Literal.strVal nameStr)

/-! Elaborators: Map Syntax to AST -/
mutual
@[term_elab effValParser]
def elabEffVal : Term.TermElab := fun stx _ => do
  let `(eff $val:effVal) := stx | throwUnsupportedSyntax
  let expr ← match val with
    | `(effVal| $n:ident) =>
       pure (mkApp (mkConst ``Value.varV) (getIdentName n))
    | `(effVal| true) => pure (mkConst ``Value.ttV)
    | `(effVal| false) => pure (mkConst ``Value.ffV)
    | `(effVal| fun $x:ident ↦ $c:effComp) =>throwUnsupportedSyntax
      -- let c' ← elabEffComp c
      -- return (mkApp3 (mkConst ``AlgEffectus.Core.Value.funV) x c')
    | `(effVal| handler { return $x ↦ $c, $op:ident ($y:ident; $k:ident) ↦ $c' }) => throwUnsupportedSyntax
      -- let c' ← elabEffComp c'
      -- let h ← mkApp4 (mkConst ``AlgEffectus.Core.Handler.mk) x c' op y k
      -- return h
    | _ => throwUnsupportedSyntax
  return expr

@[term_elab effCompParser]
def elabEffComp : Term.TermElab := fun stx _ => do
  let `(eff $comp:effComp) := stx | throwUnsupportedSyntax
  let expr ← match comp with
    | `(effComp| return $v:effVal) => do
      let v' ← elabEffVal v none
      pure (mkApp (mkConst ``AlgEffectus.Core.Computation.retC) v')
    | `(effComp| call $op:ident ($arg:effVal; $k:ident. $c:effComp)) =>
      let arg' ← elabEffVal arg none
      let c' ← elabEffComp c none
      pure (mkApp4 (mkConst ``AlgEffectus.Core.Computation.callC) (getIdentName op) arg' (getIdentName k) c')
    | `(effComp| do $x:ident ← $c₁:effComp in $c₂:effComp) => throwUnsupportedSyntax
      -- let c₁' ← elabEffComp c₁
      -- let c₂' ← elabEffComp c₂
      -- pure (mkApp3 (mkConst ``AlgEffectus.Core.Computation.seqC) x c₁' c₂')
    | `(effComp| if $cond:effVal then $c₁:effComp else $c₂:effComp) => throwUnsupportedSyntax
      -- let cond' ← elabEffVal cond
      -- let c₁' ← elabEffComp c₁
      -- let c₂' ← elabEffComp c₂
      -- pure (mkApp3 (mkConst ``AlgEffectus.Core.Computation.ifC) cond' c₁' c₂')
    | `(effComp| with $h:effVal handle $c:effComp) => throwUnsupportedSyntax
      -- let h' ← elabEffVal h
      -- let c' ← elabEffComp c
      -- pure (mkApp2 (mkConst ``AlgEffectus.Core.Computation.withC) h' c')
    | `(effComp| ($f:effVal) ($arg:effVal)) => throwUnsupportedSyntax
      -- let f' ← elabEffVal f
      -- let arg' ← elabEffVal arg
      -- pure (mkApp f' arg')
    | _ => throwUnsupportedSyntax

  return expr
end

example := eff true

#guard_msgs in
example := eff handler { return x ↦ return x, op(x; k) ↦ return x }

#guard_msgs in
example := eff
  with handler { return x ↦ return x, op(x; k) ↦ return x } handle
    do x ← return true in
    do y ← call op(x; v. return v) in
    return x

-- @[term_elab effValParser]
-- def elabEffVal : TermElab := fun stx _ => do
--   let expr ← match stx with
--     | `(effVal| true) => pure (mkConst ``AlgEffectus.Core.Value.ttV)
--     | `(effVal| false) => pure (mkConst ``AlgEffectus.Core.Value.ffV)
--     | _ => throwUnsupportedSyntax
--   return expr
-- @[term_elab trueEffVal]
-- def elabTrueEffVal : Term.TermElab := fun stx _ => do
--   let expr ← match stx with
--     | `(effVal| true)   => pure (Lean.mkConst ``AlgEffectus.Core.Value.ttV)
--     | _         => throwUnsupportedSyntax
--   return expr
-- @[term_elab falseEffVal]
-- def elabFalseEffVal : Term.TermElab := fun stx _ => do
--   let expr ← match stx with
--     | `(effVal| false)   => pure (Lean.mkConst ``AlgEffectus.Core.Value.ffV)
--     | _         => throwUnsupportedSyntax
--   return expr


-- tests
#eval true

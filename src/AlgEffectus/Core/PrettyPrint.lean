/-
Pretty-print support for AlgEffectus values, computations, and handlers.
-/
import Lean
import AlgEffectus.Core.Syntax
import AlgEffectus.Core.Delab

-- Note: I don't know how delaboration be used befor this simple pretty printing

open Lean Meta AlgEffectus.Core

/-! ----------------------------------------------------------------
    Helper: Convert AST nodes to core `Expr`
    (Avoids using `quote`, which requires a `Quote` instance.)
----------------------------------------------------------------- -/

mutual
private partial def valueToExpr : Value → Expr
  | .varV name     =>
      mkApp (mkConst ``Value.varV) (Expr.lit (Literal.strVal name))
  | .ttV           => mkConst ``Value.ttV
  | .ffV           => mkConst ``Value.ffV
  | .funV b c      =>
      mkApp2 (mkConst ``Value.funV)
                  (Expr.lit (Literal.strVal b))
                  (compToExpr c)
  | .handV h       =>
      mkApp (mkConst ``Value.handV) (handlerToExpr h)

/-- Convert a computation AST into `Expr`. -/
private partial def compToExpr : Computation → Expr
  | .retC v                       =>
      mkApp (mkConst ``Computation.retC) (valueToExpr v)
  | .callC op arg k b             =>
      mkApp4 (mkConst ``Computation.callC)
                  (Expr.lit (Literal.strVal op))
                  (valueToExpr arg)
                  (Expr.lit (Literal.strVal k))
                  (compToExpr b)
  | .seqC x c₁ c₂                 =>
      mkApp3 (mkConst ``Computation.seqC)
                  (Expr.lit (Literal.strVal x))
                  (compToExpr c₁)
                  (compToExpr c₂)
  | .ifC cond t e                 =>
      mkApp3 (mkConst ``Computation.ifC)
                  (valueToExpr cond)
                  (compToExpr t)
                  (compToExpr e)
  | .appC f a                     =>
      mkApp2 (mkConst ``Computation.appC)
                  (valueToExpr f)
                  (valueToExpr a)
  | .withC h c                    =>
      mkApp2 (mkConst ``Computation.withC)
                  (valueToExpr h)
                  (compToExpr c)

/-- Convert a handler AST into `Expr`. -/
private partial def handlerToExpr : Handler → Expr
  | .mk rb rc clauses             =>
      let rbLit     := Expr.lit (Literal.strVal rb)
      let rcExpr    := compToExpr rc
      let tupTy     := mkAppN (mkConst ``Prod)
        #[mkConst ``OpName, mkConst ``AlgEffectus.Core.Name, mkConst ``AlgEffectus.Core.Name, mkConst ``Computation]
      -- Encode each clause as a 4-tuple using nested Prod.mk
      let clauseExprs := clauses.map fun (op, x, k, body) =>
        let p1 := mkApp2 (mkConst ``Prod.mk)
                              (Expr.lit (Literal.strVal op))
                              (Expr.lit (Literal.strVal x))
        let p2 := mkApp2 (mkConst ``Prod.mk)
                              (Expr.lit (Literal.strVal k))
                              (compToExpr body)
        mkApp2 (mkConst ``Prod.mk) p1 p2
      let nil  := mkApp (mkConst ``List.nil) tupTy
      let cons := mkConst ``List.cons
      let listExpr := clauseExprs.foldr
          (fun hd tl => mkApp3 cons tupTy hd tl)
          nil
      mkApp3 (mkConst ``Handler.mk) rbLit rcExpr listExpr
end


/-! ----------------------------------------------------------------
     Lightweight pretty printer (pure functions, no MetaM required)
----------------------------------------------------------------- -/

mutual
  /-- Pretty-print a `Value`. Pure function, no `MetaM`. -/
  private partial def valueStr : Value → String
    | .varV n       => n
    | .ttV          => "true"
    | .ffV          => "false"
    | .funV x c     => s!"fun {x} ⇒ {compStr c}"
    | .handV h      => handlerStr h

  /-- Pretty-print a `Computation`. Pure function. -/
  private partial def compStr : Computation → String
    | .retC v               => s!"return {valueStr v}"
    | .callC op arg k c     => s!"call {op} ({valueStr arg}; {k}. {compStr c})"
    | .seqC x c₁ c₂         => s!"do {x} ← {compStr c₁} in {compStr c₂}"
    | .ifC b t e            => s!"if {valueStr b} then {compStr t} else {compStr e}"
    | .appC f a             => s!"{valueStr f} @ {valueStr a}"
    | .withC h c            => s!"with {valueStr h} handle {compStr c}"

  /-- Pretty-print a `Handler`. Pure function. -/
  private partial def handlerStr : Handler → String
    | .mk rb rbody clauses  =>
        let retPart := s!"return {rb} ⇒ {compStr rbody}"
        let opParts := clauses.map fun (op, x, k, body) =>
          s!"{op}({x}; {k}) ⇒ {compStr body}"
        s!"handler \{ {retPart}" ++ (if opParts.isEmpty then " }"
            else ", " ++ ", ".intercalate opParts ++ " }")
end

/-! ### Register `ToString` and `Repr` instances -/

instance : ToString Value       where toString := valueStr
instance : ToString Computation where toString := compStr
instance : ToString Handler     where toString := handlerStr

instance : Repr Value       where reprPrec v _ := valueStr v
instance : Repr Computation where reprPrec c _ := compStr c
instance : Repr Handler     where reprPrec h _ := handlerStr h

#eval (Computation.retC (Value.varV "x"))

#eval (Computation.seqC "y"
          (Computation.retC (Value.ttV))
          (Computation.retC (Value.varV "y")))

#eval (Value.handV
          (Handler.mk "x"
            (Computation.retC (Value.varV "y"))
            []))

#eval (Value.handV
          (Handler.mk "x"
            (Computation.retC (Value.varV "x"))
            [("op", "v", "k",
              Computation.appC (Value.varV "k") (Value.varV "v")),
              ("op2", "v2", "k2",
              Computation.appC (Value.varV "k2") (Value.varV "v2"))
              ]))

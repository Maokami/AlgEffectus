/-
Pretty-print support for AlgEffectus values, computations, and handlers.
-/
import Lean
import AlgEffectus.Core.Syntax
import AlgEffectus.Core.Delab

namespace AlgEffectus.Core
namespace PP

open Lean Meta

mutual
  /-- Pretty-print a `Value`. -/
  private partial def ppVal : Value → String
    | .varV n       => n
    | .ttV          => "true"
    | .ffV          => "false"
    | .funV x c     => s!"fun {x} ↦ {ppComp c}"
    | .handV h      => ppHandler h

  /-- Pretty-print a `Handler`. -/
  private partial def ppHandler : Handler → String
    | .mk rb rc clauses  =>
        let retPart := s!"return {rb} ↦ {ppComp rc}"
        let opParts := clauses.map fun (op, x, k, body) =>
          s!"{op}({x}; {k}) ↦ {ppComp body}"
        s!"handler \{ {retPart}" ++ (if opParts.isEmpty then " }"
            else ", " ++ ", ".intercalate opParts ++ " }")

  /-- Pretty-print a `Computation`. -/
  private partial def ppComp : Computation → String
    | .retC v               => s!"return {ppVal v}"
    | .callC op arg k c     => s!"call {op} ({ppVal arg}; {k}. {ppComp c})"
    | .seqC x c₁ c₂         => s!"do {x} ← {ppComp c₁} in {ppComp c₂}"
    | .ifC b t e            => s!"if {ppVal b} then {ppComp t} else {ppComp e}"
    | .appC f a             => s!"{ppVal f} {ppVal a}"
    | .withC h c            => s!"with {ppVal h} handle {ppComp c}"
end

/-! ### Register `Repr` instances -/

instance : Repr Computation where
  reprPrec c _ := Lean.format <| PP.ppComp c

instance : Repr Value where
  reprPrec v _ := Lean.format <| PP.ppVal v

instance : Repr Handler where
  reprPrec h _ := Lean.format <| PP.ppHandler h

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

eff_program demo2 :=
  with handler { return x ↦ return x,
                 op1(x; k) ↦ return x,
                 op2(x; k) ↦ k x } handle
    do x ← return true in
    do y ← call op2(a; v. return v) in
    return x

#eval demo2

end PP
end AlgEffectus.Core

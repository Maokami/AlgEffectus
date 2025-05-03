import AlgEffectus.Core.Syntax
import Lean.Data.RBMap
import Mathlib.Data.Finset.Basic

import Aesop
import LeanCopilot

/-!
# Core Type System for Algebraic Effects and Handlers

This module defines the core type system for algebraic effects and handlers.
-/

open scoped Finset Lean.RBMap

namespace AlgEffectus.Core

/-! ## Syntax of Types -/
mutual
  /-- Represents the type of values in the language. -/
  inductive VTy : Type
  | boolT                                   -- bool
  | funT  (A : VTy) (C : CTy)               -- A → C
  | hdlT  (C D : CTy)                       -- C ⇒ D
  deriving DecidableEq

  /-- Represents the type of computations in the language. -/
  structure CTy where
    retT  : VTy
    effs : Finset OpName
  deriving DecidableEq
end

attribute [simp] CTy.effs CTy.retT

-- Pretty notation  A !{ Δ }  for `CTy.mk A Δ`
notation:55 A " !{" Δ:55 "}" => CTy.mk A Δ

namespace CTy
  /-- Remove many operations from an effect set. -/
  def eraseMany (Δ : Finset OpName) (ops : List OpName) : Finset OpName :=
    ops.foldl (fun s op => s.erase op) Δ
end CTy

abbrev Ctx := Lean.RBMap Name VTy (compare)

namespace Ctx
  def insertMany (Γ : Ctx) (l : List (Name × VTy)) : Ctx :=
    l.foldl (fun m ⟨x, τ⟩ => Lean.RBMap.insert m x τ) Γ
end Ctx

/-- Parameter/result pair for an operation. -/
structure OpSig where
  param : VTy
  res : VTy

/-- A global signature mapping (`σ`) each `OpName` to its parameter/return types. -/
abbrev OpSigMap := Lean.RBMap OpName OpSig (compare)

/-! ## Typing judgements -/
mutual
  /-- Typing judgement for values and computations. -/
  inductive TyVal :
    (σ : OpSigMap) → (Γ : Ctx) → Value → VTy → Prop
  | var  {x A}  (hx: Γ.find? x = some A) : TyVal σ Γ (Value.varV x) A
  | tt : TyVal σ Γ Value.ttV VTy.boolT
  | ff : TyVal σ Γ Value.ffV VTy.boolT
  | funV {x A C body} (hbody : TyComp σ (Γ.insert x A) body C) : TyVal σ Γ (Value.funV x body) (VTy.funT A C)
  | hand {h C D} (th : TyHdl σ Γ h C D) : TyVal σ Γ (Value.handV h) (VTy.hdlT C D)

  /-- Handler typing (*auxiliary*, mirror of rule (Handler) in the paper). -/
  inductive TyHdl :
  (σ : OpSigMap) → (Γ : Ctx) → Handler → CTy → CTy → Prop
  | mk
      {rb   : Name} {rc : Computation}
      {opcs : List (OpName × Name × Name × Computation)}
      {A B : VTy } {Δ Δ' : Finset OpName}
      (ret : TyComp σ (Γ.insert rb A) rc (B !{Δ'}))
      (ops :
        ∀ {op x k body Aop Bop},
        (op, x, k, body) ∈ opcs →
        σ.find? op = some ⟨Aop, Bop⟩ →
        TyComp
          σ
          (Γ.insertMany
            [(x,Aop),(k, VTy.funT Bop (B !{Δ'}))]
          )
          body
          -- Maybe `A !{Δ}` instead of `B !{Δ'}`?
          (A !{Δ})
      )
      (eff :
        CTy.eraseMany Δ (opcs.map (fun t => t.fst)) ⊆ Δ'
      )
      :
      TyHdl σ Γ (Handler.mk rb rc opcs) (A !{Δ}) (B !{Δ'})

  inductive TyComp :
  (σ : OpSigMap) → (Γ : Ctx)  → Computation → CTy → Prop
  | ret   {v A Δ}        : TyVal σ Γ v A →
                             TyComp σ Γ (Computation.retC v) (A !{Δ})
  | call  {Γ op arg y body Aop Bop A Δ}
          (sig  : σ.find? op = some ⟨Aop, Bop⟩)
          (targ : TyVal σ Γ arg Aop)
          (tcont: TyComp σ (Γ.insert y Bop) body (A !{Δ}))
          (mem  : op ∈ Δ)
          : TyComp σ Γ (Computation.callC op arg y body) (A !{Δ})
  | seq   {Γ c₁ c₂ A B Δ}
          (t1 : TyComp σ Γ c₁ (A !{Δ}))
          (t2 : TyComp σ (Γ.insert "_" A) c₂ (B !{Δ}))   -- “_” dummy binder
          : TyComp σ Γ (Computation.seqC "_" c₁ c₂) (B !{Δ})
  | if_   {Γ b t e A Δ}
          (tb : TyVal σ Γ b VTy.boolT)
          (tt : TyComp σ Γ t (A !{Δ}))
          (te : TyComp σ Γ e (A !{Δ}))
          : TyComp σ Γ (Computation.ifC b t e) (A !{Δ})
  | app   {Γ f a A C}      (tf : TyVal σ Γ f (VTy.funT A C))
                            (ta : TyVal σ Γ a A)
                            : TyComp σ Γ (Computation.appC f a) C
  | with_ {Γ h c C D}      (th : TyVal σ Γ h (VTy.hdlT C D))
                            (tc : TyComp σ Γ c C)
                            : TyComp σ Γ (Computation.withC h c) D
end

end AlgEffectus.Core

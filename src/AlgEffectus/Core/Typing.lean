import AlgEffectus.Core.Syntax
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap

/-!
# Core Type System for Algebraic Effects and Handlers

This module defines the core type system for algebraic effects and handlers.
-/

open scoped Finset

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

abbrev Ctx := Finmap (fun _ : Name => VTy)

namespace Ctx
  @[simp] def insert (Γ : Ctx) (x : Name) (A : VTy) : Ctx :=
    Finmap.insert x A Γ

  @[simp] def insertMany (Γ : Ctx) (l : List (Name × VTy)) : Ctx :=
    l.foldl (fun m ⟨x, τ⟩ => Finmap.insert x τ m) Γ

  @[simp] def lookup (Γ : Ctx) (x : Name) : Option VTy :=
    Finmap.lookup x Γ
end Ctx

namespace CtxLemmas
  @[simp] lemma lookup_insert_self {Γ : Ctx} {x A} :
  (Γ.insert x A).lookup x = some A := by simp

  @[simp] lemma lookup_insert_ne {x y} {Γ : Ctx} (h : y ≠ x) :
      (Γ.insert x A).lookup y = Γ.lookup y := by simp [h]

  lemma insert_insert_of_ne {Γ : Ctx} {x y : Name} {A B: VTy} (hxy : x ≠ y) :
    (Γ.insert x A).insert y B = (Γ.insert y B).insert x A := by
    simp [Finmap.insert_insert_of_ne Γ hxy]

end CtxLemmas

/-- Parameter/result pair for an operation. -/
structure OpSig where
  param : VTy
  res : VTy

/-- A global signature  (`σ`) each `OpName` to its parameter/return types. -/
abbrev OpSigMap := Finmap (fun _ : OpName => OpSig)

/-! ## Typing judgements -/
mutual
  /-- Typing judgement for values and computations. -/
  inductive TyVal :
    (σ : OpSigMap) → (Γ : Ctx) → Value → VTy → Prop
  | var  {x A}  (hx: Γ.lookup x = some A) : TyVal σ Γ (Value.varV x) A
  | tt : TyVal σ Γ Value.ttV VTy.boolT
  | ff : TyVal σ Γ Value.ffV VTy.boolT
  | fun_ {x A C body} (hbody : TyComp σ (Γ.insert x A) body C) : TyVal σ Γ (Value.funV x body) (VTy.funT A C)
  | hand {h C D} (th : TyHdl σ Γ h C D) : TyVal σ Γ (Value.handV h) (VTy.hdlT C D)

  /-- Handler typing (*auxiliary*, mirror of rule (Handler) in the paper). -/
  inductive TyHdl :
  (σ : OpSigMap) → (Γ : Ctx) → Handler → CTy → CTy → Prop
  | mk {rb   : Name} {rc : Computation}
      {opcs : List (OpName × Name × Name × Computation)}
      {A B : VTy } {Δ Δ' : Finset OpName}
      (hkfresh : ∀ {op x k body}, (op, x, k, body) ∈ opcs → Γ.lookup k = none ∧ x ≠ k)
      (ret : TyComp σ (Γ.insert rb A) rc (B !{Δ'}))
      (ops : ∀ {op x k body Aᵢ Bᵢ}, (op, x, k, body) ∈ opcs → σ.lookup op = some ⟨Aᵢ, Bᵢ⟩ →
        TyComp σ (Γ.insertMany [(x,Aᵢ),(k, VTy.funT Bᵢ (B !{Δ'}))]) body (B !{Δ'})
      )
      (eff : CTy.eraseMany Δ (opcs.map (fun t => t.fst)) ⊆ Δ') :
      TyHdl σ Γ (Handler.mk rb rc opcs) (A !{Δ}) (B !{Δ'})

  inductive TyComp :
  (σ : OpSigMap) → (Γ : Ctx)  → Computation → CTy → Prop
  | ret   {v A Δ}        : TyVal σ Γ v A →
                             TyComp σ Γ (Computation.retC v) (A !{Δ})
  | call_ {Γ op arg y body Aᵢ Bᵢ A Δ}
          (hfresh : Γ.lookup y = none)
          (sig  : σ.lookup op = some ⟨Aᵢ, Bᵢ⟩)
          (targ : TyVal σ Γ arg Aᵢ)
          (tcont: TyComp σ (Γ.insert y Bᵢ) body (A !{Δ}))
          (mem  : op ∈ Δ)
          : TyComp σ Γ (Computation.callC op arg y body) (A !{Δ})
  | seq   {Γ x c₁ c₂ A B Δ}
          (t₁ : TyComp σ Γ c₁ (A !{Δ}))
          (t₂ : TyComp σ (Γ.insert x A) c₂ (B !{Δ}))
          : TyComp σ Γ (Computation.seqC x c₁ c₂) (B !{Δ})
  | if_   {Γ b t e A Δ}
          (tb : TyVal σ Γ b VTy.boolT)
          (tt : TyComp σ Γ t (A !{Δ}))
          (te : TyComp σ Γ e (A !{Δ}))
          : TyComp σ Γ (Computation.ifC b t e) (A !{Δ})
  | app   {Γ f a A C}
          (tf : TyVal σ Γ f (VTy.funT A C))
          (ta : TyVal σ Γ a A)
          : TyComp σ Γ (Computation.appC f a) C
  | with_ {Γ h c C D}
          (th : TyVal σ Γ h (VTy.hdlT C D))
          (tc : TyComp σ Γ c C)
          : TyComp σ Γ (Computation.withC h c) D
end

namespace Typing
scoped notation:55 σ ", " Γ " ⊢ᵥ " v " : " A => TyVal σ Γ v A
scoped notation:55 σ ", " Γ " ⊢ " c " : " C => TyComp σ Γ c C
end Typing

end AlgEffectus.Core

import AlgEffectus.Core.Parser
import AlgEffectus.Core.Semantics
import AlgEffectus.Core.Substitution
import AlgEffectus.Core.Typing
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.DHashMap.Lemmas

-- import LeanCopilot
-- import aesop

open AlgEffectus.Core
open scoped AlgEffectus.Core.Typing
open scoped AlgEffectus.Core.Semantics

open Std
lemma insert_insert_eq_override {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) (v₁ v₂ : β) :
  (m.insert k v₁).insert k v₂ = m.insert k v₂ := by
  sorry

mutual
  lemma substComp_retC_eq_retC_substValue (x : Name) (vA : Value) (v : Value) :
      substComp x vA (Computation.retC v) = Computation.retC (substValue x vA v) := by
    unfold substComp substValue StateT.run
    simp [substCompM]; rfl

  lemma subst_val_preserves
      {σ Γ x vA A v B}
      (hv : σ, Γ ⊢ᵥ vA : A)
      (hvs: σ, (Γ.insert x A) ⊢ᵥ v : B)
    : σ, Γ ⊢ᵥ (substValue x vA v) : B := by
    unfold substValue StateT.run
    cases v with
    | varV n => cases hvs with
      | var h_mem =>
        simp [substValueM] at *
        split_ifs with hnx
        · -- 1.  n = x  ----------------------------------------------------
          cases hnx
          have hAB : A = B := by
            have h': (Γ.insert x A).get? x = some A := by simp
            simp [h'] at h_mem; exact h_mem
          cases hAB; simpa using hv
        · -- 2.  n ≠ x  ----------------------------------------------------
          have hΓ : Γ.get? n = some B := by
            simp [hnx]; simp [Std.HashMap.getElem?_insert] at h_mem
            rwa [if_neg] at h_mem; tauto
          simpa using TyVal.var hΓ
    | ttV => cases hvs with
      | tt => simpa [substValueM] using TyVal.tt
    | ffV => cases hvs with
      | ff => simpa [substValueM] using TyVal.ff
    | funV x c => cases hvs with
      | fun_ hbody =>
        rename_i x' A' C
        simp [substValueM] at *
        split_ifs with hnx
        · -- 1.  x = x'  ----------------------------------------------------
          cases hnx
          split; rename_i  y result' snd' heq'
          cases heq'
          have h₁: σ, Γ ⊢ᵥ (Value.funV x' c) :  (VTy.funT A' C) := by
            apply TyVal.fun_
            have h₀: (Γ.insert x' A).insert x' A' = Γ.insert x' A' := by
              apply insert_insert_eq_override
            simp [h₀] at hbody; exact hbody
          exact h₁
        · -- 2.  x ≠ x'  ----------------------------------------------------
          rename_i h'
          cases hbody
          sorry
        · -- 3.
          sorry
    | handV h =>
      simp [substValueM] at *
      cases h with
      | mk rb rc opcls =>
        cases hvs
        sorry


        simp [substHandlerM]
        sorry


  lemma subst_comp_preserves
      {σ Γ x vA A c C}
      (hv : σ, Γ ⊢ᵥ vA : A)
      (hc : σ, (Γ.insert x A) ⊢ c : C)
    : σ, Γ ⊢ (substComp x vA c) : C := by
    cases c with
    | retC v =>
      cases hc with | ret hv_v =>
      rename_i B Δ
      admit
    | callC op arg k body =>
      admit
    | seqC x c₁ c₂ => admit
    | ifC b t e => admit
    | appC f a => admit
    | withC h c => admit

  lemma subst_hdl_preserves
      {σ Γ x vA A h C D}
      (hv : σ, Γ ⊢ᵥ vA : A)
      (hh : TyHdl σ (Γ.insert x A) h C D)
    : TyHdl σ Γ (substHandler x vA h) C D
    := by admit
end

theorem preservation {σ Γ c c' C} :
  (σ, Γ ⊢ c : C) → (c ⤳ c') → (σ, Γ ⊢ c' : C)
:= by
  intro hTy hStep
  induction hStep generalizing C with
  | seq_step h₁ ih  =>
    rename_i x c₁ c₁' c₂
    cases hTy with | seq t₁ t₂ =>
      rename_i A B Δ
      have hTy₁' : σ, Γ ⊢ c₁' : (A !{Δ}) := by
        apply ih; exact t₁
      have hTy₂' : σ, Γ.insert x A ⊢ c₂ : (B !{Δ}) := by
        exact t₂
      apply TyComp.seq hTy₁' hTy₂'
  | seq_return =>
    rename_i x v c₁
    cases hTy with | seq t₁ t₂ =>
      rename_i A B Δ
      cases t₁ with | ret t₁' =>
        exact subst_comp_preserves t₁' t₂
  | seq_op     => admit
  | if_true    => admit
  | if_false   => admit
  | app_β      => admit
  | with_step  => admit
  | with_ret   => admit
  | with_handled   => admit
  | with_unhandled => admit

theorem progress {σ c A Δ} :
  (σ, ∅ ⊢ c : (A !{Δ})) →
  (∃ v, c = Computation.retC v) ∨
  (∃ op v k cBody, c = Computation.callC op v k cBody ∧ op ∈ Δ) ∨
  (∃ c', c ⤳ c')
:= by
  intro hTy
  cases hTy with
  | ret hVal        => admit
  | call_ sig targ tcont mem => admit
  | seq t1 t2       => admit
  | app tf ta       => admit
  | if_ tb tt te    => admit
  | with_ th tc     => admit

-- mutual
--   lemma weaken_val {σ Γ x A v B} (hv : σ, Γ ⊢ᵥ v : B) :
--     σ, (Γ.insert x A) ⊢ᵥ v : B := by
--     cases hv with
--     | var h_mem =>
--       rename_i n; apply TyVal.var
--       simp [Std.HashMap.getElem?_insert]
--       simp at h_mem
--       by_cases h_eq_keys : x = n
--       · rw [← h_eq_keys] at h_mem
--         sorry
--       · split <;> simp_all
--     | tt => exact TyVal.tt
--     | ff => exact TyVal.ff
--     | fun_ hbody =>
--       rename_i x' A' C body; apply TyVal.fun_
--       by_cases h_eq_keys : x = x'
--       · sorry
--       · sorry
--       rw [hΓ]; apply weaken_comp; exact hbody
--     | hand h =>
--       admit
--
--
--   lemma weaken_comp
--       {σ Γ x A c C}
--       (hc : TyComp σ Γ c C) :
--       TyComp σ (Γ.insert x A) c C := by admit
--
--   lemma weaken_hdl {σ Γ x A h C D} (hh : TyHdl σ Γ h C D) :
--     TyHdl σ (Γ.insert x A) h C D := by
--     cases hh with
--     | mk hret hops heff =>
--       rename_i rb rc opcs A' B' Δ Δ'
--       apply TyHdl.mk
--       repeat admit
-- end

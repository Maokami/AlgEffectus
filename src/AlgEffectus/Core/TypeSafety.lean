import AlgEffectus.Core.Parser
import AlgEffectus.Core.Semantics
import AlgEffectus.Core.Substitution
import AlgEffectus.Core.Typing

-- import LeanCopilot
import aesop

open AlgEffectus.Core
open scoped AlgEffectus.Core.Typing
open scoped AlgEffectus.Core.Semantics

open Std
mutual
  lemma weaken_val {σ Γ x A v B}
    (hfresh : Γ.lookup x = none ∨ Γ.lookup x = some A)
    (hv : σ, Γ ⊢ᵥ v : B) :
    σ, Γ.insert x A ⊢ᵥ v : B := by
    cases hv with
    | var h_mem =>
      rename_i n; apply TyVal.var
      -- split hfresh
      cases hfresh with
      | inl h_none => admit
      | inr h_some => admit
    | tt => exact TyVal.tt
    | ff => exact TyVal.ff
    | fun_ hbody =>
      rename_i x' A' C body; apply TyVal.fun_
      -- split hfresh
      cases hfresh with
      | inl h_none => admit
      | inr h_some => admit
    | hand h =>
      simp [StateT.run] at *
      cases h with
      | mk rb rc opcls =>
      cases hfresh with
      | inl h_none => admit
      | inr h_some => admit

  lemma weaken_comp {σ Γ x A c C}
    (hfresh : Γ.lookup x = none ∨ Γ.lookup x = some A)
    (hc : σ, Γ ⊢ c : C) :
    σ, Γ.insert x A ⊢ c : C := by
    admit

  lemma weaken_hdl {σ Γ x A h C D}
    (hfresh : Γ.lookup x = none ∨ Γ.lookup x = some A)
    (hh : TyHdl σ Γ h C D) :
    TyHdl σ (Γ.insert x A) h C D := by
    admit
end

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
        · -- 1.  n = x
          cases hnx
          have hAB : A = B := by simpa using h_mem
          cases hAB; simpa using hv
        · -- 2.  n ≠ x
          have hΓ : Γ.lookup n = some B := by
            rw [← h_mem]; simp [hnx]
          simpa using TyVal.var hΓ
    | ttV => cases hvs with
      | tt => simpa [substValueM] using TyVal.tt
    | ffV => cases hvs with
      | ff => simpa [substValueM] using TyVal.ff
    | funV x c => cases hvs with | fun_ hbody =>
      rename_i x' A' C
      simp [substValueM] at *
      split_ifs with hnx hxf
      · -- 1.  x = x'
        cases hnx
        split; rename_i  y result' snd' heq'
        cases heq'
        apply TyVal.fun_; simp at hbody; exact hbody
      · -- 2.  x ≠ x' ∧ x ∈ freeVarsValue vA
        apply TyVal.fun_
        simp [substCompM]
        cases hbody
        repeat sorry
      · -- 3. x ≠ x' ∧ x ∉ freeVarsValue vA
        apply TyVal.fun_
        simp [substCompM]
        cases hbody
        repeat sorry
    | handV h =>
      simp [substValueM] at *
      cases h with
      | mk rb rc opcls =>
        cases hvs
        rename_i C D th
        simp [substValueM] at *
        split_ifs with hrbx
        · admit
        · admit

lemma subst_valM_preserves
  {σ Γ x vA A v B ctx}
  (hv : σ, Γ ⊢ᵥ vA : A)
  (hvs: σ, (Γ.insert x A) ⊢ᵥ v : B)
  : σ, Γ ⊢ᵥ (substValueM x vA v ctx).1 : B := by
  admit

lemma subst_compM_preserves
  {σ Γ x vA A c C ctx}
  (hv : σ, Γ ⊢ᵥ vA : A)
  (hc : σ, (Γ.insert x A) ⊢ c : C) :
  σ, Γ ⊢ (substCompM x vA c ctx).1 : C := by
  revert ctx
  cases c with
  | retC v =>
    intro ctx
    cases hc with | ret hv_v =>
    rename_i B Δ
    simp [substCompM]
    apply TyComp.ret
    apply subst_valM_preserves hv hv_v

  | callC op arg k body =>
    intro ctx
    cases hc with | call_ hfresh sig targ tcont mem =>
    rename_i Aᵢ Bᵢ A' Δ
    simp [substCompM]
    split_ifs with hkx
    · -- 1. k = x
      cases hkx; simp at hfresh
    · -- 2. k ≠ x
      have h₁ : σ, Γ ⊢ᵥ (substValueM x vA arg ctx).1 : Aᵢ := by apply subst_valM_preserves hv targ
      have hfresh': Γ.lookup k = none := by
        simpa [hkx] using hfresh
      have hv' : σ, Γ.insert k Bᵢ ⊢ᵥ vA : A := by
        exact weaken_val (Or.inl hfresh') hv
      have tcont' : σ, (Γ.insert k Bᵢ).insert x A ⊢ body : A' !{Δ} := by
        rw [CtxLemmas.insert_insert_of_ne hkx]; exact tcont
      have hbody' : σ, Γ.insert k Bᵢ ⊢
      (substCompM x vA body (substValueM x vA arg ctx).2).1 : A' !{Δ} := by
        exact subst_compM_preserves hv' tcont'
      exact TyComp.call_ hfresh' sig h₁ hbody' mem
  | seqC x c₁ c₂ => admit
  | ifC b t e => admit
  | appC f a => admit
  | withC h c => admit

  lemma subst_comp_preserves
      {σ Γ x vA A c C}
      (hv : σ, Γ ⊢ᵥ vA : A)
      (hc : σ, (Γ.insert x A) ⊢ c : C)
    : σ, Γ ⊢ (substComp x vA c) : C := by
    cases c with
    | retC v =>
      cases hc with | ret hv_v =>
      rename_i B Δ
      simp [substComp]
      apply TyComp.ret
      apply subst_val_preserves hv hv_v
    | callC op arg k body =>
      cases hc with | call_ hfresh sig targ tcont mem =>
      rename_i Aᵢ Bᵢ A' Δ
      simp [substComp]
      split_ifs with hkx
      · -- 1. k = x
        cases hkx; simp at hfresh
      · -- 2. k ≠ x
        have h₁ : σ, Γ ⊢ᵥ (substValue x vA arg) : Aᵢ := by apply subst_val_preserves hv targ
        have hfresh': Γ.lookup k = none := by
          simpa [hkx] using hfresh
        apply TyComp.call_ hfresh' sig h₁
        · simp [StateT.run]
          apply weaken_comp (Or.inl hfresh')
          · admit
        · exact mem
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

theorem preservation {σ Γ c c' C}
  (hTy: σ, Γ ⊢ c : C)
  (hStep: c ⤳ c')
: σ, Γ ⊢ c' : C
:= by
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
  | seq_op     =>
    rename_i op x v y c₁ c₂ hxy
    cases hTy with | seq t₁ t₂ =>
      rename_i A B Δ
      cases t₁ with | call_ hfresh sig targ tcont mem =>
      rename_i Aᵢ Bᵢ
      have tcont' : σ, Γ.insert y Bᵢ ⊢ Computation.seqC x c₁ c₂ : B !{Δ} := by
        apply TyComp.seq tcont
        have hyx : y ≠ x := Ne.symm hxy
        rw [CtxLemmas.insert_insert_of_ne hyx]
        apply weaken_comp
        · rw [CtxLemmas.lookup_insert_ne hyx]; rw [hfresh]; simp
        · exact t₂
      exact TyComp.call_ hfresh sig targ tcont' mem
  | if_true  =>
    rename_i c₁' c₂'
    cases hTy with | if_ tb tt te => exact tt
  | if_false   =>
    rename_i c₁' c₂'
    cases hTy with | if_ tb tt te => exact te
  | app_β      =>
    rename_i x c₁' v
    cases hTy with | app tf ta =>
      apply subst_comp_preserves ta
      cases tf with | fun_ hbody => exact hbody
  | with_step hStep ih =>
    rename_i h c₁' c₂'
    cases hTy with | with_ th tc =>
      rename_i C'
      apply TyComp.with_ th; exact ih tc
  | with_ret hyRet  =>
    rename_i h c₁
    cases hTy with | with_ th tc =>
      rename_i x c_ret C'
      admit
  | with_handled hySucc => admit
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

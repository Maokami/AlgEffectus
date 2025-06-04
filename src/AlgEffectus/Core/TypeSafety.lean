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

/--
If `op` is a member of the effect set `Δ` **and** does **not** occur in the
list of handled operations `ops`, then it is still a member of
`CTy.eraseMany Δ ops`.  We will use this fact to show that an un‑handled
operation persists after the erasure passes performed by a handler.
-/
lemma mem_eraseMany_of_mem
    {Δ : Finset OpName} {ops : List OpName} {op : OpName}
    (hΔ   : op ∈ Δ)
    (hnot : op ∉ ops) :
    op ∈ CTy.eraseMany Δ ops := by
  induction ops with
  | nil => simpa [CTy.eraseMany] using hΔ
  | cons hd tl ih =>
      have hnot_tl : op ∉ tl := by
        intro h_in; exact hnot (List.mem_cons_of_mem _ h_in)
      have ih' := ih hnot_tl
      by_cases hop : op = hd
      · rw [← hop]
        simp [CTy.eraseMany] at *
        exact (False.elim (hnot.left hop))
      · admit
        -- have h_mem_in_Δ_erase : op ∈ (Δ.erase hd) := by
        --   have : op ∈ Δ ∧ op ≠ hd := ⟨hΔ, hop⟩
        --   simpa [Finset.mem_erase] using this
        -- have h_rec :
        --     op ∈ CTy.eraseMany (Δ.erase hd) tl :=
        --   mem_eraseMany_of_mem h_mem_in_Δ_erase hnot_tl
        -- -- Now rewrite the goal and finish with `simpa`.
        -- simpa [CTy.eraseMany, hop] using h_rec

end

mutual
  lemma substComp_retC_eq_retC_substValue (x : Name) (vA : Value) (v : Value) :
      substComp x vA (Computation.retC v) = Computation.retC (substValue x vA v) := by
    unfold substComp substValue StateT.run
    simp [substCompM]; rfl

  lemma subst_valM_preserves
    {σ Γ x vA A v B ctx}
    (hv : σ, Γ ⊢ᵥ vA : A)
    (hvs: σ, (Γ.insert x A) ⊢ᵥ v : B)
    : σ, Γ ⊢ᵥ (substValueM x vA v ctx).1 : B := by
  -- unfold substValue StateT.run
  -- cases v with
  -- | varV n => cases hvs with
  --   | var h_mem =>
  --     simp [substValueM] at *
  --     split_ifs with hnx
  --     · -- 1.  n = x
  --       cases hnx
  --       have hAB : A = B := by simpa using h_mem
  --       cases hAB; simpa using hv
  --     · -- 2.  n ≠ x
  --       have hΓ : Γ.lookup n = some B := by
  --         rw [← h_mem]; simp [hnx]
  --       simpa using TyVal.var hΓ
  -- | ttV => cases hvs with
  --   | tt => simpa [substValueM] using TyVal.tt
  -- | ffV => cases hvs with
  --   | ff => simpa [substValueM] using TyVal.ff
  -- | funV x c => cases hvs with | fun_ hbody =>
  --   rename_i x' A' C
  --   simp [substValueM] at *
  --   split_ifs with hnx hxf
  --   · -- 1.  x = x'
  --     cases hnx
  --     split; rename_i  y result' snd' heq'
  --     cases heq'
  --     apply TyVal.fun_; simp at hbody; exact hbody
  --   · -- 2.  x ≠ x' ∧ x ∈ freeVarsValue vA
  --     apply TyVal.fun_
  --     simp [substCompM]
  --     cases hbody
  --     repeat sorry
  --   · -- 3. x ≠ x' ∧ x ∉ freeVarsValue vA
  --     apply TyVal.fun_
  --     simp [substCompM]
  --     cases hbody
  --     repeat sorry
  -- | handV h =>
  --   simp [substValueM] at *
  --   cases h with
  --   | mk rb rc opcls =>
  --     cases hvs
  --     rename_i C D th
  --     simp [substValueM] at *
  --     split_ifs with hrbx
  --     · admit
  --     · admit

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

  lemma subst_hdlM_preserves
      {σ Γ x vA A h C D}
      (hv : σ, Γ ⊢ᵥ vA : A)
      (hh : TyHdl σ (Γ.insert x A) h C D)
    : TyHdl σ Γ (substHandler x vA h) C D := by
    admit
end

lemma subst_val_preserves
    {σ Γ x vA A v B}
    (hv : σ, Γ ⊢ᵥ vA : A)
    (hvs: σ, (Γ.insert x A) ⊢ᵥ v : B)
  : σ, Γ ⊢ᵥ (substValue x vA v) : B := by
  exact subst_valM_preserves hv hvs
lemma subst_comp_preserves
    {σ Γ x vA A c C}
    (hv : σ, Γ ⊢ᵥ vA : A)
    (hc : σ, (Γ.insert x A) ⊢ c : C)
  : σ, Γ ⊢ (substComp x vA c) : C := by
  exact subst_compM_preserves hv hc

lemma subst_hdl_preserves
    {σ Γ x vA A h C D}
    (hv : σ, Γ ⊢ᵥ vA : A)
    (hh : TyHdl σ (Γ.insert x A) h C D)
  : TyHdl σ Γ (substHandler x vA h) C D := by
  exact subst_hdlM_preserves hv hh

theorem preservation {σ Γ c c' C}
  (hTy: σ, Γ ⊢ c : C)
  (hStep: c ⤳ c')
: σ, Γ ⊢ c' : C := by
  induction hStep generalizing C with
  | seq_step h₁ ih  =>
    rename_i x _ c₁' c₂
    cases hTy with | seq t₁ t₂ =>
    rename_i A B Δ
    have hTy₁' : σ, Γ ⊢ c₁' : (A !{Δ}) := by apply ih; exact t₁
    have hTy₂' : σ, Γ.insert x A ⊢ c₂ : (B !{Δ}) := by exact t₂
    apply TyComp.seq hTy₁' hTy₂'
  | seq_return =>
    cases hTy with | seq t₁ t₂ =>
    cases t₁ with | ret t₁' =>
    exact subst_comp_preserves t₁' t₂
  | seq_op     =>
    rename_i _ x _ y c₁ c₂ hxy
    cases hTy with | seq t₁ t₂ =>
    rename_i _ B Δ
    cases t₁ with | call_ hfresh sig targ tcont mem =>
    rename_i _ Bᵢ
    have tcont' : σ, Γ.insert y Bᵢ ⊢ Computation.seqC x c₁ c₂ : B !{Δ} := by
      apply TyComp.seq tcont
      have hyx : y ≠ x := Ne.symm hxy
      rw [CtxLemmas.insert_insert_of_ne hyx]
      apply weaken_comp
      · rw [CtxLemmas.lookup_insert_ne hyx]; rw [hfresh]; simp
      · exact t₂
    exact TyComp.call_ hfresh sig targ tcont' mem
  | if_true    => cases hTy with | if_ tb tt te => exact tt
  | if_false   => cases hTy with | if_ tb tt te => exact te
  | app_β      =>
    cases hTy with | app tf ta =>
    apply subst_comp_preserves ta
    cases tf with | fun_ hbody => exact hbody
  | with_step hStep ih =>
    cases hTy with | with_ th tc =>
    apply TyComp.with_ th; exact ih tc
  | with_ret hyRet  =>
    cases hTy with | with_ th tc =>
    cases tc with | ret hv_c₁ =>
    cases th with | hand hh =>
    cases hh with | mk _ rest _ _ =>
    simp [Handler.getRetClause] at hyRet
    rw [← hyRet.right]; rw [hyRet.left] at rest
    unfold substComp StateT.run
    exact subst_compM_preserves hv_c₁ rest
  | with_handled hySucc =>
    rename_i h opName v x y k cᵢ cBody
    cases hTy with | with_ th tc =>
    rename_i CParam
    cases th with | hand hh =>
    cases tc with | call_ hfresh sig targ tcont mem =>
    rename_i Aᵢ Bᵢ A' Δ
    cases hh with | mk hkfresh ret hops heff =>
    rename_i rb rc opcs B Δ'
    simp [Handler.findOpClause] at hySucc
    have hh : TyHdl σ Γ (Handler.mk rb rc opcs) (A' !{Δ}) (B !{Δ'}) := by
      exact TyHdl.mk hkfresh ret hops heff
    have th₀ : σ, Γ ⊢ᵥ Value.handV (Handler.mk rb rc opcs) : VTy.hdlT (A' !{Δ}) (B !{Δ'}) :=
      TyVal.hand hh
    rcases hySucc with ⟨currOp, h_eq⟩
    unfold substComp StateT.run
    have th₁ : σ, Γ.insert y Bᵢ ⊢ᵥ Value.handV (Handler.mk rb rc opcs)
        : VTy.hdlT (A' !{Δ}) (B !{Δ'}) := by
      exact weaken_val (Or.inl hfresh) th₀
    have th₂ : σ, Γ.insert k (Bᵢ.funT (B !{Δ'})) ⊢ᵥ v : Aᵢ := by
      apply weaken_val; apply Or.inl; exact (hkfresh (List.mem_of_find?_eq_some h_eq)).1; exact targ
    have h_x_neq_k : x ≠ k := (hkfresh (List.mem_of_find?_eq_some h_eq)).2
    have th₃ : σ, (Γ.insert k (Bᵢ.funT (B !{Δ'}))).insert x Aᵢ ⊢ cᵢ : B !{Δ'} := by admit
      -- have h_hops := hops (List.mem_of_find?_eq_some h_eq) sig
      -- rw [Finmap.insert_comm x Aᵢ k (Bᵢ.funT (B !{Δ'})) h_x_neq_k]
      -- exact h_hops
    exact subst_compM_preserves (TyVal.fun_ (TyComp.with_ (TyVal.hand (weaken_hdl (Or.inl hfresh) hh)) tcont))
      (subst_comp_preserves th₂ th₃)
  | with_unhandled hyFail =>
    rename_i h opName v y cBody
    cases hTy with | with_ th tc =>
    rename_i CParam
    cases th with | hand hh =>
    cases tc with | call_ hfresh sig targ tcont mem =>
    rename_i Aᵢ Bᵢ A' Δ
    cases hh with | mk hkfresh ret hops heff =>
    rename_i rb rc opcs B Δ'
    simp [Handler.findOpClause] at hyFail
    have hh : TyHdl σ Γ (Handler.mk rb rc opcs) (A' !{Δ}) (B !{Δ'}) := by
      exact TyHdl.mk hkfresh ret hops heff
    have th₀ : σ, Γ ⊢ᵥ Value.handV (Handler.mk rb rc opcs)
        : VTy.hdlT (A' !{Δ}) (B !{Δ'}) := TyVal.hand hh
    have th' : σ, Γ.insert y Bᵢ ⊢ᵥ Value.handV (Handler.mk rb rc opcs)
        : VTy.hdlT (A' !{Δ}) (B !{Δ'}) :=
      weaken_val (Or.inl hfresh) th₀
    have tcont' : σ, Γ.insert y Bᵢ ⊢
        Computation.withC (Value.handV (Handler.mk rb rc opcs)) cBody
        : B !{Δ'} := by
      exact TyComp.with_ th' tcont
    have mem' : opName ∈ Δ' := by
      have hnot : opName ∉ List.map (fun t => t.1) opcs := by
        intro h_in
        rcases List.mem_map.1 h_in with
          ⟨⟨op' , x' , k' , body'⟩, h_mem, h_eq⟩
        have hneq := hyFail op' x' k' body' h_mem
        exact (hneq (by simpa [h_eq]))
      have hmemErase : opName ∈ CTy.eraseMany Δ (List.map (fun t => t.1) opcs) :=
        mem_eraseMany_of_mem mem hnot
      exact heff hmemErase
    exact TyComp.call_ hfresh sig targ tcont' mem'

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

import AlgEffectus.Core.Syntax

-- import LeanCopilot
import aesop

open AlgEffectus.Core

mutual
  def renameValue (old new : Name) : Value → Value
  | v@(Value.varV n)  => if n = old then Value.varV new else v
  | Value.funV x body =>
    let (x', body') :=
      if x = old then (x, body) else (x, renameComp old new body)
    Value.funV x' body'
  | Value.handV h    => Value.handV (renameHandler old new h)
  | v                => v

  termination_by
    v => sizeOfValue v
  decreasing_by
    repeat dsimp [sizeOfValue]; simp

  def renameHandler (old new : Name) : Handler → Handler
  | Handler.mk rb rc opcs =>
    let rb' := rb
    let rc' := if rb = old then rc else renameComp old new rc
    let opcs' := opcs.map fun opcl =>
      let (op,x,k,c) := opcl
      -- When proving termination, changing `opcl.snd.snd.snd` to `c` causes issues.
      let c' := if x = old ∨ k = old then c else renameComp old new opcl.snd.snd.snd
      (op, x, k, c')

    Handler.mk rb' rc' opcs'

  termination_by
    h => sizeOfHandler h
  decreasing_by
    repeat dsimp [sizeOfComp, sizeOfHandler]; simp +arith
    rename_i h_mem
    have h₁ : sizeOfComp opcl.snd.snd.snd ≤ sizeOfOpClauses opcs := by
      induction h_mem with
      | head _ => dsimp [sizeOfOpClauses]; simp
      | tail _ _ ih₁=>
        simp [sizeOfOpClauses, Nat.le_trans ih₁]
    apply Nat.le_trans h₁; simp +arith

  def renameComp (old new : Name) : Computation → Computation
  | Computation.retC v              => Computation.retC (renameValue old new v)
  | Computation.callC op arg k body =>
    let arg' := renameValue old new arg
    let body' := if k = old then body else renameComp old new body
    Computation.callC op arg' k body'
  | Computation.seqC x c1 c2        =>
    let c1' := renameComp old new c1
    let c2' := if x = old then c2 else renameComp old new c2
    Computation.seqC x c1' c2'
  | Computation.ifC b t e           =>
    Computation.ifC (renameValue old new b)
                    (renameComp old new t)
                    (renameComp old new e)
  | Computation.appC f a            =>
    Computation.appC (renameValue old new f) (renameValue old new a)
  | Computation.withC h c           =>
    Computation.withC (renameValue old new h) (renameComp old new c)

  termination_by
    c => sizeOfComp c
  decreasing_by
    repeat dsimp [sizeOfComp, sizeOfValue]; simp +arith
end

mutual
@[simp] theorem sizeOfValue_renameValue
    (old new : Name) (v : Value) :
    sizeOfValue (renameValue old new v) = sizeOfValue v := by
  cases v with
  | varV n        => simp [renameValue, sizeOfValue]; split <;> rfl
  | ttV           => simp [renameValue, sizeOfValue]
  | ffV           => simp [renameValue, sizeOfValue]
  | funV x body   =>
      by_cases h : x = old
      <;> simp [renameValue, sizeOfValue, h, sizeOfComp_renameComp]
  | handV h       =>
      simp [renameValue, sizeOfValue, sizeOfHandler_renameHandler]

  termination_by sizeOfValue v
  decreasing_by repeat sorry

@[simp] theorem sizeOfOpClauses_rename
    (old new : Name) (opcs : List (OpName × Name × Name × Computation)) :
    sizeOfOpClauses
      (opcs.map fun (op,x,k,c) =>
        let c' := if x = old ∨ k = old then c else renameComp old new c
        (op,x,k,c')) = sizeOfOpClauses opcs := by
    induction opcs with
    | nil       => simp [sizeOfOpClauses]
    | cons hd tl ih =>
        rcases hd with ⟨op,x,k,c⟩
        by_cases h' : (x = old ∨ k = old)
        <;> simp [sizeOfOpClauses, h', renameComp, ih, sizeOfComp_renameComp]

  termination_by sizeOfOpClauses opcs
  decreasing_by sorry

@[simp] theorem sizeOfHandler_renameHandler
    (old new : Name) (h : Handler) :
    sizeOfHandler (renameHandler old new h) = sizeOfHandler h := by
  cases h with
  | mk rb rc opcs =>
      simp [renameHandler, sizeOfHandler, sizeOfOpClauses_rename]
      split <;> simp [sizeOfComp_renameComp]

  termination_by sizeOfHandler h
  decreasing_by repeat sorry

@[simp] theorem sizeOfComp_renameComp
    (old new : Name) (c : Computation) :
    sizeOfComp (renameComp old new c) = sizeOfComp c := by
  cases c with
  | retC v => simp [renameComp, sizeOfComp, sizeOfValue_renameValue]
  | callC op arg k body =>
      simp [renameComp, sizeOfComp, sizeOfValue_renameValue]
      split <;> simp [sizeOfComp_renameComp]
  | seqC x c₁ c₂ =>
      simp [renameComp, sizeOfComp]
      split <;> simp [sizeOfComp_renameComp]
  | ifC b t e => simp [sizeOfComp_renameComp]
  | appC f a => simp [renameComp, sizeOfComp, sizeOfValue_renameValue]
  | withC h c =>
    simp [renameComp, sizeOfComp, sizeOfValue_renameValue, sizeOfComp_renameComp]

  termination_by sizeOfComp c
  decreasing_by repeat sorry
end

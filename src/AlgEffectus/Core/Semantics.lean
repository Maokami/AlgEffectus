import AlgEffectus.Core.Syntax
import AlgEffectus.Core.Substitution

import AlgEffectus.Core.Delab
import AlgEffectus.Core.PrettyPrint
/-!
# Core Semantics for Algebraic Effects and Handlers

This module defines the small-step operational semantics (`⤳`) for the language.
It uses an inductive predicate `Step` to define the reduction relation.

-/

namespace AlgEffectus.Core

/-! ## Small-Step Operational Semantics (`⤳`) -/

/--
The small-step operational semantics relation `c ⤳ c'`, defined as an inductive predicate.
-/

inductive Step : Computation → Computation → Prop where
  /-- Rule (Seq-S): `do x ← c₁ in c₂ ⤳ do x ← c₁' in c₂` if `c₁ ⤳ c₁'`.
      Steps inside the first computation of a do-block. -/
  | seq_step {x c₁ c₁' c₂} (hyStep : Step c₁ c₁') :
    Step (Computation.seqC x c₁ c₂)
         (Computation.seqC x c₁' c₂)

  /-- Rule (Seq-R): `do x ← return v in c ⤳ c[v/x]`.
      Substitutes the returned value into the continuation. -/
  | seq_return {x v c} :
    Step (Computation.seqC x (Computation.retC v) c)
         (substComp x v c)

  /-- Rule (Seq-O): `do x ← call op(v; y. c₁) in c₂ ⤳ call op(v ; y. do x ← c₁ in c₂)`.
      Propagates an operation out of a do-block. -/
  | seq_op {op x v y c₁ c₂} :
    Step (Computation.seqC x (Computation.callC op v y c₁) c₂)
         (Computation.callC op v y (Computation.seqC x c₁ c₂))

  /-- Rule (If-T): `if true then c₁ else c₂ ⤳ c₁`.
       Evaluate the then branch of an if statement. -/
  | if_true {c₁ c₂} :
    Step (Computation.ifC Value.ttV c₁ c₂)
         c₁

  /-- Rule (If-F): `if false then c₁ else c₂ ⤳ c₂`.
       Evaluate the else branch of an if statement. -/
  | if_false {c₁ c₂} :
    Step (Computation.ifC Value.ffV c₁ c₂)
         c₂

  /-- Rule (App-R): `(fun x ↦ c) v ⤳ c[v/x]`.
      This is also called "β-reduction". -/
  | app_β {x c v} :
    Step (Computation.appC (Value.funV x c) v)
         (substComp x v c)

  -- In the following rules, we set h = handler {return x ↦ cᵣ, op₁ (x; k) ↦ c₁, . . . , opₙ(x; k) ↦ cₙ}

  /-- Rule (With-S): `with h handle c ⤳ with h handle c'` if `c ⤳ c'`.
      Steps inside the computation being handled. -/
  | with_step {h c c'} (hyStep : Step c c') :
    Step (Computation.withC h c)
         (Computation.withC h c')

  /-- Rule (With-R): `with h handle return v ⤳ cᵣ[v/x]`.
      Substitutes the returned value into the return clause of the handler. -/
  | with_ret {x c_ret h v} (hyRet : h.getRetClause = (x, c_ret)) :
    Step (Computation.withC (Value.handV h) (Computation.retC v))
         (substComp x v c_ret)

  /-- Rule (With-H):
      `with h handle call opᵢ(v; y. c) ⤳ cᵢ[v/x][(fun y ↦ with h handle c)/k]`.
      Handles a specific operation `opᵢ` using the corresponding clause `cᵢ` from the handler `h`.
      The operation's argument `v` substitutes the parameter `x` in the handler clause `cᵢ`. The original operation's continuation `y. c`, wrapped again by the handler `h`, substitutes the continuation parameter `k` in the handler clause `cᵢ`.  -/
  | with_handled
  {h op v x y k cᵢ c} (hySucc : h.findOpClause op = some (x, k, cᵢ)) :
    Step
      (Computation.withC (Value.handV h) (Computation.callC op v y c))
      (substComp k (Value.funV y (Computation.withC (Value.handV h) c))
                 (substComp x v cᵢ))

  /-- Rule (With-U):
    `with h handle op(v; y. c) ⤳ call op(v; y. with h handle c)` if `op ∉ {op₁, . . . , opₙ}`.
   -/
  | with_unhandled {h opName v y c} (hyFail : h.findOpClause opName = none) :
    Step (Computation.withC (Value.handV h) (Computation.callC opName v y c))
         (Computation.callC opName v y (Computation.withC (Value.handV h) c))

/--
Multi-step reduction (`⤳*`), the reflexive transitive closure of `Step`.
-/
inductive Reduces : Computation → Computation → Prop where
  | refl (c : Computation) : Reduces c c
  | step {c₁ c₂ c₃} (h₁ : Step c₁ c₂) (h₂ : Reduces c₂ c₃) : Reduces c₁ c₃

/-- `step?` returns `some c'` if `c` can step to `c'`, otherwise it returns `none`.  -/
def step? (c : Computation) : Option Computation :=
match c with
    -- Return values are irreducible
  | Computation.retC _ => none -- Return values are irreducible
    -- Sequential binding (`do x ← c₁ in c₂`)
  | Computation.seqC x c₁ c₂ =>
    -- Try to step within the first computation (Rule seq_step)
    match step? c₁ with
    | some c₁' => some (Computation.seqC x c₁' c₂)
    | none =>
      -- If c₁ cannot step, check if it's a return or call
      match c₁ with
      | Computation.retC v => some (substComp x v c₂) -- Rule seq_return
      | Computation.callC op arg y kBody => -- Rule seq_op
          some (Computation.callC op arg y (Computation.seqC x kBody c₂))
      | _ => none -- c₁ is irreducible but not return/call, so seqC is stuck here

  -- Conditional (`if cond then c₁ else c₂`)
  | Computation.ifC cond t e =>
    match cond with
    | Value.ttV => some t -- Rule if_true
    | Value.ffV => some e -- Rule if_false
    | _ => none -- Condition must be a concrete boolean value

  -- Application (`f v`)
  | Computation.appC f arg =>
    match f with
    | Value.funV x body => some (substComp x arg body) -- Rule app_β
    | _ => none -- Cannot apply non-function value

  -- Handler Application (`with hVal handle comp`)
  | Computation.withC hVal comp =>
    -- Try to step within comp (Rule with_step)
    match step? comp with
    | some comp' => some (Computation.withC hVal comp')
    | none =>
      match hVal with
         -- If hVal is a handler, check if comp can step
        | Value.handV h =>
          -- If comp cannot step, check if it's a return or call
          match comp with
          | Computation.retC v => -- Rule with_ret
            let (retBinder, retBody) := h.getRetClause
            some (substComp retBinder v retBody)
          | Computation.callC op arg y kBody =>
            -- Check if the handler defines this operation
            match h.findOpClause op with
            | some (x, k, cᵢ) => -- Rule with_handled
              let kVal := Value.funV y (Computation.withC hVal kBody)
              some (substComp k kVal (substComp x arg cᵢ))
            | none => -- Rule with_unhandled
              some (Computation.callC op arg y (Computation.withC hVal kBody))
          | _ => none -- comp is irreducible but not return/call, so withC is stuck here
        | _ => none -- hVal is not a handler, so withC is stuck here

  -- Plain operation calls outside a handler/seq context are stuck
  | Computation.callC .. => none

namespace Semantics
-- Notation for single step reduction
scoped infixl:50 " ⤳ " => Step
-- Notation for multi-step reduction
scoped infixl:50 " ⤳* " => Reduces
end Semantics

/-! ## Soundness and Completeness of the Small-Step Semantics -/

/-- The soundness theorem states that if `c` can step to `c'`, then `step? c` returns `some c'`. -/
theorem soundness : ∀ {c c'}, Step c c' → step? c = some c' := by
  intro c c' hStep
  cases hStep with
  | seq_step hyStep => simp [step?]; rw [soundness hyStep]
  | seq_return => simp [step?]
  | seq_op => simp [step?]
  | if_true => simp [step?]
  | if_false => simp [step?]
  | app_β => simp [step?]
  | with_step hyStep => simp [step?, soundness hyStep]
  | with_ret hyRet => simp at hyRet; simp [step?, hyRet]
  | with_handled hySucc => simp [step?, hySucc]
  | with_unhandled hyFail => simp [step?, hyFail]

/-- The completeness theorem states that if `step? c` returns `some c'`, then `c` can step to `c'`. -/
theorem completeness : ∀ {c c'}, step? c = some c' → Step c c' := by
  intro c c' hStep
  cases c with
  | retC _ => simp [step?] at hStep;
  | seqC x c₁ c₂ =>
    simp [step?] at hStep;
    cases h₁': step? c₁ with
    | some c₁' =>
      simp [h₁'] at hStep; subst hStep; exact Step.seq_step (completeness h₁')
    | none =>
      simp [h₁'] at hStep
      cases c₁ with
      | retC v => simp at hStep; subst hStep; exact Step.seq_return
      | callC op arg y kBody => simp at hStep; subst hStep; exact Step.seq_op
      | _ => contradiction
  | ifC cond t e =>
    simp [step?] at hStep
    cases cond with
    | ttV => simp at hStep; subst hStep; exact Step.if_true
    | ffV => simp at hStep; subst hStep; exact Step.if_false
    | _ => contradiction
  | appC f arg =>
    simp [step?] at hStep
    cases f with
    | funV x body =>
      simp at hStep
      subst hStep
      exact Step.app_β
    | _ => contradiction
  | withC hVal comp =>
    simp [step?] at hStep
    cases h₁': step? comp with
    | some comp' =>
      simp [h₁'] at hStep; subst hStep; exact Step.with_step (completeness h₁')
    | none =>
      simp [h₁'] at hStep
      cases hVal with
      | handV h =>
        simp at hStep
        cases comp with
        | retC v =>
          simp at hStep
          cases h with
          | mk rb rc opcs => subst hStep; simp [Step.with_ret]
        | callC op arg y kBody =>
          simp at hStep
          match r: h.findOpClause op with
          | some (x, k, cᵢ) =>
            simp [r] at hStep; subst hStep; exact Step.with_handled r
          | none =>
            simp [r] at hStep; subst hStep; exact Step.with_unhandled r
        | _ => contradiction
      | _ => contradiction
  | callC _ _ _ _ => simp [step?] at hStep

/-- The equivalence theorem states that `c ⤳ c'` if and only if `step? c = some c'`. -/
theorem step_equivalence : ∀ {c c'}, Step c c' ↔ step? c = some c' := by
  intro c c'
  constructor
  · intro mp
    exact soundness mp
  · intro mpr
    exact completeness mpr

/--  interp runs recursively the small-step semantics to a fixpoint. -/
partial def interp (c : Computation) : Computation :=
  match step? c with
  | some c' => interp c'
  | none    => c

eff_program demo := if true then return x else return y

eff_program demo2 :=
  with handler { return x ↦ return true,
                 op1(x; k) ↦ return false,
                 read(x; k) ↦ k @ Bob } handle
    do x ← call read(a; v. fun v ↦ return v) in
    return x

#eval demo2
#eval! (step? demo2).get!
#eval! (step? (step? demo2).get!).get!
-- Examples of evaluation
#eval interp demo
#eval interp demo2

end AlgEffectus.Core

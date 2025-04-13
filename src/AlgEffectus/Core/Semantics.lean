import AlgEffectus.Core.Syntax

/-!
# Core Semantics for Algebraic Effects and Handlers

This module defines the small-step operational semantics (`⤳`) for the language.
It uses an inductive predicate `Step` to define the reduction relation.

-/

namespace AlgEffectus.Core

mutual
  /--
  Substitution v[v'/x] for values.
  Replaces free occurrences of targetVar with replacement value.
  Needs proper handling of variable capture. (Simplified here)
  -/
  partial def substValue (targetVar : Name) (replacement : Value) : Value → Value
    | v@(Value.varV name) =>
      if name == targetVar then replacement else v
    | v@(Value.ttV) | v@(Value.ffV) => v
    | v@(Value.funV binder body) =>
      -- If binder matches targetVar, it shadows it; stop substitution in the body.
      -- NOTE: Proper impl requires checking free vars in replacement and alpha-renaming binder if collision occurs.
      if binder == targetVar then v
      else
        -- Assuming replacement doesn't capture binder. Recurse.
        Value.funV binder (substComp targetVar replacement body)
    | Value.handV handler =>
      -- Substitute inside the handler definition itself.
      Value.handV (substHandler targetVar replacement handler)

  partial def substHandler (targetVar : Name) (replacement : Value) : Handler → Handler
    | Handler.mk retBinder retBody opClauses =>
      -- Substitute in the return body, avoiding capture by retBinder
      let retBody' :=
        if retBinder == targetVar then
          retBody
        else
          substComp targetVar replacement retBody
      -- Substitute in each operation clause
      let opClauses' := opClauses.map fun (op, contBinder, argBinderVal, handlerBody) =>
        -- Substitute in the argument binder value (pattern)
        let argBinderVal' := substValue targetVar replacement argBinderVal
        -- Substitute in the handler body, avoiding capture by contBinder and the argBinder (if it's a var)
        let handlerBody' :=
          let shadowedByCont := contBinder == targetVar
          -- Check if the argument binder *pattern* itself introduces shadowing
          -- TODO : If `argBinderVal` is always a function, the `shadowedByArg` check is unnecessary.
          let shadowedByArg := match Value.getBinderName? argBinderVal with
                               | some argName => argName == targetVar
                               | none => false -- If argBinderVal isn't a simple var, assume no shadowing for simplicity
          if shadowedByCont || shadowedByArg then
            handlerBody
          else
            substComp targetVar replacement handlerBody
        (op, contBinder, argBinderVal', handlerBody')
      Handler.mk retBinder retBody' opClauses'

  partial def substComp (targetVar : Name) (replacement : Value) : Computation → Computation
    | Computation.retC v => Computation.retC (substValue targetVar replacement v)
    | Computation.callC opName param res cont =>
      -- Substitute in the parameter of the operation call
      -- TODO : This may be wrong.
      Computation.callC opName param res (substComp targetVar replacement cont)
      -- Note: If the original callC with continuation `k` and `c` was used, substitute there too, respecting `k` binder.
    | Computation.seqC binder bound cont =>
      -- Substitute in the bound computation first
      let bound' := substComp targetVar replacement bound
      -- Substitute in the continuation, avoiding capture by the binder
      -- NOTE: Proper impl requires alpha-renaming binder if it conflicts with free vars in replacement.
      if binder == targetVar then
        Computation.seqC binder bound' cont
      else
        Computation.seqC binder bound' (substComp targetVar replacement cont)
    | Computation.ifC cond thenBranch elseBranch =>
      Computation.ifC (substValue targetVar replacement cond)
                      (substComp targetVar replacement thenBranch)
                      (substComp targetVar replacement elseBranch)
    | Computation.appC func arg =>
      Computation.appC (substValue targetVar replacement func)
                       (substValue targetVar replacement arg)
    | Computation.withC handlerComp comp =>
      -- Substitute in the handler value AND in the computation being handled
      Computation.withC (substValue targetVar replacement handlerComp)
                        (substComp targetVar replacement comp)
end

/-! ## Small-Step Operational Semantics (`⤳`) -/

mutual
/--
The small-step operational semantics relation `c ⤳ c'`, defined as an inductive predicate.
-/

  inductive Step : Computation → Computation → Prop where
    /-- Rule (Seq-S): `do x ← c₁ in c₂ ⤳ do x ← c₁' in c₂` if `c₁ ⤳ c₁'`.
        Steps inside the first computation of a do-block. -/
    | seq_step {x c₁ c₁' c₂} {hy_step : Step c₁ c₁'} :
        Step (Computation.seqC x c₁ c₂)
             (Computation.seqC x c₁' c₂)

    /-- Rule (Seq-R): `do x ← return v in c ⤳ c[v/x]`.
        Substitutes the returned value into the continuation. -/
    | seq_return {x v c} :
        Step (Computation.seqC x (Computation.retC v) c)
             (substComp x v c)

    /-- Rule (Seq-O): `do x ← op(v; y. c₁) in c₂ ⤳ op(v ; y. do x ← c₁ in c₂)`.
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
    | with_step {h c c'} {hy_step : Step c c'} :
        Step (Computation.withC h c)
             (Computation.withC h c')

    /-- Rule (With-R): `with h handle return v ⤳ cᵣ[v/x]`.
        Substitutes the returned value into the return clause of the handler. -/
    | with_ret {x c_ret h v} {hy_ret : h.getRetClause = (x, c_ret)} :
        Step (Computation.withC (Value.handV h) (Computation.retC v))
             (substComp x v c_ret)

    /-- Rule (With-H):
        `with h handle opᵢ(v; y. c) ⤳ cᵢ[v/x][(fun y ↦ with h handle c)/k]`.
        Handles a specific operation `opᵢ` using the corresponding clause `cᵢ` from the handler `h`.
        The operation's argument `v` substitutes the parameter `x` in the handler clause `cᵢ`. The original operation's continuation `y. c`, wrapped again by the handler `h`, substitutes the continuation parameter `k` in the handler clause `cᵢ`.  -/
    | with_handled {h opName v x k cᵢ} {hy_succ : h.findOpClause opName = some (x, k, cᵢ)} :
        -- TODO : This is wrong. We need to substitute the continuation `k` in `cᵢ` with `fun y ↦ with h handle c`.
        Step (Computation.withC (Value.handV h) (Computation.callC opName v y cᵢ))
             (substComp x v cᵢ)

    /-- Rule (With-U):
      `with h handle op(v; y. c) ⤳ op(v; y. with h handle c)` if `op ∉ {op₁, . . . , opₙ}`.
     -/
    | with_unhandled {h opName v y c} {hy_fail : h.findOpClause opName = none} :
        Step (Computation.withC (Value.handV h) (Computation.callC opName v y c))
             (Computation.callC opName v y (Computation.withC (Value.handV h) c))

  /--
  Multi-step reduction (`⤳*`), the reflexive transitive closure of `Step`.
  -/
  inductive Reduces : Computation → Computation → Prop where
    | refl (c : Computation) : Reduces c c
    | step {c₁ c₂ c₃} (h₁ : Step c₁ c₂) (h₂ : Reduces c₂ c₃) : Reduces c₁ c₃

end

-- Notation for single step reduction
infixl:50 " ⤳ " => Step
-- Notation for multi-step reduction
infixl:50 " ⤳* " => Reduces

end AlgEffectus.Core

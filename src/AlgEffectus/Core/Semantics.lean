import AlgEffectus.Core.Syntax
import AlgEffectus.Core.Substitution

/-!
# Core Semantics for Algebraic Effects and Handlers

This module defines the small-step operational semantics (`⤳`) for the language.
It uses an inductive predicate `Step` to define the reduction relation.

-/

namespace AlgEffectus.Core

/-! ## Small-Step Operational Semantics (`⤳`) -/

mutual
/--
The small-step operational semantics relation `c ⤳ c'`, defined as an inductive predicate.
-/

  inductive Step : Computation → Computation → Prop where
    /-- Rule (Seq-S): `do x ← c₁ in c₂ ⤳ do x ← c₁' in c₂` if `c₁ ⤳ c₁'`.
        Steps inside the first computation of a do-block. -/
    | seq_step {x c₁ c₁' c₂} {hyStep : Step c₁ c₁'} :
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
    | with_step {h c c'} {hyStep : Step c c'} :
        Step (Computation.withC h c)
             (Computation.withC h c')

    /-- Rule (With-R): `with h handle return v ⤳ cᵣ[v/x]`.
        Substitutes the returned value into the return clause of the handler. -/
    | with_ret {x c_ret h v} {hyRet : h.getRetClause = (x, c_ret)} :
        Step (Computation.withC (Value.handV h) (Computation.retC v))
             (substComp x v c_ret)

    /-- Rule (With-H):
        `with h handle opᵢ(v; y. c) ⤳ cᵢ[v/x][(fun y ↦ with h handle c)/k]`.
        Handles a specific operation `opᵢ` using the corresponding clause `cᵢ` from the handler `h`.
        The operation's argument `v` substitutes the parameter `x` in the handler clause `cᵢ`. The original operation's continuation `y. c`, wrapped again by the handler `h`, substitutes the continuation parameter `k` in the handler clause `cᵢ`.  -/
    | with_handled
    {h op v x y k cᵢ c} {hySucc : h.findOpClause op = some (x, k, cᵢ)} :
        Step
          (Computation.withC (Value.handV h) (Computation.callC op v y c))
          (substComp k (Value.funV y (Computation.withC (Value.handV h) c))
                     (substComp x v cᵢ))

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

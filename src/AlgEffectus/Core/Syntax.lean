import Lean

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic

open Classical
open Lean

/-!
# Core Syntax for Algebraic Effects and Handlers

This module defines the abstract syntax for values, computations, and handlers
-/

namespace AlgEffectus.Core

/-- Type alias for variable names. -/
abbrev Name := Lean.Name

/-- Type alias for operation names. -/
abbrev OpName := Lean.Name

mutual
  /--
  Represents values `v` in the language.
  Values can be variables, boolean values, function abstractions, or handlers.
  -/
  inductive Value : Type where
    -- Variable `x`
    | varV (name : Name)
    -- boolean values(`true`, `false`)
    | ttV  | ffV : Value
    -- Abstraction `fun x => c`
    | funV (binder : Name) (body : Computation)
    -- Handler `h`
    | handV (handler : Handler)
    deriving Repr, Inhabited -- For printing, default instance

  /--
  Represents handlers `h`.
  Handlers define custom interpretations for effects (operations) and specify
  how to handle the final result of a computation.
  -/
  inductive Handler : Type where
    -- Handler structure: `{ return x => c_ret, op₁ x₁ k => c₁, ..., opₘ xₘ k => cₘ }`
    -- `opClauses` stores tuples of: (operation_name, continuation_binder, argument_binder, handler_body)
    | mk (retBinder : Name) (retBody : Computation)
         (opClauses : List (OpName × Name × Name × Computation))
    deriving Repr -- For printing

  /--
  Represents computations `c` in the language.
  Computations can be value returns, operation calls, sequential bindings, conditionals, function applications,
  and handler applications.
  -/
  inductive Computation : Type where
    -- Return a value: `return v`
    | retC (val : Value)
    -- Call an operation: `call op(v; y. c)`
    | callC (op : OpName) (arg : Value) (kBinder : Name) (kBody : Computation)
    -- Sequential binding: `do x ← c₁ in c₂`
    | seqC  (binder : Name) (bound : Computation) (cont : Computation)
    -- Conditional: `if b then c₁ else c₂`
    | ifC   (cond : Value) (thenBranch elseBranch : Computation)
    -- Function application: `f(x)`
    | appC  (func arg : Value)
    -- Handler application with a handler: `with h handle c`
    | withC (handler : Value) (comp : Computation)
    deriving Repr, Inhabited -- For printing, default instance
end

instance : Inhabited Handler where
  default := Handler.mk (Name.mkStr1 "") (Computation.retC (Value.ttV)) []

/-! Helper functions for syntax manipulation -/
mutual
  /-- Calculates the size of a list of operation clauses. -/
  def sizeOfOpClauses : List (OpName × Name × Name × Computation) → Nat
    | [] => 0
    | (_,_,_,b)::rest => sizeOfComp b + sizeOfOpClauses rest

  /-- Calculates the size of a value. -/
  def sizeOfValue : Value → Nat
    | Value.varV _ => 1
    | Value.ttV => 1
    | Value.ffV => 1
    | Value.funV _ body => 1 + sizeOfComp body
    | Value.handV h => 1 + sizeOfHandler h

  /-- Calculates the size of a handler. -/
  def sizeOfHandler : Handler → Nat
    | Handler.mk _ rc opcs => 1 + sizeOfComp rc + sizeOfOpClauses opcs

  /-- Calculates the size of a computation. -/
  def sizeOfComp : Computation → Nat
    | Computation.retC v => 1 + sizeOfValue v
    | Computation.callC _ arg _ body => 1 + sizeOfValue arg + sizeOfComp body
    | Computation.seqC _ c1 c2 => 1 + sizeOfComp c1 + sizeOfComp c2
    | Computation.ifC b t e => 1 + sizeOfValue b + sizeOfComp t + sizeOfComp e
    | Computation.appC f a => 1 + sizeOfValue f + sizeOfValue a
    | Computation.withC h c => 1 + sizeOfValue h + sizeOfComp c
end

/-
Helpers: every `sizeOf…` measure is a natural number, hence
trivially non‑negative.  We register these facts with `[simp]`
so that `simp` (and therefore `simp_wf`) can use them automatically.
-/
@[simp] theorem sizeOfOpClauses_nonneg
    (opcs : List (OpName × Name × Name × Computation)) :
    (0 : Nat) ≤ sizeOfOpClauses opcs := by
  exact Nat.zero_le _

@[simp] theorem sizeOfValue_nonneg (v : Value) :
    (0 : Nat) ≤ sizeOfValue v := by
  exact Nat.zero_le _

@[simp] theorem sizeOfHandler_nonneg (h : Handler) :
    (0 : Nat) ≤ sizeOfHandler h := by
  exact Nat.zero_le _

@[simp] theorem sizeOfComp_nonneg (c : Computation) :
    (0 : Nat) ≤ sizeOfComp c := by
  exact Nat.zero_le _

@[simp] theorem sizeOfComp_le_sizeOfOpClauses
    {opcs : List (OpName × Name × Name × Computation)}
    {op x k c}
    (h : (op, x, k, c) ∈ opcs) :
    sizeOfComp c ≤ sizeOfOpClauses opcs := by
  induction h with
  | head _ => dsimp [sizeOfOpClauses]; simp
  | tail _ _ ih₁=>
    simp [sizeOfOpClauses, Nat.le_trans ih₁]

/-- Extract the binder name if the Value is a simple variable -/
def Value.getBinderName? : Value → Option Name
  | Value.varV name => some name
  | _               => none

/-- Retrieves the return clause (binder and body) from a handler. -/
@[simp]
def Handler.getRetClause : Handler → (Name × Computation)
  | Handler.mk rb rc _ => (rb, rc)

/-- Retrieves the list of operation clauses from a handler. -/
@[simp]
def Handler.getOpClauses : Handler → List (OpName × Name × Name × Computation)
  | Handler.mk _ _ opc => opc

/-- Finds the corresponding operation clause in a handler given an operation name. -/
def Handler.findOpClause (h : Handler) (opName : OpName) : Option (Name × Name × Computation) :=
  h.getOpClauses.find? (fun (op, _, _, _) => op == opName) -- Find clause by op name
  |>.map (fun (_, x, k, body) => (x, k, body)) -- Extract (continuation_binder, arg_binder, body)

/-- Checks if a computation is a value (specifically, `return v`). -/
def Computation.isValue : Computation → Bool
  | Computation.retC _ => true
  | _                  => false

/-- Thread a `NameGenerator` together with the set of names to avoid. -/
structure AlphaCtx where
  gen   : Lean.NameGenerator
  avoid : Finset Name
deriving Inhabited

namespace AlphaCtx

/--
Helper lemma: Shows that `Lean.Name.mkNum p n` is injective with respect to `n`
for a fixed prefix `p`.
-/
theorem name_num_inj_on_num (p : Name) :
  Function.Injective (fun n : Nat => Name.mkNum p n) := by

  intros n₁ n₂ h_str
  have h_name : Name.mkNum p n₁ = Name.mkNum p n₂ := by
    simp [Name, Name.mkNum] at h_str
    simp [h_str]

  --    `Name.num.injEq : Name.num p n₁ = Name.num p n₂ → (p = p ∧ n₁ = n₂)`
  simp [Name.mkNum] at h_name
  exact h_name

theorem exists_steps_to_fresh_nat (prefix_ : Name) (startIdx : Nat) (avoidSet : Finset Name) :
  ∃ (steps : Nat), prefix_.mkNum (startIdx + steps) ∉ avoidSet := by
  -- 1. Assume the negation of the goal for a proof by contradiction.
  by_contra h_neg

  -- `push_neg` simplifies the negation to a more usable form:
  push_neg at h_neg

  -- 2. Define the function `S` that generates the name.
  let S := fun (steps : Nat) => prefix_.mkNum (startIdx + steps)

  -- The hypothesis `h_neg` can be rewritten using `S`.
  have h_all_S_in_avoidSet : ∀ steps, S steps ∈ avoidSet := h_neg

  -- 3. Prove that `S` is an injective function.
  have h_S_inj : Function.Injective S := by
    intros steps₁ steps₂ h_S_eq_S -- Assume S steps₁ = S steps₂
    dsimp [S, Name.mkNum] at h_S_eq_S
    apply Nat.add_left_cancel
    apply name_num_inj_on_num prefix_
    exact h_S_eq_S

  -- 4. Use the Pigeonhole Principle for the contradiction.
  -- Let N be the number of elements in `avoidSet`.
  let N := avoidSet.card

  -- Consider the first `N + 1` `steps` values: `0, 1, ..., N`.
  let fin_domain_steps := Finset.range (N + 1) -- This is the set {0, 1, ..., N}

  -- -- Generate the set of names corresponding to these `steps`.
  let generated_finset := Finset.image S fin_domain_steps

  -- Since `S` is injective, the `N + 1` distinct `steps` values map to `N + 1` distinct names.
  -- So, the cardinality of `generated_finset` is `N + 1`.
  have h_card_generated : Finset.card generated_finset = N + 1 := by
    simp [generated_finset]
    -- goal : (Finset.image S fin_domain_steps).card = N + 1
    simp_all [S, generated_finset, fin_domain_steps, N, Finset.card_image_of_injective]


  -- According to `h_all_S_in_avoidSet`, all names in `generated_finset` must be in `avoidSet`.
  -- This means `generated_finset` is a subset of `avoidSet.toFinset`.
  have h_subset_avoidSet : generated_finset ⊆ avoidSet := by
    intro s hs_mem_generated -- Assume s ∈ generated_finset
    rw [Finset.mem_image] at hs_mem_generated
    rcases hs_mem_generated with ⟨steps, h_steps_in_domain, h_s_eq_S_steps⟩
    rw [←h_s_eq_S_steps]; simp [h_all_S_in_avoidSet steps]

  -- The cardinality of a subset is less than or equal to the cardinality of the superset.
  -- So, `Finset.card generated_finset ≤ Finset.card avoidSet.toFinset`.
  have h_card_le := Finset.card_le_card h_subset_avoidSet

  -- Substitute the known cardinalities:
  -- `N + 1 ≤ N` (since `avoidSet.toFinset.card` is `avoidSet.size` which is `N`).
  rw [h_card_generated] at h_card_le

  have h_length_avoidSet : avoidSet.card = N := by
    simp [N]
  simp [h_length_avoidSet, Nat.not_succ_le_self] at h_card_le

/--
Defines the number of steps needed to find a fresh name.
This is the smallest `s ≥ 0` such that `ngen.namePrefix.mkNum (ngen.idx + s)`
is not in `avoidSet'`.
The existence of such `s` is guaranteed by `exists_steps_to_fresh_nat`.
-/
noncomputable def stepsToFreshNat (prefix_ : Name) (startIdx : Nat) (avoidSet' : Finset Name) : Nat :=
  Nat.find (exists_steps_to_fresh_nat prefix_ startIdx avoidSet')

theorem stepsToFreshNat_spec (prefix_ : Name) (startIdx : Nat) (avoidSet' : Finset Name) :
  prefix_.mkNum (startIdx + stepsToFreshNat prefix_ startIdx avoidSet') ∉ avoidSet' :=
  Nat.find_spec (exists_steps_to_fresh_nat prefix_ startIdx avoidSet')

theorem stepsToFreshNat_is_min (prefix_ : Name) (startIdx : Nat) (avoidSet' : Finset Name)
  (s : Nat) (h_s_fresh : prefix_.mkNum (startIdx + s) ∉ avoidSet') :
  stepsToFreshNat prefix_ startIdx avoidSet' ≤ s :=
  Nat.find_min' (exists_steps_to_fresh_nat prefix_ startIdx avoidSet') h_s_fresh

theorem stepsToFreshNat_is_min_contra (prefix_ : Name) (startIdx : Nat) (avoidSet' : Finset Name)
  (k : Nat) (h_k_lt_steps : k < stepsToFreshNat prefix_ startIdx avoidSet') :
  prefix_.mkNum (startIdx + k) ∈ avoidSet' :=
  of_not_not (Nat.find_min (exists_steps_to_fresh_nat prefix_ startIdx avoidSet') h_k_lt_steps)

theorem stepsToFreshNat_pos_of_mem {p : Name} {i : Nat} {avoidSet' : Finset Name}
  (hmem : p.mkNum i ∈ avoidSet') : 0 < stepsToFreshNat p i avoidSet' := by
  simp [stepsToFreshNat]
  exact hmem

def fresh (nameToMakeFreshAgainst : Name) (ctx : AlphaCtx) : Name × AlphaCtx :=
  -- Helper recursive function to find a fresh name.
  -- It takes the current NameGenerator and returns a pair:
  -- the found fresh name and the NameGenerator state that produced it.
  let effectiveAvoidSet := insert nameToMakeFreshAgainst ctx.avoid

  let rec findFresh (ngen : Lean.NameGenerator) : Name × Lean.NameGenerator :=
    let nameCandidate := ngen.curr

    if nameCandidate ∈ effectiveAvoidSet then
      -- If it is, try the next name from the generator
      findFresh ngen.next
    else
      -- If it's not 'nameToMakeFreshAgainst' and not in `avoid`, we found our fresh name.
      -- Return the name and the generator state that produced it.
      (nameCandidate, ngen)

    termination_by stepsToFreshNat ngen.namePrefix ngen.idx effectiveAvoidSet
    decreasing_by 
       -- Simplify definitions like ngen.curr, ngen.next
      simp [Lean.NameGenerator.next]

      -- Let s_curr be the current measure
      let s_curr := stepsToFreshNat ngen.namePrefix ngen.idx effectiveAvoidSet
      -- Let s_next be the next measure (for the recursive call)
      let s_next := stepsToFreshNat ngen.namePrefix (ngen.idx + 1) effectiveAvoidSet

      -- Prove s_curr > 0
      have h_s_curr_pos : 0 < s_curr := by
        rename_i h'
        dsimp [s_curr, nameCandidate] at h'
        exact stepsToFreshNat_pos_of_mem h'  


      -- Get the defining property of s_curr
      have h_s_curr_is_fresh_idx : ngen.namePrefix.mkNum (ngen.idx + s_curr) ∉ effectiveAvoidSet := by
        exact stepsToFreshNat_spec ngen.namePrefix ngen.idx effectiveAvoidSet

      have h_arith (h_s_curr_pos : 0 < s_curr): ngen.idx + 1 + (s_curr - 1) = ngen.idx + s_curr := by
        have h': 1 ≤ s_curr := by
          simp_all [nameCandidate, s_curr]
          exact h_s_curr_pos
        rw [← Nat.add_sub_assoc h']
        simp

      -- Rewrite this property in terms of the starting index for s_next
      have h_prop_for_s_next (h_s_curr_pos: 0 < s_curr):
        ngen.namePrefix.mkNum (ngen.idx + 1 + (s_curr - 1)) ∉ effectiveAvoidSet := by
        simpa [h_arith h_s_curr_pos] using h_s_curr_is_fresh_idx

      -- Use the minimality for s_next
      have h_s_next_le_s_curr_minus_1 : s_next ≤ s_curr - 1 := by
        apply stepsToFreshNat_is_min
        exact h_prop_for_s_next h_s_curr_pos

      -- Conclude using s_next ≤ s_curr - 1 and s_curr > 0
      exact Nat.lt_of_le_pred h_s_curr_pos h_s_next_le_s_curr_minus_1

  -- Call the helper function with the generator from the current context.
  -- The `base` parameter is ignored in this implementation strategy.
  let (foundName, generatorStateWhenFound) := findFresh ctx.gen

  -- The generator state in `AlphaCtx` needs to be advanced past the one
  -- whose `.curr` value was chosen as `foundName`.
  let nextGeneratorStateForCtx := generatorStateWhenFound.next

  -- Add the newly found name to the set of names to avoid for future calls.
  let updatedAvoidSet := insert foundName ctx.avoid

  -- Return the found fresh name and the updated AlphaCtx.
  (foundName, { gen := nextGeneratorStateForCtx, avoid := updatedAvoidSet })

end AlphaCtx
end AlgEffectus.Core

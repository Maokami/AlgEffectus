import AlgEffectus.Core.FreeVars
import AlgEffectus.Core.Rename
import AlgEffectus.Core.Syntax
import Lean

import Init.Control.State

namespace AlgEffectus.Core

abbrev AlphaSubstM := StateM AlphaCtx

mutual
  /--
  Capture-avoiding substitution with α-renaming (Monadic version).
  Replaces free occurrences of targetVar with replacement value.
  -/
  def substValueM (target : Name) (repl : Value) : Value -> AlphaSubstM Value
  | Value.varV n => do
    if n = target then return repl else return (Value.varV n)
  | Value.funV x body => do
    if x = target then
      return (Value.funV x body)
    else
      let fv := freeVarsValue repl
      if fv.contains x then
        let ctx ← get
        let (x', ctx') := ctx.fresh x
        set ctx'
        let bodyRen := renameComp x x' body
        let body' ← substCompM target repl bodyRen
        return (Value.funV x' body')
      else
        let body' ← substCompM target repl body
        return (Value.funV x body')
  | Value.handV h => do
    let h' ← substHandlerM target repl h
    return (Value.handV h')
  | v => return v

  termination_by
    v => sizeOfValue v
  decreasing_by
    repeat dsimp [sizeOfValue]; simp

  def substHandlerM (target : Name) (repl : Value) : Handler -> AlphaSubstM Handler
  | Handler.mk rb rc opcs => do
    let rc' ← if rb = target then (return rc) else substCompM target repl rc
    let opcs' ← opcs.foldlM (init := []) fun acc opcl => do
      let (op, x, k, _) := opcl
      if x = target || k = target then return opcl :: acc
      else
        let c' ← substCompM target repl opcl.snd.snd.snd
        return (op, x, k, c') :: acc
    return Handler.mk rb rc' opcs'.reverse

  termination_by
    h => sizeOfHandler h
  decreasing_by
    rename_i h_mem
    dsimp [sizeOfHandler]
    have h₁ : sizeOfComp opcl.snd.snd.snd ≤ sizeOfOpClauses opcs := by
      induction h_mem with
      | head _ => dsimp [sizeOfOpClauses]; simp
      | tail _ _ ih₁=>
        simp [sizeOfOpClauses, Nat.le_trans ih₁]
    simp +arith [Nat.le_trans h₁]
    dsimp [sizeOfHandler]; simp +arith

  def substCompM (target : Name) (repl : Value) : Computation → AlphaSubstM Computation
  | Computation.retC v => do
    let v' ← substValueM target repl v
    return (Computation.retC v')
  | Computation.callC op arg k body => do
    let arg' ← substValueM target repl arg
    if k = target then
      return (Computation.callC op arg' k body)
    else
      let body' ← substCompM target repl body
      return (Computation.callC op arg' k body')
  | Computation.seqC x c1 c2 => do
    let c1' ← substCompM target repl c1
    if x = target then
      return (Computation.seqC x c1' c2)
    else
      let c2' ← substCompM target repl c2
      return (Computation.seqC x c1' c2')
  | Computation.ifC b t e => do
    let b' ← substValueM target repl b
    let t' ← substCompM target repl t
    let e' ← substCompM target repl e
    return (Computation.ifC b' t' e')
  | Computation.appC f a => do
    let f' ← substValueM target repl f
    let a' ← substValueM target repl a
    return (Computation.appC f' a')
  | Computation.withC h c => do
    let h' ← substValueM target repl h
    let c' ← substCompM target repl c
    return (Computation.withC h' c')

  termination_by
    c => sizeOfComp c
  decreasing_by
    repeat dsimp [sizeOfComp]; simp +arith
end

/--
Runs the monadic substitution with an initial empty AlphaCtx.
This provides the clean signature needed for semantics.
-/
def substComp (target : Name) (repl : Value) (c : Computation) : Computation :=
  let (result, _) := (substCompM target repl c).run default
  result

def substValue (target : Name) (repl : Value) (v : Value) : Value :=
  let (result, _) := (substValueM target repl v).run default
  result

def substHandler (target : Name) (repl : Value) (h : Handler) : Handler :=
  let (result, _) := (substHandlerM target repl h).run default
  result

end AlgEffectus.Core

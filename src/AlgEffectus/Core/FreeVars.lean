import AlgEffectus.Core.Syntax

open AlgEffectus.Core

mutual
  /-- free variables of opclauses -/
  def freeVarsOpClauses : List OpClause → Std.HashSet Name
  | [] => {}
  | (_, x, k, c) :: opcs =>
      let base := freeVarsComp c
      let new := (base.erase x).erase k
      freeVarsOpClauses opcs ∪ new

  termination_by opcs => sizeOfOpClauses opcs
  decreasing_by
    repeat dsimp [sizeOfOpClauses]; simp

  /-- free variables of values -/
  def freeVarsValue : Value → Std.HashSet Name
  | Value.varV n          => {n}
  | Value.ttV | Value.ffV => {}
  | Value.funV x body     => (freeVarsComp body).erase x
  | Value.handV h         => freeVarsHandler h

  termination_by v => sizeOfValue v
  decreasing_by
    repeat dsimp [sizeOfValue]; simp

  /-- free variables of handlers -/
  def freeVarsHandler : Handler → Std.HashSet Name
  | Handler.mk rb rc opcs =>
    let base := freeVarsComp rc
    (base.erase rb) ∪ freeVarsOpClauses opcs

  termination_by h => sizeOfHandler h
  decreasing_by
    repeat dsimp [sizeOfHandler]; simp +arith

  /-- free variables of computations -/
  def freeVarsComp : Computation → Std.HashSet Name
  | Computation.retC v              => freeVarsValue v
  | Computation.callC _ arg k body  =>
      ((freeVarsValue arg).union (freeVarsComp body)).erase k
  | Computation.seqC x c1 c2        =>
      ((freeVarsComp c1).union (freeVarsComp c2)).erase x
  | Computation.ifC b t e           =>
      ((freeVarsValue b).union (freeVarsComp t)).union (freeVarsComp e)
  | Computation.appC f a            =>
      (freeVarsValue f).union (freeVarsValue a)
  | Computation.withC h c           =>
      (freeVarsValue h).union (freeVarsComp c)

  termination_by c => sizeOfComp c
    decreasing_by
    repeat dsimp [sizeOfComp]; simp +arith
end

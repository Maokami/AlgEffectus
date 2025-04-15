import AlgEffectus.Core.Syntax

open AlgEffectus.Core

mutual
  /-- free variables of values -/
  partial def freeVarsValue : Value → Std.HashSet Name
  | Value.varV n          => {n}
  | Value.ttV | Value.ffV => {}
  | Value.funV x body     => (freeVarsComp body).erase x
  | Value.handV h         => freeVarsHandler h

  /-- free variables of handlers -/
  partial def freeVarsHandler : Handler → Std.HashSet Name
  | Handler.mk rb rc opcs =>
      let base := (freeVarsComp rc).erase rb
      opcs.foldl (init := base) fun acc (_, x, k, c) =>
        (((freeVarsComp c).erase x).erase k).union acc

  /-- free variables of computations -/
  partial def freeVarsComp : Computation → Std.HashSet Name
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
end

import AlgEffectus.Core.Syntax

open AlgEffectus.Core

mutual
  partial def renameValue (old new : Name) : Value → Value
  | v@(Value.varV n)     => if n = old then Value.varV new else v
  | Value.funV x body    =>
      let (x', body') :=
        if x = old then (x, body) else (x, renameComp old new body)
      Value.funV x' body'
  | Value.handV h        => Value.handV (renameHandler old new h)
  | v                    => v

  partial def renameHandler (old new : Name) : Handler → Handler
  | Handler.mk rb rc opcs =>
      let rb' := rb
      let rc' := if rb = old then rc else renameComp old new rc
      let opcs' := opcs.map fun (op,x,k,c) =>
        let x' := x; let k' := k
        let c' := if x = old ∨ k = old then c else renameComp old new c
        (op,x',k',c')
      Handler.mk rb' rc' opcs'

  partial def renameComp (old new : Name) : Computation → Computation
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
end

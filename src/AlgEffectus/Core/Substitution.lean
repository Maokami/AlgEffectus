import AlgEffectus.Core.FreeVars
import AlgEffectus.Core.Rename
import AlgEffectus.Core.Syntax

import Lean

namespace AlgEffectus.Core

-- TODO: Refactor substitutions by using Monad transformers
mutual
  /--
  Capture-avoiding substitution with α-renaming.
  Replaces free occurrences of targetVar with replacement value.
  -/
  partial def substValue (target : Name) (repl : Value)
    : Value -> AlphaCtx -> Value × AlphaCtx
  | Value.varV n, ctx => if n = target then (repl, ctx) else (Value.varV n, ctx)
  | Value.funV x body, ctx =>
      if x = target then (Value.funV x body, ctx)
      else
        let fv := freeVarsValue repl
        if fv.contains x then
          let (x', ctx') := ctx.fresh x
          let bodyRen   := (renameComp x x' body)
          let (body', ctx'') := substComp target repl bodyRen ctx'
          (Value.funV x' body', ctx'')
        else
          let (body', ctx') := substComp target repl body ctx
          (Value.funV x body', ctx')
  | Value.handV h, ctx =>
      let (h', ctx') := substHandler target repl h ctx
      (Value.handV h', ctx')
  | v, ctx => (v, ctx)

  partial def substHandler (target : Name) (repl : Value)
    : Handler -> AlphaCtx -> Handler × AlphaCtx
  | Handler.mk rb rc opcs, ctx =>
      let (rc', ctx1) :=
        if rb = target then (rc, ctx) else substComp target repl rc ctx
      let (opcs', ctx2) :=
        opcs.foldl (init := ([], ctx1)) fun (acc : List (OpName × Name × Name × Computation) × AlphaCtx) (op, x, k, c) =>
          let (acc', ctx') := acc
          if x = target || k = target then
            ((op, x, k, c) :: acc', ctx')
          else
            let (c', ctx'') := substComp target repl c ctx'
            ((op, x, k, c') :: acc', ctx'')
      let opcs' := opcs'.reverse
      (Handler.mk rb rc' opcs', ctx2)

  partial def substComp (target : Name) (repl : Value)
    : Computation → AlphaCtx → Computation × AlphaCtx
  | Computation.retC v, ctx =>
      let (v', ctx') := substValue target repl v ctx
      (Computation.retC v', ctx')
  | Computation.callC op arg k body, ctx =>
      let (arg', ctx1) := substValue target repl arg ctx
      if k = target then
        (Computation.callC op arg' k body, ctx1)
      else
        let (body', ctx2) := substComp target repl body ctx1
        (Computation.callC op arg' k body', ctx2)
  | Computation.seqC x c1 c2, ctx =>
      let (c1', ctx1) := substComp target repl c1 ctx
      if x = target then
        (Computation.seqC x c1' c2, ctx1)
      else
        let (c2', ctx2) := substComp target repl c2 ctx1
        (Computation.seqC x c1' c2', ctx2)
  | Computation.ifC b t e, ctx =>
      let (b', ctx1) := substValue target repl b ctx
      let (t', ctx2) := substComp target repl t ctx1
      let (e', ctx3) := substComp target repl e ctx2
      (Computation.ifC b' t' e', ctx3)
  | Computation.appC f a, ctx =>
      let (f', ctx1) := substValue target repl f ctx
      let (a', ctx2) := substValue target repl a ctx1
      (Computation.appC f' a', ctx2)
  | Computation.withC h c, ctx =>
      let (h', ctx1) := substValue target repl h ctx
      let (c', ctx2) := substComp target repl c ctx1
      (Computation.withC h' c', ctx2)
end

end AlgEffectus.Core

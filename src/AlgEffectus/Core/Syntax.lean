/-!
# Core Syntax for Algebraic Effects and Handlers

This module defines the abstract syntax for values, computations, and handlers
-/

namespace AlgEffectus.Core

/-- Type alias for variable names. Using String for simplicity. -/
abbrev Name := String

/-- Type alias for operation names. Using String for simplicity. -/
abbrev OpName := String

mutual -- Mutual definitions for the core syntax
  /--
  Represents values `v` in the language.
  Values can be variables, boolean values, function abstractions, or handlers.
  -/
  inductive Value : Type where
    | varV (name : Name) : Value                          -- Variable `x`
    -- boolean values
    | ttV : Value  | ffV : Value                          -- True, False
    | funV (binder : Name) (body : Computation) : Value   -- Abstraction `fun x => c`
    | handV (handler : Handler) : Value                   -- Handler `h`
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
         (opClauses : List (OpName × Name × Value × Computation)) : Handler
    deriving Repr -- For printing

  /--
  Represents computations `c` in the language.
  Computations can be value returns, operation calls, sequential bindings, conditionals, function applications,
  and handler applications.
  -/
  inductive Computation : Type where
    | retC (val : Value) : Computation -- Return a value: `return v`
    | callC (op : OpName) (param : Value) (res: Value) (cont: Computation): Computation -- Call an operation: `op(v; y. c)`
    | seqC (binder: Name) (body: Computation) (cont: Computation) : Computation -- Sequential binding: `do x ← c₁ in c₂`
    | ifC (cond: Value) (thenBranch: Computation) (elseBranch: Computation) : Computation -- Conditional: `if b then c₁ else c₂`
    | appC (func: Value) (arg: Value) : Computation -- Function application: `f(x)`
    | withC (handler: Value) (comp: Computation) : Computation -- Handler application with a handler: `with h handle c`
    deriving Repr, Inhabited -- For printing, default instance
end

instance : Inhabited Handler where
  default := Handler.mk "" (Computation.retC (Value.ttV)) []

/-! Helper functions for syntax manipulation -/

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
def Handler.getOpClauses : Handler → List (OpName × Name × Value × Computation)
  | Handler.mk _ _ opc => opc

/-- Finds the corresponding operation clause in a handler given an operation name. -/
def Handler.findOpClause (h : Handler) (opName : OpName) : Option (Name × Value × Computation) :=
  h.getOpClauses.find? (fun (op, _, _, _) => op == opName) -- Find clause by op name
  |>.map (fun (_, x, k, body) => (x, k, body)) -- Extract (continuation_binder, arg_binder, body)

/-- Checks if a computation is a value (specifically, `return v`). -/
def Computation.isValue : Computation → Bool
  | Computation.retC _ => true
  | _                  => false

end AlgEffectus.Core

import Lean
import AlgEffectus.Core.Syntax

/-!
# Parser Definition

This module defines the parser for the abstract syntax of algebraic effects and handlers.
-/

namespace AlgEffectus.Core
namespace Parser

open Lean Lean.Parser

-- Declare syntax categories for values and computations
declare_syntax_cat effVal
declare_syntax_cat effComp

-- Define the syntax for values
syntax ident : effVal
syntax "true" : effVal
syntax "false" : effVal
syntax:25 "fun " ident " ↦ " effComp : effVal
syntax opClause := ident "(" ident ";" ident ")" "↦" effComp
syntax "handler " "{" "return " ident "↦" effComp ("," opClause)* "}" : effVal

-- Define the syntax for computations
syntax effVal : effComp
syntax:max "return " effVal : effComp -- `return` keyword with trailing space
syntax:65 "call " ident "(" effVal "; " ident ". " effComp ")" : effComp
syntax:40   "do " ident " ← " effComp " in " effComp : effComp
syntax:45   "if " effVal " then " effComp " else " effComp : effComp
syntax:1024 (name := effApp) effVal effVal : effComp
syntax:35 "with " effVal " handle " effComp : effComp
syntax:1025 "(" effComp ")" : effComp

-- -- Define the syntax for types
-- syntax "bool" : effValTy
-- syntax effValTy " → " effCompTy : effValTy
-- syntax effCompTy " ⇒ " effCompTy : effValTy
-- syntax effValTy " !{" ident ("," ident)* "}" : effCompTy

-- Bridge syntax categories to the main 'term' category for elaboration
syntax (name := algEffParser) "eff " effComp : term
syntax (name := algEffBlockParser) "eff " "{" effComp "}" : term

end Parser
end AlgEffectus.Core

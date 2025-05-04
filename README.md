# AlgEffectus - Algebraic Effects & Handlers in Lean 4

*A tiny, research‑grade Lean 4 library that re‑implements the core ideas from  
"An Introduction to Algebraic Effects and Handlers" (Pretnar 2015) in order to
understand them inside out.*

---

## Overview

This repository is my learning playground for **algebraic effects and handlers**.  
Using Lean 4’s metaprogramming facilities I am:

* defining a **domain‑specific language (DSL)** for effectful programs,
* giving it an **operational semantics**,
* implementing the **type system**, and
* mechanising **type‐safety proofs** (progress & preservation).

Everything follows, as faithfully as possible, the structure of the tutorial
paper referenced below.

> **Note**  
> The codebase is  highly experimental.

> **Contributions are very welcome**  
> Since I am not a Lean expert, I would love to get feedback on the code and suggestions for improvements.

---

## Quick start

|                      | Command / File                                  |
| -------------------- | ----------------------------------------------- |
| **Prerequisites**    | [Lean 4 v4.19.0](https://leanprover.github.io/) |
| **Clone**            | `git clone https://github.com/Maokami/alg-effectus` |
| **Build**            | `lake build`                                    |
| **Run tests**        | `lake test`  (Currently there are no tests) |
| **View docs**        | `lake exe cache get` → open `doc/index.html` (Currently there are no docs) |

> Lean is managed via **Lake**; no other system‑wide installs are required.

---

##  Current status ☑️ / ☐

| Component                                  | State |
| ------------------------------------------ | ----- |
| Core syntax (`Value`, `Computation`)       | ☑️ Done |
| Core Type syntax                           | ☐ Todo |
| Parser / Elaborator                        | ☑️ Done |
| Pretty‑printer & Delaborator               | ☑️ Done |
| Operational semantics                      | ☑️ Done |
| Type system (`TyVal`, `TyComp`, …)         | ☑️ Done |
| **Progress** theorem                       | ☐ Todo |
| **Preservation** theorem                   | ☐ Todo |
| Examples & unit tests                      | ☐ Todo |
| User documentation                         | ☐ Todo |

---
## References
* Matija Pretnar. 2015. An Introduction to Algebraic Effects and Handlers. Invited tutorial paper. Electron. Notes Theor. Comput. Sci. 319, C (December 2015), 19–35. https://doi.org/10.1016/j.entcs.2015.12.003

---

##  License

This project is released under the MIT License (see LICENSE), but feel free
to suggest a different licence if that would better serve the community.
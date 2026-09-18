/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import LeanPool.Computability.Oracle
public import LeanPool.Computability.TuringDegree
public import LeanPool.Computability.Encoding
public import LeanPool.Computability.Jump
public import LeanPool.Computability.ArithHierarchy
public import LeanPool.Computability.AutGrp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Oracle Computability and Turing Degrees

Source: url:https://github.com/tannerduve/computability
Authors: Tanner Duve, Elan Roth
Status: verified
Main declarations: `Computability.RecursiveIn`, `Computability.TuringDegree`
Tags: computability, oracle-computability, turing-degrees, recursion-theory, arithmetical-hierarchy
MSC: 03D30, 03D28
-/

@[expose] public section

/-!
## Mathematical overview

This development formalises oracle-relative computability and the basic theory of
Turing degrees via partial recursive functions. All declarations live in the
`Computability` namespace.

The core relation `RecursiveIn O f` (`LeanPool.Computability.Oracle`) says that the
partial function `f : ℕ →. ℕ` is computable relative to a set of oracle functions
`O`, defined inductively by closing the basic recursive operations under access to
the oracles in `O`. From this, `TuringReducible` (`f ≤ᵀ g`), `TuringEquivalent`
(`f ≡ᵀ g`), and the quotient type `TuringDegree`
(`LeanPool.Computability.TuringDegree`) are built, and the Turing join `f ⊕ g`
(`turingJoin`) is shown to be a least upper bound, equipping `TuringDegree` with a
`SemilatticeSup` instance (`TuringDegree.instSemilatticeSup`).

A Gödel numbering of oracle programs is given by the inductive type `codeo` with its
universal evaluator `evalo` (`LeanPool.Computability.Encoding`). The encoding is shown
to be a bijection (`decodeCodeo_encodeCodeo`) and `evalo` is shown to be universal:
`RecursiveIn (Set.range g) f ↔ ∃ c, evalo g c = f` (`exists_code_rel`).

The jump operator `f⌜` (`LeanPool.Computability.Jump`) is the diagonal of the
universal machine relative to `f`; `jump_recIn` proves `f ≤ᵀ f⌜`. The iterated jump
of the empty oracle generates the arithmetical hierarchy
(`LeanPool.Computability.ArithHierarchy`), and the automorphism group of the Turing
degrees is set up in `LeanPool.Computability.AutGrp`.

## Provenance

Imported from <https://github.com/tannerduve/computability> (Apache-2.0). The upstream
repository mixes proven results with in-progress `sorry` placeholders; only the
sorry-free declarations are vendored here. The parallel `SingleOracle` development from
upstream is omitted because its foundational encoding lemmas are unproven upstream.
-/

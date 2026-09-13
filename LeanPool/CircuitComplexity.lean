/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import LeanPool.CircuitComplexity.Basic
public import LeanPool.CircuitComplexity.NF
public import LeanPool.CircuitComplexity.AON
public import LeanPool.CircuitComplexity.XOR
public import LeanPool.CircuitComplexity.EssentialInput
public import LeanPool.CircuitComplexity.Shannon
public import LeanPool.CircuitComplexity.LowerBound
public import LeanPool.CircuitComplexity.Schnorr
public import LeanPool.CircuitComplexity.AC0
public import LeanPool.CircuitComplexity.Nondeterminism
public import LeanPool.CircuitComplexity.Valiant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

/-!
# Circuit Complexity in Lean 4

Source: url:https://github.com/SamuelSchlesinger/circuit-complexity
Authors: Samuel Schlesinger
Status: verified
Main declarations: `CircuitComplexity.shannon_lower_bound_circuit`
Tags: circuit-complexity, boolean-functions, lower-bounds, shannon-bound, parity
MSC: 68Q06, 94C11
-/

@[expose] public section

/-!
# Circuit Complexity

A Lean 4 formalization of classical results in Boolean circuit complexity,
built on Mathlib. A `Circuit B N M G` is an acyclic Boolean circuit over basis
`B` with `N` primary inputs, `M` outputs, and `G` internal gates; the
`size_complexity` of a Boolean function is the minimum size of any circuit
computing it.
-/

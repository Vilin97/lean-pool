/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Basic
import LeanPool.CircuitComplexity.NF
import LeanPool.CircuitComplexity.AON
import LeanPool.CircuitComplexity.XOR
import LeanPool.CircuitComplexity.EssentialInput
import LeanPool.CircuitComplexity.Shannon
import LeanPool.CircuitComplexity.LowerBound
import LeanPool.CircuitComplexity.Schnorr
import LeanPool.CircuitComplexity.AC0
import LeanPool.CircuitComplexity.Nondeterminism
import LeanPool.CircuitComplexity.Valiant

/-!
# Circuit Complexity in Lean 4

Source: url:https://github.com/SamuelSchlesinger/circuit-complexity
Authors: Samuel Schlesinger
Status: verified
Main declarations: `CircuitComplexity.shannon_lower_bound_circuit`
Tags: circuit-complexity, boolean-functions, lower-bounds, shannon-bound, parity
MSC: 68Q06, 94C11
-/

/-!
# Circuit Complexity

A Lean 4 formalization of classical results in Boolean circuit complexity,
built on Mathlib. A `Circuit B N M G` is an acyclic Boolean circuit over basis
`B` with `N` primary inputs, `M` outputs, and `G` internal gates; the
`size_complexity` of a Boolean function is the minimum size of any circuit
computing it.
-/

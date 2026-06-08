/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import LeanPool.Circuitlib.Circuit.Wires
import Mathlib.Tactic.TypeStar
import Mathlib.Order.Monotone.Defs

/-! # Gates

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Logic gate. -/
class Gate (V : outParam Type*) [Preorder V] (G : Type*) where
  /-- The number of input wires of a gate. -/
  inputs : G → ℕ
  /-- The number of output wires of a gate. -/
  outputs : G → ℕ
  /-- The wire-function computed by a gate. -/
  gate (g : G) : Wires V (inputs g) → Wires V (outputs g)
  /-- The wire-function of a gate is monotone in the information order. -/
  gate_monotone (g : G) : Monotone (gate g)

attribute [simp] Gate.gate_monotone

end Circuit

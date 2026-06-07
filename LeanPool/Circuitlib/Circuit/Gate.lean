/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import LeanPool.Circuitlib.Circuit.Wires
public import Mathlib.Tactic.TypeStar
public import Mathlib.Order.Monotone.Defs

@[expose] public section

/-! # Gates

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Logic gate. -/
class Gate (V : outParam Type*) [Preorder V] (G : Type*) where
  inputs : G → ℕ
  outputs : G → ℕ
  gate (g : G) : Wires V (inputs g) → Wires V (outputs g)
  gate_monotone (g : G) : Monotone (gate g)

attribute [simp] Gate.gate_monotone

end Circuit

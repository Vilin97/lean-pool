/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import LeanPool.Circuitlib.Circuit.Gate
import Mathlib.CategoryTheory.Category.Basic

/-! # Circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

open CategoryTheory
open OfNat

/-- A category of circuits. -/
class CircuitCategory
    (V : outParam Type*)
    [Preorder V]
    (G : outParam Type*)
    [Gate V G]
    (C : Type u)
    [∀ n, OfNat C n]
    [Category C] where
  /-- Morphism to introduce a gate. -/
  gate (g : G) : (ofNat (Gate.inputs g) : C) ⟶ ofNat (Gate.outputs g)

  /-- Morphism to introduce a wire. -/
  stub : (ofNat 0 : C) ⟶ 1

  /-- Morphism to eliminate a wire. -/
  drop : (ofNat 1 : C) ⟶ 0

  /-- Morphism to fork a wire. -/
  fork : (ofNat 1 : C) ⟶ 2

  /-- Morphism to join two wires. -/
  join : (ofNat 2 : C) ⟶ 1

end Circuit

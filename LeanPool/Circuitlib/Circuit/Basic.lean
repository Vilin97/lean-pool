/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import LeanPool.Circuitlib.Circuit.Category.Basic
import LeanPool.Circuitlib.Circuit.Belnap.Gate
import Mathlib.CategoryTheory.Monoidal.Category

/-! # Circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

open CategoryTheory
open OfNat

universe u

variable
  {C : Type u}
  [∀ n, OfNat C n]
  [Category C]
  [MonoidalCategory C]
  [CircuitCategory BelnapLevel BelnapGate C]

/-- The AND gate as a circuit morphism. -/
abbrev and : (ofNat 2 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.and

/-- The OR gate as a circuit morphism. -/
abbrev or : (ofNat 2 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.or

/-- The NOT gate as a circuit morphism. -/
abbrev not : (ofNat 1 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.not

open MonoidalCategory

/-- The NAND gate, built as AND followed by NOT. -/
abbrev nand : (ofNat 2 : C) ⟶ 1 := and ≫ not

/-- The NOR gate, built as OR followed by NOT. -/
abbrev nor : (ofNat 2 : C) ⟶ 1 := or ≫ not

end Circuit

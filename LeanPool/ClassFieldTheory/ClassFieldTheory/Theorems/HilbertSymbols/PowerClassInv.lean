/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
/-!
# Inversion of power classes

The quotient map to power classes preserves inverses.
-/

namespace ClassFieldTheory

universe u

/-- The class of an inverse is the inverse class. -/
@[simp]
theorem powerClass_inv
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a⁻¹ = (powerClass K n a)⁻¹ :=
  map_inv (powerClass K n) a

end ClassFieldTheory

/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
/-!
# Multiplication of power classes

The quotient map to power classes preserves multiplication.
-/

namespace ClassFieldTheory

universe u

/-- The class of a product is the product of the classes. -/
@[simp]
theorem powerClass_mul
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) :
    powerClass K n (a * b) = powerClass K n a * powerClass K n b :=
  map_mul (powerClass K n) a b

end ClassFieldTheory

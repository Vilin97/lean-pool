/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
/-!
# Powers of power classes

The quotient map to power classes preserves powers.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- The class of a power is the corresponding power of the class. -/
@[simp]
theorem powerClass_pow
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) (m : ℕ) :
    powerClass K n (a ^ m) = (powerClass K n a) ^ m :=
  map_pow (powerClass K n) a m

end ClassFieldTheory

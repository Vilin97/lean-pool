/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
/-!
# Power-class laws and representatives

For a field `K` and a positive integer `n`, `PowerClassGroup K n` is the
quotient of `Kˣ` by the subgroup of `n`-th powers. A class is the identity
exactly when its representative belongs to the power subgroup.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- A power class is trivial exactly when its representative is an `n`-th
power. -/
@[simp]
theorem powerClass_eq_one_iff
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a = 1 ↔
      a ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  exact QuotientGroup.eq_one_iff a

end ClassFieldTheory

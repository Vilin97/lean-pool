/-
Copyright (c) 2026 Antoine de Saint Germain, Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint Germain, Ambrose Tang
-/

import Mathlib.LinearAlgebra.RootSystem.OfBilinear
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum

/-!
# Type-BCₙ root systems

Explicit construction of the type-`BCₙ` root pairing from a dot-product space,
exhibited as a Mathlib `RootPairing`.
-/

namespace BCn

/-- The ambient space `Fin n → ℤ` for the type-BCₙ construction. -/
abbrev Space (n : ℕ) := Fin n → ℤ
/-- The `ℤ`-linear dual of `Space n`. -/
abbrev CoSpace (n : ℕ) := Module.Dual ℤ (Space n)

/-- The standard dot product on `ℤⁿ`. -/
noncomputable def dotProduct (n : ℕ) : Space n →ₗ[ℤ] Space n →ₗ[ℤ] ℤ where
  toFun x :=
    { toFun := fun y => ∑ i, x i * y i
      map_add' := by
        intro y z
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp [Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro x y
    ext z
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    ext y
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

theorem dotProduct_apply (n : ℕ) (x y : Space n) :
    dotProduct n x y = ∑ i, x i * y i :=
  rfl

@[simp]
theorem dotProduct_single_right {n : ℕ} (x : Space n) (i : Fin n) :
    dotProduct n x (Pi.single i 1) = x i := by
  rw [dotProduct_apply]
  simp [Pi.single_apply]

@[simp]
theorem dotProduct_single_left {n : ℕ} (x : Space n) (i : Fin n) :
    dotProduct n (Pi.single i 1) x = x i := by
  rw [dotProduct_apply]
  simp [Pi.single_apply]

theorem dotProduct_isSymm (n : ℕ) : LinearMap.IsSymm (dotProduct n) where
  eq x y := by
    simp [dotProduct_apply, mul_comm]

theorem dotProduct_nondegenerate (n : ℕ) : LinearMap.Nondegenerate (dotProduct n) := by
  constructor
  · intro x hx
    ext i
    simpa using hx (Pi.single i 1)
  · intro y hy
    ext i
    simpa using hy (Pi.single i 1)

/-- The reflective vectors for the standard dot product. -/
abbrev ReflectiveIndex (n : ℕ) :=
  { x : Space n // LinearMap.IsReflective (dotProduct n) x }

/-- The `BCₙ` root pairing, built from all reflective vectors for the standard dot product. -/
noncomputable def rootPairing (n : ℕ) :
    RootPairing (ReflectiveIndex n) ℤ (Space n) (CoSpace n) :=
  RootPairing.ofBilinear (dotProduct n) (dotProduct_nondegenerate n) (dotProduct_isSymm n)
    (IsRegular.of_ne_zero (by norm_num : (2 : ℤ) ≠ 0))

end BCn

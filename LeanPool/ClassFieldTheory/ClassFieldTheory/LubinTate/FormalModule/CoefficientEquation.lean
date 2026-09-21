/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Series
/-!
# Coefficient equations for a fixed uniformizer

For a positive degree, the scalar factor 1 - π ^ r is a unit whenever π
is a uniformizer. Consequently the corresponding scalar coefficient equation
has a unique solution in the valuation ring.
-/

noncomputable section

universe u v

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- A chosen uniformizer reduces to zero in the residue field. -/
theorem residueMap_uniformizer_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    F.residueMap π = 0 :=
  (F.toCompleteDVF.residue_eq_zero_iff π).2
    (F.toCompleteDVF.uniformizer_mem_maximalIdeal hπ)

/-- An element reducing to zero is divisible by the chosen uniformizer. -/
theorem uniformizer_dvd_of_residueMap_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {a : F.valuationSubring} (ha : F.residueMap a = 0) :
    π ∣ a := by
  have hmem : a ∈ F.maximalIdeal :=
    (F.toCompleteDVF.residue_eq_zero_iff a).1 ha
  have hspan :
      a ∈ Ideal.span ({π} : Set F.valuationSubring) := by
    simpa [F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ] using hmem
  exact Ideal.mem_span_singleton.mp hspan

/-- Every positive power of a uniformizer reduces to zero. -/
theorem residueMap_uniformizer_pow_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) :
    F.residueMap (π ^ r) = 0 := by
  simp [map_pow, residueMap_uniformizer_eq_zero hπ, hr]

/-- For positive `r`, the factor `1 - pi ^ r` is a unit of `O_K`. -/
theorem isUnit_one_sub_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) :
    IsUnit (1 - π ^ r) := by
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  intro hunit
  have hresidue_ne : F.residueMap (π ^ r) ≠ 0 :=
    (F.toCompleteDVF.residue_ne_zero_iff_isUnit (π ^ r)).2 hunit
  exact hresidue_ne (residueMap_uniformizer_pow_eq_zero hπ hr)

/-- Left multiplication by a unit has a unique preimage for every
right-hand side. -/
theorem existsUnique_mul_eq_of_isUnit
    {R : Type*} [CommRing R] {a : R} (ha : IsUnit a) (b : R) :
    ∃! x : R, a * x = b := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨(↑(u⁻¹) : R) * b, by simp, ?_⟩
  intro y hy
  calc
    y = ((↑(u⁻¹) : R) * (u : R)) * y := by simp
    _ = (↑(u⁻¹) : R) * ((u : R) * y) := by rw [mul_assoc]
    _ = (↑(u⁻¹) : R) * b := by rw [hy]

/-- The scalar coefficient equation in positive total degree has a
unique solution in the valuation ring. -/
theorem existsUnique_one_sub_uniformizer_pow_mul_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) (b : F.valuationSubring) :
    ∃! x : F.valuationSubring, (1 - π ^ r) * x = b :=
  existsUnique_mul_eq_of_isUnit
    (isUnit_one_sub_uniformizer_pow hπ hr) b

end SameUniformizer
end LubinTate

end

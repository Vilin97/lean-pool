/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue

/-!
# Invariance of Berarducci's ordinal value under nonzero constant factors

Multiplication by a nonzero constant series is an automorphism of `Berarducci.Series K` fixing
`J` and `J + K` setwise and preserving supports exactly, so it leaves Berarducci's ordinal value
unchanged. Each defining branch is transported separately, the third by showing that the
candidate set `Berarducci.representativeOrderTypes` is literally the same set.

The proof of the submultiplicative property in Berarducci, Lemma 5.5(2) uses this invariance for
the cross terms produced by representatives modulo `J + K`.
-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

private theorem coe_C_mul (k : K) (b : Series K) :
    ((HahnSeries.Nonpositive.C k * b : Series K) : K⟦ℝ⟧) = k • (b : K⟦ℝ⟧) := by
  rw [Subring.coe_mul, HahnSeries.Nonpositive.coe_C, HahnSeries.C_mul_eq_smul]

/-- A nonzero constant factor leaves the support of a nonpositive series unchanged. -/
theorem support_C_mul_of_ne_zero {k : K} (hk : k ≠ 0) (b : Series K) :
    ((HahnSeries.Nonpositive.C k * b : Series K) : K⟦ℝ⟧).support =
      (b : K⟦ℝ⟧).support := by
  rw [coe_C_mul]
  ext x
  simp [HahnSeries.mem_support, hk]

/-- A nonzero constant factor leaves the ordinary support order type unchanged. -/
theorem supportOrderType_C_mul_of_ne_zero {k : K} (hk : k ≠ 0) (b : Series K) :
    ((HahnSeries.Nonpositive.C k * b : Series K) : K⟦ℝ⟧).supportOrderType =
      (b : K⟦ℝ⟧).supportOrderType :=
  le_antisymm
    (HahnSeries.supportOrderType_mono (by rw [support_C_mul_of_ne_zero hk]))
    (HahnSeries.supportOrderType_mono (by rw [support_C_mul_of_ne_zero hk]))

/-- A nonzero constant factor does not change membership in the negative-monomial ideal. -/
theorem mem_negativeMonomialIdeal_C_mul_iff {k : K} (hk : k ≠ 0) (b : Series K) :
    HahnSeries.Nonpositive.C k * b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K ↔
      b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  refine ⟨fun h ↦ ?_, fun h ↦ Ideal.mul_mem_left _ _ h⟩
  have hmem := Ideal.mul_mem_left
    (HahnSeries.Nonpositive.negativeMonomialIdeal K) (HahnSeries.Nonpositive.C k⁻¹) h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul] at hmem

private theorem C_mul_mem_nearConstantSubgroup (k : K) {b : Series K}
    (hb : b ∈ nearConstantSubgroup K) :
    HahnSeries.Nonpositive.C k * b ∈ nearConstantSubgroup K := by
  obtain ⟨j, hj, c, rfl⟩ := mem_nearConstantSubgroup_iff.mp hb
  refine mem_nearConstantSubgroup_iff.mpr
    ⟨HahnSeries.Nonpositive.C k * j, Ideal.mul_mem_left _ _ hj, k * c, ?_⟩
  rw [map_mul, mul_add]

/-- A nonzero constant factor does not change membership in `J + K`. -/
theorem mem_nearConstantSubgroup_C_mul_iff {k : K} (hk : k ≠ 0) (b : Series K) :
    HahnSeries.Nonpositive.C k * b ∈ nearConstantSubgroup K ↔ b ∈ nearConstantSubgroup K := by
  refine ⟨fun h ↦ ?_, C_mul_mem_nearConstantSubgroup k⟩
  have hmem := C_mul_mem_nearConstantSubgroup k⁻¹ h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul] at hmem

/-- A nonzero constant factor permutes the representatives modulo `J + K`, so the candidate set of
support order types is unchanged. -/
theorem representativeOrderTypes_C_mul {k : K} (hk : k ≠ 0) (b : Series K) :
    representativeOrderTypes (HahnSeries.Nonpositive.C k * b) = representativeOrderTypes b := by
  ext o
  rw [mem_representativeOrderTypes_iff, mem_representativeOrderTypes_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨HahnSeries.Nonpositive.C k⁻¹ * d, ?_, ?_⟩
    · have hmem := C_mul_mem_nearConstantSubgroup k⁻¹ hd
      rwa [mul_sub, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul] at hmem
    · rw [supportOrderType_C_mul_of_ne_zero (inv_ne_zero hk)]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨HahnSeries.Nonpositive.C k * d, ?_, ?_⟩
    · have hmem := C_mul_mem_nearConstantSubgroup k hd
      rwa [mul_sub] at hmem
    · rw [supportOrderType_C_mul_of_ne_zero hk]

/-- Berarducci's ordinal value is invariant under multiplication by a nonzero constant series. -/
theorem ordinalValue_C_mul {k : K} (hk : k ≠ 0) (b : Series K) :
    ordinalValue (HahnSeries.Nonpositive.C k * b) = ordinalValue b := by
  by_cases hbJ : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
  · rw [ordinalValue_of_mem_negativeMonomialIdeal
      ((mem_negativeMonomialIdeal_C_mul_iff hk b).mpr hbJ),
      ordinalValue_of_mem_negativeMonomialIdeal hbJ]
  by_cases hbNear : b ∈ nearConstantSubgroup K
  · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
      ((mem_nearConstantSubgroup_C_mul_iff hk b).mpr hbNear)
      (fun h ↦ hbJ ((mem_negativeMonomialIdeal_C_mul_iff hk b).mp h)),
      ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal hbNear hbJ]
  · rw [ordinalValue_of_not_mem_nearConstantSubgroup
      (fun h ↦ hbNear ((mem_nearConstantSubgroup_C_mul_iff hk b).mp h)),
      ordinalValue_of_not_mem_nearConstantSubgroup hbNear,
      representativeOrderTypes_C_mul hk]

@[simp]
theorem ordinalValue_one : ordinalValue (1 : Series K) = 1 := by
  rw [ordinalValue_eq_one_iff]
  refine ⟨mem_nearConstantSubgroup_iff.mpr ⟨0, Submodule.zero_mem _, 1, by simp⟩,
    fun h ↦ ?_⟩
  have hc := constantCoeff_eq_zero_of_mem_negativeMonomialIdeal h
  simp at hc

/-- A factor of ordinal value one does not change the value of a product: it is a nonzero
constant modulo `J`, and `J` is an ideal. -/
theorem ordinalValue_mul_of_ordinalValue_eq_one {g : Series K} (hg : ordinalValue g = 1) (y :
    Series K) :
    ordinalValue (g * y) = ordinalValue y := by
  obtain ⟨hnear, hnotJ⟩ := ordinalValue_eq_one_iff.mp hg
  set k := HahnSeries.Nonpositive.constantCoeff g with hk
  have hsub : g - HahnSeries.Nonpositive.C k ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal K :=
    mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hnear
  have hkne : k ≠ 0 := by
    intro h
    rw [h, map_zero, sub_zero] at hsub
    exact hnotJ hsub
  have hmul : g * y - HahnSeries.Nonpositive.C k * y ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    rw [← sub_mul]
    exact Ideal.mul_mem_right _ _ hsub
  rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal hmul, ordinalValue_C_mul hkne]

end Berarducci

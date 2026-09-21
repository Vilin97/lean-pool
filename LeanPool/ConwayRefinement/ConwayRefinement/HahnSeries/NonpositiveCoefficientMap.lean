/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportSupremum

/-!
# Coefficient extension of nonpositive Hahn series

Applying a ring homomorphism to every coefficient of a Hahn series supported on the nonpositive
cone leaves the support inside that cone, so it induces a ring homomorphism between the
corresponding subrings. When the coefficient map is injective, in particular for an extension of
fields, the support is preserved exactly: a coefficient vanishes after the map precisely when it
vanished before. Constants are carried to constants.

Two support computations used alongside the coefficient extension are recorded here as well. The
support supremum is monotone under inclusion of supports, across two coefficient rings, and
subtracting the constant term deletes exactly the exponent zero from the support.
-/

universe v w

open scoped HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

/-- Support inclusion is monotone for the support supremum, across coefficient rings. -/
theorem supportSup_mono {K₁ : Type v} {K₂ : Type w} [Field K₁] [Field K₂]
    {u : HahnSeries.Nonpositive ℝ K₁} {v : HahnSeries.Nonpositive ℝ K₂}
    (h : (u : K₁⟦ℝ⟧).support ⊆ (v : K₂⟦ℝ⟧).support) : supportSup u ≤ supportSup v := by
  by_cases hu : u = 0
  · simp [hu]
  · have hu' : (u : K₁⟦ℝ⟧) ≠ 0 := by simpa using hu
    have hune := HahnSeries.support_nonempty_iff.mpr hu'
    have hvne : ((v : K₂⟦ℝ⟧)).support.Nonempty := hune.mono h
    have hv : v ≠ 0 := by intro hz; rw [hz] at hvne; simp at hvne
    rw [supportSup_of_ne hu, supportSup_of_ne hv, WithBot.coe_le_coe]
    exact csSup_le_csSup (bddAbove_support v) hune h

/-- Removing the constant term deletes exactly the exponent zero from the support. -/
theorem support_sub_C_constantCoeff {K₁ : Type v} [Field K₁]
    (b : HahnSeries.Nonpositive ℝ K₁) :
    ((b - HahnSeries.Nonpositive.C (HahnSeries.Nonpositive.constantCoeff b) :
        HahnSeries.Nonpositive ℝ K₁) : K₁⟦ℝ⟧).support = (b : K₁⟦ℝ⟧).support \ {0} := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, HahnSeries.mem_support]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply,
      HahnSeries.Nonpositive.constantCoeff_apply]
  · simp [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply,
      HahnSeries.Nonpositive.constantCoeff_apply, hx]

variable {K : Type v} {E : Type w} [Field K] [Field E]

/-- Coefficientwise extension of a nonpositive Hahn series along a ring homomorphism. -/
def nonpositiveCoefficientMap (f : K →+* E) :
    HahnSeries.Nonpositive ℝ K →+* HahnSeries.Nonpositive ℝ E where
  toFun u := ⟨(u : K⟦ℝ⟧).map (f : K →+* E), by
    refine (HahnSeries.mem_nonpositiveSubring ℝ E).mpr fun x hx ↦
      HahnSeries.Nonpositive.support_subset u ?_
    rw [HahnSeries.mem_support] at hx ⊢
    intro hzero
    exact hx (show f ((u : K⟦ℝ⟧).coeff x) = 0 by rw [hzero, map_zero])⟩
  map_one' := Subtype.ext (HahnSeries.map_one (f : K →+* E).toMonoidWithZeroHom)
  map_mul' u v := Subtype.ext (HahnSeries.map_mul (f : K →+* E).toNonUnitalRingHom)
  map_zero' := Subtype.ext (HahnSeries.map_zero (f : K →+* E).toMonoidWithZeroHom.toZeroHom)
  map_add' u v := Subtype.ext (HahnSeries.map_add (f : K →+* E).toAddMonoidHom)

/-- The coefficient extension acts coefficientwise. -/
theorem coe_nonpositiveCoefficientMap (f : K →+* E)
    (u : HahnSeries.Nonpositive ℝ K) (x : ℝ) :
    ((nonpositiveCoefficientMap f u : HahnSeries.Nonpositive ℝ E) : E⟦ℝ⟧).coeff x =
      f (((u : K⟦ℝ⟧)).coeff x) :=
  (rfl)

/-- Coefficient extension along a field embedding preserves the support. -/
theorem support_nonpositiveCoefficientMap (f : K →+* E)
    (u : HahnSeries.Nonpositive ℝ K) :
    ((nonpositiveCoefficientMap f u : HahnSeries.Nonpositive ℝ E) : E⟦ℝ⟧).support =
      ((u : K⟦ℝ⟧)).support := by
  ext x
  simp only [HahnSeries.mem_support, coe_nonpositiveCoefficientMap]
  exact ⟨fun h hz ↦ h (by rw [hz, map_zero]), fun h hz ↦ h (f.injective (by simpa using hz))⟩

/-- Coefficient extension carries a constant to the constant with extended value. -/
theorem nonpositiveCoefficientMap_C (f : K →+* E) (k : K) :
    nonpositiveCoefficientMap f (HahnSeries.Nonpositive.C k) =
      HahnSeries.Nonpositive.C (f k) := by
  apply Subtype.ext
  ext x
  rw [coe_nonpositiveCoefficientMap, HahnSeries.Nonpositive.coe_C,
    HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply, HahnSeries.C_apply]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [hx]

end HahnSeries.Nonpositive

end

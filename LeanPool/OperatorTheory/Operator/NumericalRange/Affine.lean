/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import LeanPool.OperatorTheory.Operator.NumericalRange.Helpers

/-!
# Affine covariance of the numerical range

Affine changes of an operator induce the same affine changes on its numerical
range.  The general formula in this file simultaneously covers scalar
multiplication, translation by a scalar operator, and the centered-rescaled
operators used in disk normalization arguments.
-/

@[expose] public section

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range commutes with the affine normalization
`A ↦ c • (A - z₀ I)`. -/
theorem numericalRange_smul_sub_smul_one
    (A : E →L[ℂ] E) (c z₀ : ℂ) :
    numericalRange (c • (A - z₀ • 1)) =
      (fun z => c * (z - z₀)) '' numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).2 ⟨x, hx, rfl⟩, ?_⟩
    exact (inner_smul_sub_smul_one_apply_self c z₀ A hx).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_numericalRange A w).1 hw
    refine (mem_numericalRange _ _).2 ⟨x, hx, ?_⟩
    exact inner_smul_sub_smul_one_apply_self c z₀ A hx

/-- Scalar multiplication of an operator multiplies its numerical range by
the same scalar. -/
theorem numericalRange_smul (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (c • A) =
      (fun z => c * z) '' numericalRange A := by
  simpa only [zero_smul, sub_zero, sub_zero] using
    numericalRange_smul_sub_smul_one A c 0

/-- Subtracting a scalar operator translates the numerical range. -/
theorem numericalRange_sub_smul_one (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (A - c • 1) =
      (fun z => z - c) '' numericalRange A := by
  simpa only [one_smul, one_mul] using
    numericalRange_smul_sub_smul_one A 1 c

/-- Adding a scalar operator translates the numerical range. -/
theorem numericalRange_add_smul_one (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (A + c • 1) =
      (fun z => z + c) '' numericalRange A := by
  simpa only [sub_neg_eq_add, neg_smul] using
    numericalRange_sub_smul_one A (-c)

/-- On a nontrivial space, the numerical range of the zero operator is the
singleton `{0}`. -/
@[simp] theorem numericalRange_zero [Nontrivial E] :
    numericalRange (0 : E →L[ℂ] E) = {0} := by
  ext z
  constructor
  · rintro ⟨x, _hx, hz⟩
    rw [mem_singleton_iff]
    simpa only [zero_apply, inner_zero_right] using hz.symm
  · intro hz
    rw [mem_singleton_iff] at hz
    subst z
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    exact (mem_numericalRange _ _).2 ⟨x, hxnorm, by simp⟩

/-- On a nontrivial space, a scalar operator has singleton numerical range. -/
@[simp] theorem numericalRange_scalar [Nontrivial E] (c : ℂ) :
    numericalRange (c • (1 : E →L[ℂ] E)) = {c} := by
  have h := numericalRange_add_smul_one (0 : E →L[ℂ] E) c
  simpa only [zero_add, numericalRange_zero, image_singleton, zero_add] using h

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

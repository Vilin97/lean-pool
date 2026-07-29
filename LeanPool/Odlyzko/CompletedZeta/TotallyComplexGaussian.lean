/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ComplexPlaceIntegral
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem integral_totallyComplexGaussian_eq_prod
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      ∏ w,
        (q w : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
            (q w : ℂ) ^ 2))
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioi 0))) =
      ∏ w : InfinitePlace K, (2 : ℂ)⁻¹ * (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) *
        CompletedZeta.complexPlaceGammaFactor s := by
  classical
  apply integral_pi_complexPlaceGaussian_eq_prod
    (a := fun w : InfinitePlace K ↦ (w x) ^ 2)
  · intro w
    exact sq_pos_of_pos (InfinitePlace.pos_iff.mpr hx)
  · grind

variable [IsTotallyComplex K]

theorem prod_infinitePlace_sq_cpow_eq_absNorm_cpow
    (x : K) (s : ℂ) :
    (∏ w : InfinitePlace K, (((w x) ^ 2 : ℝ) : ℂ) ^ s) =
      ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ s := by
  classical
  rw [← cpow_prod_of_nonneg Finset.univ (fun w : InfinitePlace K ↦ (w x) ^ 2)
    (fun _ _ ↦ sq_nonneg _) s]
  congr 2
  simpa only [IsTotallyComplex.mult_eq] using InfinitePlace.prod_eq_abs_norm x

theorem prod_complexPlaceGaussian_eq_absNorm
    (x : K) (s : ℂ) :
    (∏ w : InfinitePlace K,
        (2 : ℂ)⁻¹ * (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) *
          CompletedZeta.complexPlaceGammaFactor s) =
      ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^
          Fintype.card (InfinitePlace K) *
        ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ (-s) := by
  classical
  rw [← prod_infinitePlace_sq_cpow_eq_absNorm_cpow K x (-s)]
  calc
    _ = ∏ w : InfinitePlace K,
        ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) *
          (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) := by grind
    _ = (∏ _w : InfinitePlace K,
          (2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) *
        ∏ w : InfinitePlace K, (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by simp

theorem integral_totallyComplexGaussian_eq_absNorm
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      ∏ w,
        (q w : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
            (q w : ℂ) ^ 2))
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioi 0))) =
      ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ (-s) := by
  rw [integral_totallyComplexGaussian_eq_prod K hx hs,
    prod_complexPlaceGaussian_eq_absNorm K x s,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

end NumberField.Odlyzko

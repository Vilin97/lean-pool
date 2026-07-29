/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredVerticalBound
public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation

/-!
# Vertical Growth

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Ideal NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered fractional class normalization norm used in the Odlyzko-bound argument. -/
noncomputable def centeredFractionalClassNormalizationNorm : ℝ :=
  ‖(torsionOrder K : ℂ)⁻¹ *
      (2 : ℂ) ^ nrComplexPlaces K *
      (shapeThetaIntegralConstant K : ℂ)‖

open Classical in
/-- A pole cleared completed dedekind zeta vertical bound used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCompletedDedekindZetaVerticalBound
    (a b : ℝ) : ℝ :=
  ∑ C : ClassGroup (𝓞 K),
    centeredFractionalClassNormalizationNorm K *
      poleClearedCenteredClassThetaVerticalBound K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCompletedDedekindZetaVerticalBound_nonneg (a b : ℝ) :
    0 ≤ poleClearedCompletedDedekindZetaVerticalBound K a b := by
  unfold poleClearedCompletedDedekindZetaVerticalBound
  apply Finset.sum_nonneg
  intro C _
  exact mul_nonneg
    (norm_nonneg _)
    (poleClearedCenteredClassThetaVerticalBound_nonneg K _ a b)

open Classical in
theorem norm_poleClearedCompletedDedekindZetaContinuation_vertical_le
    {a b σ t : ℝ} (hσ : σ ∈ Set.Icc a b) :
    ‖poleClearedCompletedDedekindZetaContinuation K
        ((σ : ℂ) + t * I)‖ ≤
      poleClearedCompletedDedekindZetaVerticalBound K a b *
        (1 + |t|) ^ 2 := by
  rw [poleClearedCompletedDedekindZetaContinuation]
  refine (norm_sum_le _ _).trans ?_
  rw [poleClearedCompletedDedekindZetaVerticalBound, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro C _
  rw [poleClearedCenteredFractionalClassContribution, norm_mul]
  calc
    ‖(torsionOrder K : ℂ)⁻¹ * (2 : ℂ) ^ nrComplexPlaces K *
          (shapeThetaIntegralConstant K : ℂ)‖ *
        ‖poleClearedCenteredClassThetaIntegral K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))
          ((σ : ℂ) + t * I)‖ ≤
      centeredFractionalClassNormalizationNorm K *
        (poleClearedCenteredClassThetaVerticalBound K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b *
            (1 + |t|) ^ 2) := by
      unfold centeredFractionalClassNormalizationNorm
      exact mul_le_mul_of_nonneg_left
        (norm_poleClearedCenteredClassThetaIntegral_vertical_le K _ hσ)
        (norm_nonneg _)
    _ = centeredFractionalClassNormalizationNorm K *
          poleClearedCenteredClassThetaVerticalBound K
            (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b *
          (1 + |t|) ^ 2 := by ring

end NumberField.Odlyzko

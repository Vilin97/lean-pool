/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaMovingCenterLogBound
public import LeanPool.Odlyzko.ExplicitFormula.SelectedHeightLogDerivative

/-!
# Selected Height Zero Count

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height zero count bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightZeroCountBound (A : ℝ) : ℝ :=
  2 * completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
    Real.log (9 / 8)

open Classical in
private theorem selected_height_positive_rectangle_subset_disk
    (A : ℝ) :
    Icc (-3 : ℝ) 7 ×ℂ Icc (A - 5) (A + 6) ⊆
      closedBall (2 + ((A + 1 / 2 : ℝ) : ℂ) * I) 8 := by
  intro z hz
  rw [mem_closedBall, dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : -5 ≤ z.re - 2 ∧ z.re - 2 ≤ 5 := by
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him :
      -(11 / 2 : ℝ) ≤ z.im - (A + 1 / 2) ∧
        z.im - (A + 1 / 2) ≤ 11 / 2 := by
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, sub_im, add_im]
  norm_num
  nlinarith [sq_nonneg (z.re - 2 + 5), sq_nonneg (5 - (z.re - 2)),
    sq_nonneg (z.im - (A + 1 / 2) + 11 / 2),
    sq_nonneg (11 / 2 - (z.im - (A + 1 / 2)))]

open Classical in
private theorem selected_height_negative_rectangle_subset_disk
    (A : ℝ) :
    Icc (-3 : ℝ) 7 ×ℂ Icc (-(A + 6)) (-(A - 5)) ⊆
      closedBall (2 + ((-(A + 1 / 2) : ℝ) : ℂ) * I) 8 := by
  intro z hz
  rw [mem_closedBall, dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : -5 ≤ z.re - 2 ∧ z.re - 2 ≤ 5 := by
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him :
      -(11 / 2 : ℝ) ≤ z.im - (-(A + 1 / 2)) ∧
        z.im - (-(A + 1 / 2)) ≤ 11 / 2 := by
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, sub_im, add_im]
  norm_num
  nlinarith [sq_nonneg (z.re - 2 + 5), sq_nonneg (5 - (z.re - 2)),
    sq_nonneg (z.im - (-(A + 1 / 2)) + 11 / 2),
    sq_nonneg (11 / 2 - (z.im - (-(A + 1 / 2))))]

open Classical in
private theorem card_selected_height_positive_rectangle_le
    {A : ℝ} (hA : 6 ≤ A) :
    ((completedDedekindZetaZerosInClosedRectangle K
        (-3) 7 (A - 5) (A + 6)).card : ℝ) ≤
      completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
        Real.log (9 / 8) := by
  let t : ℝ := A + 1 / 2
  have ht : 1 ≤ |t| := by grind
  have hc :
      poleClearedCompletedDedekindZetaContinuation K (2 + t * I) ≠ 0 :=
    poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (by simp)
  have hJ :=
    card_completedDedekindZetaZerosInClosedRectangle_le_movingJensen
      K (r := 8) (R := 9) (t := t)
      (by norm_num) (by norm_num) hc
      (by simpa [t] using selected_height_positive_rectangle_subset_disk A)
  have hMpos : 0 < completedZetaMovingCircleBound K 9 t :=
    lt_of_lt_of_le zero_lt_one
      (one_le_completedZetaMovingCircleBound K 9 t)
  have hcenterPos :
      0 < ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ :=
    norm_pos_iff.mpr hc
  rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hcenterPos)] at hJ
  exact hJ.trans (div_le_div_of_nonneg_right
    (completedZeta_moving_center_log_gap_le K ht)
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le)

open Classical in
private theorem card_selected_height_negative_rectangle_le
    {A : ℝ} (hA : 6 ≤ A) :
    ((completedDedekindZetaZerosInClosedRectangle K
        (-3) 7 (-(A + 6)) (-(A - 5))).card : ℝ) ≤
      completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
        Real.log (9 / 8) := by
  let t : ℝ := -(A + 1 / 2)
  have ht : 1 ≤ |t| := by grind
  have hc :
      poleClearedCompletedDedekindZetaContinuation K (2 + t * I) ≠ 0 :=
    poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (by simp)
  have hJ :=
    card_completedDedekindZetaZerosInClosedRectangle_le_movingJensen
      K (r := 8) (R := 9) (t := t)
      (by norm_num) (by norm_num) hc
      (by simpa [t] using selected_height_negative_rectangle_subset_disk A)
  have hMpos : 0 < completedZetaMovingCircleBound K 9 t :=
    lt_of_lt_of_le zero_lt_one
      (one_le_completedZetaMovingCircleBound K 9 t)
  have hcenterPos :
      0 < ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ :=
    norm_pos_iff.mpr hc
  rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hcenterPos)] at hJ
  have hbound := hJ.trans (div_le_div_of_nonneg_right
    (completedZeta_moving_center_log_gap_le K ht)
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le)
  have habs : |t| = |A + 1 / 2| := by grind
  simpa [completedZetaMovingCenterLogLinearBound, habs] using hbound

open Classical in
theorem card_completedZetaSelectedHeightOrdinates_le
    {A : ℝ} (hA : 6 ≤ A) :
    ((completedZetaSelectedHeightOrdinates K A).card : ℝ) ≤
      completedZetaSelectedHeightZeroCountBound K A := by
  let Z :=
    completedDedekindZetaZerosInClosedRectangle K
      (-3) 7 (-(A + 6)) (A + 6)
  let F := Z.filter fun z ↦ A - 5 ≤ |z.im|
  let P :=
    completedDedekindZetaZerosInClosedRectangle K
      (-3) 7 (A - 5) (A + 6)
  let N :=
    completedDedekindZetaZerosInClosedRectangle K
      (-3) 7 (-(A + 6)) (-(A - 5))
  have hFsubset : F ⊆ P ∪ N := by
    intro z hz
    have hzF := Finset.mem_filter.mp hz
    have hzRect :=
      (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hzF.1
    rcases le_total 0 z.im with hpos | hneg
    · apply Finset.mem_union_left
      apply (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
      refine ⟨⟨hzRect.1.1, ?_⟩, hzRect.2⟩
      rw [abs_of_nonneg hpos] at hzF
      exact ⟨hzF.2, hzRect.1.2.2⟩
    · apply Finset.mem_union_right
      apply (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
      refine ⟨⟨hzRect.1.1, ?_⟩, hzRect.2⟩
      rw [abs_of_nonpos hneg] at hzF
      exact ⟨by linarith [hzRect.1.2.1], by grind⟩
  have hcardNat :
      (completedZetaSelectedHeightOrdinates K A).card ≤ P.card + N.card := by
    calc
      (completedZetaSelectedHeightOrdinates K A).card ≤ F.card := by
        exact Finset.card_image_le
      _ ≤ (P ∪ N).card := Finset.card_le_card hFsubset
      _ ≤ P.card + N.card := Finset.card_union_le P N
  have hcardReal :
      ((completedZetaSelectedHeightOrdinates K A).card : ℝ) ≤
        (P.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((completedZetaSelectedHeightOrdinates K A).card : ℝ) ≤
        (P.card : ℝ) + (N.card : ℝ) := hcardReal
    _ ≤
        completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
            Real.log (9 / 8) +
          completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
            Real.log (9 / 8) := by
      gcongr
      · simpa [P] using card_selected_height_positive_rectangle_le K hA
      · simpa [N] using card_selected_height_negative_rectangle_le K hA
    _ = completedZetaSelectedHeightZeroCountBound K A := by
      unfold completedZetaSelectedHeightZeroCountBound
      ring

open Classical in
theorem inv_completedZetaSelectedHeightSeparation_le
    {A : ℝ} (hA : 6 ≤ A) :
    (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
      4 * (completedZetaSelectedHeightZeroCountBound K A + 1) := by
  rw [completedZetaSelectedHeightSeparation,
    finiteSetAvoidanceRadiusOnLength]
  have hcard :=
    card_completedZetaSelectedHeightOrdinates_le K hA
  simp_all

end NumberField.Odlyzko

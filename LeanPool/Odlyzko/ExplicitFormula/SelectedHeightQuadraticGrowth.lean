/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.SelectedHeightZeroCount

/-!
# Selected Height Quadratic Growth

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The linear coefficient controlling the completed-zeta zero count at a selected height. -/
noncomputable def completedZetaSelectedHeightZeroCountLinearCoefficient : ℝ :=
  4 * completedZetaMovingCenterLinearCoefficient K 9 / Real.log (9 / 8)

omit [IsTotallyComplex K] in
private theorem completedZetaSelectedHeightZeroCountLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightZeroCountLinearCoefficient K := by
  unfold completedZetaSelectedHeightZeroCountLinearCoefficient
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (zero_le_one.trans
        (one_le_completedZetaMovingCenterLinearCoefficient K 9)))
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightZeroCountBound_le_linear
    {A : ℝ} (hA : 6 ≤ A) :
    completedZetaSelectedHeightZeroCountBound K A ≤
      completedZetaSelectedHeightZeroCountLinearCoefficient K * (A + 1) := by
  have hcenter :=
    completedZetaMovingCenterLogLinearBound_le K 9 (A + 1 / 2)
  have habs : |A + 1 / 2| = A + 1 / 2 := abs_of_pos (by linarith)
  rw [habs] at hcenter
  have hlogpos : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  unfold completedZetaSelectedHeightZeroCountBound
  unfold completedZetaSelectedHeightZeroCountLinearCoefficient
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hlogpos).2
  nlinarith [mul_nonneg
    (zero_le_one.trans (one_le_completedZetaMovingCenterLinearCoefficient K 9))
    (show 0 ≤ A + 1 by linarith)]

/-- The linear coefficient controlling inverse zero separation at a selected height. -/
noncomputable def completedZetaSelectedHeightSeparationInvLinearCoefficient : ℝ :=
  4 * (completedZetaSelectedHeightZeroCountLinearCoefficient K + 1)

omit [IsTotallyComplex K] in
private theorem completedZetaSelectedHeightSeparationInvLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightSeparationInvLinearCoefficient K := by
  unfold completedZetaSelectedHeightSeparationInvLinearCoefficient
  exact mul_nonneg (by norm_num)
    (by
      have :=
        completedZetaSelectedHeightZeroCountLinearCoefficient_nonneg K
      linarith)

theorem inv_completedZetaSelectedHeightSeparation_le_linear
    {A : ℝ} (hA : 6 ≤ A) :
    (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
      completedZetaSelectedHeightSeparationInvLinearCoefficient K * (A + 1) := by
  have hInv := inv_completedZetaSelectedHeightSeparation_le K hA
  have hCount :=
    completedZetaSelectedHeightZeroCountBound_le_linear K hA
  unfold completedZetaSelectedHeightSeparationInvLinearCoefficient
  grind

/-- The linear coefficient controlling the completed zeta function at a selected center. -/
noncomputable def completedZetaSelectedHeightCenterLinearCoefficient : ℝ :=
  2 * completedZetaMovingCenterLinearCoefficient K 6

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightCenterLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K := by
  unfold completedZetaSelectedHeightCenterLinearCoefficient
  exact mul_nonneg (by norm_num)
    (zero_le_one.trans
      (one_le_completedZetaMovingCenterLinearCoefficient K 6))

omit [IsTotallyComplex K] in
private theorem completedZetaCenterLogLinearBound_selected_le
    {A T : ℝ} (hA : 6 ≤ A) (hAT : A < T) (hTA : T < A + 1) :
    completedZetaCenterLogLinearBound K T ≤
        completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) ∧
      completedZetaCenterLogLinearBound K (-T) ≤
        completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) := by
  have hTpos : 0 < T := by linarith
  have hplus :=
    completedZetaMovingCenterLogLinearBound_le K 6 T
  have hminus :=
    completedZetaMovingCenterLogLinearBound_le K 6 (-T)
  rw [← completedZetaCenterLogLinearBound_eq_moving K] at hplus hminus
  rw [abs_of_pos hTpos] at hplus
  rw [abs_neg, abs_of_pos hTpos] at hminus
  unfold completedZetaSelectedHeightCenterLinearCoefficient
  constructor
  · exact hplus.trans (by
      rw [show
        2 * completedZetaMovingCenterLinearCoefficient K 6 * (A + 1) =
          completedZetaMovingCenterLinearCoefficient K 6 * (2 * (A + 1)) by
        ring]
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact (zero_le_one.trans
          (one_le_completedZetaMovingCenterLinearCoefficient K 6)))
  · exact hminus.trans (by
      rw [show
        2 * completedZetaMovingCenterLinearCoefficient K 6 * (A + 1) =
          completedZetaMovingCenterLinearCoefficient K 6 * (2 * (A + 1)) by
        ring]
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact (zero_le_one.trans
          (one_le_completedZetaMovingCenterLinearCoefficient K 6)))

/-- The quadratic coefficient controlling the completed-zeta logarithmic derivative
at a selected height. -/
noncomputable def completedZetaSelectedHeightLogDerivativeQuadraticCoefficient : ℝ :=
  completedZetaSelectedHeightCenterLinearCoefficient K *
    (completedZetaCanonicalJensenCoefficient *
        completedZetaSelectedHeightSeparationInvLinearCoefficient K +
      completedZetaCanonicalJensenCoefficient + 32)

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K := by
  unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
  exact mul_nonneg
    (completedZetaSelectedHeightCenterLinearCoefficient_nonneg K)
    (by
      have hJ := completedZetaCanonicalJensenCoefficient_pos.le
      have hD :=
        completedZetaSelectedHeightSeparationInvLinearCoefficient_nonneg K
      positivity)

theorem exists_height_norm_logDeriv_poleClearedCompletedZeta_le_quadratic
    {A : ℝ} (hA : 6 ≤ A) :
    ∃ T : ℝ, A < T ∧ T < A + 1 ∧
      ∀ x ∈ Icc (-1 : ℝ) 5,
        (poleClearedCompletedDedekindZetaContinuation K (x + T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x + T * I)‖ ≤
          completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
            (A + 1) ^ 2) ∧
        (poleClearedCompletedDedekindZetaContinuation K (x - T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x - T * I)‖ ≤
          completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
            (A + 1) ^ 2) := by
  obtain ⟨T, hAT, hTA, hbound⟩ :=
    exists_height_norm_logDeriv_poleClearedCompletedZeta_le K hA
  refine ⟨T, hAT, hTA, ?_⟩
  have hCenter :=
    completedZetaCenterLogLinearBound_selected_le K hA hAT hTA
  have hInv :=
    inv_completedZetaSelectedHeightSeparation_le_linear K hA
  have hSepPos :=
    completedZetaSelectedHeightSeparation_pos K A
  have hJ :
      0 ≤ completedZetaCanonicalJensenCoefficient :=
    completedZetaCanonicalJensenCoefficient_pos.le
  have hC :
      0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K :=
    completedZetaSelectedHeightCenterLinearCoefficient_nonneg K
  intro x hx
  rcases hbound x hx with ⟨⟨hfplus, hplus⟩, ⟨hfminus, hminus⟩⟩
  have hA1 : 1 ≤ A + 1 := by linarith
  have hCenterUpper :
      0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) :=
    mul_nonneg hC (zero_le_one.trans hA1)
  have hInvNonneg :
      0 ≤ (completedZetaSelectedHeightSeparation K A)⁻¹ :=
    inv_nonneg.mpr hSepPos.le
  refine ⟨⟨hfplus, ?_⟩, ⟨hfminus, ?_⟩⟩
  · apply hplus.trans
    rw [div_eq_mul_inv]
    have hprod :
        completedZetaCenterLogLinearBound K T *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
          (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparationInvLinearCoefficient K *
              (A + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hCenter.1 hJ
      · grind
      · simp_all
      · exact mul_nonneg hCenterUpper hJ
    have hlinJ :
        completedZetaCenterLogLinearBound K T *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient :=
      mul_le_mul_of_nonneg_right hCenter.1 hJ
    have hlin32 :
        32 * completedZetaCenterLogLinearBound K T ≤
          32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
      mul_le_mul_of_nonneg_left hCenter.1 (by norm_num)
    have hu : A + 1 ≤ (A + 1) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ A + 1 by linarith)
        (show 0 ≤ A by linarith)]
    have hlinJQ :
        completedZetaCenterLogLinearBound K T *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) ^ 2 := by
      calc
        _ ≤ completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient := hlinJ
        _ = completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg hC hJ)
    have hlin32Q :
        32 * completedZetaCenterLogLinearBound K T ≤
          32 * completedZetaSelectedHeightCenterLinearCoefficient K *
            (A + 1) ^ 2 := by
      calc
        _ ≤ 32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
          hlin32
        _ = (32 * completedZetaSelectedHeightCenterLinearCoefficient K) *
            (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num) hC)
    unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
    grind
  · apply hminus.trans
    rw [div_eq_mul_inv]
    have hprod :
        completedZetaCenterLogLinearBound K (-T) *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
          (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparationInvLinearCoefficient K *
              (A + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hCenter.2 hJ
      · grind
      · simp_all
      · exact mul_nonneg hCenterUpper hJ
    have hlinJ :
        completedZetaCenterLogLinearBound K (-T) *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient :=
      mul_le_mul_of_nonneg_right hCenter.2 hJ
    have hlin32 :
        32 * completedZetaCenterLogLinearBound K (-T) ≤
          32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
      mul_le_mul_of_nonneg_left hCenter.2 (by norm_num)
    have hu : A + 1 ≤ (A + 1) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ A + 1 by linarith)
        (show 0 ≤ A by linarith)]
    have hlinJQ :
        completedZetaCenterLogLinearBound K (-T) *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) ^ 2 := by
      calc
        _ ≤ completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient := hlinJ
        _ = completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg hC hJ)
    have hlin32Q :
        32 * completedZetaCenterLogLinearBound K (-T) ≤
          32 * completedZetaSelectedHeightCenterLinearCoefficient K *
            (A + 1) ^ 2 := by
      calc
        _ ≤ 32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
          hlin32
        _ = (32 * completedZetaSelectedHeightCenterLinearCoefficient K) *
            (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num) hC)
    unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
    grind

end NumberField.Odlyzko

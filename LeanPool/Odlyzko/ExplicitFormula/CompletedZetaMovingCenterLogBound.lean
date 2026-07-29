/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaCenterLogBound

/-!
# Completed Zeta Moving Center Log Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta moving vertical coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingVerticalCoefficient (R : ℝ) : ℝ :=
  max 1
    (poleClearedCompletedDedekindZetaVerticalBound K
      (2 - |R|) (2 + |R|))

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingVerticalCoefficient (R : ℝ) :
    1 ≤ completedZetaMovingVerticalCoefficient K R :=
  le_max_left _ _

/-- A completed zeta moving center log linear bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterLogLinearBound
    (R t : ℝ) : ℝ :=
  max 1 <|
    completedZetaMovingVerticalCoefficient K R +
      2 * (1 + |t| + |R|) +
      Real.log (dedekindZetaInverseVerticalMajorant K) -
      (nrComplexPlaces K : ℝ) / 2 *
        Real.log complexPlaceGammaVerticalLowerConstant +
      (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t|

omit [IsTotallyComplex K] in
theorem log_completedZetaMovingCircleBound_le
    (R t : ℝ) :
    Real.log (completedZetaMovingCircleBound K R t) ≤
      completedZetaMovingVerticalCoefficient K R +
        2 * (1 + |t| + |R|) := by
  let V : ℝ :=
    poleClearedCompletedDedekindZetaVerticalBound K
      (2 - |R|) (2 + |R|)
  let D : ℝ := completedZetaMovingVerticalCoefficient K R
  let Q : ℝ := 1 + |t| + |R|
  have hD : 1 ≤ D := one_le_completedZetaMovingVerticalCoefficient K R
  have hVD : V ≤ D := le_max_right _ _
  have hQ : 1 ≤ Q := by grind
  have hmajor :
      completedZetaMovingCircleBound K R t ≤ D * Q ^ 2 := by
    change max 1 (V * Q ^ 2) ≤ D * Q ^ 2
    apply max_le
    · nlinarith [sq_nonneg Q]
    · exact mul_le_mul_of_nonneg_right hVD (sq_nonneg Q)
  calc
    Real.log (completedZetaMovingCircleBound K R t) ≤
        Real.log (D * Q ^ 2) :=
      Real.log_le_log
        (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaMovingCircleBound K R t)) hmajor
    _ = Real.log D + 2 * Real.log Q := by
      rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hD))
        (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hQ))),
        Real.log_pow]
      norm_num
    _ ≤ D + 2 * Q := by
      gcongr
      · exact Real.log_le_self (zero_le_one.trans hD)
      · exact Real.log_le_self (zero_le_one.trans hQ)
    _ = completedZetaMovingVerticalCoefficient K R +
          2 * (1 + |t| + |R|) := rfl

theorem completedZeta_moving_center_log_gap_le
    {R t : ℝ} (ht : 1 ≤ |t|) :
    Real.log (completedZetaMovingCircleBound K R t) -
        Real.log
          ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤
      completedZetaMovingCenterLogLinearBound K R t := by
  apply le_trans ?_ (le_max_right _ _)
  linarith [log_completedZetaMovingCircleBound_le K R t,
    neg_log_norm_poleClearedCompletedZeta_two_add_mul_I_le K ht]

/-- A completed zeta moving center constant part used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterConstantPart (R : ℝ) : ℝ :=
  completedZetaMovingVerticalCoefficient K R +
    2 * (1 + |R|) +
    |Real.log (dedekindZetaInverseVerticalMajorant K)| +
    (nrComplexPlaces K : ℝ) / 2 *
      |Real.log complexPlaceGammaVerticalLowerConstant|

/-- A completed zeta moving center slope used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterSlope : ℝ :=
  2 + (nrComplexPlaces K : ℝ) / 2 * Real.pi

/-- A completed zeta moving center linear coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterLinearCoefficient (R : ℝ) : ℝ :=
  1 + completedZetaMovingCenterConstantPart K R +
    completedZetaMovingCenterSlope K

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingCenterLinearCoefficient (R : ℝ) :
    1 ≤ completedZetaMovingCenterLinearCoefficient K R := by
  have hD : 0 ≤ completedZetaMovingVerticalCoefficient K R :=
    zero_le_one.trans (one_le_completedZetaMovingVerticalCoefficient K R)
  unfold completedZetaMovingCenterLinearCoefficient
  unfold completedZetaMovingCenterConstantPart
  unfold completedZetaMovingCenterSlope
  nlinarith [abs_nonneg R,
    abs_nonneg (Real.log (dedekindZetaInverseVerticalMajorant K)),
    mul_nonneg (by positivity : 0 ≤ (nrComplexPlaces K : ℝ) / 2)
      (abs_nonneg (Real.log complexPlaceGammaVerticalLowerConstant)),
    mul_nonneg (by positivity : 0 ≤ (nrComplexPlaces K : ℝ) / 2)
      Real.pi_pos.le]

omit [IsTotallyComplex K] in
theorem completedZetaMovingCenterLogLinearBound_le
    (R t : ℝ) :
    completedZetaMovingCenterLogLinearBound K R t ≤
      completedZetaMovingCenterLinearCoefficient K R * (1 + |t|) := by
  let P := completedZetaMovingCenterConstantPart K R
  let S := completedZetaMovingCenterSlope K
  let C := completedZetaMovingCenterLinearCoefficient K R
  have hP : 0 ≤ P := by
    dsimp [P, completedZetaMovingCenterConstantPart]
    have hD : 0 ≤ completedZetaMovingVerticalCoefficient K R :=
      zero_le_one.trans (one_le_completedZetaMovingVerticalCoefficient K R)
    positivity
  have hS : 0 ≤ S := by
    dsimp [S, completedZetaMovingCenterSlope]
    positivity
  have hC : C = 1 + P + S := by rfl
  have hraw :
      completedZetaMovingVerticalCoefficient K R +
          2 * (1 + |t| + |R|) +
          Real.log (dedekindZetaInverseVerticalMajorant K) -
          (nrComplexPlaces K : ℝ) / 2 *
            Real.log complexPlaceGammaVerticalLowerConstant +
          (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t| ≤
        P + S * |t| := by
    dsimp [P, S, completedZetaMovingCenterConstantPart,
      completedZetaMovingCenterSlope]
    have hlogC :
        Real.log (dedekindZetaInverseVerticalMajorant K) ≤
          |Real.log (dedekindZetaInverseVerticalMajorant K)| :=
      le_abs_self _
    have hlogG :
        -Real.log complexPlaceGammaVerticalLowerConstant ≤
          |Real.log complexPlaceGammaVerticalLowerConstant| := by grind
    nlinarith [mul_le_mul_of_nonneg_left hlogG (by positivity :
      0 ≤ (nrComplexPlaces K : ℝ) / 2)]
  unfold completedZetaMovingCenterLogLinearBound
  change max 1 _ ≤ C * (1 + |t|)
  apply max_le
  · rw [hC]
    nlinarith [abs_nonneg t]
  · rw [hC]
    calc
      _ ≤ P + S * |t| := hraw
      _ ≤ (1 + P + S) * (1 + |t|) := by
        nlinarith [abs_nonneg t, mul_nonneg hP (abs_nonneg t)]

omit [IsTotallyComplex K] in
theorem completedZetaCenterLogLinearBound_eq_moving (t : ℝ) :
    completedZetaCenterLogLinearBound K t =
      completedZetaMovingCenterLogLinearBound K 6 t := by
  unfold completedZetaCenterLogLinearBound
  unfold completedZetaCenterLogLinearExpression
  unfold completedZetaRadiusSixVerticalCoefficient
  unfold completedZetaMovingCenterLogLinearBound
  unfold completedZetaMovingVerticalCoefficient
  grind

end NumberField.Odlyzko

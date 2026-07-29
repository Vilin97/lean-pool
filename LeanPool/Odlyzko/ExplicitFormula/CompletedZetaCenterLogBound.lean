/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.VerticalLowerBound
public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaCanonicalLogDerivative

/-!
# Completed Zeta Center Log Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta radius six vertical coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaRadiusSixVerticalCoefficient : ℝ :=
  max 1 (poleClearedCompletedDedekindZetaVerticalBound K (-4) 8)

/-- A completed zeta center log linear expression used in the Odlyzko-bound argument. -/
noncomputable def completedZetaCenterLogLinearExpression (t : ℝ) : ℝ :=
  completedZetaRadiusSixVerticalCoefficient K + 2 * (7 + |t|) +
    Real.log (dedekindZetaInverseVerticalMajorant K) -
    (nrComplexPlaces K : ℝ) / 2 *
      Real.log complexPlaceGammaVerticalLowerConstant +
    (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t|

/-- A completed zeta center log linear bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaCenterLogLinearBound (t : ℝ) : ℝ :=
  max 1 (completedZetaCenterLogLinearExpression K t)

omit [IsTotallyComplex K] in
theorem one_le_completedZetaCenterLogLinearBound (t : ℝ) :
    1 ≤ completedZetaCenterLogLinearBound K t :=
  le_max_left _ _

private theorem neg_log_le_of_pow_mul_exp_le_sq
    {g C X u : ℝ} {n : ℕ}
    (hg : 0 < g) (hC : 0 < C) (hX : 0 < X)
    (h : (g * Real.exp (-u)) ^ n ≤ C ^ 2 * X ^ 2) :
    -Real.log X ≤
      Real.log C - (n : ℝ) / 2 * Real.log g + (n : ℝ) / 2 * u := by
  have hleft : 0 < (g * Real.exp (-u)) ^ n := by positivity
  have hlog := Real.log_le_log hleft h
  rw [Real.log_pow, Real.log_mul (ne_of_gt hg) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, Real.log_mul (pow_ne_zero _ (ne_of_gt hC))
      (pow_ne_zero _ (ne_of_gt hX)), Real.log_pow, Real.log_pow] at hlog
  grind

theorem neg_log_norm_poleClearedCompletedZeta_two_add_mul_I_le
    {t : ℝ} (ht : 1 ≤ |t|) :
    -Real.log
        ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤
      Real.log (dedekindZetaInverseVerticalMajorant K) -
        (nrComplexPlaces K : ℝ) / 2 *
          Real.log complexPlaceGammaVerticalLowerConstant +
        (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t| := by
  have hX : 0 <
      ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ :=
    norm_pos_iff.mpr
      (poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
        (by simp))
  have hlower :
      (complexPlaceGammaVerticalLowerConstant *
          Real.exp (-(Real.pi * |t|))) ^ nrComplexPlaces K ≤
        dedekindZetaInverseVerticalMajorant K ^ 2 *
          ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ^ 2 := by
    simpa [mul_assoc] using
      complexGammaExponential_pow_le_majorant_sq_mul_completedZeta_sq K ht
  have h := neg_log_le_of_pow_mul_exp_le_sq
    (g := complexPlaceGammaVerticalLowerConstant)
    (C := dedekindZetaInverseVerticalMajorant K)
    (X := ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖)
    (u := Real.pi * |t|) (n := nrComplexPlaces K)
    complexPlaceGammaVerticalLowerConstant_pos
    (lt_of_lt_of_le zero_lt_one
      (one_le_dedekindZetaInverseVerticalMajorant K))
    hX hlower
  grind

omit [IsTotallyComplex K] in
theorem log_completedZetaMovingCircleBound_six_le (t : ℝ) :
    Real.log (completedZetaMovingCircleBound K 6 t) ≤
      completedZetaRadiusSixVerticalCoefficient K + 2 * (7 + |t|) := by
  let V : ℝ := poleClearedCompletedDedekindZetaVerticalBound K (-4) 8
  let D : ℝ := completedZetaRadiusSixVerticalCoefficient K
  let Q : ℝ := 7 + |t|
  have hD : 1 ≤ D := le_max_left _ _
  have hVD : V ≤ D := le_max_right _ _
  have hQ : 1 ≤ Q := by grind
  have hmajor :
      completedZetaMovingCircleBound K 6 t ≤ D * Q ^ 2 := by
    have hraw : max 1 (V * Q ^ 2) ≤ D * Q ^ 2 := by
      apply max_le
      · nlinarith [sq_nonneg Q]
      · apply mul_le_mul_of_nonneg_right hVD
        positivity
    simpa [completedZetaMovingCircleBound, V, Q,
      show (2 : ℝ) - 6 = -4 by norm_num,
      show (2 : ℝ) + 6 = 8 by norm_num,
      show 1 + |t| + 6 = 7 + |t| by ring] using hraw
  calc
    Real.log (completedZetaMovingCircleBound K 6 t) ≤
        Real.log (D * Q ^ 2) :=
      Real.log_le_log
        (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaMovingCircleBound K 6 t)) hmajor
    _ = Real.log D + 2 * Real.log Q := by
      rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hD))
        (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hQ))),
        Real.log_pow]
      norm_num
    _ ≤ D + 2 * Q := by
      gcongr
      · exact Real.log_le_self (zero_le_one.trans hD)
      · exact Real.log_le_self (zero_le_one.trans hQ)
    _ = completedZetaRadiusSixVerticalCoefficient K + 2 * (7 + |t|) := rfl

theorem completedZeta_center_log_gap_le
    {t : ℝ} (ht : 1 ≤ |t|) :
    Real.log (completedZetaMovingCircleBound K 6 t) -
        Real.log
          ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤
      completedZetaCenterLogLinearBound K t := by
  apply le_trans ?_ (le_max_right _ _)
  dsimp [completedZetaCenterLogLinearExpression]
  linarith [log_completedZetaMovingCircleBound_six_le K t,
    neg_log_norm_poleClearedCompletedZeta_two_add_mul_I_le K ht]

end NumberField.Odlyzko

/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedSeries
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic evaluation of an `ℓ¹` coefficient sequence

An `ℓ¹` sequence defines a power series on the open unit disc.  More
importantly for preparation, evaluation is jointly analytic in the coefficient
sequence and the scalar variable at every point whose scalar coordinate is
zero.  The proof packages the coordinate evaluations into an operator-valued
formal multilinear series with radius at least one.
-/

open scoped ENNReal NNReal Topology
noncomputable section


namespace ClassicalComplexWPT

/-- Complex `ℓ¹` sequences, viewed as coefficients of one-variable power series. -/
abbrev L1Sequence := L1Coeff ℕ

/-- Evaluation of the `k`-th coefficient as a continuous linear functional. -/
noncomputable def coefficientEval (k : ℕ) : L1Sequence →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 k

theorem norm_coefficientEval_le (k : ℕ) : ‖coefficientEval k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖a k‖ ≤ 1 * ‖a‖
  simpa using lp.norm_apply_le_norm (by norm_num) a k

/-- The operator-valued series `w ↦ (a ↦ ∑ k, a k * w^k)`. -/
noncomputable def l1OperatorSeries :
    FormalMultilinearSeries ℂ ℂ (L1Sequence →L[ℂ] ℂ) :=
  fun k ↦ (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).smulRight (coefficientEval k)

theorem norm_l1OperatorSeries_le (k : ℕ) : ‖l1OperatorSeries k‖ ≤ 1 := by
  rw [l1OperatorSeries, ContinuousMultilinearMap.norm_smulRight,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, one_mul]
  exact norm_coefficientEval_le k

theorem one_le_radius_l1OperatorSeries : 1 ≤ l1OperatorSeries.radius := by
  apply l1OperatorSeries.le_radius_of_bound 1
  intro k
  simpa using norm_l1OperatorSeries_le k

/-- The continuous-linear evaluation operator at `w`. -/
noncomputable def l1EvalOperator (w : ℂ) : L1Sequence →L[ℂ] ℂ :=
  l1OperatorSeries.sum w

theorem analyticAt_l1EvalOperator : AnalyticAt ℂ l1EvalOperator 0 := by
  exact (l1OperatorSeries.hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) one_le_radius_l1OperatorSeries)).analyticAt

/-- Evaluate an `ℓ¹` sequence as a one-variable power series. -/
noncomputable def evalL1PowerSeries (a : L1Sequence) (w : ℂ) : ℂ :=
  l1EvalOperator w a

/-- Evaluation is jointly analytic in the sequence and scalar at scalar coordinate zero. -/
theorem analyticAt_evalL1PowerSeries (a : L1Sequence) :
    AnalyticAt ℂ (fun x : L1Sequence × ℂ ↦ evalL1PowerSeries x.1 x.2) (a, 0) := by
  let app : (L1Sequence →L[ℂ] ℂ) →L[ℂ] L1Sequence →L[ℂ] ℂ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℂ ℂ)
  have happ : AnalyticAt ℂ (fun x : (L1Sequence →L[ℂ] ℂ) × L1Sequence ↦ app x.1 x.2)
      (l1EvalOperator 0, a) := app.analyticAt_bilinear _
  have hop : AnalyticAt ℂ (fun x : L1Sequence × ℂ ↦ l1EvalOperator x.2) (a, 0) :=
    analyticAt_l1EvalOperator.comp (f := fun x : L1Sequence × ℂ ↦ x.2) analyticAt_snd
  exact happ.comp₂ hop analyticAt_fst

/-- An analytic family of `ℓ¹` coefficients evaluates to a jointly analytic function. -/
theorem AnalyticAt.evalL1PowerSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : E → L1Sequence} (hq : AnalyticAt ℂ q 0) (s : ℂ) :
    AnalyticAt ℂ
      (fun x : E × ℂ ↦ evalL1PowerSeries (q x.1) (s * x.2)) 0 := by
  have hq' : AnalyticAt ℂ (fun x : E × ℂ ↦ q x.1) 0 :=
    hq.comp (f := fun x : E × ℂ ↦ x.1) analyticAt_fst
  have hw' : AnalyticAt ℂ (fun x : E × ℂ ↦ s * x.2) 0 :=
    analyticAt_const.mul analyticAt_snd
  have hpair : AnalyticAt ℂ
      (fun x : E × ℂ ↦ (q x.1, s * x.2)) 0 := hq'.prod hw'
  have hout : AnalyticAt ℂ
      (fun x : L1Sequence × ℂ ↦ ClassicalComplexWPT.evalL1PowerSeries x.1 x.2)
      ((fun x : E × ℂ ↦ (q x.1, s * x.2)) 0) := by
    simpa using analyticAt_evalL1PowerSeries (q 0)
  have hcomp := hout.comp (f := fun x : E × ℂ ↦ (q x.1, s * x.2)) hpair
  simpa [Function.comp_def] using hcomp

/-- Inside the unit disc, bundled evaluation is the usual scalar power-series sum. -/
theorem evalL1PowerSeries_eq_tsum (a : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries a w = ∑' k : ℕ, a k * w ^ k := by
  have hball : w ∈ Metric.eball (0 : ℂ) l1OperatorSeries.radius := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact (show ENNReal.ofReal ‖w‖ < 1 from ENNReal.ofReal_lt_one.mpr hw).trans_le
      one_le_radius_l1OperatorSeries
  let app : (L1Sequence →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ a
  have hsum := (l1OperatorSeries.summable hball).hasSum.mapL app
  calc
    evalL1PowerSeries a w = ∑' k : ℕ, l1OperatorSeries k (fun _ ↦ w) a := by
      simpa [evalL1PowerSeries, l1EvalOperator, FormalMultilinearSeries.sum, app] using
        hsum.tsum_eq.symm
    _ = ∑' k : ℕ, a k * w ^ k := by
      congr 1
      funext k
      rw [l1OperatorSeries]
      simp only [ContinuousMultilinearMap.smulRight_apply,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate]
      change w ^ k • coefficientEval k a = a k * w ^ k
      rw [show coefficientEval k a = a k from rfl]
      simp [smul_eq_mul, mul_comm]

lemma summable_norm_l1_mul_pow (a : L1Sequence) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k : ℕ ↦ ‖a k * w ^ k‖) := by
  exact (L1Coeff.summable_norm a).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw))

lemma summable_l1_mul_pow (a : L1Sequence) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k : ℕ ↦ a k * w ^ k) :=
  Summable.of_norm (summable_norm_l1_mul_pow a hw)

/-- Evaluation turns `ℓ¹` convolution into multiplication inside the unit disc. -/
theorem evalL1PowerSeries_convolution (a b : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (convolution a b) w =
      evalL1PowerSeries a w * evalL1PowerSeries b w := by
  rw [evalL1PowerSeries_eq_tsum _ hw, evalL1PowerSeries_eq_tsum _ hw,
    evalL1PowerSeries_eq_tsum _ hw]
  let A : ℕ → ℂ := fun k ↦ a k * w ^ k
  let B : ℕ → ℂ := fun k ↦ b k * w ^ k
  have hA : Summable A := summable_l1_mul_pow a hw.le
  have hB : Summable B := summable_l1_mul_pow b hw.le
  have hAB : Summable (fun x : ℕ × ℕ ↦ A x.1 * B x.2) :=
    summable_mul_of_summable_norm
      (summable_norm_l1_mul_pow a hw.le) (summable_norm_l1_mul_pow b hw.le)
  rw [hA.tsum_mul_tsum_eq_tsum_sum_antidiagonal hB hAB]
  apply tsum_congr
  intro n
  rw [convolution_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  dsimp only [A, B]
  subst n
  rw [pow_add]
  ring

end ClassicalComplexWPT

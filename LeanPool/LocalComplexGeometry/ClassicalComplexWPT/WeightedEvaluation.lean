/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedCoefficientMap
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1PowerSeries

/-!
# Reconstruction from weighted `ℓ¹` coefficients

Evaluating the analytic weighted moving-coefficient map at `r⁻¹ w`
reconstructs the original ambient formal multilinear series wherever the
change-of-origin expansion converges.  A second theorem identifies the result
with any function represented by that series on a ball.
-/


open scoped ENNReal NNReal Topology
noncomputable section

namespace ClassicalComplexWPT

theorem eval_weightedCoefficientSeries_eq {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (z : Base n) (w : ℂ)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzw : (‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ : ℝ≥0∞) < p.radius)
    (hw : ‖w‖ < r) :
    evalL1PowerSeries ((weightedCoefficientSeries p r).sum z) ((r : ℂ)⁻¹ * w) =
      p.sum (z, w) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hscaled : ‖(r : ℂ)⁻¹ * w‖ < 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg]
    exact (inv_mul_lt_one₀ (by exact_mod_cast hr0)).2 (by exact_mod_cast hw)
  rw [evalL1PowerSeries_eq_tsum _ hscaled]
  have hzp : (z, (0 : ℂ)) ∈ Metric.eball (0 : Ambient n) p.radius := by
    rw [mem_eball_zero_iff]
    exact (show (‖(z, (0 : ℂ))‖₊ : ℝ≥0∞) ≤
        ‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ by
      exact le_add_right le_rfl).trans_lt hzw
  calc
    (∑' k : ℕ, (weightedCoefficientSeries p r).sum z k * ((r : ℂ)⁻¹ * w) ^ k) =
        ∑' k : ℕ, p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n) * w ^ k := by
      apply tsum_congr
      intro k
      rw [weightedCoefficientSeries_sum_apply_lastTaylorCoefficient p r z k hrp hzq hzp]
      simp only [lastTaylorCoefficient]
      let c : ℂ := p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n)
      change ((r : ℂ) ^ k * c) * ((r : ℂ)⁻¹ * w) ^ k = c * w ^ k
      rw [mul_pow]
      calc
        ((r : ℂ) ^ k * c) * ((r : ℂ)⁻¹ ^ k * w ^ k) =
            (((r : ℂ) ^ k * (r : ℂ)⁻¹ ^ k) * c) * w ^ k := by ring
        _ = c * w ^ k := by rw [← mul_pow]; simp [hrC]
    _ = (p.changeOrigin (z, 0)).sum (0, w) := by
      unfold FormalMultilinearSeries.sum
      apply tsum_congr
      intro k
      rw [show ((0 : Base n), w) = w • lastDirection n by
        ext <;> simp [lastDirection]]
      rw [(p.changeOrigin (z, 0) k).map_smul_univ]
      simp [Finset.prod_const, smul_eq_mul, mul_comm]
    _ = p.sum (z, w) := by
      rw [p.changeOrigin_eval hzw]
      congr 1
      ext <;> simp

/-- The weighted coefficient family can be evaluated analytically in the base
and distinguished variables.  This is the specialization of
`AnalyticAt.evalL1PowerSeries` used for analytic quotients and units. -/
theorem analyticAt_eval_weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius) :
    AnalyticAt ℂ (fun x : Base n × ℂ ↦
      evalL1PowerSeries ((weightedCoefficientSeries p r).sum x.1)
        ((r : ℂ)⁻¹ * x.2)) 0 :=
  ClassicalComplexWPT.AnalyticAt.evalL1PowerSeries
    (analyticAt_weightedCoefficientSeries_sum p r hrp) (r : ℂ)⁻¹

/-- If `p` represents `f` on a ball, weighted evaluation reconstructs `f` on
the explicit common convergence region. -/
theorem eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall {n : ℕ}
    {f : Ambient n → ℂ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (r : ℝ≥0) {ρ : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 ρ)
    (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (z : Base n) (w : ℂ)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzw : (‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ : ℝ≥0∞) < ρ)
    (hw : ‖w‖ < r) :
    evalL1PowerSeries ((weightedCoefficientSeries p r).sum z) ((r : ℂ)⁻¹ * w) =
      f (z, w) := by
  rw [eval_weightedCoefficientSeries_eq p r hr0 hrp z w hzq
    (hzw.trans_le hp.r_le) hw]
  symm
  have hball : (z, w) ∈ Metric.eball (0 : Ambient n) ρ := by
    rw [mem_eball_zero_iff]
    have hpair : (‖(z, w)‖₊ : ℝ≥0∞) ≤
      ‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ := by
      rw [show (z, w) = (z, (0 : ℂ)) + ((0 : Base n), w) by ext <;> simp]
      exact_mod_cast nnnorm_add_le (z, (0 : ℂ)) ((0 : Base n), w)
    exact hpair.trans_lt hzw
  simpa only [zero_add] using hp.sum hball

end ClassicalComplexWPT

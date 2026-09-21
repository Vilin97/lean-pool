/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Complex polynomial approximation on closed disks

This file proves the disk model of the polynomial-approximation input used by
the Crouzeix--Palencia smooth-exhaustion assembly.  Boundary approximation is
obtained by radially contracting into the open disk and taking a diagonal
sequence of Taylor partial sums.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

open Complex Filter Metric Set
open scoped Topology

private noncomputable def formalPartialSumPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n,
    Polynomial.C (p k (fun _ => 1)) * Polynomial.X ^ k

private theorem eval_formalPartialSumPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (z : ℂ) :
    Polynomial.eval z (formalPartialSumPolynomial p n) = p.partialSum n z := by
  unfold formalPartialSumPolynomial FormalMultilinearSeries.partialSum
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [show p k (fun _ : Fin k => z) = z ^ k * p k (fun _ => 1) by
    simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin] using
      (p k).map_smul_univ (fun _ => z) (fun _ => 1)]
  exact mul_comm _ _

private noncomputable def radialFactor (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

private theorem radialFactor_nonneg (n : ℕ) : 0 ≤ radialFactor n := by
  unfold radialFactor
  positivity

private theorem radialFactor_lt_one (n : ℕ) : radialFactor n < 1 := by
  unfold radialFactor
  rw [div_lt_one]
  · linarith only
  · positivity

private theorem one_sub_radialFactor (n : ℕ) :
    1 - radialFactor n = 1 / ((n : ℝ) + 1) := by
  unfold radialFactor
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hn]
  ring

private noncomputable def radialMap (c : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  c + (radialFactor n : ℂ) * (z - c)

private theorem radialMap_mem_closedBall (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (n : ℕ) {z : ℂ} (hz : z ∈ Metric.closedBall c R) :
    radialMap c n z ∈ Metric.closedBall c R := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
  have hsub : radialMap c n z - c = (radialFactor n : ℂ) * (z - c) := by
    unfold radialMap
    ring
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (radialFactor_nonneg n)]
  calc
    radialFactor n * ‖z - c‖ ≤ radialFactor n * R :=
      mul_le_mul_of_nonneg_left hz (radialFactor_nonneg n)
    _ ≤ 1 * R := mul_le_mul_of_nonneg_right (radialFactor_lt_one n).le hR
    _ = R := one_mul R

private theorem tendstoUniformlyOn_radialMap (c : ℂ) (R : ℝ) :
    TendstoUniformlyOn (fun n z => radialMap c n z) id atTop
      (Metric.closedBall c R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hzero : Tendsto
      (fun n : ℕ => (1 / ((n : ℝ) + 1)) * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const R
  have hevent := hzero.eventually (gt_mem_nhds hε)
  filter_upwards [hevent] with n hn z hz
  have hz' : ‖z - c‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hsub : z - radialMap c n z =
      ((1 - radialFactor n : ℝ) : ℂ) * (z - c) := by
    unfold radialMap
    push_cast
    ring
  rw [id_eq, dist_eq_norm, hsub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by
      rw [one_sub_radialFactor]
      positivity), one_sub_radialFactor]
  exact (mul_le_mul_of_nonneg_left hz' (by positivity)).trans_lt hn

private noncomputable def radialTaylorPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n k : ℕ) (c : ℂ) : Polynomial ℂ :=
  (formalPartialSumPolynomial p k).comp
    (Polynomial.C (radialFactor n : ℂ) * (Polynomial.X - Polynomial.C c))

private theorem eval_radialTaylorPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n k : ℕ) (c z : ℂ) :
    Polynomial.eval z (radialTaylorPolynomial p n k c) =
      p.partialSum k ((radialFactor n : ℂ) * (z - c)) := by
  rw [radialTaylorPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    eval_formalPartialSumPolynomial]
  simp only [Polynomial.eval_C]

/-- Every complex function differentiable on an open disk and continuous on
its closure is a compact-uniform limit of complex polynomials. -/
theorem SmoothJordanDomain.ball_hasMergelyanPolynomialApproximation
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    (SmoothJordanDomain.ball c R hR).HasMergelyanPolynomialApproximation := by
  intro f hf
  let Rnn : NNReal := ⟨R, hR.le⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f c Rnn
  have hp : HasFPowerSeriesOnBall f p c Rnn := by
    exact hf.hasFPowerSeriesOnBall (show 0 < Rnn from hR)
  have hradial : TendstoUniformlyOn
      (fun n z => f (radialMap c n z)) f atTop (Metric.closedBall c R) := by
    have huc : UniformContinuousOn f (Metric.closedBall c R) :=
      (isCompact_closedBall c R).uniformContinuousOn_of_continuous
        hf.continuousOn_ball
    simpa only [id_eq] using
      huc.comp_tendstoUniformlyOn_eventually
        (Eventually.of_forall fun n z hz =>
          radialMap_mem_closedBall c hR.le n hz)
        (fun _z hz => hz) (tendstoUniformlyOn_radialMap c R)
  have hpartial : ∀ n : ℕ, ∃ k : ℕ, ∀ z ∈ Metric.closedBall c R,
      dist (f (radialMap c n z))
        (p.partialSum k ((radialFactor n : ℂ) * (z - c))) <
          1 / ((n : ℝ) + 1) := by
    intro n
    have hmid_pos : 0 < ((radialFactor n + 1) / 2) * R := by
      apply mul_pos
      · have := radialFactor_nonneg n
        linarith only [radialFactor_nonneg n]
      · exact hR
    let r : NNReal := ⟨((radialFactor n + 1) / 2) * R, hmid_pos.le⟩
    have hr_lt : (r : ENNReal) < (Rnn : ENNReal) := by
      apply ENNReal.coe_lt_coe.2
      change ((radialFactor n + 1) / 2) * R < R
      nlinarith only [radialFactor_lt_one n, hR]
    have hpartialUniform := hp.tendstoUniformlyOn hr_lt
    have heps : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hevent :=
      (Metric.tendstoUniformlyOn_iff.mp hpartialUniform)
        (1 / ((n : ℝ) + 1)) heps
    obtain ⟨k, hk⟩ := eventually_atTop.1 hevent
    refine ⟨k, fun z hz => ?_⟩
    have hz' : ‖z - c‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hfactor_lt_mid :
        radialFactor n < (radialFactor n + 1) / 2 := by
      linarith only [radialFactor_lt_one n]
    have hy : (radialFactor n : ℂ) * (z - c) ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (radialFactor_nonneg n)]
      calc
        radialFactor n * ‖z - c‖ ≤ radialFactor n * R :=
          mul_le_mul_of_nonneg_left hz' (radialFactor_nonneg n)
        _ < ((radialFactor n + 1) / 2) * R :=
          mul_lt_mul_of_pos_right hfactor_lt_mid hR
        _ = (r : ℝ) := rfl
    have h := hk k le_rfl ((radialFactor n : ℂ) * (z - c)) hy
    simpa only [radialMap] using h
  choose k hk using hpartial
  refine ⟨fun n => radialTaylorPolynomial p n (k n) c, ?_⟩
  rw [show closure (SmoothJordanDomain.ball c R hR).carrier =
      Metric.closedBall c R by
    change closure (Metric.ball c R) = Metric.closedBall c R
    exact closure_ball c hR.ne']
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hradialEvent :=
    (Metric.tendstoUniformlyOn_iff.mp hradial) (ε / 2) (half_pos hε)
  have herrZero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have herrorEvent := herrZero.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hradialEvent, herrorEvent] with n hn hsmall z hz
  calc
    dist (f z) (Polynomial.eval z (radialTaylorPolynomial p n (k n) c)) ≤
        dist (f z) (f (radialMap c n z)) +
          dist (f (radialMap c n z))
            (Polynomial.eval z (radialTaylorPolynomial p n (k n) c)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add (hn z hz)
      simpa only [eval_radialTaylorPolynomial] using (hk n z hz).trans hsmall
    _ = ε := by ring

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

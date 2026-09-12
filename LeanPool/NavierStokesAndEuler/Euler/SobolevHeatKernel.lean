/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Jointly continuous positive-time heat kernels with an explicit integrable parabolic bound. -/

@[expose] public section


noncomputable section

namespace EulerSobolevHeat

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGaussianCylinderHeat MeasureTheory Set
    Metric
open intervalIntegral
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A local name for the inherited Sobolev normed group avoids repeated subtype-instance expansion.
-/
local instance sobolevNormedGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

/-- A local name for the inherited Sobolev scalar structure. -/
local instance sobolevNormedSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The ordinary Sobolev heat flow is a contraction in its input field. -/
theorem heatOperator_dist_le {q : ℕ} (v : ℝ≥0) (u z : SobolevSpace period q) :
    dist (heatOperator period q v u) (heatOperator period q v z) ≤ dist u z := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact heatOperator_bound period v (u - z)

/-- Strong continuity and contraction imply joint continuity of the actual Sobolev heat flow. -/
theorem heatOperator_joint_continuous (q : ℕ) :
    Continuous (fun p : ℝ≥0 × SobolevSpace period q => heatOperator period q p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := (Metric.continuousAt_iff.mp (heatOperator_continuous period
      p.2).continuousAt)
    (ε / 2) (by linarith)
  refine ⟨min δ (ε / 2), lt_min hδ (by linarith), ?_⟩
  intro z hz
  have ht : dist z.1 p.1 < δ := (show dist z.1 p.1 ≤ dist z p from le_max_left _ _).trans_lt
      (lt_min_iff.mp hz).1
  have hf : dist z.2 p.2 < ε / 2 := (show dist z.2 p.2 ≤ dist z p from le_max_right _ _).trans_lt
      (lt_min_iff.mp hz).2
  have h := dist_triangle (heatOperator period q z.1 z.2) (heatOperator period q z.1 p.2)
    (heatOperator period q p.1 p.2)
  have h1 := heatOperator_dist_le period z.1 z.2 p.2
  have h2 := hd ht
  linarith

/-- A fixed amount of smoothing composed with jointly continuous heat remains jointly continuous. -/
theorem fixed_heatGain_continuous (q : ℕ) (ε : ℝ≥0) (hε : 0 < ε) :
    Continuous (fun z : {v : ℝ≥0 // 0 < v} × SobolevSpace period q =>
      heatGain period q ε hε (heatOperator period q (z.1.val - ε) z.2)) := by
  have hp : Continuous (fun z : {v : ℝ≥0 // 0 < v} × SobolevSpace period q =>
      (z.1.val - ε, z.2)) :=
    (((continuous_subtype_val.comp continuous_fst).sub continuous_const).prodMk continuous_snd)
  have hh : Continuous (fun z : {v : ℝ≥0 // 0 < v} × SobolevSpace period q =>
      heatOperator period q (z.1.val - ε) z.2) :=
    Continuous.comp
      (g := fun p : ℝ≥0 × SobolevSpace period q => heatOperator period q p.1 p.2)
      (f := fun z : {v : ℝ≥0 // 0 < v} × SobolevSpace period q => (z.1.val - ε, z.2))
      (heatOperator_joint_continuous period q) hp
  have hg : Continuous (fun u : SobolevSpace period q => heatGain period q ε hε u) :=
    (heatGain period q ε hε).continuous
  exact hg.comp hh

/-- Factoring off a smaller variance leaves the same actual derivative-gaining heat output. -/
theorem heatGain_tsub {q : ℕ} (ε v : ℝ≥0) (hε : 0 < ε) (hev : ε ≤ v)
    (u : SobolevSpace period q) :
    heatGain period q ε hε (heatOperator period q (v - ε) u) =
      heatGain period q v (hε.trans_le hev) u := by
  apply value_injective period
  simp only [heatGain_value, heatOperator_value, cylinderHeat_semigroup]
  rw [add_tsub_cancel_of_le hev]

/-- Splitting off a fixed positive smoothing time gives joint continuity with one gained derivative.
-/
theorem heatGain_joint_continuous (q : ℕ) :
    Continuous (fun p : {v : ℝ≥0 // 0 < v} × SobolevSpace period q =>
      heatGain period q p.1.val p.1.property p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let ε : ℝ≥0 := p.1.val / 2
  have hε : 0 < ε := div_pos p.1.property (by norm_num)
  have hep : ε < p.1.val := by dsimp [ε]; exact half_lt_self p.1.property
  have hc := fixed_heatGain_continuous period q ε hε
  apply hc.continuousAt.congr_of_eventuallyEq
  have he : ∀ᶠ z : {v : ℝ≥0 // 0 < v} × SobolevSpace period q in 𝓝 p, ε < z.1.val :=
    ((continuous_subtype_val.comp continuous_fst).tendsto p).eventually (Ioi_mem_nhds hep)
  filter_upwards [he] with z hz
  exact (heatGain_tsub period ε z.1.val hε hz.le z.2).symm

/-- The positive real-time heat kernel, with zero chosen at nonpositive time. -/
def heatKernel (q : ℕ) (ν : ℝ) (hν : 0 < ν) (t : ℝ) :
    SobolevSpace period q →L[ℝ] SobolevSpace period (q + 1) :=
  if ht : 0 < t then
    heatGain period q ⟨2 * ν * t, by positivity⟩ (by change (0 : ℝ) < 2 * ν * t; positivity)
  else 0

/-- The scalar coefficient multiplying the inverse square root in the heat-kernel bound. -/
def parabolicConstant (ν : ℝ) : ℝ := gaussianAbsMoment 1 / Real.sqrt (2 * ν)

/-- The explicit integrable majorant for one-derivative heat smoothing. -/
def parabolicKernelBound (ν t : ℝ) : ℝ := 1 + parabolicConstant ν * t ^ (-(1 / 2 : ℝ))

/-- The scalar parabolic majorant is nonnegative on positive times. -/
theorem parabolicKernelBound_nonneg (ν t : ℝ) (ht : 0 < t) : 0 ≤ parabolicKernelBound ν t := by
  unfold parabolicKernelBound parabolicConstant
  have hm := gaussianAbsMoment_nonneg 1
  positivity

/-- The actual viscosity-scaled heat kernel satisfies the explicit inverse-square-root bound. -/
theorem heatKernel_bound (q : ℕ) (ν : ℝ) (hν : 0 < ν) (t : ℝ) (ht : 0 < t)
    (u : SobolevSpace period q) :
    ‖heatKernel period q ν hν t u‖ ≤ parabolicKernelBound ν t * ‖u‖ := by
  rw [heatKernel, dite_eq_left ht]
  have h := heatGain_bound period (⟨2 * ν * t, by positivity⟩ : ℝ≥0)
    (by change (0 : ℝ) < 2 * ν * t; positivity) u
  have he : heatDerivativeConstant (⟨2 * ν * t, by positivity⟩ : ℝ≥0) =
      parabolicConstant ν * t ^ (-(1 / 2 : ℝ)) := by
    change gaussianAbsMoment 1 / Real.sqrt (2 * ν * t) =
      (gaussianAbsMoment 1 / Real.sqrt (2 * ν)) * t ^ (-(1 / 2 : ℝ))
    rw [Real.sqrt_mul (by positivity), Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  apply max_le
  · unfold parabolicKernelBound
    have : 0 ≤ parabolicConstant ν * t ^ (-(1 / 2 : ℝ)) := by
      unfold parabolicConstant
      have hm := gaussianAbsMoment_nonneg 1
      positivity
    linarith
  · unfold parabolicKernelBound
    linarith

/-- The scalar heat majorant is genuinely integrable at time zero. -/
theorem parabolicKernelBound_integrable (ν T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (parabolicKernelBound ν) (Ioc 0 T) := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegrable_rpow' (by norm_num)
  have h : IntervalIntegrable (parabolicKernelBound ν) volume 0 T :=
    intervalIntegrable_const.add (hr.const_mul (parabolicConstant ν))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp h

/-- The exact kernel mass is T plus the square-root parabolic contribution. -/
theorem parabolicKernelBound_integral (ν T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Ioc 0 T, parabolicKernelBound ν t) = T + 2 * parabolicConstant ν * Real.sqrt T := by
  rw [← intervalIntegral.integral_of_le hT]
  unfold parabolicKernelBound
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegrable_rpow' (by norm_num : -1 < -(1 / 2 : ℝ))).const_mul (parabolicConstant ν)),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

end EulerSobolevHeat

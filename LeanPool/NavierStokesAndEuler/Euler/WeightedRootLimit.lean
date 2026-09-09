/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
import LeanPool.NavierStokesAndEuler.Euler.MetricRootLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Weighted removal of root regularization, preserving the signed derivative of the radius. -/

@[expose] public section


noncomputable section

namespace EulerWeightedRootLimit

open MeasureTheory Set Real EulerNoncompactTransport EulerMetricRootLimit
open scoped Topology

/-- Dominated convergence for the regularized scalar energy integrand on a fixed finite interval. -/
theorem regularized_integral_tendsto (Q A F : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hQ : ContinuousOn Q (Icc s t)) (hQ0 : ∀ u ∈ Icc s t, 0 ≤ Q u)
    (hA : IntegrableOn A (Icc s t)) (hF : IntegrableOn F (Icc s t)) :
    Filter.Tendsto (fun n => ∫ u in s..t, (A u * √(Q u + cutoffScale n ^ 2) + F u))
      Filter.atTop (𝓝 (∫ u in s..t, (A u * √(Q u) + F u))) := by
  let μ : Measure ℝ := volume.restrict (Ioc s t)
  let fn := fun n u => A u * √(Q u + cutoffScale n ^ 2) + F u
  have hAQ : IntegrableOn (fun u => A u * √(Q u)) (Icc s t) :=
    hA.mul_continuousOn hQ.sqrt isCompact_Icc
  have hAn : Integrable A μ := hA.mono_set Ioc_subset_Icc_self
  have hFn : Integrable F μ := hF.mono_set Ioc_subset_Icc_self
  have hAQn : Integrable (fun u => A u * √(Q u)) μ := hAQ.mono_set Ioc_subset_Icc_self
  have hmeas (n : ℕ) : AEStronglyMeasurable (fn n) μ :=
    (((hA.mul_continuousOn ((hQ.add continuousOn_const).sqrt) isCompact_Icc).add hF).mono_set
        Ioc_subset_Icc_self).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ u ∂μ,
      ‖fn n u‖ ≤ ‖A u * √(Q u)‖ + ‖A u‖ + ‖F u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hq := hQ0 u ⟨hu.1.le, hu.2⟩
    have hr := (regularized_root_le (Q u) (cutoffScale n) hq (cutoffScale_pos n).le).trans
      (add_le_add_right (cutoffScale_le_one n) (√(Q u)))
    calc
      _ ≤ ‖A u‖ * √(Q u + cutoffScale n ^ 2) + ‖F u‖ := by
        simpa only [fn, norm_mul, Real.norm_of_nonneg (sqrt_nonneg _)] using
          norm_add_le (A u * √(Q u + cutoffScale n ^ 2)) (F u)
      _ ≤ ‖A u‖ * (√(Q u) + 1) + ‖F u‖ :=
        add_le_add_left (mul_le_mul_of_nonneg_left hr (norm_nonneg (A u))) ‖F u‖
      _ = _ := by
        rw [norm_mul, Real.norm_of_nonneg (sqrt_nonneg _)]
        ring
  have hlim : ∀ᵐ u ∂μ, Filter.Tendsto (fun n => fn n u) Filter.atTop (𝓝 (A u * √(Q u) + F u)) :=
    Filter.Eventually.of_forall (fun u =>
      ((regularized_root_tendsto (Q u)).const_mul (A u)).add_const (F u))
  have hi := tendsto_integral_of_dominated_convergence
    (fun u => ‖A u * √(Q u)‖ + ‖A u‖ + ‖F u‖) hmeas
    ((hAQn.norm.add hAn.norm).add hFn.norm) hbound hlim
  have hii : Filter.Tendsto (fun n => ∫ u in s..t, fn n u) Filter.atTop
      (𝓝 (∫ u in s..t, (A u * √(Q u) + F u))) := by
    simpa only [intervalIntegral.integral_of_le hst] using hi
  exact hii

/-- Endpoint weights pass through the same genuine regularization limit. -/
theorem weighted_root_integral_limit (Q A F w : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hQ : ContinuousOn Q (Icc s t)) (hQ0 : ∀ u ∈ Icc s t, 0 ≤ Q u)
    (hA : IntegrableOn A (Icc s t)) (hF : IntegrableOn F (Icc s t))
    (hineq : ∀ δ : ℝ, 0 < δ → w t * √(Q t + δ ^ 2) - w s * √(Q s + δ ^ 2) ≤
      ∫ u in s..t, (A u * √(Q u + δ ^ 2) + F u)) :
    w t * √(Q t) - w s * √(Q s) ≤ ∫ u in s..t, (A u * √(Q u) + F u) := by
  exact le_of_tendsto_of_tendsto'
    (((regularized_root_tendsto (Q t)).const_mul (w t)).sub
      ((regularized_root_tendsto (Q s)).const_mul (w s)))
    (regularized_integral_tendsto Q A F s t hst hQ hQ0 hA hF)
    (fun n => hineq (cutoffScale n) (cutoffScale_pos n))

/-- A nonnegative differentiable weight preserves an energy differential bound with its signed
derivative. -/
theorem weighted_root_integral_of_deriv_bound (Q a F w w' : ℝ → ℝ) (s t : ℝ)
    (hst : s ≤ t) (hQ : ContinuousOn Q (Icc s t)) (hQ0 : ∀ u ∈ Icc s t, 0 ≤ Q u)
    (hwc : ContinuousOn w (Icc s t)) (hw : ∀ u ∈ Ioo s t, 0 ≤ w u)
    (hwd : ∀ u ∈ Ioo s t, HasDerivAt w (w' u) u)
    (hregd : ∀ δ : ℝ, 0 < δ → ∀ u ∈ Ioo s t,
      DifferentiableAt ℝ (fun v => √(Q v + δ ^ 2)) u)
    (hreg : ∀ δ : ℝ, 0 < δ → ∀ u ∈ Ioo s t,
      deriv (fun v => √(Q v + δ ^ 2)) u ≤ a u * √(Q u + δ ^ 2) + F u)
    (hA : IntegrableOn (fun u => w u * a u + w' u) (Icc s t))
    (hF : IntegrableOn (fun u => w u * F u) (Icc s t)) :
    w t * √(Q t) - w s * √(Q s) ≤
      ∫ u in s..t, ((w u * a u + w' u) * √(Q u) + w u * F u) := by
  apply weighted_root_integral_limit Q (fun u => w u * a u + w' u) (fun u => w u * F u)
    w s t hst hQ hQ0 hA hF
  intro δ hδ
  have hrc : ContinuousOn (fun u => √(Q u + δ ^ 2)) (Icc s t) :=
    (hQ.add continuousOn_const).sqrt
  have hcont := hwc.mul hrc
  have hφint : IntegrableOn (fun u => (w u * a u + w' u) * √(Q u + δ ^ 2) + w u * F u)
      (Icc s t) := (hA.mul_continuousOn hrc isCompact_Icc).add hF
  refine intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (g' := fun u => deriv (fun v => w v * √(Q v + δ ^ 2)) u) hst hcont ?_ hφint ?_
  · intro u hu
    exact ((hwd u hu).fun_mul (hregd δ hδ u
        hu).hasDerivAt).differentiableAt.hasDerivAt.hasDerivWithinAt
  · intro u hu
    rw [((hwd u hu).fun_mul (hregd δ hδ u hu).hasDerivAt).deriv]
    have h := mul_le_mul_of_nonneg_left (hreg δ hδ u hu) (hw u hu)
    nlinarith

end EulerWeightedRootLimit

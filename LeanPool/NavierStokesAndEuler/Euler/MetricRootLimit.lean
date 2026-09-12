/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteMetricEnergy
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Removal of square-root regularization in actual finite metric-energy integral inequalities. -/

@[expose] public section


noncomputable section

namespace EulerMetricRootLimit

open MeasureTheory Set Real InnerProductSpace EulerNoncompactTransport EulerFiniteMetricEnergy
open scoped Topology

/-- A regularized square root differs from the nonnegative root by at most the regularization. -/
theorem regularized_root_le (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) :
    √(q + δ ^ 2) ≤ √q + δ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (sqrt_nonneg q) hδ, ?_⟩
  have hsq := sq_sqrt hq
  have hp := mul_nonneg (sqrt_nonneg q) hδ
  nlinarith

/-- The canonical positive regularization sequence converges at every quadratic energy value. -/
theorem regularized_root_tendsto (q : ℝ) :
    Filter.Tendsto (fun n => √(q + cutoffScale n ^ 2)) Filter.atTop (𝓝 (√q)) := by
  have hq : Filter.Tendsto (fun n => q + cutoffScale n ^ 2) Filter.atTop (𝓝 q) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      (tendsto_const_nhds.add (cutoffScale_tendsto.pow 2))
  exact (continuous_sqrt.tendsto q).comp hq

/-- At fixed finite cutoff, an integrable energy inequality survives removal of the root
regularization. -/
theorem root_integral_limit (Q A F : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hQ : ContinuousOn Q (Icc s t)) (hQ0 : ∀ u ∈ Icc s t, 0 ≤ Q u)
    (hA : IntegrableOn A (Icc s t)) (hF : IntegrableOn F (Icc s t))
    (hineq : ∀ δ : ℝ, 0 < δ → √(Q t + δ ^ 2) - √(Q s + δ ^ 2) ≤
      ∫ u in s..t, (A u * √(Q u + δ ^ 2) + F u)) :
    √(Q t) - √(Q s) ≤ ∫ u in s..t, (A u * √(Q u) + F u) := by
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
  exact le_of_tendsto_of_tendsto' ((regularized_root_tendsto (Q t)).sub
    (regularized_root_tendsto (Q s))) hii (fun n => hineq (cutoffScale n) (cutoffScale_pos n))

/-- The unregularized finite-family energy obeys an integral inequality even when the norm vanishes.
-/
theorem family_energy_integral_bound {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : ℝ → H →L[ℝ] H) (e : ι → ℝ → H)
    (s t c ν : ℝ) (K' : ℝ → H →L[ℝ] H)
    (e' transport pressure forcing lap : ι → ℝ → H) (B C : ℝ → ℝ)
    (hst : s ≤ t) (hc : 0 < c) (hν : 0 ≤ ν)
    (hKc : ContinuousOn K (Icc s t)) (hec : ∀ i, ContinuousOn (e i) (Icc s t))
    (hB : ∀ u ∈ Ioo s t, 0 ≤ B u) (hC : ∀ u ∈ Ioo s t, 0 ≤ C u)
    (hcoercive : ∀ u ∈ Icc s t, ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K u v, v⟫_ℝ)
    (hKd : ∀ u ∈ Ioo s t, HasDerivAt K (K' u) u)
    (hed : ∀ i u, u ∈ Ioo s t → HasDerivAt (e i) (e' i u) u)
    (hsym : ∀ u ∈ Ioo s t, ∀ v w, ⟪K u v, w⟫_ℝ = ⟪v, K u w⟫_ℝ)
    (heq : ∀ i u, u ∈ Ioo s t → e' i u + transport i u + pressure i u =
      forcing i u + ν • lap i u)
    (hp : ∀ i u, u ∈ Ioo s t → ⟪K u (e i u), pressure i u⟫_ℝ = 0)
    (ht : ∀ i u, u ∈ Ioo s t → |⟪K u (e i u), transport i u⟫_ℝ| ≤ B u * ‖e i u‖ ^ 2)
    (hheat : ∀ i u, u ∈ Ioo s t → ⟪K u (e i u), lap i u⟫_ℝ ≤ C u * ‖e i u‖ ^ 2)
    (hAint : IntegrableOn (fun u => (‖K' u‖ + 2 * B u + 2 * ν * C u) / (2 * c ^ 2)) (Icc s t))
    (hFint : IntegrableOn (fun u => (‖K u‖ / c) * familyNorm (fun i => forcing i u)) (Icc s t)) :
    familyMetricNorm (K t) (fun i => e i t) - familyMetricNorm (K s) (fun i => e i s) ≤
      ∫ u in s..t, (((‖K' u‖ + 2 * B u + 2 * ν * C u) / (2 * c ^ 2)) *
        familyMetricNorm (K u) (fun i => e i u) + (‖K u‖ / c) * familyNorm (fun i => forcing i u))
            := by
  let Q := fun u => familyEnergy (K u) (fun i => e i u)
  let A := fun u => (‖K' u‖ + 2 * B u + 2 * ν * C u) / (2 * c ^ 2)
  let F := fun u => (‖K u‖ / c) * familyNorm (fun i => forcing i u)
  have hQ : ContinuousOn Q (Icc s t) :=
    continuousOn_finsetSum Finset.univ (fun i _ => (hKc.clm_apply (hec i)).inner (hec i))
  have hQ0 (u : ℝ) (hu : u ∈ Icc s t) : 0 ≤ Q u := by
    have h := familyEnergy_coercive (K u) (fun i => e i u) c (hcoercive u hu)
    exact (mul_nonneg (sq_nonneg c) (familySquaredNorm_nonneg _)).trans h
  apply root_integral_limit Q A F s t hst hQ hQ0 hAint hFint
  intro δ hδ
  have hrootc : ContinuousOn (fun u => √(Q u + δ ^ 2)) (Icc s t) :=
    (hQ.add continuousOn_const).sqrt
  have hφint : IntegrableOn (fun u => A u * √(Q u + δ ^ 2) + F u) (Icc s t) :=
    (hAint.mul_continuousOn hrootc isCompact_Icc).add hFint
  refine intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (g' := fun u => deriv (fun v => √(Q v + δ ^ 2)) u) hst hrootc ?_ hφint ?_
  · intro u hu
    have hd := family_energy_hasDerivAt K e u ν (K' u) (fun i => e' i u)
      (fun i => transport i u) (fun i => pressure i u) (fun i => forcing i u) (fun i => lap i u)
      (hKd u hu) (fun i => hed i u hu) (hsym u hu) (fun i => heq i u hu) (fun i => hp i u hu)
    have hq := hQ0 u ⟨hu.1.le, hu.2.le⟩
    have hr := HasDerivAt.sqrt (hd.add_const (δ ^ 2)) (by nlinarith : Q u + δ ^ 2 ≠ 0)
    exact hr.differentiableAt.hasDerivAt.hasDerivWithinAt
  · intro u hu
    exact family_regularized_energy_evolution K e u δ c (B u) (C u) ν (K' u)
      (fun i => e' i u) (fun i => transport i u) (fun i => pressure i u)
      (fun i => forcing i u) (fun i => lap i u) hδ hc (hB u hu) (hC u hu) hν
      (hcoercive u ⟨hu.1.le, hu.2.le⟩) (hKd u hu) (fun i => hed i u hu) (hsym u hu)
      (fun i => heq i u hu) (fun i => hp i u hu) (fun i => ht i u hu) (fun i => hheat i u hu)

end EulerMetricRootLimit

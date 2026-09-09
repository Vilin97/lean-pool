/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MaximalTopCauchy
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMap

@[expose] public section

/-! Genuine all-finite-order maximal regularity for actual viscous cylinder mild solutions. -/

noncomputable section

namespace EulerSobolevMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerTimeLp EulerVolterraConvolution EulerRegularizedTopBlocks EulerMaximalTopCauchy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The complete actual Bochner Sobolev space realizes every strong Cauchy sequence. -/
theorem exists_sobolev_time_limit (q : ℕ) (T : ℝ)
    (u : ℕ → TimeLp T (SobolevSpace period (2+q))) (hu : CauchySeq u) :
    ∃ U : TimeLp T (SobolevSpace period (2+q)), Filter.Tendsto u Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete hu

/-- Completion supplies the genuine higher-order limit of the actual viscous approximations. -/
theorem exists_maximal_mild_limit {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop (𝓝
        U) := by
  have hc : CauchySeq (fun n => pathLp T hT (maximalApproximation period q T n u)) :=
    maximalApproximation_cauchy period ν hν T hT u₀ f u hsol
  exact exists_sobolev_time_limit period q T (fun n => pathLp T hT (maximalApproximation period q T
    n u)) hc

/-- The actual higher-order limit restricts to the original viscous solution almost everywhere. -/
theorem maximal_limit_restriction {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (U : TimeLp T (SobolevSpace period (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
      (𝓝 U)) :
    ((fun t => restrictOperator period (by omega : q+1 ≤ 2+q) (U t)) =ᵐ[timeMeasure T] extendPath T
      hT u) :=
  limit_restriction_ae T hT (restrictOperator period (by omega : q+1 ≤ 2+q))
    (fun n => maximalApproximation period q T n u) u U hU (maximalApproximation_low_tendsto period
      q T u)

/-- Actual viscous mild solutions with continuous Hq forcing and H^(q+1) values possess full H^(q+2) regularity in Bochner L² time.
The stronger field is constructed from genuine heat approximations and identified with the original
  field almost everywhere. -/
theorem viscous_mild_maximal_regularity {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period (2+q)),
      ((fun t => restrictOperator period (by omega : q+1 ≤ 2+q) (U t)) =ᵐ[timeMeasure T] extendPath
        T hT u) ∧
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop (𝓝
        U) := by
  refine (exists_maximal_mild_limit period ν hν T hT u₀ f u hsol).imp ?_
  intro U hU
  exact ⟨maximal_limit_restriction period T hT u U hU, hU⟩

/-- The genuine full higher-order spatial derivatives exist at almost every time of the actual viscous solution. -/
theorem viscous_mild_ae_higher {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    ∀ᵐ t ∂timeMeasure T, ∃ v : SobolevSpace period (2+q),
      restrictOperator period (by omega : q+1 ≤ 2+q) v = extendPath T hT u t := by
  obtain ⟨U, hU, _⟩ := viscous_mild_maximal_regularity period ν hν T hT u₀ f u hsol
  filter_upwards [hU] with t ht
  exact ⟨U t, ht⟩

end EulerSobolevMaximalRegularity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatMaximalCauchy
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMildEquation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMap

@[expose] public section

/-! Genuine maximal spatial regularity of the actual viscous mild solution, proved by strong Cauchy
  limits. -/

noncomputable section

namespace EulerHeatMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevLaplacian EulerTimeLp EulerVolterraConvolution EulerRegularizedMildEquation
  EulerHeatMaximalCauchy EulerHeatMaximalEstimate
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual regularized mild solutions are strongly Cauchy in Bochner L² time with two derivatives. -/
theorem regularized_mild_cauchy (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) := by
  apply heat_H2_cauchy period T hT ν hν (fun n => regularizedState period T n u)
    (fun n => regularizedForcing period T n f)
    (regularizedState_first_time_derivative period T hT ν hν u₀ f u hsol)
  · exact (regularizedState_low_tendsto period T u).cauchySeq
  · exact (pathLp_tendsto T hT _ _ (regularizedForcing_value_tendsto period T f)).cauchySeq

/-- The strong higher-order limit has exactly the original lower-order field almost everywhere in time. -/
theorem regularized_limit_restriction (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1)) (U : TimeLp T (SobolevSpace period 2))
    (hU : Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u))
      Filter.atTop (𝓝 U)) :
    ((fun t => truncateOperator period 1 (U t)) =ᵐ[timeMeasure T] extendPath T hT u) := by
  have hlow := regularizedState_low_tendsto period T u
  have hrestrict : Filter.Tendsto (fun n => (truncateOperator period 1).compLeftContinuous ℝ (Icc
    (0 : ℝ) T)
      ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedState period T
        n u))) Filter.atTop (𝓝 u) := by
    convert hlow using 1
    funext n
    apply ContinuousMap.ext
    intro t
    apply value_injective period
    rfl
  exact limit_restriction_ae T hT (truncateOperator period 1)
    (fun n => (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedState
      period T n u)) u U hU hrestrict

/-- The genuine heat estimate passes to the strong higher-order time limit without weak compactness. -/
theorem regularized_limit_bound (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period 0)) (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ n t, t ∈ Ioo 0 T → ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT
        (regularizedState period T n u) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (regularizedState period T n u) t) +
            extendPath T hT (regularizedForcing period T n f) t))) t)
    (U : TimeLp T (SobolevSpace period 2))
    (hU : Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u))
      Filter.atTop (𝓝 U)) :
    ‖U‖^2 ≤ (T+4*ν⁻¹)*‖u‖^2 + (ν⁻¹)^2 *
      ‖pathLp T hT ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)‖^2 := by
  have hlow := regularizedState_low_tendsto period T u
  have hsource := pathLp_tendsto T hT _
    ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)
    (regularizedForcing_value_tendsto period T f)
  exact EulerQuadraticCauchy.limit_quadratic_bound
    (fun n => lowerPath period T (regularizedState period T n u))
    (fun n => sourceTime period T hT (regularizedForcing period T n f))
    (fun n => higherTime period T hT (regularizedState period T n u)) u _ U (T+4*ν⁻¹) ((ν⁻¹)^2)
    hlow hsource hU (fun n => heat_time_H2_bound period T hT ν hν
      (regularizedState period T n u) (regularizedForcing period T n f) (hd n))

/-- Completeness of actual H² Bochner space constructs its strong Cauchy limit. -/
theorem exists_H2_time_limit (T : ℝ) (u : ℕ → TimeLp T (SobolevSpace period 2)) (hu : CauchySeq u) :
    ∃ U : TimeLp T (SobolevSpace period 2), Filter.Tendsto u Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete hu

/-- Strong completion constructs the higher-order limit of the concrete mild-solution approximations. -/
theorem exists_regularized_mild_limit (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop
        (𝓝 U) := by
  have hc : CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) :=
    regularized_mild_cauchy period T hT ν hν u₀ f u hsol
  exact exists_H2_time_limit period T (fun n => higherTime period T hT (regularizedState period T n
    u)) hc

/-- The actual viscous mild solution with H¹ values and continuous L² source has two full spatial derivatives in L² time.
The higher-regularity element is constructed in the complete Bochner space and identified with the
  original field almost everywhere. -/
theorem viscous_mild_maximal_regularity (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      ((fun t => truncateOperator period 1 (U t)) =ᵐ[timeMeasure T] extendPath T hT u) ∧
      Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop
        (𝓝 U) := by
  refine (exists_regularized_mild_limit period T hT ν hν u₀ f u hsol).imp ?_
  intro U hU
  exact ⟨regularized_limit_restriction period T hT u U hU, hU⟩

/-- Actual H² spatial representatives exist for almost every time of the genuine H¹ viscous mild solution. -/
theorem viscous_mild_ae_H2 (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∀ᵐ t ∂timeMeasure T, ∃ v : SobolevSpace period 2, value period v = value period (extendPath T
      hT u t) := by
  obtain ⟨U, hU, _⟩ := viscous_mild_maximal_regularity period T hT ν hν u₀ f u hsol
  filter_upwards [hU] with t ht
  exact ⟨U t, congrArg (value period) ht⟩

end EulerHeatMaximalRegularity

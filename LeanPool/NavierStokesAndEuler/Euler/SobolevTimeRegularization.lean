/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpStrongOperators
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.HeatRegularizedPaths

@[expose] public section

/-! Strong actual heat approximation and time-dependent operator commutators in Bochner Sobolev
  spaces. -/

noncomputable section

namespace EulerSobolevTimeRegularization

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerHeatRegularizedPaths EulerTimeLp
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine Sobolev heat regularizations converge strongly on every Bochner L² time field. -/
theorem heat_timeLp_tendsto (q : ℕ) (T : ℝ) (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n => (heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure
      T) u)
      Filter.atTop (𝓝 u) := by
  apply strong_operator_timeLp_tendsto T (fun n => heatOperator period q (regularizerVariance n)) 1
  · intro n x
    simpa only [one_mul] using heatOperator_bound period (regularizerVariance n) x
  · intro x
    have h := (heatOperator_continuous period x).continuousAt.tendsto.comp
      regularizerVariance_tendsto
    simpa only [heatOperator_zero, Function.comp_def] using h

/-- Actual heat approximation commutes asymptotically with every continuous bounded time-dependent Sobolev operator. -/
theorem heat_time_commutator_tendsto (p q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period q →L[ℝ] SobolevSpace period p))
    (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n =>
      timeMultiplier T hT A ((heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure
        T) u) -
        (heatOperator period p (regularizerVariance n)).compLpL 2 (timeMeasure T) (timeMultiplier T
          hT A u))
      Filter.atTop (𝓝 0) := by
  have hA := (timeMultiplier T hT A).continuous.continuousAt.tendsto.comp (heat_timeLp_tendsto
    period q T u)
  have hB := heat_timeLp_tendsto period p T (timeMultiplier T hT A u)
  simpa only [sub_self, Function.comp_def] using hA.sub hB

/-- The actual heat commutator vanishes in the full L² time norm. -/
theorem heat_time_commutator_norm_tendsto (p q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period q →L[ℝ] SobolevSpace period p))
    (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n => ‖
      timeMultiplier T hT A ((heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure
        T) u) -
        (heatOperator period p (regularizerVariance n)).compLpL 2 (timeMeasure T) (timeMultiplier T
          hT A u)‖)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  simpa only [norm_zero] using (heat_time_commutator_tendsto period p q T hT A u).norm

end EulerSobolevTimeRegularization

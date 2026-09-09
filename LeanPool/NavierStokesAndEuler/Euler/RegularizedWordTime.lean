/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedWordConvergence
public import LeanPool.NavierStokesAndEuler.Euler.SobolevMaximalRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpStrongOperators
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpLinearity
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpObservation

@[expose] public section

/-! Strong L²-time convergence of actual energy-order regularized state, source, and pressure
  words. -/

noncomputable section

namespace EulerRegularizedWordTime

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerMildWordEquation EulerMildTopWord EulerRegularizedWordEquation EulerRegularizedTopBlocks
  EulerHeatRegularizedPaths EulerTimeLp EulerVolterraConvolution EulerGaussianCylinderHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual L² cylinder heat approximation converges on every Bochner L² time field. -/
theorem field_heat_timeLp_tendsto (T : ℝ) (u : TimeLp T (LiftL2 period)) :
    Filter.Tendsto (fun n => (cylinderHeat period (regularizerVariance n)).compLpL 2 (timeMeasure
      T) u)
      Filter.atTop (𝓝 u) := by
  apply strong_operator_timeLp_tendsto T (fun n => cylinderHeat period (regularizerVariance n)) 1
  · intro n x
    simpa only [one_mul] using cylinderHeat_norm_le period (regularizerVariance n) x
  · intro x
    have h := (cylinderHeat_continuous period x).continuousAt.tendsto.comp
      regularizerVariance_tendsto
    simpa only [cylinderHeat_zero, Function.comp_def] using h

/-- An actual regularized energy-order derivative of a continuous low-order source, as an L² time path. -/
def sourceWordPath {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  ((valueOperator period 2).comp (regularizedWordBlock period hm n w)).compLeftContinuous ℝ (Icc (0
    : ℝ) T) f

/-- Source smoothing agrees exactly with heat on a genuinely higher-order Bochner representative, whenever their lower fields agree almost everywhere. -/
theorem sourceWordPath_time_eq {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (F : TimeLp T (SobolevSpace period (q+1)))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f) :
    pathLp T hT (sourceWordPath period hm n w T f) =
      (cylinderHeat period (regularizerVariance n)).compLpL 2 (timeMeasure T)
        ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2
          (timeMeasure T) F) := by
  let W := wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))
  let D := (valueOperator period 2).comp (regularizedWordBlock period hm n w)
  have hobs := observation_time_eq T hT (truncateOperator period q) D
    ((cylinderHeat period (regularizerVariance n)).comp W)
    (regularizedWordBlock_value period hm n w) F f hF
  exact hobs.trans (compLpL_comp T W (cylinderHeat period (regularizerVariance n)) F).symm

/-- The actual regularized source words converge strongly at the full energy order using the proved higher time regularity. -/
theorem sourceWordPath_time_tendsto {q m : ℕ} (hm : m ≤ q+1) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (F : TimeLp T (SobolevSpace period (q+1)))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f) :
    Filter.Tendsto (fun n => pathLp T hT (sourceWordPath period hm n w T f)) Filter.atTop
      (𝓝 ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2
        (timeMeasure T) F)) := by
  simpa only [sourceWordPath_time_eq period hm _ w T hT f F hF] using
    field_heat_timeLp_tendsto period T
      ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2
        (timeMeasure T) F)

/-- The H¹ restriction of a regularized energy word is literally the corresponding block of the full maximal-regularity approximation. -/
theorem regularizedWordPath_first_eq {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) :
    (truncateOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedWordPath period hm
      n w T u) =
      (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (maximalApproximation period q T n u) := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  change value period (truncateOperator period 1 (regularizedWordBlock period hm n w
    (truncateOperator period q (u t)))) =
    value period (boundedWordBlock period 1 m (by omega) w
      (restrictOperator period (by omega : 2+q ≤ q+3) (heatRegularizer period q n (truncateOperator
        period q (u t)))))
  rw [value_truncateOperator, boundedWordBlock_value]
  change value period (boundedWordBlock period 2 m (by omega) w (heatRegularizer period q n
    (truncateOperator period q (u t)))) = _
  rw [boundedWordBlock_value]
  rfl

/-- Genuine maximal regularity gives strong H¹ time convergence for every full energy-order derivative word. -/
theorem regularizedWordPath_first_tendsto {q m : ℕ} (hm : m ≤ q+1) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (U : TimeLp T (SobolevSpace period (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
      (𝓝 U)) :
    Filter.Tendsto (fun n => pathLp T hT ((truncateOperator period 1).compLeftContinuous ℝ (Icc (0
      : ℝ) T)
      (regularizedWordPath period hm n w T u))) Filter.atTop
      (𝓝 ((boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w).compLpL 2 (timeMeasure T) U)) := by
  let A := boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w
  have h := (A.compLpL 2 (timeMeasure T)).continuous.continuousAt.tendsto.comp hU
  simpa only [regularizedWordPath_first_eq, pathLp_map, Function.comp_def] using h

end EulerRegularizedWordTime

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedWordEquation
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat
import LeanPool.NavierStokesAndEuler.Euler.SobolevWordConstraints

/-! The actual energy-order regularized words converge uniformly in time and preserve pressure
closedness. -/

@[expose] public section


noncomputable section

namespace EulerRegularizedWordEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerMildWordEquation EulerMildTopWord EulerHeatRegularizedPaths EulerVolterraConvolution
  EulerSobolevWordConstraints EulerDivergenceFreeHeat EulerGaussianCylinderHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The unregularized energy-order word retained as an actual H⁰ time path. -/
def energyWordPath {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    C(Icc (0 : ℝ) T, SobolevSpace period 0) :=
  mapPath period T (boundedWordBlock period 0 m (by omega : 0+m ≤ q+1) w) u

/-- The actual regularized energy word is exactly the L² value of its genuine H⁰ heat path. -/
theorem regularizedWordPath_heat_value {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    (valueOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedWordPath period hm n
        w T u) =
      (valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (pathHeat period 0 T (regularizerVariance n) (energyWordPath period hm w T u)) := by
  apply ContinuousMap.ext
  intro t
  change value period (regularizedWordBlock period hm n w (truncateOperator period q (u t))) =
    value period (heatOperator period 0 (regularizerVariance n) (boundedWordBlock period 0 m (by
        omega) w (u t)))
  rw [regularizedWordBlock_value, heatOperator_value, boundedWordBlock_value]

/-- Every actual energy-order word of the regularized mild solution converges uniformly in L² time
paths, including the top order. -/
theorem regularizedWordPath_value_tendsto {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    Filter.Tendsto (fun n => (valueOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (regularizedWordPath period hm n w T u)) Filter.atTop
      (𝓝 ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) (energyWordPath period hm w
          T u))) := by
  let v := energyWordPath period hm w T u
  have h := (pathHeat_continuous period T v).continuousAt.tendsto.comp regularizerVariance_tendsto
  have hzero : pathHeat period 0 T 0 v = v := by
    apply ContinuousMap.ext
    intro t
    exact heatOperator_zero period (v t)
  rw [hzero] at h
  have hv := ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ)
      T)).continuous.continuousAt.tendsto.comp h
  simpa only [regularizedWordPath_heat_value, Function.comp_def] using hv

/-- Genuine heat smoothing preserves the lifted gradient subspace. -/
theorem cylinderHeat_gradient (κ : ℝ) (m : Vector3) (v : NNReal) (p : LiftL2 period)
    (hp : p ∈ gradientSpace period κ m) : cylinderHeat period v p ∈ gradientSpace period κ m := by
  apply (gradientSpace period κ m).starProjection_eq_self_iff.mp
  change gradientProjection period κ m (cylinderHeat period v p) = cylinderHeat period v p
  rw [gradientProjection_cylinderHeat]
  have hproj : gradientProjection period κ m p = p := (gradientSpace period κ
      m).starProjection_eq_self_iff.mpr hp
  rw [hproj]

/-- Every regularized pressure word stays in the actual lifted gradient space, without assuming an
unregularized derivative of that order. -/
theorem regularizedWordBlock_gradient {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (κ : ℝ) (m₀ : Vector3) (p : SobolevSpace period q)
    (hp : value period p ∈ gradientSpace period κ m₀) :
    value period (regularizedWordBlock period hm n w p) ∈ gradientSpace period κ m₀ := by
  change value period (boundedWordBlock period 2 m (by omega) w (heatRegularizer period q n p)) ∈ _
  rw [boundedWordBlock_value]
  apply word_gradient period (by omega : m ≤ q+3) κ m₀ (heatRegularizer period q n p) _ w
  rw [heatRegularizer_value]
  exact cylinderHeat_gradient period κ m₀ (regularizerVariance n) (value period p) hp

end EulerRegularizedWordEquation

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MildTopWord
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMildEquation

/-! Exact compatibility of the actual heat regularizations with highest derivative blocks. -/

@[expose] public section


noncomputable section

namespace EulerRegularizedTopBlocks

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerGaussianCylinderHeat EulerHeatRegularizedPaths EulerMildWordEquation
  EulerMildTopWord EulerRegularizedMildEquation EulerSobolevWordBlocks
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every preexisting derivative word of a genuine heat regularizer is regularized by the same L²
heat operator. -/
theorem heatRegularizer_word {q m : ℕ} (n : ℕ) (hm : m ≤ q) (w : Fin m → Fin 4)
    (u : SobolevSpace period q) :
    word period (heatRegularizer period q n u) (by omega : m ≤ q+3) w =
      cylinderHeat period (regularizerVariance n) (word period u hm w) := by
  have h := congrArg (fun v : SobolevSpace period q => word period v hm w)
    (restrict_heatRegularizer period n u)
  exact h

/-- The actual regularized state, retained at the full maximal-regularity spatial order. -/
def maximalApproximation (q : ℕ) (T : ℝ) (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    C(Icc (0 : ℝ) T, SobolevSpace period (2+q)) :=
  mapPath period T ((restrictOperator period (by omega : 2+q ≤ q+3)).comp
    ((heatRegularizer period q n).comp (truncateOperator period q))) u

/-- Restricting the maximal-regularity approximation is the genuine original-order heat path. -/
theorem maximalApproximation_low (q : ℕ) (T : ℝ) (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    (restrictOperator period (by omega : q+1 ≤ 2+q)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (maximalApproximation period q T n u) = pathHeat period (q+1) T (regularizerVariance n) u :=
          by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  change value period (restrictOperator period (by omega : q+1 ≤ 2+q)
    (restrictOperator period (by
        omega : 2+q ≤ q+3) (heatRegularizer period q n (truncateOperator period q (u t))))) =
      value period (heatOperator period (q+1) (regularizerVariance n) (u t))
  rw [value_restrictOperator, value_restrictOperator, heatRegularizer_value,
      value_truncateOperator, heatOperator_value]

/-- The full approximation converges uniformly in the original actual Sobolev topology. -/
theorem maximalApproximation_low_tendsto (q : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    Filter.Tendsto (fun n => (restrictOperator period (by omega : q+1 ≤ 2+q)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (maximalApproximation period q T n u)) Filter.atTop (𝓝 u) := by
  have h := (pathHeat_continuous period T u).continuousAt.tendsto.comp regularizerVariance_tendsto
  have hzero : pathHeat period (q+1) T 0 u = u := by
    apply ContinuousMap.ext
    intro t
    exact heatOperator_zero period (u t)
  rw [hzero] at h
  simpa only [maximalApproximation_low, Function.comp_def] using h

/-- Every top derivative block of the full approximation is exactly the corresponding H²
approximation of the actual H¹ word solution. -/
theorem maximalApproximation_word (q : ℕ) (T : ℝ) (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (w : Fin q → Fin 4) :
    (wordBlock period 2 q w).compLeftContinuous ℝ (Icc (0 : ℝ) T) (maximalApproximation period q T
        n u) =
      (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (regularizedState period T n (mapPath period T (boundedWordBlock period 1 q (by
            omega) w) u)) := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  change value period (wordBlock period 2 q w
    (restrictOperator period (by
        omega : 2+q ≤ q+3) (heatRegularizer period q n (truncateOperator period q (u t))))) =
      value period (truncateOperator period 2 (heatRegularizer period 0 n
        (truncateOperator period 0 (boundedWordBlock period 1 q (by omega) w (u t)))))
  rw [wordBlock_value, value_truncateOperator, heatRegularizer_value, value_truncateOperator,
    boundedWordBlock_value]
  exact heatRegularizer_word period n (le_refl q) w (truncateOperator period q (u t))

end EulerRegularizedTopBlocks

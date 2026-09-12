/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothApproximation
public import LeanPool.NavierStokesAndEuler.Euler.MildWordEquation

/-! Genuine heat regularization of continuous Sobolev paths, uniformly in time. -/

@[expose] public section


noncomputable section

namespace EulerHeatRegularizedPaths

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerGaussianCylinderHeat EulerMildWordEquation
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A concrete three-derivative heat regularizer on the actual Sobolev scale. -/
def heatRegularizer (q n : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period (q+3) :=
  heatGainThree period q (smoothingVariance n) (smoothingVariance_pos n)

/-- The total actual Gaussian variance of the regularizer. -/
def regularizerVariance (n : ℕ) : ℝ≥0 := smoothingVariance n + (smoothingVariance n +
    smoothingVariance n)

/-- The total regularizing variance tends to zero. -/
theorem regularizerVariance_tendsto : Filter.Tendsto regularizerVariance Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n => smoothingVariance n + (smoothingVariance n + smoothingVariance
      n)) Filter.atTop (𝓝 0)
  simpa only [add_zero] using
    smoothingVariance_tendsto.add (smoothingVariance_tendsto.add smoothingVariance_tendsto)

/-- The regularizer has exactly its stated genuine L² heat value. -/
theorem heatRegularizer_value {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    value period (heatRegularizer period q n u) = cylinderHeat period (regularizerVariance n)
        (value period u) :=
  heatGainThree_value period _ _ u

/-- Forgetting the three extra derivatives gives the actual contractive heat evolution. -/
theorem restrict_heatRegularizer {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    restrictOperator period (by omega : q ≤ q+3) (heatRegularizer period q n u) =
      heatOperator period q (regularizerVariance n) u :=
  restrict_heatGainThree period _ _ u

/-- The genuine regularizer commutes with actual heat. -/
theorem heatRegularizer_heat {q : ℕ} (n : ℕ) (v : ℝ≥0) (u : SobolevSpace period q) :
    heatRegularizer period q n (heatOperator period q v u) =
      heatOperator period (q+3) v (heatRegularizer period q n u) := by
  apply value_injective period
  rw [heatRegularizer_value, heatOperator_value, heatOperator_value, heatRegularizer_value,
    cylinderHeat_semigroup, cylinderHeat_semigroup, add_comm]

/-- Heat acting pointwise on a continuous Sobolev time path. -/
def pathHeat (q : ℕ) (T : ℝ) (v : ℝ≥0) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    C(Icc (0 : ℝ) T, SobolevSpace period q) := mapPath period T (heatOperator period q v) u

/-- Strong heat continuity is uniform over every compact continuous time path. -/
theorem pathHeat_continuous {q : ℕ} (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    Continuous (fun v : ℝ≥0 => pathHeat period q T v u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact Continuous.comp
    (g := fun p : ℝ≥0 × SobolevSpace period q => heatOperator period q p.1 p.2)
    (f := fun p : ℝ≥0 × Icc (0 : ℝ) T => (p.1, u p.2))
    (heatOperator_joint_continuous period q) (continuous_fst.prodMk (u.continuous.comp
        continuous_snd))

/-- A continuous path regularized by three genuine spatial heat derivatives. -/
def regularizedPath {q : ℕ} (T : ℝ) (n : ℕ) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    C(Icc (0 : ℝ) T, SobolevSpace period (q+3)) := mapPath period T (heatRegularizer period q n) u

/-- Regularized paths converge uniformly in their original complete Sobolev norm. -/
theorem regularizedPath_tendsto {q : ℕ} (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    Filter.Tendsto (fun n => mapPath period T (restrictOperator period (by omega : q ≤ q+3))
      (regularizedPath period T n u)) Filter.atTop (𝓝 u) := by
  have h := (pathHeat_continuous period T u).continuousAt.tendsto.comp regularizerVariance_tendsto
  have hzero : pathHeat period q T 0 u = u := by
    apply ContinuousMap.ext
    intro t
    exact heatOperator_zero period (u t)
  rw [hzero] at h
  convert h using 1
  funext n
  apply ContinuousMap.ext
  intro t
  exact restrict_heatRegularizer period n (u t)

/-- Regularization at adjacent Sobolev levels has exactly the same underlying field. -/
theorem heatRegularizer_truncate {q : ℕ} (n : ℕ) (u : SobolevSpace period (q + 1)) :
    heatRegularizer period q n (truncateOperator period q u) =
      restrictOperator period (by omega : q+3 ≤ q+1+3) (heatRegularizer period (q+1) n u) := by
  apply value_injective period
  rw [heatRegularizer_value, value_truncateOperator, value_restrictOperator, heatRegularizer_value]

end EulerHeatRegularizedPaths

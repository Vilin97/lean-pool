/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate
public import LeanPool.NavierStokesAndEuler.Euler.MetricPathConvergence

@[expose] public section

/-! The actual finite Gevrey metric energy passes to strong Sobolev limits. -/

noncomputable section

namespace EulerGevreyEnergyLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricComparison
  EulerGevreyDifferentiatedEquation EulerGevreyMetricEstimate EulerGevreyRestriction
  EulerMetricPathConvergence EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual energy coordinates depend continuously on the Sobolev field. -/
theorem energyValues_continuous {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) :
    Continuous (energyValues period q N hN) := by
  apply continuous_pi
  intro I
  apply continuous_pi
  intro a
  exact (energyWordOperator period q N hN I a).continuous.congr
    (fun u => energyWordOperator_apply period q N hN I a u)

/-- The actual finite Gevrey metric energy is continuous in its Sobolev field, including zero energy. -/
theorem energyNorm_continuous {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) :
    Continuous (energyNorm period N hN ρ K) := by
  unfold energyNorm weightedMetricSum
  apply continuous_finsetSum
  intro I _
  apply Continuous.const_mul
  exact familyMetricNorm_continuous.comp
    (continuous_const.prodMk ((continuous_apply I).comp (energyValues_continuous period 6 N hN)))

/-- Restriction preserving the derivative cutoff leaves the actual Gevrey energy unchanged. -/
theorem energyNorm_restrict {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N+6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period p) :
    energyNorm period N hN ρ K (restrictOperator period hqp u) =
      energyNorm period N (hN.trans hqp) ρ K u := by
  unfold energyNorm
  rw [energyValues_restrict]

/-- A genuine strong lower-order limit retains every finite metric-energy bound whose derivative cutoff is retained. -/
theorem energyNorm_limit_bound {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N+6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : ℕ → SobolevSpace period p) (e : SobolevSpace
      period q)
    (h : Filter.Tendsto (fun n => restrictOperator period hqp (u n)) Filter.atTop (𝓝 e))
    (M : ℝ) (hb : ∀ n, energyNorm period N (hN.trans hqp) ρ K (u n) ≤ M) :
    energyNorm period N hN ρ K e ≤ M := by
  apply le_of_tendsto ((energyNorm_continuous period N hN ρ K).continuousAt.tendsto.comp h)
  exact Filter.Eventually.of_forall (fun n => by
    change energyNorm period N hN ρ K (restrictOperator period hqp (u n)) ≤ M
    rw [energyNorm_restrict]
    exact hb n)

end EulerGevreyEnergyLimit

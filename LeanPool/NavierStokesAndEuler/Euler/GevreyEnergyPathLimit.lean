/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyEnergyCutoff

@[expose] public section

/-! Quantitative finite Gevrey bounds survive the actual strong time-path limit. -/

noncomputable section

namespace EulerGevreyEnergyPathLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricEstimate
  EulerGevreyEnergyLimit EulerGevreyEnergyCutoff
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every retained Gevrey cutoff of the actual strong path limit keeps the genuine uniform approximation bound. -/
theorem energyNorm_path_limit_bound {p q N : ℕ} (hqp : q ≤ p) (hN : N+6 ≤ p) (T : ℝ)
    (ρ : Icc (0 : ℝ) T → ℝ) (hρ : ∀ t, 0 < ρ t)
    (K : Icc (0 : ℝ) T → LiftL2 period →L[ℝ] LiftL2 period)
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period p))
    (e : C(Icc (0 : ℝ) T,SobolevSpace period q))
    (hconv : Filter.Tendsto (fun n => (restrictOperator period hqp).compLeftContinuous ℝ (Icc (0 :
      ℝ) T) (u n))
      Filter.atTop (𝓝 e))
    (B : Icc (0 : ℝ) T → ℝ)
    (hb : ∀ n t, energyNorm period N hN (ρ t) (K t) (u n t) ≤ B t)
    (P : ℕ) (hPN : P ≤ N) (hP : P+6 ≤ q) :
    ∀ t, energyNorm period P hP (ρ t) (K t) (e t) ≤ B t := by
  intro t
  have ht := (ContinuousMap.evalCLM ℝ t).continuous.tendsto e |>.comp hconv
  apply energyNorm_limit_bound period hqp P hP (ρ t) (K t) (fun n => u n t) (e t) ht (B t)
  intro n
  exact (energyNorm_cutoff_mono period hPN hN (ρ t) (hρ t) (K t) (u n t)).trans (hb n t)

end EulerGevreyEnergyPathLimit

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricComparison
public import LeanPool.NavierStokesAndEuler.Euler.GevreyTransportCommutator
import LeanPool.NavierStokesAndEuler.Euler.GevreyDifferentiatedEquation

/-! Exact restriction compatibility of actual finite Gevrey energies and derivative losses. -/

@[expose] public section


noncomputable section

namespace EulerGevreyRestriction

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
    EulerSpatialSobolevInverse
  EulerH6Pressure EulerSobolevGevreyOperators EulerSobolevWordLevel EulerGevreyMetricComparison
  EulerGevreyDifferentiatedEquation EulerBaseWordMetric EulerGevreyBaseTransport
      EulerSobolevTransportCommutator

variable (period : ℝ) [Fact (0 < period)]

/-- Actual Gevrey norms are identical under every restriction retaining their derivative cutoff. -/
theorem weightedNorm_restrict {p q : ℕ} (hqp : q ≤ p) (r N : ℕ) (hN : N + r ≤ q) (ρ : ℝ)
    (u : SobolevSpace period p) :
    weightedNorm period r N ρ (restrictOperator period hqp u) = weightedNorm period r N ρ u := by
  apply Finset.sum_congr rfl
  intro n hn
  apply congrArg (fun x : ℝ => EulerPacketWeights.weight ρ n*x)
  exact blockNorm_unique period (toJet period (restrictOperator period hqp u)) (toJet period u) rfl
    (by have := Finset.mem_range.mp hn; omega) (by have := Finset.mem_range.mp hn; omega)

/-- The actual radius-loss sum is identical under every restriction retaining its cutoff. -/
theorem weightedLoss_restrict {p q : ℕ} (hqp : q ≤ p) (r N : ℕ) (hN : N + r ≤ q) (ρ : ℝ)
    (u : SobolevSpace period p) :
    weightedLoss period r N ρ (restrictOperator period hqp u) = weightedLoss period r N ρ u := by
  apply Finset.sum_congr rfl
  intro n hn
  apply congrArg (fun x : ℝ => (n : ℝ)*EulerPacketWeights.weight ρ n*x)
  exact blockNorm_unique period (toJet period (restrictOperator period hqp u)) (toJet period u) rfl
    (by have := Finset.mem_range.mp hn; omega) (by have := Finset.mem_range.mp hn; omega)

/-- Actual derivative words agree after restricting the input to any sufficiently high Sobolev
level. -/
theorem wordAtLevel_restrict {p q r n : ℕ} (hqp : q ≤ p) (w : Fin n → Fin 4) (hq : n + r ≤ q)
    (u : SobolevSpace period p) :
    wordAtLevel period r n w hq (restrictOperator period hqp u) = wordAtLevel period r n w
        (hq.trans hqp) u := by
  apply value_injective period
  rw [wordAtLevel_value, wordAtLevel_value]
  exact EulerPressureJetIdentities.SpatialJet.word_unique _ _ rfl (by omega) (by omega) w

/-- Every literal metric-energy derivative is unchanged by a valid Sobolev restriction. -/
theorem energyValues_restrict {p q : ℕ} (hqp : q ≤ p) (r N : ℕ) (hN : N + r ≤ q)
    (u : SobolevSpace period p) :
    energyValues period r N hN (restrictOperator period hqp u) = energyValues period r N (hN.trans
        hqp) u := by
  funext I a
  rw [← energyWordOperator_apply, ← energyWordOperator_apply]
  change value period (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega)
    (wordAtLevel period r I.1.val I.2 (by
        have := I.1.isLt; omega) (restrictOperator period hqp u))) = _
  exact congrArg (fun x => value period (wordAtLevel period 0 a.1.val a.2 (by
      have := a.1.isLt; omega) x))
    (wordAtLevel_restrict period hqp I.2 (by have := I.1.isLt; omega) u)

/-- The complete-solution truncation leaves every retained actual Gevrey norm unchanged. -/
theorem weightedNorm_truncate {s : ℕ} (r N : ℕ) (hN : N + r ≤ s) (ρ : ℝ)
    (u : SobolevSpace period (s + 1)) :
    weightedNorm period r N ρ (truncateOperator period s u) = weightedNorm period r N ρ u :=
  weightedNorm_restrict period (by omega : s ≤ s+1) r N hN ρ u

/-- The complete-solution truncation leaves the retained radius-loss sum unchanged. -/
theorem weightedLoss_truncate {s : ℕ} (r N : ℕ) (hN : N + r ≤ s) (ρ : ℝ)
    (u : SobolevSpace period (s + 1)) :
    weightedLoss period r N ρ (truncateOperator period s u) = weightedLoss period r N ρ u :=
  weightedLoss_restrict period (by omega : s ≤ s+1) r N hN ρ u

end EulerGevreyRestriction

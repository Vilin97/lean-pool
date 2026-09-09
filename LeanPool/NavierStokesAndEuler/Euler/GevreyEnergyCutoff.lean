/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate
import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
import LeanPool.NavierStokesAndEuler.ForMathlib.FiniteSum

/-! Monotonicity of the actual finite Gevrey metric energy in the external cutoff. -/

@[expose] public section


noncomputable section

namespace EulerGevreyEnergyCutoff

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricComparison
  EulerGevreyMetricEstimate  EulerEnergyWordCoordinates
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy EulerPacketWeights EulerBaseWordMetric

/-- The literal inclusion of external words into a larger cutoff. -/
def externalWordInclusion {N M : ℕ} (hNM : N ≤ M) (I : ExternalWord N) : ExternalWord M :=
  ⟨Fin.castLE (Nat.succ_le_succ hNM) I.1,I.2⟩

/-- Increasing the cutoff does not identify distinct derivative words. -/
theorem externalWordInclusion_injective {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (externalWordInclusion hNM) := by
  intro I J h
  obtain ⟨i,w⟩ := I
  obtain ⟨j,v⟩ := J
  have h1 := congrArg Sigma.fst h
  have hij : i=j := Fin.castLE_injective (Nat.succ_le_succ hNM) h1
  subst j
  have hw : w=v := by
    have hh := (Sigma.mk.inj h).2
    exact eq_of_heq hh
  subst v
  rfl

variable (period : ℝ) [Fact (0 < period)]

/-- The retained energy coordinates are identical in a larger cutoff. -/
theorem energyValues_inclusion {s N M q : ℕ} (hNM : N ≤ M) (hM : M + q ≤ s)
    (u : SobolevSpace period s) (I : ExternalWord N) :
    energyValues period q M hM u (externalWordInclusion hNM I) =
      energyValues period q N (by omega) u I := by
  funext a
  rw [energyValues_eq_word,energyValues_eq_word]
  rfl

/-- The literal finite Gevrey metric energy increases with its external derivative cutoff. -/
theorem energyNorm_cutoff_mono {s N M : ℕ} (hNM : N ≤ M) (hM : M + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    energyNorm period N (by omega) ρ K u ≤ energyNorm period M hM ρ K u := by
  unfold energyNorm weightedMetricSum
  apply NavierStokesAndEuler.sum_le_sum_of_injOn (externalWordInclusion hNM)
    (externalWordInclusion_injective hNM).injOn (Finset.subset_univ _)
  · intro I _
    rw [energyValues_inclusion]
    exact le_refl _
  · intro I _ _
    exact mul_nonneg (weight_pos hρ I.1.val).le (Real.sqrt_nonneg _)

end EulerGevreyEnergyCutoff

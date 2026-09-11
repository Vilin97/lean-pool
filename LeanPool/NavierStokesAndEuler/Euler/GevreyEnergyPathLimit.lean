/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate
import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
import LeanPool.NavierStokesAndEuler.ForMathlib.FiniteSum
import LeanPool.NavierStokesAndEuler.Euler.GevreyDifferentiatedEquation
import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction
import LeanPool.NavierStokesAndEuler.Euler.MetricPathConvergence

/-! Quantitative finite Gevrey bounds survive the actual strong time-path limit. -/

section

/-! The actual finite Gevrey metric energy passes to strong Sobolev limits. -/

@[expose] public section

noncomputable section

namespace EulerGevreyEnergyLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricComparison
  EulerGevreyDifferentiatedEquation EulerGevreyMetricEstimate EulerGevreyRestriction
  EulerMetricPathConvergence EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual energy coordinates depend continuously on the Sobolev field. -/
theorem energyValues_continuous {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) :
    Continuous (energyValues period q N hN) := by
  apply continuous_pi
  intro I
  apply continuous_pi
  intro a
  exact (energyWordOperator period q N hN I a).continuous.congr
    (fun u => energyWordOperator_apply period q N hN I a u)

/-- The actual finite Gevrey metric energy is continuous in its Sobolev field, including zero
energy. -/
theorem energyNorm_continuous {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) :
    Continuous (energyNorm period N hN ρ K) := by
  unfold energyNorm weightedMetricSum
  apply continuous_finsetSum
  intro I _
  apply Continuous.const_mul
  exact familyMetricNorm_continuous.comp
    (continuous_const.prodMk ((continuous_apply I).comp (energyValues_continuous period 6 N hN)))

/-- Restriction preserving the derivative cutoff leaves the actual Gevrey energy unchanged. -/
theorem energyNorm_restrict {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period p) :
    energyNorm period N hN ρ K (restrictOperator period hqp u) =
      energyNorm period N (hN.trans hqp) ρ K u := by
  unfold energyNorm
  rw [energyValues_restrict]

/-- A genuine strong lower-order limit retains every finite metric-energy bound whose derivative
cutoff is retained. -/
theorem energyNorm_limit_bound {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N + 6 ≤ q) (ρ : ℝ)
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

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerGevreyEnergyPathLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricEstimate
  EulerGevreyEnergyLimit EulerGevreyEnergyCutoff
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every retained Gevrey cutoff of the actual strong path limit keeps the genuine uniform
approximation bound. -/
theorem energyNorm_path_limit_bound {p q N : ℕ} (hqp : q ≤ p) (hN : N + 6 ≤ p) (T : ℝ)
    (ρ : Icc (0 : ℝ) T → ℝ) (hρ : ∀ t, 0 < ρ t)
    (K : Icc (0 : ℝ) T → LiftL2 period →L[ℝ] LiftL2 period)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period p))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hconv : Filter.Tendsto (fun n => (restrictOperator period hqp).compLeftContinuous ℝ (Icc (0 :
        ℝ) T) (u n))
      Filter.atTop (𝓝 e))
    (B : Icc (0 : ℝ) T → ℝ)
    (hb : ∀ n t, energyNorm period N hN (ρ t) (K t) (u n t) ≤ B t)
    (P : ℕ) (hPN : P ≤ N) (hP : P + 6 ≤ q) :
    ∀ t, energyNorm period P hP (ρ t) (K t) (e t) ≤ B t := by
  intro t
  have ht := (ContinuousMap.evalCLM ℝ t).continuous.tendsto e |>.comp hconv
  apply energyNorm_limit_bound period hqp P hP (ρ t) (K t) (fun n => u n t) (e t) ht (B t)
  intro n
  exact (energyNorm_cutoff_mono period hPN hN (ρ t) (hρ t) (K t) (u n t)).trans (hb n t)

end EulerGevreyEnergyPathLimit

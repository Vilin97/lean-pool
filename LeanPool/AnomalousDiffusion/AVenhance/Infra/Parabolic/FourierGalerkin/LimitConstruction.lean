/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitRepresentation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductCompactness

/-!
# Synchronized path and product-space limits

The pointwise weakly continuous representative, Bochner time-space limits, and product-space
limits are extracted along one common subsequence of the concrete Galerkin family.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- One subsequence carries the pointwise weak path, the Bochner time-space limits, and the
product-space scalar and gradient limits. The path retains its trace and all-times scalar
bound. -/
theorem FrozenDriftProblem.exists_synchronized_weak_product_limit (P : FrozenDriftProblem) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ u : Icc (0 : ℝ) 1 → ScalarTorusL2,
      ∃ U : ScalarTimeL2, ∃ G : GradientTimeL2,
      ∃ Uprod : ScalarProductTimeL2, ∃ Gprod : GradientProductTimeL2,
        (∀ v, Continuous (fun t => inner ℝ (u t) v)) ∧
        (∀ t v, Tendsto (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
          (𝓝 (inner ℝ (u t) v))) ∧
        (∀ v, Tendsto (fun n => inner ℝ (scalarTimeLp P (σ n)) v) atTop
          (𝓝 (inner ℝ U v))) ∧
        (∀ v, Tendsto (fun n => inner ℝ (gradientTimeLp P (σ n)) v) atTop
          (𝓝 (inner ℝ G v))) ∧
        (∀ v, Tendsto (fun n => inner ℝ (scalarProductLp P (σ n)) v) atTop
          (𝓝 (inner ℝ Uprod v))) ∧
        (∀ v, Tendsto (fun n => inner ℝ (gradientProductLp P (σ n)) v) atTop
          (𝓝 (inner ℝ Gprod v))) ∧
        (∀ t, ‖u t‖ ≤ P.scalarBound) ∧
        u ⟨0, by norm_num, by norm_num⟩ = P.initialTorusL2 ∧
        ‖U‖ ≤ P.scalarBound ∧ ‖G‖ ^ 2 ≤ P.gradientEnergyBound ∧
        ‖Uprod‖ ≤ P.scalarBound ∧ ‖Gprod‖ ^ 2 ≤ P.gradientEnergyBound := by
  obtain ⟨σ₀, hσ₀, u, U, G, hucont, huweak, hUweak, hGweak, hubound, hutrace,
      hUbound, hGbound⟩ := P.exists_simultaneous_weak_limit
  obtain ⟨σ₁, hσ₁, Uprod, Gprod, hUprod, hGprod, hUprodBound, hGprodBound⟩ :=
    P.exists_product_weak_subsequence_of_sequence σ₀
  refine ⟨σ₀ ∘ σ₁, hσ₀.comp hσ₁, u, U, G, Uprod, Gprod, hucont, ?_, ?_, ?_, ?_, ?_,
    hubound, hutrace, hUbound, hGbound, hUprodBound, hGprodBound⟩
  · intro t v
    exact (huweak t v).comp hσ₁.tendsto_atTop
  · intro v
    exact (hUweak v).comp hσ₁.tendsto_atTop
  · intro v
    exact (hGweak v).comp hσ₁.tendsto_atTop
  · intro v
    exact hUprod v
  · intro v
    exact hGprod v

end AVenhance.Infra.Parabolic.FourierGalerkin

end

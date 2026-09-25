/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Step 2: Bellman Lower Bound  ✓ FULLY VERIFIED
-/
module

public import LeanPool.BicausalOT.BicausalOT.Defs


/-!
# LowerBound

Supporting results for bicausal optimal transport and measurable selection.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ENNReal

noncomputable section

variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

omit [MeasurableSpace X₀] [MeasurableSpace Y₀] in
theorem V₀_le_cost_pointwise
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) (γ : Measure (X₁ × Y₁))
    (hγ : γ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    V₀ c₀ c₁ κ_μ κ_ν z₀ ≤ c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂γ := by
  unfold V₀; gcongr; exact iInf₂_le γ hγ

theorem bellman_lower_bound
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (kd : KernelDecomp π)
    (h_feas : ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂kd.γ₀
    ≤ totalCost c₀ c₁ kd.γ₀ kd.γ₁ := by
  unfold totalCost; apply lintegral_mono_ae
  filter_upwards [h_feas] with z₀ hz₀
  exact V₀_le_cost_pointwise c₀ c₁ κ_μ κ_ν z₀ (kd.γ₁ z₀) hz₀

end

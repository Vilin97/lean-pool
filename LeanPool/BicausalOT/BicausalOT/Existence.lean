/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Step 5: Existence of optimal coupling  ✓ FULLY VERIFIED
  Uses Mathlib's LowerSemicontinuousOn.exists_isMinOn (no axiom needed).
-/
import LeanPool.BicausalOT.BicausalOT.Defs
import Mathlib.Topology.Semicontinuity.Basic

open MeasureTheory ProbabilityTheory Set ENNReal

noncomputable section

variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem optimal_kernel_exists_pointwise
    [TopologicalSpace (Measure (X₁ × Y₁))]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀)
    (h_ne : (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (h_compact : IsCompact (FeasibleSet₀ κ_μ κ_ν z₀ :
        Set (Measure (X₁ × Y₁))))
    (h_lsc : LowerSemicontinuousOn
        (fun γ : Measure (X₁ × Y₁) => ∫⁻ z₁, c₁ (z₀, z₁) ∂γ)
        (FeasibleSet₀ κ_μ κ_ν z₀)) :
    ∃ γ_star ∈ FeasibleSet₀ κ_μ κ_ν z₀,
      ∀ γ ∈ FeasibleSet₀ κ_μ κ_ν z₀,
        ∫⁻ z₁, c₁ (z₀, z₁) ∂γ_star ≤ ∫⁻ z₁, c₁ (z₀, z₁) ∂γ := by
  obtain ⟨a, ha_mem, ha_min⟩ := h_lsc.exists_isMinOn h_ne h_compact
  exact ⟨a, ha_mem, fun γ hγ => ha_min hγ⟩

end

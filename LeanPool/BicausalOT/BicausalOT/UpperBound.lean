/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Step 3: Upper Bound via ε-optimal selection
-/
module

public import LeanPool.BicausalOT.BicausalOT.Defs
public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.JankovVonNeumann


/-!
# UpperBound

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
theorem eps_optimal_kernel_bound
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_ne : ∀ z₀ : X₀ × Y₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)),
      (∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) ∧
      ∀ z₀, ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
        ≤ (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
            ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε := by
  obtain ⟨sel, h_feas, h_opt⟩ :=
    eps_optimal_selection (FeasibleSet₀ κ_μ κ_ν) h_ne
      (fun z₀ γ => ∫⁻ z₁, c₁ (z₀, z₁) ∂γ) ε hε
  exact ⟨sel, h_feas, h_opt⟩

theorem totalCost_le_V₀_plus_eps
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (γ₀ : Measure (X₀ × Y₀))
    (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
    (ε : ENNReal)
    (h_opt : ∀ z₀, ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
      ≤ (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε) :
    totalCost c₀ c₁ γ₀ γ₁
    ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ := by
  unfold totalCost; apply lintegral_mono; intro z₀
  change c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀) ≤ V₀ c₀ c₁ κ_μ κ_ν z₀ + ε
  have h := h_opt z₀
  have hV : V₀ c₀ c₁ κ_μ κ_ν z₀ = c₀ z₀ +
    ⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
      ∫⁻ z₁, c₁ (z₀, z₁) ∂m := rfl
  rw [hV]
  calc c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
      ≤ c₀ z₀ + ((⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε) := by gcongr
    _ = c₀ z₀ + (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε := by rw [← add_assoc]

end

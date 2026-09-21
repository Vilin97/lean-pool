/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Step 4: Value Representation (equality)  ✓ FULLY VERIFIED
  Combines lower and upper bounds.
-/
import LeanPool.BicausalOT.BicausalOT.Defs
import LeanPool.BicausalOT.BicausalOT.LowerBound
import LeanPool.BicausalOT.BicausalOT.UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory ProbabilityTheory Set ENNReal

noncomputable section

variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem bellman_value_geq
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀
    ≤ ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁ := by
  apply le_iInf; intro γ₀; apply le_iInf; intro γ₁
  apply le_iInf; intro h_coup; apply le_iInf; intro h_feas
  calc ⨅ (γ₀' : Measure (X₀ × Y₀)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀'
      ≤ ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ := iInf₂_le γ₀ h_coup
    _ ≤ totalCost c₀ c₁ γ₀ γ₁ := by
        unfold totalCost; apply lintegral_mono; intro z₀
        exact V₀_le_cost_pointwise c₀ c₁ κ_μ κ_ν z₀ (γ₁ z₀) (h_feas z₀)

theorem bellman_value_leq_aux
    {μ₀ : Measure X₀} {ν₀ : Measure Y₀}
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_Gamma_ne : ∀ z₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (γ₀ : Measure (X₀ × Y₀))
    (h_coup : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
    (ε : ENNReal) (hε : 0 < ε) :
    ⨅ (γ₀' : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀' γ₁
    ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ := by
  obtain ⟨γ₁_sel, hγ₁_feas, hγ₁_opt⟩ :=
    eps_optimal_kernel_bound c₁ κ_μ κ_ν h_Gamma_ne ε hε
  calc ⨅ (γ₀' : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀' γ₁
      ≤ totalCost c₀ c₁ γ₀ γ₁_sel := by
        apply iInf_le_of_le γ₀; apply iInf_le_of_le γ₁_sel
        apply iInf_le_of_le h_coup; exact iInf_le _ hγ₁_feas
    _ ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ :=
        totalCost_le_V₀_plus_eps c₀ c₁ κ_μ κ_ν γ₀ γ₁_sel ε hγ₁_opt

theorem bellman_value_leq
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀) [IsProbabilityMeasure ν₀]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_Gamma_ne : ∀ z₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (h_prob : ∀ γ₀ ∈ CouplingSet₀ μ₀ ν₀, γ₀ Set.univ ≤ 1) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    ≤ ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ := by
  apply le_iInf; intro γ₀; apply le_iInf; intro h_coup
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨γ₁_sel, hγ₁_feas, hγ₁_opt⟩ :=
    eps_optimal_kernel_bound c₁ κ_μ κ_ν h_Gamma_ne ε (by positivity)
  calc ⨅ (γ₀' : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀' γ₁
      ≤ totalCost c₀ c₁ γ₀ γ₁_sel := by
        apply iInf_le_of_le γ₀; apply iInf_le_of_le γ₁_sel
        apply iInf_le_of_le h_coup; exact iInf_le _ hγ₁_feas
    _ ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ↑ε) ∂γ₀ :=
        totalCost_le_V₀_plus_eps c₀ c₁ κ_μ κ_ν γ₀ γ₁_sel ↑ε hγ₁_opt
    _ = ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ + ↑ε * γ₀ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ + ↑ε := by
        gcongr
        calc ↑ε * γ₀ Set.univ ≤ ↑ε * 1 := by
              gcongr; exact h_prob γ₀ h_coup
          _ = ↑ε := mul_one _

/-- **Main Theorem**: Bellman value representation (equality). -/
theorem bellman_value_eq
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀) [IsProbabilityMeasure ν₀]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_Gamma_ne : ∀ z₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (h_prob : ∀ γ₀ ∈ CouplingSet₀ μ₀ ν₀, γ₀ Set.univ ≤ 1) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    = ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ :=
  le_antisymm
    (bellman_value_leq c₀ c₁ μ₀ ν₀ κ_μ κ_ν h_Gamma_ne h_prob)
    (bellman_value_geq c₀ c₁ μ₀ ν₀ κ_μ κ_ν)

end

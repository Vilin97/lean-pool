/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Proposition 1: Bicausal ⟺ Kernel Decomposition  ✓ FULLY VERIFIED
-/
import LeanPool.BicausalOT.BicausalOT.Defs

open MeasureTheory ProbabilityTheory Set ENNReal

noncomputable section

variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]

theorem kernel_decomp_implies_bicausal
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (kd : KernelDecomp π)
    (h_coupling : kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀)
    (h_feas : ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    IsBicausal₂ μ₀ ν₀ κ_μ κ_ν π :=
  ⟨kd, h_coupling, h_feas⟩

theorem bicausal_implies_decomp
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (hbc : IsBicausal₂ μ₀ ν₀ κ_μ κ_ν π) :
    ∃ (kd : KernelDecomp π),
      kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀ := by
  obtain ⟨kd, h_coupling, h_feas⟩ := hbc
  exact ⟨kd, h_coupling, h_feas⟩

end

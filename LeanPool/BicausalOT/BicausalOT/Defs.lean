/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Bicausal OT — Definitions
  Couplings, feasible sets, kernel decomposition, bicausality, Bellman value.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic

open MeasureTheory ProbabilityTheory Set ENNReal

noncomputable section

variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]

def CouplingSet₀ (μ₀ : Measure X₀) (ν₀ : Measure Y₀) :
    Set (Measure (X₀ × Y₀)) :=
  { γ | γ.map Prod.fst = μ₀ ∧ γ.map Prod.snd = ν₀ }

def FeasibleSet₀
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) : Set (Measure (X₁ × Y₁)) :=
  { γ | γ.map Prod.fst = κ_μ z₀.1 ∧ γ.map Prod.snd = κ_ν z₀.2 }

structure KernelDecomp
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁))) where
  γ₀ : Measure (X₀ × Y₀)
  γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)
  γ₁_measurable : Measurable γ₁
  decomp : ∀ ⦃s : Set ((X₀ × X₁) × (Y₀ × Y₁))⦄,
    MeasurableSet s →
    π s = ∫⁻ z₀, (γ₁ z₀) {z₁ | ((z₀.1, z₁.1), (z₀.2, z₁.2)) ∈ s} ∂γ₀

def IsBicausal₂
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁))) : Prop :=
  ∃ (kd : KernelDecomp π),
    kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
    ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀

variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

def V₀ (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) : ENNReal :=
  c₀ z₀ + ⨅ (γ : Measure (X₁ × Y₁)) (_ : γ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
    ∫⁻ z₁, c₁ (z₀, z₁) ∂γ

def totalCost (kd_γ₀ : Measure (X₀ × Y₀))
    (kd_γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)) : ENNReal :=
  ∫⁻ z₀, (c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂(kd_γ₁ z₀)) ∂kd_γ₀

end

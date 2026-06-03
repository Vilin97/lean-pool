/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

/-!
# LeanPool.RlTheoryInLean.MeasureTheory.Measure.Prod
-/

open MeasureTheory MeasureTheory.Measure  ProbabilityTheory Finset NNReal ENNReal Preorder Filter

namespace MeasureTheory.Measure

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma prod_preimage_snd
  (μ : Measure α) (ν : Measure β) (hν : SFinite ν) (A : Set β) :
  (μ.prod ν) (Prod.snd ⁻¹' A) = μ Set.univ * ν A := by
    have h : Prod.snd ⁻¹' A = (Set.univ : Set α) ×ˢ A := by
      ext p; obtain ⟨x, y⟩ := p; simp
    rw [h, Measure.prod_prod]

lemma prod_preimage_fst
  (μ : Measure α) (ν : Measure β) (hν : SFinite ν) (A : Set α) :
  (μ.prod ν) (Prod.fst ⁻¹' A) = μ A * ν Set.univ := by
    have h : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set β) := by
      ext p; obtain ⟨x, y⟩ := p; simp
    rw [h, Measure.prod_prod]

lemma map_prodMk_dirac
  {X : α → β} {Y : α → γ} {μ : Measure α}
  {C : β} (hC : ∀ᵐ a ∂μ, X a = C)
  (hY : Measurable Y) [SFinite (Measure.map Y μ)] :
  (Measure.map (fun a ↦ (X a, Y a)) μ) =
    (Measure.dirac C).prod (Measure.map Y μ) := by
  have h₁ : Measure.map (fun a ↦ (X a, Y a)) μ = Measure.map (fun a ↦ (C, Y a)) μ := by
    apply Measure.map_congr
    filter_upwards [hC] with x hx
    rw [hx]
  rw [h₁, dirac_prod, Measure.map_map measurable_prodMk_left hY]
  rfl

end MeasureTheory.Measure

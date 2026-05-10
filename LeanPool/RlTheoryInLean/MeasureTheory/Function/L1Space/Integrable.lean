/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open Filter

namespace MeasureTheory
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

lemma integrable_of_norm_le {α : Type*} {β : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] [NormedAddCommGroup β] {f : α → β}
  (hm : AEStronglyMeasurable f μ) (hbdd : ∃ C, ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C)
  : Integrable f μ := by
  obtain ⟨C, hC⟩ := hbdd
  apply integrable_of_norm_sub_le (f₀ := 0) (g := fun ω => C)
  · exact hm
  · apply integrable_const
  · apply integrable_const
  · apply Eventually.mono hC
    intro ω hC
    simp only [Pi.zero_apply, zero_sub, norm_neg]
    exact hC

lemma Integrable.finset_sum
  {α ι : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι} {f : ι → α → ℝ}
  (hf : ∀ i ∈ s, Integrable (f i) μ) :
  Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    apply Integrable.add
    · exact hf a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MeasureTheory

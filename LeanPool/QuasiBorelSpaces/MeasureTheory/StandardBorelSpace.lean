/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.StandardBorelSpace

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.StandardBorelSpace`.
-/


namespace MeasureTheory

lemma standardBorelSpace_iff (A : Type*) [MeasurableSpace A]
    : StandardBorelSpace A
    ↔ Countable A ∧ DiscreteMeasurableSpace A ∨ Nonempty (A ≃ᵐ ℝ) := by
  apply Iff.intro
  · intro h₁
    by_cases h₂ : Countable A
    · simp only [h₂, true_and]
      cases finite_or_infinite A with
      | inl h₃ =>
        obtain ⟨n, ⟨h₄⟩⟩ := MeasureTheory.exists_nat_measurableEquiv_range_coe_fin_of_finite A
        left
        constructor
        intro s
        have h₅ : MeasurableSet (h₄ '' s) := by
          simp only [Set.image, measurableSet_setOf]
          fun_prop
        have := h₄.measurable h₅
        simpa only [MeasurableEquiv.preimage_image] using this
      | inr h₃ =>
        obtain ⟨h₄⟩ := MeasureTheory.measurableEquiv_range_coe_nat_of_infinite_of_countable A
        left
        constructor
        intro s
        have h₅ : MeasurableSet (h₄ '' s) := by
          simp only [Set.image, measurableSet_setOf]
          fun_prop
        have := h₄.measurable h₅
        simpa only [MeasurableEquiv.preimage_image] using this
    · exact .inr ⟨PolishSpace.measurableEquivOfNotCountable h₂ not_countable⟩
  · rintro (⟨h₁, h₂⟩|⟨⟨h₂⟩⟩)
    · infer_instance
    · let := TopologicalSpace.induced h₂.toEquiv inferInstance
      let := Equiv.polishSpace_induced h₂.toEquiv
      refine ⟨inferInstance, ⟨?_⟩, inferInstance⟩
      ext s
      rw [borel_comap, MeasurableSpace.measurableSet_comap]
      apply Iff.intro
      · intro hs
        use h₂.symm ⁻¹' s, h₂.symm.measurable hs
        simp only [
          MeasurableEquiv.coe_toEquiv, ← Set.preimage_comp,
          MeasurableEquiv.symm_comp_self, Set.preimage_id_eq, id_eq]
      · rintro ⟨s, hs, rfl⟩
        apply h₂.measurable hs

end MeasureTheory

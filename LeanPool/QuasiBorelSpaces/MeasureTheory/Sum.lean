/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Sum

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Sum`.
-/

open scoped MeasureTheory


namespace Sum

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

instance
    [TopologicalSpace A] [hA : BorelSpace A]
    [TopologicalSpace B] [hB : BorelSpace B]
    : BorelSpace (A ⊕ B) where
  measurable_eq := by
    ext s
    have
        : MeasurableSet[borel (A ⊕ B)] s
        ↔ MeasurableSet[borel A] (Sum.inl ⁻¹' s)
        ∧ MeasurableSet[borel B] (Sum.inr ⁻¹' s) := by
      apply Iff.intro
      · intro h
        induction h with
        | basic u hu =>
          simp only [isOpen_sum_iff, Set.mem_setOf_eq] at hu
          simp only [Set.mem_setOf_eq, hu, MeasurableSpace.measurableSet_generateFrom, and_self]
        | empty => simp only [Set.preimage_empty, MeasurableSet.empty, and_self]
        | compl t _ ih => simp only [Set.preimage_compl, MeasurableSet.compl_iff, ih, and_self]
        | iUnion f _ ih =>
          simp only [Set.preimage_iUnion]
          apply And.intro
          · apply MeasurableSet.iUnion fun n ↦ (ih n).1
          · apply MeasurableSet.iUnion fun n ↦ (ih n).2
      · intro ⟨h₁, h₂⟩
        generalize hs₁ : Sum.inl ⁻¹' s = s₁
        generalize hs₂ : Sum.inr ⁻¹' s = s₂
        have : s = Sum.inl '' s₁ ∪ Sum.inr '' s₂ := by grind
        subst this
        clear hs₁ hs₂
        simp only [Set.preimage_union, Sum.inl_injective, Set.preimage_image_eq,
          Set.preimage_inl_image_inr, Set.union_empty, Set.preimage_inr_image_inl,
          Sum.inr_injective, Set.empty_union] at h₁ h₂
        apply MeasurableSet.union
        · induction h₁ with
          | basic u hu =>
            simp only [Set.mem_setOf_eq] at hu
            apply MeasurableSpace.measurableSet_generateFrom
            simp only [
              isOpen_sum_iff, Set.mem_setOf_eq, Sum.inl_injective, Set.preimage_image_eq,
              hu, Set.preimage_inr_image_inl, isOpen_empty, and_self]
          | empty => simp only [Set.image_empty, MeasurableSet.empty]
          | compl t _ ih =>
            have : Sum.inl '' tᶜ = (Sum.inl '' t)ᶜ \ (Sum.inr (β := B) '' Set.univ) := by grind
            rw [this]
            apply MeasurableSet.diff
            · apply MeasurableSet.compl
              apply ih
            · apply MeasurableSpace.measurableSet_generateFrom
              simp only [Set.image_univ, Set.mem_setOf_eq, isOpen_range_inr]
          | iUnion f _ ih => simp only [Set.image_iUnion, MeasurableSet.iUnion ih]
        · induction h₂ with
          | basic u hu =>
            simp only [Set.mem_setOf_eq] at hu
            apply MeasurableSpace.measurableSet_generateFrom
            simp only [
              isOpen_sum_iff, Set.mem_setOf_eq, Set.preimage_inl_image_inr, isOpen_empty,
              Sum.inr_injective, Set.preimage_image_eq, hu, and_self]
          | empty => simp only [Set.image_empty, MeasurableSet.empty]
          | compl t _ ih =>
            have : Sum.inr '' tᶜ = (Sum.inr '' t)ᶜ \ (Sum.inl (α := A) '' Set.univ) := by grind
            rw [this]
            apply MeasurableSet.diff
            · apply MeasurableSet.compl
              apply ih
            · apply MeasurableSpace.measurableSet_generateFrom
              simp only [Set.image_univ, Set.mem_setOf_eq, isOpen_range_inl]
          | iUnion f _ ih => simp only [Set.image_iUnion, MeasurableSet.iUnion ih]
    rw [hA.measurable_eq, hB.measurable_eq, measurableSet_sum_iff]
    exact this.symm

instance [StandardBorelSpace A] [StandardBorelSpace B] : StandardBorelSpace (A ⊕ B) where
  polish := by
    have ⟨_, _, _⟩ := ‹StandardBorelSpace A›.polish
    have ⟨_, _, _⟩ := ‹StandardBorelSpace B›.polish
    refine ⟨inferInstance, inferInstance, inferInstance⟩

instance
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    : DiscreteMeasurableSpace (A ⊕ B) where
  forall_measurableSet s := by
    simp only [measurableSet_sum_iff, MeasurableSet.of_discrete, and_self]

end Sum

/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.MeasureTheory.StandardBorelSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LeanPool.QuasiBorelSpaces.MeasureTheory.Sum

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Option

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Option`.
-/


variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

namespace MeasureTheory.Option

instance instMeasurableSpaceOptionLeanPool : MeasurableSpace (Option A) :=
  MeasurableSpace.comap (Option.elim' (Sum.inl ()) Sum.inr) inferInstance

instance [DiscreteMeasurableSpace A] : DiscreteMeasurableSpace (Option A) where
  forall_measurableSet s := by
    simp only [MeasurableSpace.measurableSet_comap]
    use Option.elim' (Sum.inl ()) Sum.inr '' s
    simp only [MeasurableSet.of_discrete, true_and]
    rw [Set.preimage_image_eq]
    intro x₁ x₂
    cases x₁ <;> cases x₂ <;> simp_all

@[simp, fun_prop]
lemma measurable_some : Measurable (some : A → Option A) := by
  rw [measurable_comap_iff]
  simp +unfoldPartialApp only [Function.comp, Option.elim'_some]
  fun_prop

@[fun_prop]
lemma measurable_elim (g : C) {h : B → C} (hh : Measurable h) : Measurable (Option.elim · g h) := by
  have : (Option.elim · g h) = Sum.elim (fun _ ↦ g) h ∘ Option.elim' (Sum.inl ()) Sum.inr := by
    ext x
    cases x <;> rfl
  simp only [this]
  apply Measurable.comp ?_ (comap_measurable _)
  fun_prop

@[fun_prop]
lemma measurable_elim' (g : C) {h : B → C} (hh : Measurable h) : Measurable (Option.elim' g h) := by
  have : Option.elim' g h = (Option.elim · g h) := by
    ext x
    cases x <;> rfl
  simp only [this]
  fun_prop

@[simp, fun_prop]
lemma measurable_isSome : Measurable (fun x : Option A ↦ x.isSome) := by
  have (x : Option A) : x.isSome = x.elim false (fun _ ↦ true) := by
    cases x <;> rfl
  simp only [this]
  fun_prop

instance [StandardBorelSpace A] : StandardBorelSpace (Option A) := by
  by_cases h : Countable A
  · infer_instance
  · have h₁ : ¬Countable (Option A) := by
      intro
      apply h
      apply Function.Injective.countable (Option.some_injective A)
    have h₂ : ¬Countable (Unit ⊕ A) := by
      intro
      apply h
      apply Function.Injective.countable (Sum.inr_injective (α := Unit))
    simp only [standardBorelSpace_iff, h₁, false_and, false_or]
    constructor
    have : StandardBorelSpace (Unit ⊕ A) := inferInstance
    simp only [standardBorelSpace_iff, h₂, false_and, false_or] at this
    apply MeasurableEquiv.trans ?_ this.some
    exact {
      toFun := Option.elim' (.inl ()) .inr
      invFun := Sum.elim (fun _ ↦ .none) .some
      right_inv x := by cases x <;> rfl
      left_inv x := by cases x <;> rfl
      measurable_toFun := by
        simp only [Equiv.coe_fn_mk]
        fun_prop
      measurable_invFun := by
        simp only [Equiv.coe_fn_symm_mk]
        fun_prop
    }

end MeasureTheory.Option

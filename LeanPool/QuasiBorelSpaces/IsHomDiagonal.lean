/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Prop
import LeanPool.QuasiBorelSpaces.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# LeanPool.QuasiBorelSpaces.IsHomDiagonal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.IsHomDiagonal`.
-/

namespace QuasiBorelSpace

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]

/-- The class of `QuasiBorelSpace`s where equality is a morphism. -/
class IsHomDiagonal (A : Type*) [QuasiBorelSpace A] where
  /-- Equality is a morphism. -/
  isHom_eq : IsHom (fun x : A × A ↦ x.1 = x.2)

export IsHomDiagonal (isHom_eq)
attribute [simp, fun_prop] isHom_eq

lemma isHom_eq'
    [IsHomDiagonal B] {f g : A → B} (hf : IsHom f) (hg : IsHom g)
    : IsHom fun x ↦ f x = g x := by
  fun_prop

instance
    [Countable A] [MeasurableSpace A]
    [DiscreteQuasiBorelSpace A]
    : IsHomDiagonal A where
  isHom_eq := by simp only [isHom_of_discrete_countable]

instance [IsHomDiagonal A] [IsHomDiagonal B] : IsHomDiagonal (A × B) where
  isHom_eq := by
    simp only [Prod.ext_iff]
    fun_prop

instance [IsHomDiagonal A] [IsHomDiagonal B] : IsHomDiagonal (A ⊕ B) where
  isHom_eq := by
    have {x y : A ⊕ B}
        : x = y
        ↔ x.elim
            (fun x ↦ y.elim (x = ·) (fun _ ↦ False))
            (fun x ↦ y.elim (fun _ ↦ False) (x = ·)) := by
      cases x <;> cases y <;>
        simp only [
          reduceCtorEq, Sum.elim_inr, Sum.elim_inl,
          Sum.inl.inj_iff, Sum.inr.inj_iff]
    simp only [this]
    fun_prop

instance : IsHomDiagonal ℝ where
  isHom_eq := by
    rw [isHom_def]
    intro φ hφ
    simp only [Prod.isHom_iff, isHom_ofMeasurableSpace] at ⊢ hφ
    rcases hφ with ⟨hφ₁, hφ₂⟩
    rw [←measurableSet_setOf]
    apply measurableSet_eq_fun <;> fun_prop

instance : IsHomDiagonal ENNReal where
  isHom_eq := by
    rw [isHom_def]
    intro φ hφ
    simp only [Prod.isHom_iff, isHom_ofMeasurableSpace] at ⊢ hφ
    rcases hφ with ⟨hφ₁, hφ₂⟩
    rw [←measurableSet_setOf]
    apply measurableSet_eq_fun <;> fun_prop

end QuasiBorelSpace

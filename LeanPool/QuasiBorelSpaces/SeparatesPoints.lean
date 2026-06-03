/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Prop
import LeanPool.QuasiBorelSpaces.Sigma
import LeanPool.QuasiBorelSpaces.Sum

/-!
# LeanPool.QuasiBorelSpaces.SeparatesPoints

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.SeparatesPoints`.
-/

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {I : Type*} [Countable I]
  {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]

namespace QuasiBorelSpace

/--
A `QuasiBorelSpace` _separates points_ if any two elements are equal iff all
morphism predicates agree on the elements.

This class is the `QuasiBorelSpace` analogue of `MeasurableSingletonClass`.
-/
class SeparatesPoints (A : Type*) [QuasiBorelSpace A] where
  /-- Two elements are equal iff they agree for all morphism predicates. -/
  separates (x y : A) : (∀ (p : A → Prop), IsHom p → p x → p y) → x = y

lemma separatesPoints_def
    [SeparatesPoints A] {x y : A}
    (h : ∀ (p : A → Prop), IsHom p → p x → p y)
    : x = y :=
  ‹SeparatesPoints A›.separates x y h

instance [MeasurableSpace A] [DiscreteQuasiBorelSpace A] : SeparatesPoints A where
  separates x y h := by
    apply h _ ?_ rfl
    rw [isHom_def]
    intro φ hφ
    simp only [isHom_iff_measurable] at ⊢ hφ
    fun_prop

instance [SeparatesPoints A] [SeparatesPoints B] : SeparatesPoints (A × B) where
  separates x y h := by
    ext
    · apply separatesPoints_def (fun p hp ↦ h (p ∘ Prod.fst) (by fun_prop))
    · apply separatesPoints_def (fun p hp ↦ h (p ∘ Prod.snd) (by fun_prop))

instance [∀ i, SeparatesPoints (P i)] : SeparatesPoints ((i : I) → P i) where
  separates f g h := by
    ext i
    apply separatesPoints_def
    intro p hp hfi
    apply h _ ?_ hfi
    fun_prop

instance [∀ i, SeparatesPoints (P i)] : SeparatesPoints ((i : I) × P i) where
  separates x y h := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    have : x₁ = y₁ := by
      apply h (fun z ↦ x₁ = z.1) ?_ rfl
      apply isHom_cases (f := fun z₁ _ ↦ x₁ = z₁) <;> fun_prop
    subst this
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    apply separatesPoints_def
    intro p hp hx₂
    classical
    specialize h (fun z ↦ if h : z.1 = x₁ then p (h ▸ z.2) else False)
    simp only [dite_else_false, ↓reduceDIte] at h
    apply h ?_ hx₂
    apply Sigma.isHom_elim
    intro z₁
    by_cases h : z₁ = x₁
    · subst h
      simp only [exists_const, hp]
    · simp only [h, IsEmpty.exists_iff, isHom_const']

instance [SeparatesPoints A] [SeparatesPoints B] : SeparatesPoints (A ⊕ B) where
  separates x y h := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        congr 1
        apply separatesPoints_def
        intro p hp hx
        apply h (Sum.elim p (fun _ ↦ False)) (by fun_prop) hx
      | inr y =>
        specialize h (Sum.elim (fun _ ↦ True) (fun _ ↦ False)) (by fun_prop)
        simp only [Sum.elim_inl, Sum.elim_inr, imp_false, not_true_eq_false] at h
    | inr x =>
      cases y with
      | inl y =>
        specialize h (Sum.elim (fun _ ↦ False) (fun _ ↦ True)) (by fun_prop)
        simp only [Sum.elim_inl, Sum.elim_inr, imp_false, not_true_eq_false] at h
      | inr y =>
        congr 1
        apply separatesPoints_def
        intro p hp hx
        apply h (Sum.elim (fun _ ↦ False) p) (by fun_prop) hx

instance [SeparatesPoints A] [SeparatesPoints B] : SeparatesPoints (QuasiBorelHom A B) where
  separates f g h := by
    ext x
    apply separatesPoints_def
    intro p hp hfx
    exact h (fun k ↦ p (k x)) (by fun_prop) hfx

instance
    [MeasurableSpace A]
    [MeasurableSpace.SeparatesPoints A]
    [MeasurableQuasiBorelSpace A]
    : SeparatesPoints A where
  separates x y h := by
    apply MeasurableSpace.separatesPoints_def
    intro X hX hx
    apply h (· ∈ X) ?_ hx
    rw [isHom_def]
    intro φ hφ
    simp only [isHom_iff_measurable] at ⊢ hφ
    apply Measurable.fun_comp ?_ hφ
    simp only [measurable_mem, hX]

end QuasiBorelSpace

/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Defs

/-!
# LeanPool.QuasiBorelSpaces.Chain

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Chain`.
-/


namespace QuasiBorelSpace.Chain

open OmegaCompletePartialOrder

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}

instance [Preorder A] [QuasiBorelSpace A] : QuasiBorelSpace (Chain A) where
  IsVar φ := ∀ i, IsHom (φ · i)
  isVar_const f i := by simp only [isHom_const']
  isVar_comp hf hφ i := by
    rw [←isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' hix hφ i := by
    apply isHom_cases ?_ (hφ · i)
    simp only [isHom_ofMeasurableSpace, hix]

@[local simp]
private lemma isHom_def [Preorder A] (φ : ℝ → Chain A) : IsHom φ ↔ ∀ i, IsHom (φ · i) := by
  rw [←isVar_iff_isHom]
  rfl

@[fun_prop]
lemma isHom_apply [Preorder A] (i : ℕ) : IsHom (fun (f : Chain A) ↦ f i) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[fun_prop]
lemma isHom_pi [Preorder B] {f : A → Chain B} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[simp]
lemma isHom_iff [Preorder B] {f : A → Chain B} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · intro hf i
    apply isHom_comp' (isHom_apply i) hf
  · exact isHom_pi

end QuasiBorelSpace.Chain

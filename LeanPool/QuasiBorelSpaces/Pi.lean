/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Prod
import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace


/-!
# Small Products of Quasi-Borel Spaces

This file defines small products of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· → ·` type.

See [HeunenKSY17], Proposition 16.
-/

namespace QuasiBorelSpace.Pi

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {I : Type*} {P : I → Type*} {_ : ∀ i, QuasiBorelSpace (P i)}

instance [∀ i, QuasiBorelSpace (P i)] : QuasiBorelSpace (∀i : I, P i) where
  IsVar φ := ∀ i, IsHom (φ · i)
  isVar_const f i := by simp only [isHom_const']
  isVar_comp hf hφ i := by
    rw [←isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' hix hφ i := by
    exact isHom_cases (by simp only [isHom_ofMeasurableSpace, hix]) (hφ · i)

@[local simp]
lemma isHom_def (φ : ℝ → ∀ i, P i) : IsHom φ ↔ ∀ i, IsHom (φ · i) := by
  rw [←isVar_iff_isHom]
  rfl

@[fun_prop]
lemma isHom_apply (i : I) : IsHom (fun (f : (i : I) → P i) ↦ f i) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[fun_prop]
lemma isHom_pi {f : A → ∀ i, P i} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[simp]
lemma isHom_iff {f : A → (i : I) → P i} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · fun_prop
  · exact isHom_pi

@[simp, fun_prop]
lemma isHom_eval (i) : IsHom (Function.eval i : (∀ i, P i) → P i) := by
  unfold Function.eval
  fun_prop

instance
    [∀ i, MeasurableSpace (P i)]
    [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (∀i, P i) where
  isHom_iff_measurable φ := by
    apply Iff.intro <;>
    · simp only [isHom_iff, isHom_iff_measurable]
      fun_prop

end QuasiBorelSpace.Pi

namespace OmegaQuasiBorelSpace.Pi

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {I : Type*} {P : I → Type*} [∀ i, OmegaQuasiBorelSpace (P i)]

instance : OmegaQuasiBorelSpace (∀i, P i) where
  isHom_ωSup := by
    simp only [ωSup, Pi.isHom_iff]
    intro i
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.coe_map, Pi.evalOrderHom_coe,
      Function.comp_apply, Function.eval]
    fun_prop

end OmegaQuasiBorelSpace.Pi

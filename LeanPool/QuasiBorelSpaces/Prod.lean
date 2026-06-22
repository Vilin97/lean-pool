/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Measure.Prod
import LeanPool.QuasiBorelSpaces.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace


/-!
# Binary Products of Quasi-Borel Spaces

This file defines binary products of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· × ·` type.

See [HeunenKSY17], Proposition 16.
-/

namespace QuasiBorelSpace.Prod

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {D : Type*} {_ : QuasiBorelSpace D}

instance [QuasiBorelSpace A] [QuasiBorelSpace B] : QuasiBorelSpace (A × B) where
  IsVar φ := IsHom (fun x ↦ Prod.fst (φ x)) ∧ IsHom (fun x ↦ Prod.snd (φ x))
  isVar_const x := by
    simp only [isHom_const', and_self]
  isVar_comp hf := by
    rintro ⟨hφ₁, hφ₂⟩
    refine ⟨isHom_comp' hφ₁ ?_, isHom_comp' hφ₂ ?_⟩ <;>
      simp only [isHom_ofMeasurableSpace, hf]
  isVar_cases' {ix} {φ} hix hφ := by
    refine ⟨isHom_cases (ix := ix) (f := fun n r ↦ (φ n r).1) ?_ (fun n ↦ (hφ n).1),
      isHom_cases (ix := ix) (f := fun n r ↦ (φ n r).2) ?_ (fun n ↦ (hφ n).2)⟩ <;>
      simp only [isHom_ofMeasurableSpace, hix]

@[local simp]
private lemma isHom_def (f : ℝ → A × B)
    : IsHom f ↔ IsHom (fun x ↦ (f x).1) ∧ IsHom (fun x ↦ (f x).2) := by
  rw [← isVar_iff_isHom]
  rfl

@[simp]
lemma isHom_fst : IsHom (Prod.fst : A × B → A) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all only [isHom_def, implies_true]

@[fun_prop]
lemma isHom_fst' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).1) :=
  isHom_comp isHom_fst hf

@[simp]
lemma isHom_snd : IsHom (Prod.snd : A × B → B) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all only [isHom_def, implies_true]

@[fun_prop]
lemma isHom_snd' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).2) :=
  isHom_comp isHom_snd hf

@[fun_prop]
lemma isHom_mk
    {f : A → B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    : IsHom (fun x ↦ (f x, g x)) := by
  rw [QuasiBorelSpace.isHom_def] at ⊢ hf hg
  simp only [isHom_def]
  grind

@[simp]
lemma isHom_iff (f : A → B × C) : IsHom f ↔ IsHom (fun x ↦ (f x).1) ∧ IsHom (fun x ↦ (f x).2) := by
  apply Iff.intro
  · intro hf
    exact ⟨isHom_fst' hf, isHom_snd' hf⟩
  · rintro ⟨h₁, h₂⟩
    exact isHom_mk h₁ h₂

instance
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableQuasiBorelSpace A] [MeasurableQuasiBorelSpace B]
    : MeasurableQuasiBorelSpace (A × B) where
  isHom_iff_measurable φ := by
    simp only [isHom_iff, isHom_iff_measurable]
    apply Iff.intro
    · rintro ⟨h₁, h₂⟩
      exact Measurable.prodMk h₁ h₂
    · intro h
      exact ⟨by fun_prop, by fun_prop⟩

@[fun_prop]
lemma isHom_map {f : A → B} {g : C → D} (hf : IsHom f) (hg : IsHom g) : IsHom (Prod.map f g) := by
  simp only [isHom_iff, Prod.map_fst, Prod.map_snd]
  apply And.intro <;> fun_prop

lemma isHom_of_uncurry
    {f : A → B → C} (hf : IsHom (Function.uncurry f))
    {g : D → A} (hg : IsHom g)
    {h : D → B} (hh : IsHom h)
    : IsHom fun x ↦ f (g x) (h x) := by
  exact isHom_comp' (f := Function.uncurry f) (g := fun x ↦ (g x, h x)) hf (by fun_prop)

end QuasiBorelSpace.Prod

namespace OmegaQuasiBorelSpace.Prod

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {A B : Type*} [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B]

instance : OmegaQuasiBorelSpace (A × B) where
  isHom_ωSup := by
    rw [Prod.isHom_iff]
    constructor <;>
    · apply isHom_ωSup'
      simp only [
        Chain.isHom_iff, Chain.coe_map, Function.comp_apply,
        OrderHom.fst_coe, OrderHom.snd_coe]
      fun_prop

end OmegaQuasiBorelSpace.Prod

namespace QuasiBorelSpace

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

namespace Measure

@[fun_prop]
lemma isHom_lintegral
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [MeasurableQuasiBorelSpace B]
    {f : A → B → ENNReal} (hf : IsHom fun x : _ × _ ↦ f x.1 x.2)
    (μ : MeasureTheory.Measure B) [MeasureTheory.SFinite μ]
    : IsHom fun x ↦ ∫⁻ y, f x y ∂μ := by
  rw [isHom_def]
  intro φ hφ
  apply isHom_of_measurable
  apply Measurable.lintegral_prod_left
  apply measurable_of_isHom
  fun_prop

end Measure

end QuasiBorelSpace

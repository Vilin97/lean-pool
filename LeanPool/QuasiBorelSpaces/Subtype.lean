/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace

/-!
# LeanPool.QuasiBorelSpaces.Subtype

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Subtype`.
-/


namespace QuasiBorelSpace.Subtype

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {P : A → Prop}

instance [QuasiBorelSpace A] : QuasiBorelSpace (Subtype P) := lift Subtype.val

@[simp]
lemma isHom_def {P : B → Prop} (f : A → Subtype P) : IsHom f ↔ IsHom fun x ↦ (f x).val := by
  rw [isHom_to_lift]

instance
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : MeasurableQuasiBorelSpace (Subtype P) where
  isHom_iff_measurable φ := by
    apply Iff.intro
    · intro h
      simp only [isHom_to_lift, isHom_iff_measurable] at h
      exact h.subtype_mk
    · intro h
      simp only [isHom_def, isHom_iff_measurable]
      apply h.subtype_val

@[fun_prop]
lemma isHom_mk {P : B → Prop}
    {f : A → B} (hf₁ : IsHom f) (hf₂ : (x : A) → P (f x))
    : IsHom (fun x ↦ Subtype.mk (f x) (hf₂ x)) := by
  simp only [isHom_def]
  apply hf₁

@[fun_prop]
lemma isHom_val {P : B → Prop} {f : A → Subtype P} (hf : IsHom f) : IsHom (fun x ↦ (f x).val) := by
  rw [← isHom_def]
  exact hf

end QuasiBorelSpace.Subtype

namespace OmegaQuasiBorelSpace.Subtype

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable
  {I : Type*} {P : I → Prop} [OmegaQuasiBorelSpace I]
  (hP : ∀ (c : OmegaCompletePartialOrder.Chain I),
    (∀ i ∈ c, P i) → P (OmegaCompletePartialOrder.ωSup c))

/-- Constructs an `OmegaQuasiBorelSpace` instance for a `Subtype`. -/
@[reducible] def subtype : OmegaQuasiBorelSpace (Subtype P) where
  toOmegaCompletePartialOrder := OmegaCompletePartialOrder.subtype P hP
  isHom_ωSup := by
    simp only [ωSup, Subtype.isHom_def]
    apply isHom_comp
    · fun_prop
    · simp only [Chain.isHom_iff, Chain.coe_map, OrderHom.Subtype.val_coe, Function.comp_apply]
      fun_prop

end OmegaQuasiBorelSpace.Subtype

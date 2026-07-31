/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

noncomputable def isColimitBinaryCofan (sq : IsPushout f g inl inr) (hZ : IsInitial Z) :
    IsColimit (BinaryCofan.mk inl inr) :=
  BinaryCofan.IsColimit.mk _ (fun {U} s t ↦ sq.desc s t (hZ.hom_ext _ _))
    (fun s t ↦ sq.inl_desc s t _) (fun s t ↦ sq.inr_desc s t _)
    (fun s t m h₁ h₂ ↦ by apply sq.hom_ext <;> simpa)

end IsPushout

end CategoryTheory

/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29

/-!
# Transporting an odd line along a monoidal functor

A strong braided monoidal additive functor carries an odd line to an
odd line: the square of the image is the image of the square, and
the self-braiding of the image is the image of the self-braiding,
which is minus an identity.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v₁ u₁ v₂ u₂

variable {A : Type u₁}

/-- **The image of an odd line under a strong braided monoidal
additive functor is an odd line.** -/
noncomputable def OddLine.map
    [Category.{v₁} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
    [SymmetricCategory B] [Preadditive B]
    (F : A ⥤ B) [F.Braided]
    [F.Additive] (L : OddLine A) : OddLine B where
  obj := F.obj L.obj
  sq := CategoryTheory.Functor.Monoidal.μIso F L.obj L.obj ≪≫
    F.mapIso L.sq ≪≫ (CategoryTheory.Functor.Monoidal.εIso F).symm
  braid_neg := by
    have hb := CategoryTheory.Functor.LaxBraided.braided
      (F := F) L.obj L.obj
    have hn : F.map (β_ L.obj L.obj).hom =
        -𝟙 (F.obj (L.obj ⊗ L.obj)) := by
      rw [L.braid_neg, F.map_neg, CategoryTheory.Functor.map_id]
    rw [hn, Preadditive.comp_neg, Category.comp_id] at hb
    have h := congrArg
      (fun t => t ≫ CategoryTheory.Functor.OplaxMonoidal.δ F
        L.obj L.obj) hb
    simp only [Preadditive.neg_comp, Category.assoc] at h
    have hmd : CategoryTheory.Functor.LaxMonoidal.μ F L.obj L.obj ≫
        CategoryTheory.Functor.OplaxMonoidal.δ F L.obj L.obj =
        𝟙 (F.obj L.obj ⊗ F.obj L.obj) :=
      CategoryTheory.Functor.Monoidal.μ_δ F L.obj L.obj
    rw [hmd, Category.comp_id] at h
    exact h.symm

end RS

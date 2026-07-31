/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Monoidal

open CategoryTheory Simplicial MonoidalCategory MonoidalClosed

namespace SSet

@[ext]
lemma ihom_ext (Y Z : SSet) (n : SimplexCategoryᵒᵖ)
    (a b : (((ihom Y).obj Z)).obj n) : a.app = b.app → a = b := fun h ↦ by
  apply Functor.functorHom_ext
  intro m f; exact congr_fun (congr_fun h m) f

@[ext]
lemma ihom_ihom_ext (X Y Z : SSet) (n : SimplexCategoryᵒᵖ)
    (a b : ((ihom X).obj ((ihom Y).obj Z)).obj n) : a.app = b.app → a = b := fun h ↦ by
  apply Functor.functorHom_ext
  intro m f; exact congr_fun (congr_fun h m) f

@[simps]
noncomputable
def ihom_ihom_iso_ihom_tensor_hom (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ⟶ (ihom (X ⊗ Y)).obj Z where
  app n x := by
    refine ⟨fun m f ⟨Xm, Ym⟩ ↦ (x.app m f Xm).app m (𝟙 m) Ym, ?_⟩
    · intro m l f g
      ext ⟨Xm, Ym⟩
      have := (congr_fun (x.naturality f g) Xm)
      simp at this
      change
        (x.app l (g ≫ f) (X.map f Xm)).app l (𝟙 l) (Y.map f Ym) =
          Z.map f ((x.app m g Xm).app m (𝟙 m) Ym)
      rw [this]
      exact congr_fun ((x.app m g Xm).naturality f (𝟙 m)) Ym

@[simps]
def ihom_ihom_iso_ihom_tensor_inv (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ⟶ (ihom X).obj ((ihom Y).obj Z) where
  app := fun n x ↦ by
    refine ⟨?_, ?_⟩
    · intro m f Xm
      refine ⟨fun l g Yl ↦ x.app l (f ≫ g) (X.map g Xm, Yl), ?_⟩
      · intro l k g h
        ext Yl
        have := congr_fun (x.naturality g (f ≫ h)) (X.map h Xm, Yl)
        simp at this ⊢
        exact this
    · intro m l f g
      ext
      simp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.functorHom, Functor.homObjFunctor]

/-- `[X, [Y, Z]] ≅ [X ⊗ Y, Z]` -/
noncomputable
def ihom_ihom_iso_ihom_tensor (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom (X ⊗ Y)).obj Z where
  hom := ihom_ihom_iso_ihom_tensor_hom X Y Z
  inv := ihom_ihom_iso_ihom_tensor_inv X Y Z
  hom_inv_id := by
    ext n x m f Xm l g Yl
    change (x.app l (f ≫ g) (X.map g Xm)).app l (𝟙 l) Yl = (x.app m f Xm).app l g Yl
    have := congr_fun (x.naturality g f) Xm
    dsimp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.functorHom,
      Functor.homObjFunctor] at this
    rw [this]
    aesop

@[simp]
lemma ihom_tensor_symm_iso_hom_eq {X Y Z : SSet} {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : ((ihom (Y ⊗ X)).obj Z).obj n) :
    (((pre (β_ X Y).hom).app Z).app n a).app m f =
      (β_ X Y).hom.app m ≫ a.app m f := by
  ext ⟨Xm, Ym⟩
  change (((Y ⊗ X).functorHom Z).map f a).app m (𝟙 m) (Ym, Xm) = a.app m f (Ym, Xm)
  simp [Functor.functorHom]

@[simp]
lemma ihom_tensor_symm_iso_inv_eq {X Y Z : SSet} {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : ((ihom (X ⊗ Y)).obj Z).obj n) :
    (((pre (β_ X Y).inv).app Z).app n a).app m f = (β_ X Y).inv.app m ≫ a.app m f := by
  ext ⟨Ym, Xm⟩
  change (((X ⊗ Y).functorHom Z).map f a).app m (𝟙 m) (Xm, Ym) = a.app m f (Xm, Ym)
  simp [Functor.functorHom]

/-- `[X ⊗ Y, Z] ≅ [Y ⊗ X, Z]` -/
noncomputable
def ihom_tensor_symm_iso (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ≅ (ihom (Y ⊗ X)).obj Z where
  hom := (pre (β_ X Y).inv).app Z
  inv := (pre (β_ X Y).hom).app Z

/-- `[X, [Y, Z]] ≅ [X ⊗ Y, Z] ≅ [Y ⊗ X, Z] ≅ [Y, [X, Z]]` -/
noncomputable
def ihom_ihom_symm_iso (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) :=
  (ihom_ihom_iso_ihom_tensor X Y Z) ≪≫ (ihom_tensor_symm_iso X Y Z) ≪≫ (ihom_ihom_iso_ihom_tensor Y X Z).symm

end SSet

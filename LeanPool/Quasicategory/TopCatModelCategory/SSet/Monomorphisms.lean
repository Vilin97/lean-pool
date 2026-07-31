/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.CategoryWithFibrations
import LeanPool.Quasicategory.TopCatModelCategory.ULift
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

universe w v u

open CategoryTheory MorphismProperty Limits HomotopicalAlgebra

namespace CategoryTheory

namespace Types

instance : IsStableUnderCoproducts.{v} (monomorphisms (Type u)) where
  isStableUnderCoproductsOfShape J  := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    simp only [monomorphisms.iff, mono_iff_injective] at hf ⊢
    intro x y h
    obtain ⟨⟨i⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit (coproductIsCoproduct X₁) x
    obtain ⟨⟨j⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit (coproductIsCoproduct X₁) y
    dsimp at x y h ⊢
    change (Sigma.ι X₁ i ≫ Limits.Sigma.map f) x =
      (Sigma.ι X₁ j ≫ Limits.Sigma.map f) y at h
    simp only [ι_colimMap] at h
    dsimp at h
    obtain rfl := Types.eq_cofanInj_apply_eq_of_isColimit (coproductIsCoproduct X₂) _ _ h
    obtain rfl := hf _ (Types.cofanInj_injective_of_isColimit (coproductIsCoproduct X₂) _ h)
    rfl

instance [HasCoproducts.{v} (Type u)] (J : Type*) [Category J] :
    IsStableUnderCoproducts.{v} (monomorphisms (J ⥤ Type u)) where
  isStableUnderCoproductsOfShape J := by
    rw [← functorCategory_monomorphisms]
    apply IsStableUnderColimitsOfShape.functorCategory
    apply isStableUnderCoproductsOfShape_of_isStableUnderCoproducts

end Types

end CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

@[simp]
lemma rlp_transfiniteCompositions (W : MorphismProperty C) :
    (transfiniteCompositions.{w} W).rlp = W.rlp := by
  apply le_antisymm
  · exact antitone_rlp W.le_transfiniteCompositions
  · rw [← le_llp_iff_le_rlp]
    exact transfiniteCompositions_le_llp_rlp W

instance [(monomorphisms C).IsStableUnderCobaseChange] [HasPushouts C]
    [HasPullbacks C] (J : Type*) [Category J] :
    (monomorphisms (J ⥤ C)).IsStableUnderCobaseChange := by
  rw [← functorCategory_monomorphisms]
  infer_instance

end CategoryTheory.MorphismProperty

namespace SSet

instance : IsStableUnderTransfiniteComposition.{u} (monomorphisms (SSet.{u})) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderTransfiniteCompositionOfShape _
    infer_instance

instance : IsStableUnderCobaseChange (monomorphisms (SSet.{u})) :=
  inferInstanceAs (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange

instance : IsStableUnderCoproducts.{u} (monomorphisms (SSet.{u})) :=
  inferInstanceAs (IsStableUnderCoproducts.{u} (monomorphisms (_ ⥤ _)))

instance {ι : Type u} {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    [∀ i, Mono (f i)] : Mono (Limits.Sigma.map f) :=
  ((monomorphisms SSet.{u}).isStableUnderCoproductsOfShape_of_isStableUnderCoproducts
    ι).colimMap _ (fun _ ↦ monomorphisms.infer_property (f _))

end SSet

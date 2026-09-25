/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndDayClosure

/-!
# The monoidal structure on ind-objects

Deligne's 2.2: the tensor product of a small ℂ-tensorielle
category extends to its ind-completion by
`(colim Xᵢ) ⊗ (colim Yⱼ) = colim (Xᵢ ⊗ Yⱼ)`.  Here the extension
is packaged through Day convolution: presheaves on `C` carry the
Day monoidal structure (`Cᵒᵖ ⊛⥤ Type v`, with the instances of
`DayType.lean`), the ind-objects are closed under it — the Day
tensor preserves colimits in each variable and sends a pair of
representables to the representable of the tensor — and `Ind C`
inherits the structure through `Ind.equivalence` and the full
monoidal subcategory of the ind-property.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable (C : Type v)

/-- The ind-property, read on the Day synonym of the presheaf
category. -/
def IsIndDay [SmallCategory C] [MonoidalCategory C]
    (F : MonoidalCategory.DayFunctor Cᵒᵖ (Type v)) : Prop :=
  IsIndObject F.functor

/-- The ind-property is monoidal: it holds for the unit and is
stable under the Day tensor. -/
instance isIndDay_isMonoidal [SmallCategory C] [MonoidalCategory C] :
    ObjectProperty.IsMonoidal (IsIndDay C) where
  prop_unit := isIndObject_day_unit C
  prop_tensor _ _ h₁ h₂ := isIndObject_day_tensor h₁ h₂

/-- The full subcategory of ind-objects of the Day presheaf
category is monoidal. -/
noncomputable example
    [SmallCategory C] [MonoidalCategory C] : MonoidalCategory
    (ObjectProperty.FullSubcategory
      (C := MonoidalCategory.DayFunctor Cᵒᵖ (Type v))
      (IsIndDay C)) :=
  inferInstance

/-- The ind-property respects isomorphisms. -/
instance isIndDay_closedUnderIso [SmallCategory C] [MonoidalCategory C] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsIndDay C) where
  of_iso e h := IsIndObject.map (dayFunctorIso e).hom h

/-- The wrapper equivalence between the ind-subcategory of the
presheaf category and the ind-subcategory of its Day synonym. -/
noncomputable def indDayCongr [SmallCategory C] [MonoidalCategory C] :
    ObjectProperty.FullSubcategory
      (IsIndObject (C := C)) ≌
    ObjectProperty.FullSubcategory
      (C := MonoidalCategory.DayFunctor Cᵒᵖ (Type v))
      (IsIndDay C) where
  functor := ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      (MonoidalCategory.DayFunctor.equiv Cᵒᵖ (Type v)).inverse)
    (fun X => X.2)
  inverse := ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      (MonoidalCategory.DayFunctor.equiv Cᵒᵖ (Type v)).functor)
    (fun X => X.2)
  unitIso := (ObjectProperty.fullyFaithfulι _).whiskeringRight _
    |>.preimageIso ((ObjectProperty.ι _).isoWhiskerLeft
      (MonoidalCategory.DayFunctor.equiv Cᵒᵖ (Type v)).symm.unitIso)
  counitIso := (ObjectProperty.fullyFaithfulι _).whiskeringRight _
    |>.preimageIso ((ObjectProperty.ι _).isoWhiskerLeft
      (MonoidalCategory.DayFunctor.equiv Cᵒᵖ (Type v)).symm.counitIso)
  functor_unitIso_comp X := ObjectProperty.hom_ext _
    ((MonoidalCategory.DayFunctor.equiv Cᵒᵖ
      (Type v)).symm.functor_unit_comp X.obj)

/-- `Ind C` is equivalent to the monoidal full subcategory of
ind-objects of the Day presheaf category. -/
noncomputable def indDayEquivalence [SmallCategory C] [MonoidalCategory C] :
    Ind C ≌ ObjectProperty.FullSubcategory
      (C := MonoidalCategory.DayFunctor Cᵒᵖ (Type v))
      (IsIndDay C) :=
  (Ind.equivalence C).trans (indDayCongr C)

/-- **Deligne 2.2, structure half**: the tensor product of a small
monoidal category extends to its ind-completion — the Day tensor
structure transported across the indization equivalence. -/
noncomputable instance indMonoidalCategory
    [SmallCategory C] [MonoidalCategory C] :
    MonoidalCategory (Ind C) :=
  Monoidal.transport ((indDayEquivalence C).symm)

/-- The opposite of a symmetric category is symmetric (the braided
instance exists in Mathlib at this pin; the symmetric one does
not). -/
instance symmetricCategoryOp {D : Type*} [Category D]
    [MonoidalCategory D] [SymmetricCategory D] :
    SymmetricCategory Dᵒᵖ where
  symmetry X Y := by
    change (β_ (Opposite.unop Y) (Opposite.unop X)).hom.op ≫
      (β_ (Opposite.unop X) (Opposite.unop Y)).hom.op = 𝟙 _
    rw [← op_comp, SymmetricCategory.symmetry]
    rfl

/-- The braiding transports as well: `Ind C` of a braided small
category is braided. -/
noncomputable instance indBraidedCategory [SmallCategory C] [MonoidalCategory C]
    [BraidedCategory C] :
    BraidedCategory (Ind C) :=
  inferInstanceAs
    (BraidedCategory (Monoidal.Transported ((indDayEquivalence C).symm)))

/-- And the symmetry: `Ind C` of a symmetric small category is
symmetric. -/
noncomputable instance indSymmetricCategory
    [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] :
    SymmetricCategory (Ind C) :=
  inferInstanceAs
    (SymmetricCategory (Monoidal.Transported ((indDayEquivalence C).symm)))

end RS

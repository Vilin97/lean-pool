/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.DayCalculus

/-!
# Ind-objects are closed under Day convolution

Over a small monoidal category `C`, the presheaf category
`Cᵒᵖ ⥤ Type v` carries the Day-convolution monoidal structure through
the synonym `Cᵒᵖ ⊛⥤ Type v` set up in `RS.Classical.Deligne.DayType`.
This file proves that the ind-objects among presheaves are closed
under the Day tensor and contain the Day unit:

* `RS.dayYonedaIso`: the Day tensor of the representables at `x` and
  `y` is the representable at `x ⊗ y` (this is `RS.dayCoyonedaIso` at
  the base `Cᵒᵖ`, read through `Coyoneda.objOpOp` and the definitional
  identification `op x ⊗ op y = op (x ⊗ y)` in `Cᵒᵖ`);
* `RS.isIndObject_day_tensor`: if `F.functor` and `G.functor` are
  ind-objects, so is `(F ⊗ G).functor`;
* `RS.isIndObject_day_unit`: the Day unit is an ind-object.

The argument is the classical one.  Each tensor factor is a small
filtered colimit of representables (`IsIndObject.presentation`); Day
tensoring on either side preserves `v`-small colimits (the instances
of `RS.Classical.Deligne.DayCalculus`), so the tensor is a small
filtered colimit of tensors of representables, and those are
representable by the co-Yoneda computation; closure of ind-objects
under small filtered colimits (`isIndObject_colimit`) concludes.  The
two colimit steps are the same manoeuvre, factored out as
`RS.isIndObject_obj_of_preservesColimits`.
-/

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open Opposite

universe v

noncomputable section

variable {C : Type v}

/-- Transport an isomorphism of plain presheaves to the Day synonym
category. -/
def dayMkIso [SmallCategory C] [MonoidalCategory C]
    {A B : Cᵒᵖ ⥤ Type v} (e : A ≅ B) :
    (DayFunctor.mk A : Cᵒᵖ ⊛⥤ Type v) ≅ DayFunctor.mk B :=
  (equiv Cᵒᵖ (Type v)).inverse.mapIso e

/-- Transport an isomorphism of the Day synonym category to the plain
presheaf category. -/
def dayFunctorIso [SmallCategory C] [MonoidalCategory C]
    {F G : Cᵒᵖ ⊛⥤ Type v} (e : F ≅ G) :
    F.functor ≅ G.functor :=
  (equiv Cᵒᵖ (Type v)).functor.mapIso e

/-- Day convolution of representables: the Day tensor of the yoneda
presheaves at `x` and `y` is the yoneda presheaf at `x ⊗ y`.  This is
`RS.dayCoyonedaIso` at the base `Cᵒᵖ`, transported along
`Coyoneda.objOpOp`, using that `op x ⊗ op y = op (x ⊗ y)` holds
definitionally in `Cᵒᵖ`. -/
def dayYonedaIso [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    (DayFunctor.mk (yoneda.obj x) : Cᵒᵖ ⊛⥤ Type v) ⊗
        DayFunctor.mk (yoneda.obj y) ≅
      DayFunctor.mk (yoneda.obj (x ⊗ y)) :=
  tensorIso (dayMkIso (Coyoneda.objOpOp x).symm)
      (dayMkIso (Coyoneda.objOpOp y).symm) ≪≫
    dayCoyonedaIso (op x) (op y) ≪≫
    dayMkIso (Coyoneda.objOpOp (x ⊗ y))

/-- The Day tensor of two representable presheaves is an
ind-object. -/
theorem isIndObject_day_tensor_yoneda [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    IsIndObject ((DayFunctor.mk (yoneda.obj x) ⊗
      DayFunctor.mk (yoneda.obj y) : Cᵒᵖ ⊛⥤ Type v)).functor :=
  (isIndObject_yoneda (x ⊗ y)).map (dayFunctorIso (dayYonedaIso x y).symm).hom

/-- A colimit-preserving endofunctor of the Day synonym category that
sends representables to ind-objects sends every ind-object to an
ind-object: apply the functor to a presentation of the argument as a
small filtered colimit of representables and use closure of
ind-objects under small filtered colimits.  This is the induction step
used twice below, for Day tensoring on either side. -/
theorem isIndObject_obj_of_preservesColimits
    [SmallCategory C] [MonoidalCategory C]
    (T : (Cᵒᵖ ⊛⥤ Type v) ⥤ Cᵒᵖ ⊛⥤ Type v)
    [PreservesColimitsOfSize.{v, v} T]
    (hT : ∀ y : C,
      IsIndObject (T.obj (DayFunctor.mk (yoneda.obj y))).functor)
    {G : Cᵒᵖ ⊛⥤ Type v} (hG : IsIndObject G.functor) :
    IsIndObject (T.obj G).functor := by
  obtain ⟨⟨Q⟩⟩ := hG
  let E : Q.I ⥤ Cᵒᵖ ⥤ Type v :=
    (((Q.F ⋙ yoneda) ⋙ (equiv Cᵒᵖ (Type v)).inverse) ⋙ T) ⋙
      (equiv Cᵒᵖ (Type v)).functor
  have hc₁ : IsColimit ((equiv Cᵒᵖ (Type v)).inverse.mapCocone Q.cocone) :=
    isColimitOfPreserves _ Q.coconeIsColimit
  have hc₂ : IsColimit (T.mapCocone
      ((equiv Cᵒᵖ (Type v)).inverse.mapCocone Q.cocone)) :=
    isColimitOfPreserves T hc₁
  have hc₃ : IsColimit ((equiv Cᵒᵖ (Type v)).functor.mapCocone
      (T.mapCocone ((equiv Cᵒᵖ (Type v)).inverse.mapCocone Q.cocone))) :=
    isColimitOfPreserves _ hc₂
  have hE : ∀ i, IsIndObject (E.obj i) := fun i => hT (Q.F.obj i)
  exact (isIndObject_colimit Q.I E hE).map
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit E) hc₃).hom

/-- The Day tensor of a representable presheaf with an ind-object is
an ind-object. -/
theorem isIndObject_day_tensor_yoneda_left
    [SmallCategory C] [MonoidalCategory C]
    (x : C) {G : Cᵒᵖ ⊛⥤ Type v}
    (hG : IsIndObject G.functor) :
    IsIndObject ((DayFunctor.mk (yoneda.obj x) ⊗ G).functor) :=
  isIndObject_obj_of_preservesColimits
    (tensorLeft (DayFunctor.mk (yoneda.obj x)))
    (fun y => isIndObject_day_tensor_yoneda x y) hG

/-- Ind-objects are closed under Day convolution. -/
theorem isIndObject_day_tensor [SmallCategory C] [MonoidalCategory C]
    {F G : Cᵒᵖ ⊛⥤ Type v}
    (hF : IsIndObject F.functor) (hG : IsIndObject G.functor) :
    IsIndObject ((F ⊗ G).functor) :=
  isIndObject_obj_of_preservesColimits (tensorRight G)
    (fun y => isIndObject_day_tensor_yoneda_left y hG) hF

variable (C) in
/-- The Day unit is an ind-object: by `RS.dayUnitIso` it is the
representable at the monoidal unit of `C`. -/
theorem isIndObject_day_unit [SmallCategory C] [MonoidalCategory C] :
    IsIndObject (𝟙_ (Cᵒᵖ ⊛⥤ Type v)).functor :=
  (isIndObject_yoneda (𝟙_ C)).map
    (dayFunctorIso (dayMkIso (Coyoneda.objOpOp (𝟙_ C)).symm ≪≫
      (dayUnitIso Cᵒᵖ).symm)).hom

end

end RS

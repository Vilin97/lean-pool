/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Subcomplex
import LeanPool.Quasicategory.TopCatModelCategory.Set

universe u

open CategoryTheory Limits

namespace SSet.Subcomplex

@[simps]
def evaluation (X : SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    X.Subcomplex ⥤ Set (X.obj j) where
  obj A := A.obj j
  map f := CategoryTheory.homOfLE (leOfHom f j)

instance {J : Type*} [Category J] {X : SSet.{u}} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subcomplex.toPresheafFunctor (X := X)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone (CompleteLattice.colimitCocone F).isColimit
      (evaluationJointlyReflectsColimits _ (fun j ↦
        IsColimit.ofIsoColimit (isColimitOfPreserves Set.functorToTypes
          (CompleteLattice.colimitCocone (F ⋙ evaluation _ j)).isColimit)
            (Cocones.ext (Set.functorToTypes.mapIso (eqToIso (by aesop))))))

end SSet.Subcomplex

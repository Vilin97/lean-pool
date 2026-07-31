/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.MonoCoprod
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Subcomplex

universe v' u' u
open CategoryTheory Limits

namespace SSet

section

instance [HasCoproducts.{v} (Type u)] : HasCoproducts.{v} (SSet.{u}) :=
  inferInstanceAs (HasCoproducts.{v} (_ ⥤ _))

end

section

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type u)]
  {F : J ⥤ SSet.{u}} {c : Cocone F}

lemma Subcomplex.top_eq_iSup_of_isColimit (hc : IsColimit c) :
    (⊤ : c.pt.Subcomplex) = ⨆ (j : J), range (c.ι.app j) := by
  ext n x
  simpa using Types.jointly_surjective _
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x

end

end SSet

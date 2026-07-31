/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import LeanPool.Quasicategory.TopCatModelCategory.MonoCoprod

universe u

open CategoryTheory Limits

namespace SSet

instance : MonoCoprod SSet.{u} :=
  inferInstanceAs (MonoCoprod (SimplexCategoryᵒᵖ ⥤ Type u))

end SSet

/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.WhiskerAdditive
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModTensor

/-!
# Vanishing transport through the module tensor product

The relative tensor product of modules vanishes when either
factor does: the projection from the ordinary tensor product is
epic, and the ordinary tensor product with a zero object is
zero.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The module tensor product of a zero module vanishes**,
left-factor version. -/
theorem isZero_modTensor_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] (M : Mod D A) (N : Mod D A)
    (h : IsZero M.X) :
    IsZero (modTensor A M N) := by
  rw [IsZero.iff_id_eq_zero]
  have hπ : modTensorπ A M N = 0 :=
    (isZero_whiskerRight h N.X).eq_of_src _ _
  have := modTensor_hom_ext A M N
    (k := 𝟙 (modTensor A M N)) (l := 0)
  apply this
  rw [hπ, Limits.zero_comp, Limits.zero_comp]

end RS

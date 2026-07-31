/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.ColimitsType
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Set

open CategoryTheory Limits

/-namespace CompleteLattice

variable {J : Type*} [Category J] {X : Type*} [CompleteLattice X]
  (F : J ⥤ X)

@[simps]
def cocone : Cocone F where
  pt := ⨆ (j : J), F.obj j
  ι := { app j := homOfLE (le_iSup F.obj j) }

def isColimitCocone : IsColimit (cocone F) where
  desc s := homOfLE (by
    dsimp
    simp only [iSup_le_iff]
    intro j
    exact leOfHom (s.ι.app j))
  fac _ _ := rfl
  uniq _ _ _ := rfl

instance : HasColimitsOfShape J X where
  has_colimit F := ⟨_, isColimitCocone F⟩

end CompleteLattice

namespace Set

instance {J : Type*} [Category J] {X : Type*} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (functorToTypes (X := X)) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (CompleteLattice.isColimitCocone F)
    apply Types.FilteredColimit.isColimitOf
    · rintro ⟨x, hx⟩
      simp only [CompleteLattice.cocone_pt, iSup_eq_iUnion, mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    · intro i j ⟨x, hx⟩ ⟨y, hy⟩ h
      obtain rfl : x = y := by simpa using h
      exact ⟨IsFiltered.max i j, IsFiltered.leftToMax i j, IsFiltered.rightToMax i j, rfl⟩

end Set-/

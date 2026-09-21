/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
/-!
# Hilbert class fields without real places

When the base has no real places, no extension can ramify at an infinite
place. Thus the small and big Hilbert class field conditions agree.
-/

namespace ClassFieldTheory

universe u

/-- Over a number field without real places, the small and big Hilbert
class field predicates on a fixed finite abelian extension coincide. -/
theorem isSmallHilbertClassField_iff_isBig_of_noReal
    (K : Type u) [Field K] [NumberField K]
    [IsEmpty (RayClassRealPlace K)]
    (E : FiniteAbelianExtension K) :
    IsSmallHilbertClassField E ↔ IsBigHilbertClassField E := by
  classical
  have hInf (L : FiniteAbelianExtension K) :
      IsUnramifiedAtInfinitePlaces K L := by
    refine ⟨?_⟩
    intro w
    by_contra hram
    have hreal : (w.comap (algebraMap K L)).IsReal :=
      (NumberField.InfinitePlace.not_isUnramified_iff.mp hram).2
    exact isEmptyElim
      (⟨w.comap (algebraMap K L), hreal⟩ : RayClassRealPlace K)
  have hFinite (L : FiniteAbelianExtension K) :
      IsUnramifiedAtFinitePlaces K L ↔ IsEverywhereUnramified K L := by
    constructor
    · intro h
      exact ⟨h, hInf L⟩
    · intro h
      exact h.1
  constructor
  · intro hSmall
    refine ⟨hSmall.1.1, ?_⟩
    intro F hF
    exact hSmall.2 F ((hFinite F).mp hF)
  · intro hBig
    refine ⟨(hFinite E).mp hBig.1, ?_⟩
    intro F hF
    exact hBig.2 F ((hFinite F).mpr hF)

end ClassFieldTheory

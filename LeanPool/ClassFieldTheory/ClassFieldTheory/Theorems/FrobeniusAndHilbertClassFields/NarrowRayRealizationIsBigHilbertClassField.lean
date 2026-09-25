/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsRayArtinModulusProjection
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldExists
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldNarrowRayRealization
/-!
# A narrow ray realization is a big Hilbert class field

The Frobenius-normalized realization of the narrow ray class group is
maximal among finite abelian extensions unramified at finite places.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- Every realization of the narrow ray class group is a big Hilbert class
field, including its maximality property. -/
theorem narrowRayRealization_isBigHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (R : RayClassFieldRealization K (narrowRayClassModulus K)) :
    IsBigHilbertClassField R.extension := by
  obtain ⟨E, hE⟩ := exists_bigHilbertClassField K
  obtain ⟨S, hS⟩ := bigHilbertClassField_hasNarrowRayRealization K E hE
  subst E
  obtain ⟨f, _⟩ :=
    exists_rayArtin_modulusProjection
      (le_refl (narrowRayClassModulus K)) S R
  constructor
  · intro v
    exact R.unramifiedOutsideModulus.1 v (by simp [narrowRayClassModulus])
  · intro F hF
    obtain ⟨g⟩ := hE.2 F hF
    exact ⟨f.comp g⟩

end ClassFieldTheory

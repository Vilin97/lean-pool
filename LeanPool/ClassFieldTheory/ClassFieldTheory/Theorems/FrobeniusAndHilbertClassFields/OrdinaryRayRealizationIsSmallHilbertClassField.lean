/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsRayArtinModulusProjection
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldExists
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldOrdinaryRayRealization
/-!
# An ordinary ray realization is a small Hilbert class field

The Frobenius-normalized realization of the ordinary ray class group is
maximal among finite abelian extensions unramified at all places.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- Every realization of the ordinary ray class group is a small Hilbert
class field, including its maximality property. -/
theorem ordinaryRayRealization_isSmallHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (R : RayClassFieldRealization K (ordinaryRayClassModulus K)) :
    IsSmallHilbertClassField R.extension := by
  obtain ⟨E, hE⟩ := exists_smallHilbertClassField K
  obtain ⟨S, hS⟩ := smallHilbertClassField_hasOrdinaryRayRealization K E hE
  subst E
  obtain ⟨f, _⟩ :=
    exists_rayArtin_modulusProjection
      (le_refl (ordinaryRayClassModulus K)) S R
  constructor
  · constructor
    · intro v
      exact R.unramifiedOutsideModulus.1 v (by simp [ordinaryRayClassModulus])
    · refine ⟨fun w => ?_⟩
      by_contra hw
      have hvreal : (w.comap (algebraMap K R.extension)).IsReal :=
        (InfinitePlace.not_isUnramified_iff.mp hw).2
      have hbase := R.unramifiedOutsideModulus.2
        (w.comap (algebraMap K R.extension)) hvreal
        (by simp [ordinaryRayClassModulus])
      exact hw (hbase w rfl)
  · intro F hF
    obtain ⟨g⟩ := hE.2 F hF
    exact ⟨f.comp g⟩

end ClassFieldTheory

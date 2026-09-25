/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldArtinEquiv
/-!
# The small Hilbert class field as an ordinary ray class field

Its ordinary-class Artin isomorphism and everywhere-unramifiedness give a
ray-class-field realization whose extension is the original field.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- A small Hilbert class field realizes the ordinary ray class group, with
the same extension and arithmetic Frobenius normalization. -/
theorem smallHilbertClassField_hasOrdinaryRayRealization
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∃ R : RayClassFieldRealization K (ordinaryRayClassModulus K),
      R.extension = E := by
  obtain ⟨artin, hartin⟩ := smallHilbertClassField_artinEquiv K E hE
  let R : RayClassFieldRealization K (ordinaryRayClassModulus K) := {
    extension := E
    unramifiedOutsideModulus := by
      constructor
      · intro v _
        exact hE.1.1 v
      · intro _ _ _ w _
        exact hE.1.2.isUnramified w
    artinEquiv := artin
    artin_frobenius := by
      intro v _ w hw
      change artin (ordinaryRayClassOfFinitePrime v) =
        arithmeticFrobeniusAt (K := K) w
      exact hartin v w hw }
  exact ⟨R, rfl⟩

end ClassFieldTheory

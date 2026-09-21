/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FinitePlaceArtinQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ProductFormula
/-!
# Prime norm classes at unramified finite places

For a finite abelian extension of number fields, the normalized
order-one element at a finite place defines a class in the chosen
local norm quotient.  Under local reciprocity this class is the actual
prime Artin element in the chosen decomposition group.

At a chosen unramified place, its order is therefore the local degree,
and its triviality is equivalent to complete splitting.  The
one-place local-to-global norm map sends this local class to the
corresponding prime class in the global idèle-class norm quotient, so
the order of the global class divides the local degree.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

private theorem unramifiedPrimeNormClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] unramifiedPrimeNormClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section FiniteGalois

variable [IsGalois K L]

/-- The class of the normalized order-one local element in the chosen
finite-place norm quotient. -/
def finitePlacePrimeNormClass
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.ChosenFinitePlaceNormQuotient
      (K := K) (L := L) v :=
  _root_.finitePlaceTensorNormClass
    (K := K) (L := L) v
    (FiniteIdeleGroup.chosenLocalOrderSection v 1)

/-- The one-place local-to-global norm map sends the local prime norm
class to the corresponding prime class in the global idèle-class norm
quotient. -/
@[simp]
theorem finitePlaceNormQuotientToGlobalClass_finitePlacePrimeNormClass
    (v : HeightOneSpectrum (𝓞 K)) :
    Reciprocity.finitePlaceNormQuotientToGlobalClass
        (K := K) (L := L) v
        (finitePlacePrimeNormClass
          (K := K) (L := L) v) =
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v := by
  change
    Reciprocity.finitePlaceNormQuotientToGlobalClass
        (K := K) (L := L) v
        (_root_.finitePlaceTensorNormClass
          (K := K) (L := L) v
          (FiniteIdeleGroup.chosenLocalOrderSection v 1)) =
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v
  rw [
    Reciprocity.finitePlaceNormQuotientToGlobalClass_localClass
      (K := K) (L := L) v]
  rfl

end FiniteGalois

variable [IsAbelianGalois K L]

/-- The local prime norm class corresponds to the actual prime Artin
element under the finite-place reciprocity equivalence. -/
@[simp]
theorem
    coe_chosenFinitePlaceNormQuotientEquivDecompositionGroup_finitePlacePrimeNormClass
    (v : HeightOneSpectrum (𝓞 K)) :
    ((chosenFinitePlaceNormQuotientEquivDecompositionGroup
          (K := K) (L := L) v
          (finitePlacePrimeNormClass
            (K := K) (L := L) v) :
        _root_.finitePlaceDecompositionGroup
          (K := K) (L := L) v) :
      L ≃ₐ[K] L) =
      finitePlacePrimeArtin (K := K) (L := L) v := by
  change
    ((chosenFinitePlaceNormQuotientEquivDecompositionGroup
          (K := K) (L := L) v
          (QuotientGroup.mk
            (FiniteIdeleGroup.chosenLocalOrderSection v 1)) :
        _root_.finitePlaceDecompositionGroup
          (K := K) (L := L) v) :
      L ≃ₐ[K] L) =
      finitePlacePrimeArtin (K := K) (L := L) v
  rw [
    chosenFinitePlaceNormQuotientEquivDecompositionGroup_mk
      (K := K) (L := L) v]
  change
    Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) =
      finitePlacePrimeArtin (K := K) (L := L) v
  exact
    (finitePlacePrimeArtin_eq_chosenFinitePlaceArtin
      (K := K) (L := L) v).symm

/-- The order of the local prime norm class always divides the local
extension degree. -/
theorem orderOf_finitePlacePrimeNormClass_dvd_finitePlaceLocalDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (finitePlacePrimeNormClass
          (K := K) (L := L) v) ∣
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  rw [
    ←
      chosenFinitePlaceNormQuotient_card_eq_finitePlaceLocalDegree
        (K := K) (L := L) v]
  exact
    orderOf_dvd_natCard
      (finitePlacePrimeNormClass
        (K := K) (L := L) v)

/-- At a chosen unramified finite place, the order of the local prime
norm class is the local extension degree. -/
theorem
    orderOf_finitePlacePrimeNormClass_eq_finitePlaceLocalDegree_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    orderOf
        (finitePlacePrimeNormClass
          (K := K) (L := L) v) =
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  let e :
      _root_.ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v ≃*
        _root_.finitePlaceDecompositionGroup
          (K := K) (L := L) v :=
    chosenFinitePlaceNormQuotientEquivDecompositionGroup
      (K := K) (L := L) v
  let f :
      _root_.ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v →*
        (L ≃ₐ[K] L) :=
    (_root_.finitePlaceDecompositionGroup
        (K := K) (L := L) v).subtype.comp
      e.toMonoidHom
  have hf : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    change
      (e x : L ≃ₐ[K] L) =
        (e y : L ≃ₐ[K] L) at hxy
    exact hxy
  have hprime :
      f
          (finitePlacePrimeNormClass
            (K := K) (L := L) v) =
        finitePlacePrimeArtin
          (K := K) (L := L) v := by
    change
      (e (finitePlacePrimeNormClass
          (K := K) (L := L) v) : L ≃ₐ[K] L) =
        finitePlacePrimeArtin
          (K := K) (L := L) v
    exact
      coe_chosenFinitePlaceNormQuotientEquivDecompositionGroup_finitePlacePrimeNormClass
        (K := K) (L := L) v
  have horder :=
    orderOf_injective f hf
      (finitePlacePrimeNormClass
        (K := K) (L := L) v)
  rw [hprime] at horder
  exact
    horder.symm.trans
      (orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
        (K := K) (L := L) v hunram)

/-- At a chosen unramified finite place, the local prime norm class is
trivial exactly when the place splits completely. -/
theorem
    finitePlacePrimeNormClass_eq_one_iff_splitsCompletely_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    finitePlacePrimeNormClass
          (K := K) (L := L) v =
        1 ↔
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  rw [
    _root_.finitePlaceSplitsCompletely_iff_localDegree_eq_one,
    ←
      orderOf_finitePlacePrimeNormClass_eq_finitePlaceLocalDegree_of_chosenUnramified
        (K := K) (L := L) v hunram]
  exact orderOf_eq_one_iff.symm

/-- The order of the global idèle-class norm prime class always
divides the local extension degree. -/
theorem orderOf_ideleClassNormFrobeniusClass_dvd_finitePlaceLocalDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (ideleClassNormFrobeniusClass
          (K := K) (L := L) v) ∣
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  rw [
    ←
      finitePlaceNormQuotientToGlobalClass_finitePlacePrimeNormClass
        (K := K) (L := L) v]
  exact
    (orderOf_map_dvd
        (Reciprocity.finitePlaceNormQuotientToGlobalClass
          (K := K) (L := L) v)
        (finitePlacePrimeNormClass
          (K := K) (L := L) v)).trans
      (orderOf_finitePlacePrimeNormClass_dvd_finitePlaceLocalDegree
        (K := K) (L := L) v)

end GlobalClassFields
end GlobalClassFieldTheory

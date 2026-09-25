/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
/-!
# Finite-place Artin quotients

For a finite abelian extension of number fields, the chosen local
Artin homomorphism has image equal to the actual decomposition group
and kernel equal to the chosen local norm subgroup.  Restricting its
codomain and applying the first isomorphism theorem therefore
identifies the concrete local norm quotient with the decomposition
group.
-/

@[expose] public section

open scoped NumberField
noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

open scoped Classical in
/-- The chosen finite-place Artin homomorphism with codomain restricted
to the actual decomposition group at the chosen place above `v`. -/
noncomputable def chosenFinitePlaceArtinToDecompositionGroup
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      _root_.finitePlaceDecompositionGroup
        (K := K) (L := L) v :=
  (Reciprocity.chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v).codRestrict
    (_root_.finitePlaceDecompositionGroup
      (K := K) (L := L) v)
    (fun x => by
      rw [
        ← Reciprocity.chosenFinitePlaceArtinMonoidHom_range
          (K := K) (L := L) v]
      exact ⟨x, rfl⟩)

open scoped Classical in
/-- The decomposition-group-valued finite-place Artin homomorphism is
surjective. -/
theorem chosenFinitePlaceArtinToDecompositionGroup_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (chosenFinitePlaceArtinToDecompositionGroup
        (K := K) (L := L) v) := by
  intro g
  have hg :
      (g : L ≃ₐ[K] L) ∈
        (Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range := by
    rw [
      Reciprocity.chosenFinitePlaceArtinMonoidHom_range
        (K := K) (L := L) v]
    exact g.property
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

open scoped Classical in
/-- The kernel of the decomposition-group-valued finite-place Artin
homomorphism is exactly the chosen local norm subgroup. -/
theorem chosenFinitePlaceArtinToDecompositionGroup_ker
    (v : HeightOneSpectrum (𝓞 K)) :
    MonoidHom.ker
        (chosenFinitePlaceArtinToDecompositionGroup
          (K := K) (L := L) v) =
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [chosenFinitePlaceArtinToDecompositionGroup,
    MonoidHom.ker_codRestrict,
    Reciprocity.chosenFinitePlaceArtinMonoidHom_ker]

open scoped Classical in
/-- The first-isomorphism identification of the chosen local norm
quotient with the actual finite-place decomposition group. -/
noncomputable def chosenFinitePlaceNormQuotientEquivDecompositionGroup
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.ChosenFinitePlaceNormQuotient
        (K := K) (L := L) v ≃*
      _root_.finitePlaceDecompositionGroup
        (K := K) (L := L) v :=
  QuotientGroup.liftEquiv
    (_root_.chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
    (chosenFinitePlaceArtinToDecompositionGroup_surjective
      (K := K) (L := L) v)
    (chosenFinitePlaceArtinToDecompositionGroup_ker
      (K := K) (L := L) v).symm

open scoped Classical in
/-- On a quotient representative, the finite-place first-isomorphism
equivalence is the decomposition-group-valued Artin map. -/
@[simp]
theorem chosenFinitePlaceNormQuotientEquivDecompositionGroup_mk
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    chosenFinitePlaceNormQuotientEquivDecompositionGroup
        (K := K) (L := L) v
        (QuotientGroup.mk x) =
      chosenFinitePlaceArtinToDecompositionGroup
        (K := K) (L := L) v x := by
  rfl

open scoped Classical in
/-- The order of the chosen finite-place norm quotient is the actual
local extension degree. -/
theorem chosenFinitePlaceNormQuotient_card_eq_finitePlaceLocalDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card
        (_root_.ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v) =
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  calc
    Nat.card
        (_root_.ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v) =
        Nat.card
          (_root_.finitePlaceDecompositionGroup
            (K := K) (L := L) v) :=
      Nat.card_congr
        (chosenFinitePlaceNormQuotientEquivDecompositionGroup
          (K := K) (L := L) v).toEquiv
    _ =
        _root_.finitePlaceLocalDegree
          (K := K) (L := L) v :=
      _root_.finitePlaceDecompositionGroup_card_eq_localDegree
        (K := K) (L := L) v

end GlobalClassFields
end GlobalClassFieldTheory

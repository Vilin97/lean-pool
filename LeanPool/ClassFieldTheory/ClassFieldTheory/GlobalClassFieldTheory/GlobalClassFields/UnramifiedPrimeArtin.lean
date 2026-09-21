/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
/-!
# Prime Artin elements at unramified finite places

For a finite abelian extension of number fields, the global Artin image
of the normalized one-place prime idèle is the chosen local Artin image
of an element of normalized order one.

At a chosen unramified finite place, integral units lie in the local norm
group.  Consequently the local Artin symbol depends only on normalized
order, the prime Artin element generates the full decomposition group,
and its order is the local degree.  This gives the genuine
decomposition law: the prime Artin element is trivial exactly when the
place splits completely.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The actual global Artin element of the normalized one-place prime
idèle at a finite place. -/
def finitePlacePrimeArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    L ≃ₐ[K] L :=
  Reciprocity.globalArtinMonoidHom
    (K := K) (L := L) (finitePrimeIdele v)

/-- The global prime Artin element is the chosen local Artin image of
the normalized order-one local element. -/
@[simp]
theorem finitePlacePrimeArtin_eq_chosenFinitePlaceArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlacePrimeArtin (K := K) (L := L) v =
      Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [finitePlacePrimeArtin, finitePrimeIdele,
    Reciprocity.globalArtinMonoidHom_finitePlaceIdele]

/-- At a chosen unramified finite place, two local elements of equal
normalized order have the same local Artin symbol. -/
theorem
    chosenFinitePlaceArtin_eq_of_localOrder_eq_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v)
    {x y : (v.adicCompletion K)ˣ}
    (hxy :
      FiniteIdeleGroup.localOrder v x =
        FiniteIdeleGroup.localOrder v y) :
    Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x =
      Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v y := by
  have hunit :
      x * y⁻¹ ∈
        (v.adicCompletionIntegers K).units := by
    apply
      (FiniteIdeleGroup.localOrder_eq_zero_iff
        v (x * y⁻¹)).1
    rw [map_mul, map_inv, hxy]
    simp
  have hker :
      x * y⁻¹ ∈
        (Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).ker := by
    rw [
      Reciprocity.chosenFinitePlaceArtinMonoidHom_ker
        (K := K) (L := L) v]
    exact
      _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v hunram hunit
  exact
    mul_inv_eq_one.mp
      (by
        simpa only [map_mul, map_inv] using
          MonoidHom.mem_ker.mp hker)

/-- At a chosen unramified finite place, every local Artin symbol is a
power of the normalized prime Artin element, with exponent its
normalized local order. -/
theorem
    chosenFinitePlaceArtin_eq_primeArtin_zpow_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v)
    (x : (v.adicCompletion K)ˣ) :
    Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x =
      finitePlacePrimeArtin (K := K) (L := L) v ^
        (FiniteIdeleGroup.localOrder v x).toAdd := by
  rw [finitePlacePrimeArtin_eq_chosenFinitePlaceArtin]
  let n := (FiniteIdeleGroup.localOrder v x).toAdd
  calc
    Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x =
        Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          ((FiniteIdeleGroup.chosenLocalOrderSection v 1) ^ n) := by
      apply
        chosenFinitePlaceArtin_eq_of_localOrder_eq_of_chosenUnramified
          (K := K) (L := L) v hunram
      apply Multiplicative.ext
      rw [map_zpow, Int.toAdd_zpow,
        FiniteIdeleGroup.localOrder_chosenLocalOrderSection]
      simp only [n, one_mul]
    _ =
        Reciprocity.chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v
            (FiniteIdeleGroup.chosenLocalOrderSection v 1) ^ n := by
      exact map_zpow
        (Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v)
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) n

/-- At a chosen unramified finite place, the prime Artin element
generates the actual decomposition group. -/
theorem
    finitePlaceDecompositionGroup_eq_zpowers_finitePlacePrimeArtin_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    _root_.finitePlaceDecompositionGroup
        (K := K) (L := L) v =
      Subgroup.zpowers
        (finitePlacePrimeArtin
          (K := K) (L := L) v) := by
  rw [
    ← Reciprocity.chosenFinitePlaceArtinMonoidHom_range
      (K := K) (L := L) v]
  apply le_antisymm
  · rintro σ ⟨x, rfl⟩
    rw [
      chosenFinitePlaceArtin_eq_primeArtin_zpow_of_chosenUnramified
        (K := K) (L := L) v hunram x]
    exact
      Subgroup.zpow_mem_zpowers
        (finitePlacePrimeArtin
          (K := K) (L := L) v)
        (FiniteIdeleGroup.localOrder v x).toAdd
  · intro σ hσ
    obtain ⟨n, rfl⟩ :=
      (Subgroup.mem_zpowers_iff.mp hσ)
    refine
      ⟨(FiniteIdeleGroup.chosenLocalOrderSection v 1) ^ n, ?_⟩
    rw [map_zpow,
      ← finitePlacePrimeArtin_eq_chosenFinitePlaceArtin
        (K := K) (L := L) v]

/-- At a chosen unramified finite place, the order of the actual prime
Artin element is the local extension degree. -/
theorem
    orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    orderOf
        (finitePlacePrimeArtin
          (K := K) (L := L) v) =
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  calc
    orderOf
        (finitePlacePrimeArtin
          (K := K) (L := L) v) =
        Nat.card
          (Subgroup.zpowers
            (finitePlacePrimeArtin
              (K := K) (L := L) v)) :=
      (Nat.card_zpowers
        (finitePlacePrimeArtin
          (K := K) (L := L) v)).symm
    _ =
        Nat.card
          (_root_.finitePlaceDecompositionGroup
            (K := K) (L := L) v) := by
      rw [
        finitePlaceDecompositionGroup_eq_zpowers_finitePlacePrimeArtin_of_chosenUnramified
          (K := K) (L := L) v hunram]
    _ =
        _root_.finitePlaceLocalDegree
          (K := K) (L := L) v :=
      _root_.finitePlaceDecompositionGroup_card_eq_localDegree
        (K := K) (L := L) v

/-- At a chosen unramified finite place, the actual prime Artin element
is trivial exactly when the place splits completely. -/
theorem
    finitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    finitePlacePrimeArtin
          (K := K) (L := L) v =
        1 ↔
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  rw [
    _root_.finitePlaceSplitsCompletely_iff_localDegree_eq_one,
    ←
      orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
        (K := K) (L := L) v hunram]
  exact orderOf_eq_one_iff.symm

end GlobalClassFields
end GlobalClassFieldTheory

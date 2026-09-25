/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertNormCharacterization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
/-!
# Maximality criteria for Hilbert class fields

An unramified cyclic extension reaches the big or small Hilbert norm
subgroup exactly when its degree reaches the corresponding narrow or
ordinary class number.  Thus a maximal-degree unramified cyclic
extension has the canonical Hilbert reciprocity quotient.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

private theorem hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

private instance narrowClassGroup_finite :
    Finite (RayClass.NarrowClassGroup K) :=
  Finite.of_equiv
    (RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)))
    (RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup
      (K := K)).toEquiv

private instance bigHilbertNormQuotient_finite :
    Finite
      (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) :=
  Finite.of_equiv
    (RayClass.NarrowClassGroup K)
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.toEquiv

private instance bigHilbertNormSubgroup_finiteIndex :
    (bigHilbertClassFieldNormSubgroup
      (K := K)).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

/-- A cyclic extension unramified at all finite places has the big
Hilbert norm subgroup exactly when its degree is the order of the
narrow class group. -/
theorem
    ideleClassNorm_range_eq_bigHilbertClassFieldNormSubgroup_iff_finrank_eq_narrowClassGroup_card
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (_root_.ideleClassNorm K L).range =
        bigHilbertClassFieldNormSubgroup (K := K) ↔
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K) := by
  constructor
  · intro hnorm
    calc
      Module.finrank K L =
          ((_root_.ideleClassNorm K L).range).index :=
        (ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
          K L).symm
      _ =
          (bigHilbertClassFieldNormSubgroup
            (K := K)).index := by
        rw [hnorm]
      _ =
          Nat.card
            (IdeleClassGroup K ⧸
              bigHilbertClassFieldNormSubgroup
                (K := K)) :=
        Subgroup.index_eq_card
          (bigHilbertClassFieldNormSubgroup (K := K))
      _ = Nat.card (RayClass.NarrowClassGroup K) :=
        Nat.card_congr
          (bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K)).toEquiv
  · intro hdegree
    have hcard :
        Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup
              (K := K)) =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) := by
      calc
        Nat.card
            (IdeleClassGroup K ⧸
              bigHilbertClassFieldNormSubgroup
                (K := K)) =
          Nat.card (RayClass.NarrowClassGroup K) :=
          Nat.card_congr
            (bigHilbertClassFieldQuotientEquivNarrowClassGroup
              (K := K)).toEquiv
        _ = Module.finrank K L := hdegree.symm
        _ =
            ((_root_.ideleClassNorm K L).range).index :=
          (ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
            K L).symm
        _ =
            Nat.card
              (IdeleClassGroup K ⧸
                (_root_.ideleClassNorm K L).range) :=
          Subgroup.index_eq_card
            ((_root_.ideleClassNorm K L).range)
    refine
      (eq_of_le_of_not_lt
        (bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
          (K := K) (L := L) hunramified)
        ?_).symm
    intro hlt
    have hstrict := Subgroup.index_strictAnti hlt
    rw [Subgroup.index_eq_card
      ((_root_.ideleClassNorm K L).range)] at hstrict
    rw [Subgroup.index_eq_card
      (bigHilbertClassFieldNormSubgroup (K := K))] at hstrict
    rw [hcard] at hstrict
    exact (lt_irrefl _ hstrict)

/-- The canonical narrow-class reciprocity map for a finite-unramified
cyclic extension is injective exactly at maximal possible degree. -/
theorem
    narrowClassGroupToIdeleClassNormQuotient_injective_iff_finrank_eq_narrowClassGroup_card
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Function.Injective
        (narrowClassGroupToIdeleClassNormQuotient
          (K := K) (L := L) hunramified) ↔
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K) := by
  let f :=
    narrowClassGroupToIdeleClassNormQuotient
      (K := K) (L := L) hunramified
  have hfSurjective : Function.Surjective f :=
    narrowClassGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L) hunramified
  have hNormCard :
      Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) =
        Module.finrank K L := by
    rw [← Subgroup.index_eq_card]
    exact
      ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
        K L
  constructor
  · intro hfInjective
    have hcard :
        Nat.card (RayClass.NarrowClassGroup K) =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) :=
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
    exact hNormCard.symm.trans hcard.symm
  · intro hdegree
    have hcard :
        Nat.card (RayClass.NarrowClassGroup K) =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) := by
      rw [hNormCard]
      exact hdegree.symm
    exact
      (hfSurjective.bijective_of_nat_card_le
        hcard.le).1

/-- At maximal narrow-class degree, the actual norm quotient of an
unramified cyclic extension is canonically the narrow class group. -/
def maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K)) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      RayClass.NarrowClassGroup K :=
  (QuotientGroup.quotientMulEquivOfEq
      ((ideleClassNorm_range_eq_bigHilbertClassFieldNormSubgroup_iff_finrank_eq_narrowClassGroup_card
        (K := K) (L := L) hunramified).2 hdegree)).trans
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K))

/-- A cyclic extension unramified at every finite and infinite place
has the small Hilbert norm subgroup exactly when its degree is the
ordinary class number. -/
theorem
    ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber
    [IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (_root_.ideleClassNorm K L).range =
        smallHilbertClassFieldNormSubgroup (K := K) ↔
      Module.finrank K L =
        NumberField.classNumber K := by
  constructor
  · intro hnorm
    calc
      Module.finrank K L =
          ((_root_.ideleClassNorm K L).range).index :=
        (ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
          K L).symm
      _ =
          (smallHilbertClassFieldNormSubgroup
            (K := K)).index := by
        rw [hnorm]
      _ =
          Nat.card
            (IdeleClassGroup K ⧸
              smallHilbertClassFieldNormSubgroup
                (K := K)) :=
        Subgroup.index_eq_card
          (smallHilbertClassFieldNormSubgroup (K := K))
      _ = NumberField.classNumber K :=
        smallHilbertClassFieldQuotient_card_eq_classNumber
          (K := K)
  · intro hdegree
    have hcard :
        Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup
              (K := K)) =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) := by
      calc
        Nat.card
            (IdeleClassGroup K ⧸
              smallHilbertClassFieldNormSubgroup
                (K := K)) =
          NumberField.classNumber K :=
          smallHilbertClassFieldQuotient_card_eq_classNumber
            (K := K)
        _ = Module.finrank K L := hdegree.symm
        _ =
            ((_root_.ideleClassNorm K L).range).index :=
          (ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
            K L).symm
        _ =
            Nat.card
              (IdeleClassGroup K ⧸
                (_root_.ideleClassNorm K L).range) :=
          Subgroup.index_eq_card
            ((_root_.ideleClassNorm K L).range)
    refine
      (eq_of_le_of_not_lt
        (smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
          (K := K) (L := L) hunramifiedFinite)
        ?_).symm
    intro hlt
    have hstrict := Subgroup.index_strictAnti hlt
    rw [Subgroup.index_eq_card
      ((_root_.ideleClassNorm K L).range)] at hstrict
    rw [Subgroup.index_eq_card
      (smallHilbertClassFieldNormSubgroup (K := K))] at hstrict
    rw [hcard] at hstrict
    exact (lt_irrefl _ hstrict)

/-- The canonical ordinary class-group reciprocity map for an
everywhere-unramified cyclic extension is injective exactly at maximal
possible degree. -/
theorem
    classGroupToIdeleClassNormQuotient_injective_iff_finrank_eq_classNumber
    [IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Function.Injective
        (classGroupToIdeleClassNormQuotient
          (K := K) (L := L) hunramifiedFinite) ↔
      Module.finrank K L =
        NumberField.classNumber K := by
  let f :=
    classGroupToIdeleClassNormQuotient
      (K := K) (L := L) hunramifiedFinite
  have hfSurjective : Function.Surjective f :=
    classGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L) hunramifiedFinite
  have hClassCard :
      Nat.card (ClassGroup (𝓞 K)) =
        NumberField.classNumber K := by
    rw [NumberField.classNumber,
      ← Nat.card_eq_fintype_card]
  have hNormCard :
      Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) =
        Module.finrank K L := by
    rw [← Subgroup.index_eq_card]
    exact
      ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
        K L
  constructor
  · intro hfInjective
    have hcard :
        Nat.card (ClassGroup (𝓞 K)) =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) :=
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
    calc
      Module.finrank K L =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) :=
        hNormCard.symm
      _ = Nat.card (ClassGroup (𝓞 K)) :=
        hcard.symm
      _ = NumberField.classNumber K :=
        hClassCard
  · intro hdegree
    have hcard :
        Nat.card (ClassGroup (𝓞 K)) =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) := by
      rw [hClassCard, hNormCard]
      exact hdegree.symm
    exact
      (hfSurjective.bijective_of_nat_card_le
        hcard.le).1

/-- At maximal ordinary-class degree, the actual norm quotient of an
everywhere-unramified cyclic extension is canonically the ordinary
ideal class group. -/
def maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup
    [IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq
      ((ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber
        (K := K) (L := L) hunramifiedFinite).2 hdegree)).trans
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K))

/-- Any two finite-unramified cyclic extensions attaining the narrow
class number determine the same idèle-class norm subgroup.  This is
uniqueness of the big Hilbert class field at the norm-subgroup level. -/
theorem maximalFiniteUnramifiedCyclicNormRanges_eq
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    [IsCyclic (M ≃ₐ[K] M)]
    (hLunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hMunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := M) = ∅)
    (hLdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (hMdegree :
      Module.finrank K M =
        Nat.card (RayClass.NarrowClassGroup K)) :
    (_root_.ideleClassNorm K L).range =
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        bigHilbertClassFieldNormSubgroup (K := K) :=
      (ideleClassNorm_range_eq_bigHilbertClassFieldNormSubgroup_iff_finrank_eq_narrowClassGroup_card
        (K := K) (L := L) hLunramifiedFinite).2 hLdegree
    _ = (_root_.ideleClassNorm K M).range :=
      ((ideleClassNorm_range_eq_bigHilbertClassFieldNormSubgroup_iff_finrank_eq_narrowClassGroup_card
        (K := K) (L := M) hMunramifiedFinite).2 hMdegree).symm

/-- Any two everywhere-unramified cyclic extensions attaining the
ordinary class number determine the same idèle-class norm subgroup.
This is uniqueness of the small Hilbert class field at the
norm-subgroup level. -/
theorem maximalEverywhereUnramifiedCyclicNormRanges_eq
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    [IsCyclic (M ≃ₐ[K] M)]
    [IsUnramifiedAtInfinitePlaces K L]
    [IsUnramifiedAtInfinitePlaces K M]
    (hLunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hMunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := M) = ∅)
    (hLdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (hMdegree :
      Module.finrank K M =
        NumberField.classNumber K) :
    (_root_.ideleClassNorm K L).range =
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        smallHilbertClassFieldNormSubgroup (K := K) :=
      (ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber
        (K := K) (L := L) hLunramifiedFinite).2 hLdegree
    _ = (_root_.ideleClassNorm K M).range :=
      ((ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber
        (K := K) (L := M) hMunramifiedFinite).2 hMdegree).symm

omit [IsCyclic (L ≃ₐ[K] L)] in
/-- A finite-unramified cyclic extension whose degree is the narrow
class number has no proper nested finite-unramified cyclic
overextension over the same base field. -/
theorem
    maximalFiniteUnramifiedCyclicExtension_relativeDegree_eq_one
    {M : Type}
    [Field M] [NumberField M]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]
    (hLdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (hMunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := M) = ∅) :
    Module.finrank L M = 1 := by
  have hdiv :
      Module.finrank K M ∣
        Nat.card (RayClass.NarrowClassGroup K) :=
    cyclicExtensionDegree_dvd_narrowClassGroup_card_of_no_ramifiedFinitePlaces
      (K := K) (L := M) hMunramifiedFinite
  have hdiv' :
      Module.finrank K L * Module.finrank L M ∣
        Module.finrank K L := by
    rw [Module.finrank_mul_finrank K L M, hLdegree]
    exact hdiv
  obtain ⟨c, hc⟩ := hdiv'
  have hone :
      1 = Module.finrank L M * c := by
    apply
      Nat.mul_left_cancel
        (show 0 < Module.finrank K L from Module.finrank_pos)
    simpa only [mul_one, mul_assoc] using hc
  exact Nat.dvd_one.mp ⟨c, hone⟩

omit [IsCyclic (L ≃ₐ[K] L)] in
/-- An everywhere-unramified cyclic extension whose degree is the
ordinary class number has no proper nested everywhere-unramified cyclic
overextension over the same base field. -/
theorem
    maximalEverywhereUnramifiedCyclicExtension_relativeDegree_eq_one
    {M : Type}
    [Field M] [NumberField M]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]
    [IsUnramifiedAtInfinitePlaces K M]
    (hLdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (hMunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := M) = ∅) :
    Module.finrank L M = 1 := by
  have hdiv :
      Module.finrank K M ∣
        NumberField.classNumber K :=
    cyclicEverywhereUnramifiedExtensionDegree_dvd_classNumber
      (K := K) (L := M) hMunramifiedFinite
  have hdiv' :
      Module.finrank K L * Module.finrank L M ∣
        Module.finrank K L := by
    rw [Module.finrank_mul_finrank K L M, hLdegree]
    exact hdiv
  obtain ⟨c, hc⟩ := hdiv'
  have hone :
      1 = Module.finrank L M * c := by
    apply
      Nat.mul_left_cancel
        (show 0 < Module.finrank K L from Module.finrank_pos)
    simpa only [mul_one, mul_assoc] using hc
  exact Nat.dvd_one.mp ⟨c, hone⟩

omit [IsCyclic (L ≃ₐ[K] L)] in
/-- A proper cyclic overextension of a narrow-class-degree extension
must ramify at some finite place of the base field. -/
theorem
    properCyclicOverextension_of_maximalFiniteUnramifiedExtension_has_ramifiedFinitePlace
    {M : Type}
    [Field M] [NumberField M]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]
    (hLdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (hrelativeDegree :
      Module.finrank L M ≠ 1) :
    _root_.ramifiedBaseFinitePlaces
        (K := K) (L := M) ≠ ∅ := by
  intro hMunramifiedFinite
  exact
    hrelativeDegree
      (maximalFiniteUnramifiedCyclicExtension_relativeDegree_eq_one
        (K := K) (L := L) (M := M)
        hLdegree hMunramifiedFinite)

omit [IsCyclic (L ≃ₐ[K] L)] in
/-- A proper cyclic overextension which is unramified at every infinite
place and lies above an ordinary-class-degree extension must ramify at
some finite place of the base field. -/
theorem
    properCyclicOverextension_of_maximalEverywhereUnramifiedExtension_has_ramifiedFinitePlace
    {M : Type}
    [Field M] [NumberField M]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]
    [IsUnramifiedAtInfinitePlaces K M]
    (hLdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (hrelativeDegree :
      Module.finrank L M ≠ 1) :
    _root_.ramifiedBaseFinitePlaces
        (K := K) (L := M) ≠ ∅ := by
  intro hMunramifiedFinite
  exact
    hrelativeDegree
      (maximalEverywhereUnramifiedCyclicExtension_relativeDegree_eq_one
        (K := K) (L := L) (M := M)
        hLdegree hMunramifiedFinite)

end GlobalClassFields
end GlobalClassFieldTheory

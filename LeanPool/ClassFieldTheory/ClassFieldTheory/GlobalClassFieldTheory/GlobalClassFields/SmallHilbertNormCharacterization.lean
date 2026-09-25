/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
/-!
# Small Hilbert norm subgroups and everywhere-unramified extensions

For a finite Galois extension which is unramified at both finite and
infinite places, every idele integral at all finite places is an actual
relative-idele norm.  It follows that the actual idele-class norm range
contains the small-Hilbert norm subgroup.

This realizes the maximality of the small Hilbert class field on the
norm-subgroup side.  The resulting quotient transition gives a canonical
surjection from the ordinary class group, its exact kernel
factorization, and the divisibility of the extension norm quotient order
by the class number.
-/

@[expose] public section

open scoped IsMulCommutative NumberField NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    smallHilbertNormCharacterization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

omit [FiniteDimensional K L] in
/-- At an extension unramified at all infinite places, the determinant
norm image of every infinite tensor factor is the whole local
multiplicative group. -/
theorem
    infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (v : InfinitePlace K) :
    _root_.infiniteTensorNormSubgroup
        (K := K) (L := L) v = ⊤ := by
  obtain ⟨w, hw⟩ :=
    InfinitePlace.comap_surjective
      (K := L) v
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  apply top_unique
  intro x _
  refine
    ⟨Units.map
        (algebraMap
          v.Completion w.Completion).toMonoidHom x,
      ?_⟩
  apply Units.ext
  change
    Algebra.norm v.Completion
        (algebraMap v.Completion w.Completion
          (x : v.Completion)) =
      (x : v.Completion)
  rw [
    Algebra.norm_algebraMap,
    InfinitePlace.IsUnramified.finrank_eq_one
      v (w.isUnramified K),
    pow_one]

/-- If the finite ramification support is empty, the chosen completion
above every finite base place is unramified. -/
theorem chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v
  by_contra hramified
  have hv :
      v ∈ _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
    exact
      ⟨_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        hramified⟩
  rw [hunramifiedFinite] at hv
  simp at hv

/-- In an extension unramified at every finite and infinite place,
every idele integral at all finite places is an actual relative-idele
norm. -/
theorem
    integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    IdeleGroup.integralAtFinitePlaces (K := K) ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  refine
    (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := L) a).2 ⟨?_, ?_⟩
  · intro v
    rw [
      infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
        (K := K) (L := L) v]
    exact Subgroup.mem_top _
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    apply
      _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces
          (K := K) (L := L) hunramifiedFinite v)
    change a.2 v ∈ (v.adicCompletionIntegers K).units
    exact
      (FiniteIdeleGroup.mem_integralSubgroup_iff a.2).1 ha v

private theorem integralIdeleClass_mem_ideleClassNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    {a : IdeleGroup K}
    (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := K)) :
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a ∈
      (_root_.ideleClassNorm K L).range := by
  obtain ⟨z, hz⟩ :=
    integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified
      (K := K) (L := L) hunramifiedFinite ha
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z),
      ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem principalIdeleClass_mem_ideleClassNorm_range
    {a : IdeleGroup K}
    (ha : a ∈ IdeleGroup.principalSubgroup K) :
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a ∈
      (_root_.ideleClassNorm K L).range := by
  have haOne :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a = 1 :=
    (QuotientGroup.eq_one_iff a).2 ha
  rw [haOne]
  exact ((_root_.ideleClassNorm K L).range).one_mem

/-- The norm subgroup of an everywhere-unramified finite Galois
extension contains the small-Hilbert norm subgroup. -/
theorem
    smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    smallHilbertClassFieldNormSubgroup (K := K) ≤
      (_root_.ideleClassNorm K L).range := by
  rw [smallHilbertClassFieldNormSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    exact
      integralIdeleClass_mem_ideleClassNorm_range_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite ha
  · intro a ha
    exact
      principalIdeleClass_mem_ideleClassNorm_range
        (K := K) (L := L) ha

/-- The canonical transition from the small-Hilbert reciprocity
quotient to the actual norm quotient of an everywhere-unramified
extension. -/
def smallHilbertClassFieldQuotientToIdeleClassNormQuotient
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  QuotientGroup.map
    (smallHilbertClassFieldNormSubgroup (K := K))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite hx)

/-- The small-Hilbert quotient transition sends an idele class to the
same class modulo the actual norm subgroup. -/
theorem smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (x : IdeleClassGroup K) :
    smallHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramifiedFinite
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl

/-- The transition from the small-Hilbert quotient to an
everywhere-unramified actual norm quotient is surjective. -/
theorem
    smallHilbertClassFieldQuotientToIdeleClassNormQuotient_surjective
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Function.Surjective
      (smallHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramifiedFinite) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      ((_root_.ideleClassNorm K L).range) q
  exact
    ⟨QuotientGroup.mk'
        (smallHilbertClassFieldNormSubgroup (K := K)) x,
      rfl⟩

/-- The kernel of the small-Hilbert quotient transition is the image
of the actual norm subgroup modulo the small-Hilbert norm subgroup. -/
theorem
    smallHilbertClassFieldQuotientToIdeleClassNormQuotient_ker
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    MonoidHom.ker
        (smallHilbertClassFieldQuotientToIdeleClassNormQuotient
          (K := K) (L := L) hunramifiedFinite) =
      Subgroup.map
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)))
        ((_root_.ideleClassNorm K L).range) := by
  unfold smallHilbertClassFieldQuotientToIdeleClassNormQuotient
  exact
    (QuotientGroup.ker_map
      (N := smallHilbertClassFieldNormSubgroup (K := K))
      ((_root_.ideleClassNorm K L).range)
      (MonoidHom.id (IdeleClassGroup K))
      (fun _ hx =>
        smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
          (K := K) (L := L) hunramifiedFinite hx)).trans
      (congrArg
        (Subgroup.map
          (QuotientGroup.mk' (smallHilbertClassFieldNormSubgroup (K := K))))
        (Subgroup.comap_id ((_root_.ideleClassNorm K L).range)))

/-- Quotienting the small-Hilbert reciprocity quotient by the image of
the actual norm subgroup recovers the actual norm quotient. -/
def smallHilbertNormImageQuotientEquivIdeleClassNormQuotient
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    ((IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            (smallHilbertClassFieldNormSubgroup (K := K)))
          ((_root_.ideleClassNorm K L).range)) ≃*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (smallHilbertClassFieldQuotientToIdeleClassNormQuotient_ker
        (K := K) (L := L) hunramifiedFinite).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (smallHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramifiedFinite)
      (smallHilbertClassFieldQuotientToIdeleClassNormQuotient_surjective
        (K := K) (L := L) hunramifiedFinite))

/-- The ordinary class group maps canonically onto the actual norm
quotient of every everywhere-unramified finite Galois extension. -/
def classGroupToIdeleClassNormQuotient
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    ClassGroup (𝓞 K) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (smallHilbertClassFieldQuotientToIdeleClassNormQuotient
      (K := K) (L := L) hunramifiedFinite).comp
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.toMonoidHom

/-- The canonical map from the ordinary class group to the actual norm
quotient of an everywhere-unramified extension is surjective. -/
theorem classGroupToIdeleClassNormQuotient_surjective
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Function.Surjective
      (classGroupToIdeleClassNormQuotient
        (K := K) (L := L) hunramifiedFinite) :=
  (smallHilbertClassFieldQuotientToIdeleClassNormQuotient_surjective
      (K := K) (L := L) hunramifiedFinite).comp
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.surjective

/-- The actual norm quotient of an everywhere-unramified finite Galois
extension has order dividing the class number. -/
theorem
    ideleClassNormQuotient_card_dvd_classNumber_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ∣
      NumberField.classNumber K := by
  calc
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ∣
        Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup (K := K)) := by
      simpa only [Subgroup.index_eq_card] using
        Subgroup.index_dvd_of_le
          (smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
            (K := K) (L := L) hunramifiedFinite)
    _ = NumberField.classNumber K :=
      smallHilbertClassFieldQuotient_card_eq_classNumber
        (K := K)

/-- The class number factors as the kernel order of the canonical class
group map times the order of an everywhere-unramified actual norm
quotient. -/
theorem
    classNumber_eq_unramifiedNormKernel_card_mul_normQuotient_card
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    NumberField.classNumber K =
      Nat.card
          (MonoidHom.ker
            (classGroupToIdeleClassNormQuotient
              (K := K) (L := L) hunramifiedFinite)) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
  let f :=
    classGroupToIdeleClassNormQuotient
      (K := K) (L := L) hunramifiedFinite
  have hf : Function.Surjective f :=
    classGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L) hunramifiedFinite
  calc
    NumberField.classNumber K =
        Nat.card (ClassGroup (𝓞 K)) := by
      rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]
    _ =
        Nat.card (MonoidHom.ker f) *
          (MonoidHom.ker f).index :=
      (Subgroup.card_mul_index (MonoidHom.ker f)).symm
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card f.range := by
      rw [Subgroup.index_ker f]
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
      rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]

/-- The degree of every finite cyclic extension unramified at all finite
and infinite places divides the class number. -/
theorem cyclicEverywhereUnramifiedExtensionDegree_dvd_classNumber
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Module.finrank K L ∣
      NumberField.classNumber K := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      ideleClassNormQuotient_card_dvd_classNumber_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite

/-- For a finite cyclic extension unramified at all finite and infinite
places, the class number is the kernel order of the canonical class
group reciprocity map times the extension degree. -/
theorem
    classNumber_eq_unramifiedCyclicNormKernel_card_mul_extensionDegree
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    NumberField.classNumber K =
      Nat.card
          (MonoidHom.ker
            (classGroupToIdeleClassNormQuotient
              (K := K) (L := L) hunramifiedFinite)) *
        Module.finrank K L := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      classNumber_eq_unramifiedNormKernel_card_mul_normQuotient_card
        (K := K) (L := L) hunramifiedFinite

end GlobalClassFields
end GlobalClassFieldTheory

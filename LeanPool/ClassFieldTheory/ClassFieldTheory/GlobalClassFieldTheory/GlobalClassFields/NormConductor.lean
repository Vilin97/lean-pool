/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorSupport
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorRayClassMaximality
/-!
# Narrow finite conductors of actual idele-class norm subgroups

For a finite Galois extension of number fields, the image of the
idele-class norm contains an explicitly constructed ray congruence
subgroup.  At a ramified finite place we choose a sufficiently deep
higher-unit group inside the open local norm subgroup.  Outside the
finite ramification set, the full local unit group already consists of
norms.  The archimedean positive subgroup is always contained in the
corresponding tensor-norm image.

This produces a defining modulus directly from the actual extension.  In
particular, the idele-class norm range is open, closed, and of finite
index.  Its narrow finite conductor can only be supported at ramified
finite places.  The full conductor, including an archimedean component,
is deliberately not defined here.
-/

open scoped NumberField IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain Topology

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- Fix the canonical commutative idèle-class structure used by the norm
quotients in this module. -/
local instance normConductorIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] normConductorIdeleClassGroupIsMulCommutative

omit [NumberField L] in
open scoped Classical in
/-- Every chosen finite-place norm subgroup contains a local
higher-unit group.  This is the local source used to construct an
actual defining modulus. -/
theorem exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ,
      RayClass.localHigherUnitGroup v n ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
  have hnormOne :
      (1 : (v.adicCompletion K)ˣ) ∈
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v :=
    (_root_.chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v).one_mem
  have hnormNhds :
      (_root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v :
        Set (v.adicCompletion K)ˣ) ∈
        𝓝 (1 : (v.adicCompletion K)ˣ) :=
    (_root_.chosenFinitePlaceLocalNormSubgroup_isOpen
      (K := K) (L := L) v).mem_nhds hnormOne
  obtain ⟨n, hn⟩ :=
    RayClass.exists_localHigherUnitGroup_subset v hnormNhds
  exact ⟨n, fun _ hx => hn hx⟩

open scoped Classical in
/-- The least higher-unit exponent whose group lies in the chosen
finite-place norm subgroup. -/
noncomputable def ideleClassNormLocalHigherUnitExponent
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)

omit [NumberField L] in
open scoped Classical in
/-- The local higher-unit group at the selected exponent lies in the
chosen local norm subgroup. -/
theorem ideleClassNormLocalHigherUnitExponent_spec
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v
        (ideleClassNormLocalHigherUnitExponent
          (K := K) (L := L) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v :=
  Nat.find_spec
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)

omit [NumberField L] in
open scoped Classical in
/-- The selected local higher-unit exponent is minimal among all
exponents whose higher-unit group lies in the chosen local norm
subgroup. -/
theorem ideleClassNormLocalHigherUnitExponent_min
    (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ}
    (hn :
      RayClass.localHigherUnitGroup v n ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v ≤ n :=
  Nat.find_min'
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
    hn

omit [NumberField L] in
open scoped Classical in
/-- The selected local exponent is zero exactly when every integral unit
of the finite-place completion is a norm from the chosen localized
extension. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_zero_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 ↔
      (v.adicCompletionIntegers K).units ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
  constructor
  · intro hzero
    simpa only [hzero, RayClass.localHigherUnitGroup_zero] using
      ideleClassNormLocalHigherUnitExponent_spec
        (K := K) (L := L) v
  · intro hunits
    apply Nat.eq_zero_of_le_zero
    apply
      ideleClassNormLocalHigherUnitExponent_min
        (K := K) (L := L) v
    simpa only [RayClass.localHigherUnitGroup_zero] using hunits

omit [NumberField L] in
open scoped Classical in
/-- At an unramified chosen completion, the selected local exponent is
zero because the whole local integral-unit group consists of norms. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
  rw [RayClass.localHigherUnitGroup_zero]
  exact
    _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram

open scoped Classical in
/-- Outside the finite set of ramified base places, the selected local
higher-unit exponent is zero. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_zero_of_not_mem_ramified
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L)) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 := by
  apply
    ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified
      (K := K) (L := L) v
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v
  by_contra hram
  apply hv
  rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
  exact
    ⟨_root_.finitePlaceExtensionCentre
        (K := K) (L := L) v
        (_root_.chosenFinitePlaceExtension (L := L) v),
      _root_.finitePlaceExtensionCentre_liesOver
        (K := K) (L := L) v
        (_root_.chosenFinitePlaceExtension (L := L) v),
      hram⟩

open scoped Classical in
/-- A finite modulus built from the actual local norm subgroups.  Its
support is contained in the finite set of ramified base places. -/
noncomputable def ideleClassNormDefiningModulus :
    RayClass.FiniteModulus K :=
  Finsupp.onFinset
    (_root_.ramifiedBaseFinitePlaces (K := K) (L := L))
    (ideleClassNormLocalHigherUnitExponent (K := K) (L := L))
    (by
      intro v hv
      by_contra hvRamified
      exact
        hv
          (ideleClassNormLocalHigherUnitExponent_eq_zero_of_not_mem_ramified
            (K := K) (L := L) v hvRamified))

open scoped Classical in
/-- Evaluation of the actual norm defining modulus is the selected local
higher-unit exponent. -/
@[simp]
theorem ideleClassNormDefiningModulus_apply
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormDefiningModulus (K := K) (L := L) v =
      ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v :=
  Finsupp.onFinset_apply

open scoped Classical in
/-- The local higher-unit group prescribed by the actual norm defining
modulus lies in the chosen local norm subgroup at every finite place. -/
theorem ideleClassNormDefiningModulus_local_spec
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v
        (ideleClassNormDefiningModulus (K := K) (L := L) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [ideleClassNormDefiningModulus_apply]
  exact
    ideleClassNormLocalHigherUnitExponent_spec
      (K := K) (L := L) v

open scoped Classical in
/-- The norm defining modulus is pointwise minimal among all moduli whose
prescribed local higher-unit groups consist of chosen local norms. -/
theorem ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le
    (m : RayClass.FiniteModulus K)
    (hm :
      ∀ v : HeightOneSpectrum (𝓞 K),
        RayClass.localHigherUnitGroup v (m v) ≤
          _root_.chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v) :
    ideleClassNormDefiningModulus (K := K) (L := L) ≤ m := by
  intro v
  rw [ideleClassNormDefiningModulus_apply]
  exact
    ideleClassNormLocalHigherUnitExponent_min
      (K := K) (L := L) v (hm v)

open scoped Classical in
/-- A finite place occurs in the constructed norm modulus exactly when
some integral unit at that place is not a norm from the chosen localized
extension. -/
theorem mem_ideleClassNormDefiningModulus_support_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈
        (ideleClassNormDefiningModulus
          (K := K) (L := L)).support ↔
      ¬ (v.adicCompletionIntegers K).units ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
  rw [Finsupp.mem_support_iff,
    ideleClassNormDefiningModulus_apply]
  exact
    not_congr
      (ideleClassNormLocalHigherUnitExponent_eq_zero_iff
        (K := K) (L := L) v)

open scoped Classical in
/-- The constructed defining modulus is supported only at ramified
finite places of the base field. -/
theorem ideleClassNormDefiningModulus_support_subset_ramifiedBaseFinitePlaces :
    (ideleClassNormDefiningModulus
        (K := K) (L := L)).support ⊆
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  intro v hv
  by_contra hvRamified
  have hne :
      ideleClassNormDefiningModulus
          (K := K) (L := L) v ≠ 0 :=
    Finsupp.mem_support_iff.mp hv
  rw [ideleClassNormDefiningModulus_apply,
    ideleClassNormLocalHigherUnitExponent_eq_zero_of_not_mem_ramified
      (K := K) (L := L) v hvRamified] at hne
  exact hne rfl

open scoped Classical in
/-- The raw idele congruence subgroup of the constructed modulus lies
in the image of the actual relative-idele norm. -/
theorem
    ideleCongruenceSubgroup_normDefiningModulus_le_relativeIdeleNorm_range :
    (RayClass.Modulus.narrowOfFinite
        (ideleClassNormDefiningModulus
          (K := K) (L := L))).ideleCongruenceSubgroup ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  rw [RayClass.Modulus.ideleCongruenceSubgroup_narrowOfFinite] at ha
  refine
    (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := L) a).2 ⟨?_, ?_⟩
  · intro w
    apply
      _root_.infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) w
    have hw :=
      (RayClass.mem_narrowInfiniteCongruenceSubgroup_iff a.1).1 ha.1 w
    simpa only [IdeleGroup.infiniteComponent_apply] using hw
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    apply
      ideleClassNormDefiningModulus_local_spec
        (K := K) (L := L) v
    have hv :=
      (RayClass.mem_finiteCongruenceSubgroup_iff
        (ideleClassNormDefiningModulus (K := K) (L := L)) a.2).1
          ha.2 v
    simpa only [IdeleGroup.finiteComponent_apply] using hv

open scoped Classical in
/-- The explicitly constructed modulus is a defining modulus for the
actual idele-class norm subgroup. -/
theorem ideleClassNormDefiningModulus_isDefiningModulus :
    IsDefiningModulus
      ((_root_.ideleClassNorm K L).range)
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormDefiningModulus (K := K) (L := L))) := by
  rw [IsDefiningModulus, RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    change
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range
    obtain ⟨z, hz⟩ :=
      ideleCongruenceSubgroup_normDefiningModulus_le_relativeIdeleNorm_range
        (K := K) (L := L) ha
    refine
      ⟨QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L)
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z), ?_⟩
    change
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.norm K L
            (_root_.relativeIdeleBaseChangeMulEquiv
              (K := K) (L := L) z)) =
        QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a
    rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]
  · intro a ha
    change
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range
    have haOne :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a = 1 :=
      (QuotientGroup.eq_one_iff a).2 ha
    rw [haOne]
    exact ((_root_.ideleClassNorm K L).range).one_mem

open scoped Classical in
/-- The conductorial subgroup supplied by the actual idèle-class norm
range and its explicitly constructed defining modulus. -/
noncomputable def ideleClassNormConductorialSubgroup :
    ConductorialSubgroup K :=
  ⟨(_root_.ideleClassNorm K L).range,
    ⟨RayClass.Modulus.narrowOfFinite
        (ideleClassNormDefiningModulus (K := K) (L := L)),
      ideleClassNormDefiningModulus_isDefiningModulus
        (K := K) (L := L)⟩⟩

open scoped Classical in
/-- The narrow finite conductor of the actual idèle-class norm range. -/
noncomputable def ideleClassNormNarrowFiniteConductor :
    RayClass.FiniteModulus K :=
  (ideleClassNormConductorialSubgroup
    (K := K) (L := L)).narrowFiniteConductor

open scoped Classical in
/-- The actual idele-class norm subgroup is open in the ordinary
idele-class topology. -/
theorem ideleClassNorm_range_isOpen :
    IsOpen
      (((_root_.ideleClassNorm K L).range :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) := by
  exact
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).isOpen

open scoped Classical in
/-- The actual idele-class norm subgroup is closed. -/
theorem ideleClassNorm_range_isClosed :
    IsClosed
      (((_root_.ideleClassNorm K L).range :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  (ideleClassNormConductorialSubgroup
    (K := K) (L := L)).isClosed

open scoped Classical in
/-- The actual idele-class norm subgroup has finite index. -/
instance ideleClassNorm_rangeFiniteIndex :
    ((_root_.ideleClassNorm K L).range).FiniteIndex :=
  ConductorialSubgroup.finiteIndex
    (ideleClassNormConductorialSubgroup (K := K) (L := L))

open scoped Classical in
/-- The narrow finite conductor itself is a defining modulus for the actual
idele-class norm subgroup. -/
theorem ideleClassNorm_narrowFiniteConductor_isDefiningModulus :
    IsDefiningModulus
      ((_root_.ideleClassNorm K L).range)
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
  (ideleClassNormConductorialSubgroup
    (K := K) (L := L)).narrowFiniteConductor_isDefiningModulus

open scoped Classical in
/-- The canonical quotient map from the ray class group at the actual
narrow finite norm conductor onto the actual idèle-class norm quotient. -/
noncomputable def
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite
          (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      ideleClassNorm_narrowFiniteConductor_isDefiningModulus
        (K := K) (L := L) hx)

open scoped Classical in
/-- The narrow finite conductor ray-class quotient map sends an idèle class to its
class modulo the actual norm subgroup. -/
theorem narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk
    (x : IdeleClassGroup K) :
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L)
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl

open scoped Classical in
/-- The canonical map from the conductor ray class group to the actual
idele-class norm quotient is surjective. -/
theorem
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_surjective :
    Function.Surjective
      (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L)) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      ((_root_.ideleClassNorm K L).range) q
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) x,
      rfl⟩

open scoped Classical in
/-- The kernel of the conductor ray-class quotient map is the image of
the actual norm subgroup modulo the conductor congruence subgroup. -/
theorem
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_ker :
    MonoidHom.ker
        (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
          (K := K) (L := L)) =
      Subgroup.map
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))))
        ((_root_.ideleClassNorm K L).range) := by
  unfold narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
  let N :=
    RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
  let M := (_root_.ideleClassNorm K L).range
  change
    (QuotientGroup.map N M (MonoidHom.id (IdeleClassGroup K)) _).ker =
      Subgroup.map (QuotientGroup.mk' N) M
  simpa only [Subgroup.comap_id] using
    (QuotientGroup.ker_map (N := N) M
      (MonoidHom.id (IdeleClassGroup K))
      (show N ≤ Subgroup.comap (MonoidHom.id (IdeleClassGroup K)) M from
        fun _ hx =>
          ideleClassNorm_narrowFiniteConductor_isDefiningModulus
            (K := K) (L := L) hx))

open scoped Classical in
/-- Quotienting the conductor ray class group by the image of the actual
norm subgroup recovers the actual idele-class norm quotient. -/
noncomputable def
    narrowFiniteConductorRayClassNormSubgroupQuotientEquivIdeleClassNormQuotient :
    (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L))) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor
                  (K := K) (L := L)))))
          ((_root_.ideleClassNorm K L).range)) ≃*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_ker
        (K := K) (L := L)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L))
      (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_surjective
        (K := K) (L := L)))

open scoped Classical in
/-- The conductor ray class number factors as the order of the norm
subgroup modulo conductor congruence times the order of the actual
idele-class norm quotient. -/
theorem
    narrowFiniteConductorRayClassGroup_card_eq_normSubgroupImage_card_mul_normQuotient_card :
    Nat.card
        (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) =
      Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite
                  (ideleClassNormNarrowFiniteConductor
                    (K := K) (L := L)))))
            ((_root_.ideleClassNorm K L).range)) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
  let f :=
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
      (K := K) (L := L)
  have hf : Function.Surjective f :=
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L)
  calc
    Nat.card
        (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) =
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
    _ = Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite
                  (ideleClassNormNarrowFiniteConductor
                    (K := K) (L := L)))))
            ((_root_.ideleClassNorm K L).range)) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
      rw [
        narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_ker
          (K := K) (L := L)]

open scoped Classical in
/-- The order of the actual idèle-class norm quotient divides the order of
the ray class group at its narrow finite conductor. -/
theorem
    ideleClassNormQuotient_card_dvd_narrowFiniteConductorRayClassGroup_card :
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ∣
      Nat.card
        (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) := by
  simpa only [Subgroup.index_eq_card] using
    Subgroup.index_dvd_of_le
      (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
        (K := K) (L := L))

open scoped Classical in
/-- The narrow finite conductor of the actual norm subgroup is bounded by
the modulus obtained from the chosen local norm subgroups. -/
theorem ideleClassNorm_narrowFiniteConductor_le_normDefiningModulus :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) ≤
      ideleClassNormDefiningModulus (K := K) (L := L) :=
  (ideleClassNormConductorialSubgroup
    (K := K) (L := L)).narrowFiniteConductor_le
    (ideleClassNormDefiningModulus_isDefiningModulus
      (K := K) (L := L))

open scoped Classical in
/-- At every finite place, the exponent of the narrow finite conductor of
the actual norm subgroup is bounded by the least higher-unit depth already
contained in the chosen local norm subgroup. -/
theorem ideleClassNorm_narrowFiniteConductor_apply_le_localHigherUnitExponent
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) v ≤
      ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v := by
  have hle :=
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor_le
      (ideleClassNormDefiningModulus_isDefiningModulus
        (K := K) (L := L))
  simpa only [ideleClassNormNarrowFiniteConductor,
    RayClass.Modulus.finitePart_narrowOfFinite,
    ideleClassNormDefiningModulus_apply] using hle v

open scoped Classical in
/-- Every finite prime occurring in the narrow finite conductor of the
actual norm subgroup already occurs in the modulus constructed from the
chosen local norm subgroups. -/
theorem
    ideleClassNorm_narrowFiniteConductor_support_subset_normDefiningModulus_support :
    (ideleClassNormNarrowFiniteConductor
      (K := K) (L := L)).support ⊆
      (ideleClassNormDefiningModulus
        (K := K) (L := L)).support := by
  intro v hv
  have hfinite_ne :
      ideleClassNormNarrowFiniteConductor
          (K := K) (L := L) v ≠ 0 :=
    Finsupp.mem_support_iff.mp hv
  apply Finsupp.mem_support_iff.mpr
  intro hlocal_zero
  apply hfinite_ne
  exact Nat.eq_zero_of_le_zero
    ((ideleClassNorm_narrowFiniteConductor_le_normDefiningModulus
      (K := K) (L := L) v).trans_eq hlocal_zero)

open scoped Classical in
/-- If the zeroth one-place higher-unit class subgroup lies in the
actual idèle-class norm range, then that finite place is absent from
the narrow finite conductor support. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
    (v : HeightOneSpectrum (𝓞 K))
    (hlocal :
      RayClass.localHigherUnitClassSubgroup v 0 ≤
        (_root_.ideleClassNorm K L).range) :
    v ∉
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support := by
  change v ∉
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor.support
  rw [Finsupp.notMem_support_iff,
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent v]
  exact
    Nat.eq_zero_of_le_zero
      ((ideleClassNormConductorialSubgroup
        (K := K) (L := L)).narrowFiniteLocalConductorExponent_le v hlocal)

open scoped Classical in
/-- If the chosen prime of `L` above `v` is algebraically unramified,
then `v` does not occur in the conductor of the actual idele-class norm
subgroup. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    v ∉
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support := by
  apply
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
      (K := K) (L := L) v
  exact
    localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_isUnramifiedAt
      (K := K) (L := L) v hunram

open scoped Classical in
/-- A finite place which splits completely does not occur in the narrow
finite conductor of the actual idèle-class norm subgroup. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_splitsCompletely
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    v ∉
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support := by
  apply
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
      (K := K) (L := L) v
  intro c hc
  obtain ⟨x, hx, rfl⟩ := hc
  apply
    finitePlaceIdeleClass_range_le_ideleClassNorm_range_of_splitsCompletely
      (K := K) (L := L) v hsplit
  exact ⟨x, rfl⟩

open scoped Classical in
/-- The narrow finite conductor of an actual finite Galois idèle-class norm
subgroup is supported only at ramified finite places of the base field. -/
theorem ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces :
    (ideleClassNormNarrowFiniteConductor
      (K := K) (L := L)).support ⊆
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  intro v hv
  by_contra hvRamified
  have hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal := by
    by_contra hram
    apply hvRamified
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
    exact
      ⟨_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        hram⟩
  exact
    (not_mem_ideleClassNorm_narrowFiniteConductor_support_of_isUnramifiedAt
      (K := K) (L := L) v hunram) hv

end GlobalClassFields
end GlobalClassFieldTheory

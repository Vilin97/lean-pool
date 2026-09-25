/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicRayClassMaximality
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius
/-!
# Prime classes at the narrow finite norm conductor

The one-place idèle of normalized order one defines two compatible
prime classes: one in the ray class group at the exact narrow finite norm
conductor, and one in the actual idele-class norm quotient.  The
canonical narrow-finite-conductor ray-class map sends the former to the latter.

For cyclic extensions the order of the norm-quotient class divides the
extension degree.  Complete splitting forces this class to be trivial;
when the narrow-finite-conductor ray-class presentation is maximal, it also
forces the narrow finite conductor ray prime class itself to be trivial.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

-- Reuse the normality witness embedded in the imported ideal-Artin maps.
-- Without it, every occurrence of the norm quotient repeats an expensive
-- unsuccessful instance search and builds a non-definitional witness.
attribute [local instance]
  IdealClassFieldTheory.ideleClassSubgroupNormal

/-- The class of the normalized one-place prime idèle in the ray class
group at the exact narrow finite conductor of the actual norm subgroup. -/
def narrowFiniteConductorRayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
  QuotientGroup.mk'
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))))
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- The class of the normalized one-place prime idèle in the actual
idele-class norm quotient. -/
def ideleClassNormFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      (_root_.ideleClassNorm K L).range :=
  QuotientGroup.mk'
    ((_root_.ideleClassNorm K L).range)
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- At a prime outside the exact narrow finite norm conductor, the ideal-theoretic
Frobenius class agrees with the class of the normalized one-place idèle
in the actual norm quotient. -/
theorem
    narrowFiniteConductorIdealFrobeniusClass_eq_ideleClassNormFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    IdealClassFieldTheory.idealFrobeniusClass
        (RayClass.Modulus.narrowOfFinite
          (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
        ((_root_.ideleClassNorm K L).range)
        (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
          (K := K) (L := L))
        v hv =
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v := by
  let m : RayClass.Modulus K :=
    RayClass.Modulus.narrowOfFinite
      (ideleClassNormNarrowFiniteConductor (K := K) (L := L))
  let N := (_root_.ideleClassNorm K L).range
  let hm : RayClass.Modulus.congruenceSubgroup m ≤ N :=
    ideleClassNorm_narrowFiniteConductor_isDefiningModulus
      (K := K) (L := L)
  let a : RayClass.idelePrimeToModulusSubgroup m :=
    ⟨finitePrimeIdele v,
      finitePrimeIdele_mem_idelePrimeToModulusSubgroup m v hv⟩
  have hIdeal :
      RayClass.primeToIdealMap m a =
        RayClass.primeToModulusIdeal m v hv :=
    primeToIdealMap_finitePrimeIdele m v hv
  have hArtin :
      IdealClassFieldTheory.idealArtinMap m N hm
          (RayClass.primeToIdealMap m a) =
        QuotientGroup.mk' N
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K)) :=
    idealArtinMap_primeToIdealMap m N hm a
  change
    IdealClassFieldTheory.idealArtinMap m N hm
        (RayClass.primeToModulusIdeal m v hv) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v))
  calc
    _ = IdealClassFieldTheory.idealArtinMap m N hm
          (RayClass.primeToIdealMap m a) :=
      congrArg (IdealClassFieldTheory.idealArtinMap m N hm) hIdeal.symm
    _ = QuotientGroup.mk' N
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K)) := hArtin
    _ = QuotientGroup.mk' N
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (finitePrimeIdele v)) := rfl

/-- The order of a Frobenius class in the actual norm quotient is the
order of its prime ideal modulo the ideal Artin kernel at the exact narrow
finite norm conductor. -/
theorem
    orderOf_ideleClassNormFrobeniusClass_eq_orderOf_idealArtinPrimeClass
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    orderOf
        (ideleClassNormFrobeniusClass
          (K := K) (L := L) v) =
      orderOf
        (QuotientGroup.mk'
          (IdealClassFieldTheory.idealArtinKernel
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
            ((_root_.ideleClassNorm K L).range)
            (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
              (K := K) (L := L)))
          (RayClass.primeToModulusIdeal
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
            v hv)) := by
  rw [←
    narrowFiniteConductorIdealFrobeniusClass_eq_ideleClassNormFrobeniusClass
      (K := K) (L := L) v hv]
  exact
    IdealClassFieldTheory.orderOf_idealFrobeniusClass
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
      ((_root_.ideleClassNorm K L).range)
      (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
        (K := K) (L := L))
      v hv

/-- Triviality of the actual norm-quotient Frobenius class is equivalent
to membership of the corresponding prime ideal in the ideal Artin kernel at
the exact narrow finite conductor. -/
theorem
    ideleClassNormFrobeniusClass_eq_one_iff_narrowFiniteConductorPrimeIdeal_mem_idealArtinKernel
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    ideleClassNormFrobeniusClass
          (K := K) (L := L) v =
        1 ↔
      RayClass.primeToModulusIdeal
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          v hv ∈
        IdealClassFieldTheory.idealArtinKernel
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          ((_root_.ideleClassNorm K L).range)
          (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
            (K := K) (L := L)) := by
  rw [←
    narrowFiniteConductorIdealFrobeniusClass_eq_ideleClassNormFrobeniusClass
      (K := K) (L := L) v hv]
  rfl

/-- The canonical narrow-finite-conductor ray-class map sends the narrow
finite conductor ray prime class to the corresponding actual norm-quotient
Frobenius class. -/
@[simp]
theorem
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L)
        (narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v) =
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v :=
  rfl

/-- The order of the actual norm-quotient Frobenius class divides the order
of its lift to the exact narrow-finite-conductor ray class group. -/
theorem
    orderOf_ideleClassNormFrobeniusClass_dvd_orderOf_narrowFiniteConductorRayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (ideleClassNormFrobeniusClass
          (K := K) (L := L) v) ∣
      orderOf
        (narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v) := by
  rw [←
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass
      (K := K) (L := L) v]
  exact
    orderOf_map_dvd
      (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L))
      (narrowFiniteConductorRayPrimeClass
        (K := K) (L := L) v)

/-- Equal source and target orders make triviality of the narrow finite
conductor ray prime class equivalent to triviality of its actual norm-quotient
Frobenius class. -/
theorem
    narrowFiniteConductorRayPrimeClass_eq_one_iff_ideleClassNormFrobeniusClass_eq_one
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (v : HeightOneSpectrum (𝓞 K)) :
    narrowFiniteConductorRayPrimeClass
        (K := K) (L := L) v = 1 ↔
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v = 1 := by
  let f :=
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
      (K := K) (L := L)
  have hfInjective : Function.Injective f :=
    (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_injective_iff_card_eq_normQuotient_card
      (K := K) (L := L)).2 hcard
  constructor
  · intro hprime
    calc
      ideleClassNormFrobeniusClass
          (K := K) (L := L) v =
          f (narrowFiniteConductorRayPrimeClass
            (K := K) (L := L) v) := by
        rw [
          narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass]
      _ = f 1 :=
        congrArg f hprime
      _ = 1 :=
        map_one f
  · intro hnorm
    apply hfInjective
    rw [
      narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass,
      hnorm, map_one]

/-- Equal source and target orders make the narrow finite conductor ray prime class
and its actual norm-quotient image have the same order. -/
theorem
    orderOf_narrowFiniteConductorRayPrimeClass_eq_orderOf_ideleClassNormFrobeniusClass
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v) =
      orderOf
        (ideleClassNormFrobeniusClass
          (K := K) (L := L) v) := by
  let f :=
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
      (K := K) (L := L)
  have hfInjective : Function.Injective f :=
    (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_injective_iff_card_eq_normQuotient_card
      (K := K) (L := L)).2 hcard
  have horder :=
    orderOf_injective f hfInjective
      (narrowFiniteConductorRayPrimeClass
        (K := K) (L := L) v)
  rw [
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass
      (K := K) (L := L) v] at horder
  exact horder.symm

/-- When the exact narrow-finite-conductor ray presentation has the same order as
the actual norm quotient, triviality of its ray prime class is
equivalent to membership of the prime ideal in the ideal Artin kernel. -/
theorem
    narrowFiniteConductorRayPrimeClass_eq_one_iff_narrowFiniteConductorPrimeIdeal_mem_idealArtinKernel
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v =
        1 ↔
      RayClass.primeToModulusIdeal
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          v hv ∈
        IdealClassFieldTheory.idealArtinKernel
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          ((_root_.ideleClassNorm K L).range)
          (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
            (K := K) (L := L)) := by
  rw [
    narrowFiniteConductorRayPrimeClass_eq_one_iff_ideleClassNormFrobeniusClass_eq_one
      (K := K) (L := L) hcard v,
    ideleClassNormFrobeniusClass_eq_one_iff_narrowFiniteConductorPrimeIdeal_mem_idealArtinKernel
      (K := K) (L := L) v hv]

/-- Complete splitting at a finite place forces the corresponding
actual norm-quotient Frobenius class to be trivial. -/
theorem
    finitePlaceSplitsCompletely_imp_ideleClassNormFrobeniusClass_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    ideleClassNormFrobeniusClass
        (K := K) (L := L) v = 1 := by
  apply (QuotientGroup.eq_one_iff _).2
  change
    IdeleGroup.finitePlaceIdeleClass v
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) ∈
      (_root_.ideleClassNorm K L).range
  apply
    finitePlaceIdeleClass_range_le_ideleClassNorm_range_of_splitsCompletely
      (K := K) (L := L) v hsplit
  exact
    ⟨FiniteIdeleGroup.chosenLocalOrderSection v 1, rfl⟩

/-- Complete splitting at a finite place makes its ideal Frobenius class at
the exact narrow finite norm conductor trivial. -/
theorem
    finitePlaceSplitsCompletely_imp_narrowFiniteConductorIdealFrobeniusClass_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    IdealClassFieldTheory.idealFrobeniusClass
        (RayClass.Modulus.narrowOfFinite
          (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
        ((_root_.ideleClassNorm K L).range)
        (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
          (K := K) (L := L))
        v
        (not_mem_ideleClassNorm_narrowFiniteConductor_support_of_splitsCompletely
          (K := K) (L := L) v hsplit) =
      1 := by
  rw [
    narrowFiniteConductorIdealFrobeniusClass_eq_ideleClassNormFrobeniusClass,
    finitePlaceSplitsCompletely_imp_ideleClassNormFrobeniusClass_eq_one
      (K := K) (L := L) v hsplit]

/-- A finite prime which splits completely belongs to the ideal Artin kernel
at the exact narrow finite norm conductor. -/
theorem
    finitePlaceSplitsCompletely_imp_narrowFiniteConductorPrimeIdeal_mem_idealArtinKernel
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    RayClass.primeToModulusIdeal
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          v
          (not_mem_ideleClassNorm_narrowFiniteConductor_support_of_splitsCompletely
            (K := K) (L := L) v hsplit) ∈
        IdealClassFieldTheory.idealArtinKernel
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          ((_root_.ideleClassNorm K L).range)
          (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
            (K := K) (L := L)) := by
  apply
    (ideleClassNormFrobeniusClass_eq_one_iff_narrowFiniteConductorPrimeIdeal_mem_idealArtinKernel
      (K := K) (L := L) v
      (not_mem_ideleClassNorm_narrowFiniteConductor_support_of_splitsCompletely
        (K := K) (L := L) v hsplit)).1
  exact
    finitePlaceSplitsCompletely_imp_ideleClassNormFrobeniusClass_eq_one
      (K := K) (L := L) v hsplit

section Cyclic

variable [IsCyclic (L ≃ₐ[K] L)]

/-- For a finite cyclic extension, the order of every actual
norm-quotient Frobenius class divides the extension degree. -/
theorem orderOf_ideleClassNormFrobeniusClass_dvd_extensionDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (ideleClassNormFrobeniusClass
          (K := K) (L := L) v) ∣
      Module.finrank K L := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      orderOf_dvd_natCard
        (ideleClassNormFrobeniusClass
          (K := K) (L := L) v)

/-- For a finite cyclic extension, the order of every ideal Frobenius class
outside the exact narrow finite norm conductor divides the extension degree. -/
theorem
    orderOf_narrowFiniteConductorIdealFrobeniusClass_dvd_extensionDegree
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    orderOf
        (IdealClassFieldTheory.idealFrobeniusClass
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          ((_root_.ideleClassNorm K L).range)
          (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
            (K := K) (L := L))
          v hv) ∣
      Module.finrank K L := by
  rw [
    narrowFiniteConductorIdealFrobeniusClass_eq_ideleClassNormFrobeniusClass]
  exact
    orderOf_ideleClassNormFrobeniusClass_dvd_extensionDegree
      (K := K) (L := L) v

/-- For a finite cyclic extension, the order of the prime ideal class modulo
the ideal Artin kernel at the exact narrow finite conductor divides the
extension degree. -/
theorem
    orderOf_narrowFiniteConductorPrimeIdealArtinClass_dvd_extensionDegree
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    orderOf
        (QuotientGroup.mk'
          (IdealClassFieldTheory.idealArtinKernel
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
            ((_root_.ideleClassNorm K L).range)
            (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
              (K := K) (L := L)))
          (RayClass.primeToModulusIdeal
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
            v hv)) ∣
      Module.finrank K L := by
  rw [←
    orderOf_ideleClassNormFrobeniusClass_eq_orderOf_idealArtinPrimeClass
      (K := K) (L := L) v hv]
  exact
    orderOf_ideleClassNormFrobeniusClass_dvd_extensionDegree
      (K := K) (L := L) v

/-- At maximal cyclic ray-class cardinality, triviality of the exact narrow
finite conductor ray prime class is equivalent to membership of the prime
ideal in the ideal Artin kernel. -/
theorem
    rayPrimeClass_eq_one_iff_primeIdeal_mem_idealArtinKernel_of_card_eq_extensionDegree
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support) :
    narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v =
        1 ↔
      RayClass.primeToModulusIdeal
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          v hv ∈
        IdealClassFieldTheory.idealArtinKernel
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))
          ((_root_.ideleClassNorm K L).range)
          (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
            (K := K) (L := L)) := by
  have hNormCard :
      Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) =
        Module.finrank K L := by
    rw [← Subgroup.index_eq_card]
    exact
      ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L
  exact
    narrowFiniteConductorRayPrimeClass_eq_one_iff_narrowFiniteConductorPrimeIdeal_mem_idealArtinKernel
      (K := K) (L := L)
      (hcard.trans hNormCard.symm) v hv

/-- If a cyclic extension reaches the full ray class number at its exact
narrow finite conductor, complete splitting forces the corresponding ray
prime class to be trivial. -/
theorem
    finitePlaceSplitsCompletely_imp_narrowFiniteConductorRayPrimeClass_eq_one_of_card_eq_extensionDegree
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    narrowFiniteConductorRayPrimeClass
        (K := K) (L := L) v = 1 := by
  have hfInjective :
      Function.Injective
        (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
          (K := K) (L := L)) :=
    (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_injective_iff_card_eq_extensionDegree
      (K := K) (L := L)).2 hcard
  apply hfInjective
  rw [
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass,
    finitePlaceSplitsCompletely_imp_ideleClassNormFrobeniusClass_eq_one
      (K := K) (L := L) v hsplit,
    map_one]

end Cyclic

/-- Under the maximal narrow-finite-conductor ray-class cardinality
condition, the order of every corresponding ray prime class divides the
extension degree. -/
theorem
    orderOf_narrowFiniteConductorRayPrimeClass_dvd_extensionDegree_of_card_eq
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v) ∣
      Module.finrank K L := by
  simpa only [hcard] using
    orderOf_dvd_natCard
      (narrowFiniteConductorRayPrimeClass
        (K := K) (L := L) v)

end GlobalClassFields
end GlobalClassFieldTheory

/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldPrimeSplitting
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius
/-!
# Prime idèles and ideal ray classes

A normalized one-place prime idèle is prime to every modulus whose
finite support omits that prime.  Its fractional ideal is the
corresponding prime ideal, so the idelic and ideal-theoretic ray-class
constructions use exactly the same prime representative.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

universe u

private theorem rayClassPrimeIdeleClassGroupIsMulCommutative
    (F : Type u) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] rayClassPrimeIdeleClassGroupIsMulCommutative

section GenericPrimeIdele

variable {K : Type u} [Field K] [NumberField K]

/-- A normalized one-place prime idèle is prime to a modulus whenever
the supporting prime does not occur in the modulus. -/
theorem finitePrimeIdele_mem_idelePrimeToModulusSubgroup
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    finitePrimeIdele v ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  constructor
  · change
      1 ∈
        m.infiniteCongruenceSubgroup
    exact
      m.infiniteCongruenceSubgroup.one_mem
  · intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    change
      IdeleGroup.finiteComponent w
          (finitePrimeIdele v) ∈
        RayClass.localHigherUnitGroup w (m.finitePart w)
    rw [finitePrimeIdele,
      IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
        v w (FiniteIdeleGroup.chosenLocalOrderSection v 1) hwv]
    exact
      (RayClass.localHigherUnitGroup w (m.finitePart w)).one_mem

/-- The fractional-ideal image of a normalized one-place prime idèle,
viewed as prime to a modulus, is the corresponding prime-to-modulus
prime ideal. -/
@[simp]
theorem primeToIdealMap_finitePrimeIdele
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    RayClass.primeToIdealMap m
        ⟨finitePrimeIdele v,
          finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩ =
      RayClass.primeToModulusIdeal m v hv := by
  apply Subtype.ext
  exact
    fractionalIdeal_finitePrimeIdele v

/-- The ideal-ray projection of a normalized one-place prime idèle is
the ideal ray class of the corresponding prime ideal. -/
@[simp]
theorem idealRayProjection_finitePrimeIdele
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    RayClass.idealRayProjection m
        ⟨finitePrimeIdele v,
          finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩ =
      QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup m)
        (RayClass.primeToModulusIdeal m v hv) := by
  rw [RayClass.idealRayProjection,
    MonoidHom.comp_apply,
    primeToIdealMap_finitePrimeIdele]

/-- The idèle-class/full-idèle ray-class equivalence evaluates on a
double quotient representative by forgetting the intermediate
principal-idèle quotient. -/
theorem rayClassGroupEquivIdeleQuotient_mk_mk
    (m : RayClass.Modulus K)
    (a : IdeleGroup K) :
    RayClass.rayClassGroupEquivIdeleQuotient m
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.Modulus.ideleCongruenceSubgroup m ⊔
          IdeleGroup.principalSubgroup K) a := by
  exact
    QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
      (IdeleGroup.principalSubgroup K)
      (RayClass.Modulus.ideleCongruenceSubgroup m ⊔
        IdeleGroup.principalSubgroup K)
      le_sup_right a

/-- The canonical idelic-to-ideal ray-class equivalence sends a
prime-to-modulus idèle class to the ideal ray class of its fractional
ideal. -/
theorem rayClassGroupEquivIdealRayClassGroup_mk_primeTo
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    RayClass.rayClassGroupEquivIdealRayClassGroup m
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K))) =
      RayClass.idealRayProjection m a := by
  change
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        ((RayClass.quotientRaySubgroupEquivIdeleRayQuotient m).symm
          (RayClass.rayClassGroupEquivIdeleQuotient m
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup m)
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K)
                (a : IdeleGroup K))))) =
      RayClass.idealRayProjection m a
  rw [rayClassGroupEquivIdeleQuotient_mk_mk]
  change
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        ((RayClass.quotientRaySubgroupEquivIdeleRayQuotient m).symm
          (RayClass.primeToRayClassProjection m a)) =
      RayClass.idealRayProjection m a
  rw [← RayClass.quotientRaySubgroupEquivIdeleRayQuotient_mk m a,
    MulEquiv.symm_apply_apply,
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk]

end GenericPrimeIdele

variable {K : Type} [Field K] [NumberField K]

/-- The ideal Artin map of the fractional ideal attached to a
prime-to-modulus idèle is its direct class in the idèle-class
quotient.  This is the commuting square between the idelic and
ideal-theoretic ray-class constructions. -/
theorem idealArtinMap_primeToIdealMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    IdealClassFieldTheory.idealArtinMap m N hm
        (RayClass.primeToIdealMap m a) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K)) := by
  let e :=
    RayClass.rayClassGroupEquivIdealRayClassGroup m
  let c : RayClass.RayClassGroup m :=
    QuotientGroup.mk'
      (RayClass.Modulus.congruenceSubgroup m)
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (a : IdeleGroup K))
  have he :
      e c = RayClass.idealRayProjection m a := by
    exact rayClassGroupEquivIdealRayClassGroup_mk_primeTo m a
  have he' :
      e.symm (RayClass.idealRayProjection m a) = c := by
    rw [← he, e.symm_apply_apply]
  change
    IdealClassFieldTheory.rayClassToNormQuotient m N hm
        (e.symm (RayClass.idealRayProjection m a)) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K))
  rw [he', IdealClassFieldTheory.rayClassToNormQuotient_mk]

/-- Outside a defining modulus, the ideal-theoretic Frobenius class is
the quotient class of the normalized one-place prime idèle. -/
@[simp]
theorem idealFrobeniusClass_eq_finitePrimeIdeleClass
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    IdealClassFieldTheory.idealFrobeniusClass
        m N hm v hv =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v)) := by
  rw [IdealClassFieldTheory.idealFrobeniusClass,
    ← primeToIdealMap_finitePrimeIdele m v hv,
    idealArtinMap_primeToIdealMap]

/-- The ideal Artin Frobenius class for the big Hilbert norm subgroup is
the canonical big-Hilbert Frobenius class. -/
theorem bigHilbertIdealFrobeniusClass_eq_bigHilbertFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdealClassFieldTheory.idealFrobeniusClass
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K))
        (bigHilbertClassFieldNormSubgroup (K := K))
        (bigHilbertClassFieldNormSubgroup_isDefiningModulus
          (K := K))
        v (by simp) =
      bigHilbertFrobeniusClass v := by
  have hm :
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)).congruenceSubgroup ≤
          bigHilbertClassFieldNormSubgroup (K := K) := by
    simpa only [IsDefiningModulus] using
      (bigHilbertClassFieldNormSubgroup_isDefiningModulus (K := K))
  rw [idealFrobeniusClass_eq_finitePrimeIdeleClass (hm := hm)]
  apply
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).injective
  simpa only [bigHilbertFrobeniusClass, MulEquiv.apply_symm_apply] using
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
      (K := K) (finitePrimeIdele v))

/-- The order of the big-Hilbert ideal Artin Frobenius is the order of
the corresponding narrow ideal class. -/
theorem orderOf_bigHilbertIdealFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (IdealClassFieldTheory.idealFrobeniusClass
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K))
          (bigHilbertClassFieldNormSubgroup (K := K))
          (bigHilbertClassFieldNormSubgroup_isDefiningModulus
            (K := K))
          v (by simp)) =
      orderOf
        (QuotientGroup.mk'
          (RayClass.narrowDenominator (K := K))
          (finitePrimeIdele v)) := by
  rw [bigHilbertIdealFrobeniusClass_eq_bigHilbertFrobeniusClass]
  exact
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.orderOf_eq
        (QuotientGroup.mk'
          (RayClass.narrowDenominator (K := K))
          (finitePrimeIdele v))

/-- The big-Hilbert ideal Artin Frobenius is trivial exactly when its
prime ideal has a totally positive generator. -/
theorem
    bigHilbertIdealFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator
    (v : HeightOneSpectrum (𝓞 K)) :
    IdealClassFieldTheory.idealFrobeniusClass
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K))
        (bigHilbertClassFieldNormSubgroup (K := K))
        (bigHilbertClassFieldNormSubgroup_isDefiningModulus
          (K := K))
        v (by simp) =
        1 ↔
      ∃ x : Kˣ,
        IdeleGroup.principalIdele K x ∈
            RayClass.idelePrimeToModulusSubgroup
              (RayClass.Modulus.narrowOfFinite
                (0 : RayClass.FiniteModulus K)) ∧
          toPrincipalIdeal (𝓞 K) K x =
            FractionalIdealGroup.prime v := by
  rw [
    bigHilbertIdealFrobeniusClass_eq_bigHilbertFrobeniusClass,
    bigHilbertFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator]

/-- The ideal Artin Frobenius class for the small Hilbert norm subgroup
is the canonical small-Hilbert Frobenius class. -/
theorem smallHilbertIdealFrobeniusClass_eq_smallHilbertFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdealClassFieldTheory.idealFrobeniusClass
        (0 : RayClass.Modulus K)
        (smallHilbertClassFieldNormSubgroup (K := K))
        (smallHilbertClassFieldNormSubgroup_isDefiningModulus
          (K := K))
        v (by simp) =
      IdealClassFieldTheory.smallHilbertFrobeniusClass v := by
  have hm :
      (0 : RayClass.Modulus K).congruenceSubgroup ≤
        smallHilbertClassFieldNormSubgroup (K := K) := by
    simpa only [IsDefiningModulus] using
      (smallHilbertClassFieldNormSubgroup_isDefiningModulus (K := K))
  rw [idealFrobeniusClass_eq_finitePrimeIdeleClass (hm := hm)]
  apply
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).injective
  simpa only [IdealClassFieldTheory.smallHilbertFrobeniusClass,
    MulEquiv.apply_symm_apply,
    smallHilbertClassFieldQuotientEquivClassGroup_mk] using
      IdeleGroup.idealClass_finitePrimeIdele v

/-- The order of the small-Hilbert ideal Artin Frobenius is the order of
the corresponding ordinary ideal class. -/
theorem orderOf_smallHilbertIdealFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (IdealClassFieldTheory.idealFrobeniusClass
          (0 : RayClass.Modulus K)
          (smallHilbertClassFieldNormSubgroup (K := K))
          (smallHilbertClassFieldNormSubgroup_isDefiningModulus
            (K := K))
          v (by simp)) =
      orderOf
        (ClassGroup.mk K
          (FractionalIdealGroup.prime v)) := by
  rw [smallHilbertIdealFrobeniusClass_eq_smallHilbertFrobeniusClass]
  exact
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.orderOf_eq
        (ClassGroup.mk K
          (FractionalIdealGroup.prime v))

/-- The small-Hilbert ideal Artin Frobenius is trivial exactly when its
prime ideal is principal. -/
theorem smallHilbertIdealFrobeniusClass_eq_one_iff_principal
    (v : HeightOneSpectrum (𝓞 K)) :
    IdealClassFieldTheory.idealFrobeniusClass
        (0 : RayClass.Modulus K)
        (smallHilbertClassFieldNormSubgroup (K := K))
        (smallHilbertClassFieldNormSubgroup_isDefiningModulus
          (K := K))
        v (by simp) =
        1 ↔
      FractionalIdealGroup.prime v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  rw [smallHilbertIdealFrobeniusClass_eq_smallHilbertFrobeniusClass]
  exact
    IdealClassFieldTheory.splitsCompletelyInSmallHilbertClassField_iff_principal v

end GlobalClassFields
end GlobalClassFieldTheory

/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorRayClassMaximality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
/-!
# Prime Artin classes at an exact narrow finite conductor

For a conductorial idèle-class subgroup `H`, a normalized one-place prime
idèle determines compatible classes in the ray class group at
`H.narrowFiniteConductor`, in `C_K / H`, and—away from that finite
conductor—in the ideal Artin quotient.  This file proves their
compatibility, order relations, and maximal ray-class criteria.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable {K : Type} [Field K] [NumberField K]

-- Keep quotient witnesses definitionally aligned with the imported
-- ideal-Artin construction and avoid repeating generic normality search.
attribute [local instance]
  IdealClassFieldTheory.ideleClassSubgroupNormal

/-- The class of a normalized one-place prime idèle in an arbitrary
idèle-class quotient. -/
def subgroupQuotientPrimeClass
    (H : Subgroup (IdeleClassGroup K))
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸ H :=
  QuotientGroup.mk' H
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

namespace ConductorialSubgroup

/-- The ray class of a normalized one-place prime idèle at the exact
narrow finite conductor of `H`. -/
def narrowFiniteConductorRayPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) :=
  QuotientGroup.mk'
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor))
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- The exact narrow finite conductor ray-class map sends the ray prime
class to the corresponding class in `C_K / H`. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupToQuotient_rayPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorRayClassGroupToQuotient
        (H.narrowFiniteConductorRayPrimeClass v) =
      subgroupQuotientPrimeClass H.1 v :=
  rfl

/-- Under maximal exact narrow finite conductor cardinality, the canonical
ray-class equivalence sends the ray prime class to its class in `C_K / H`.
-/
@[simp]
theorem narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_rayPrimeClass
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
        hcard
        (H.narrowFiniteConductorRayPrimeClass v) =
      subgroupQuotientPrimeClass H.1 v :=
  rfl

/-- Away from the exact narrow finite conductor of `H`, the ideal Artin
Frobenius class equals the normalized prime idèle class in `C_K / H`. -/
theorem narrowFiniteConductorIdealFrobeniusClass_eq_quotientPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ H.narrowFiniteConductor.support) :
    IdealClassFieldTheory.idealFrobeniusClass
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) H.1
        H.narrowFiniteConductor_isDefiningModulus
        v hv =
      subgroupQuotientPrimeClass H.1 v := by
  let m : RayClass.Modulus K :=
    RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor
  let hm : RayClass.Modulus.congruenceSubgroup m ≤ H.1 :=
    H.narrowFiniteConductor_isDefiningModulus
  let a : RayClass.idelePrimeToModulusSubgroup m :=
    ⟨finitePrimeIdele v,
      finitePrimeIdele_mem_idelePrimeToModulusSubgroup
        m v hv⟩
  have hIdeal :
      RayClass.primeToIdealMap m a =
        RayClass.primeToModulusIdeal m v hv :=
    primeToIdealMap_finitePrimeIdele m v hv
  have hArtin :
      IdealClassFieldTheory.idealArtinMap m H.1 hm
          (RayClass.primeToIdealMap m a) =
        QuotientGroup.mk' H.1
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K)) :=
    idealArtinMap_primeToIdealMap m H.1 hm a
  change
    IdealClassFieldTheory.idealArtinMap m H.1 hm
        (RayClass.primeToModulusIdeal m v hv) =
      QuotientGroup.mk' H.1
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v))
  calc
    _ = IdealClassFieldTheory.idealArtinMap m H.1 hm
          (RayClass.primeToIdealMap m a) :=
      congrArg
        (IdealClassFieldTheory.idealArtinMap m H.1 hm)
        hIdeal.symm
    _ = QuotientGroup.mk' H.1
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K)) := hArtin
    _ = QuotientGroup.mk' H.1
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (finitePrimeIdele v)) := rfl

/-- Triviality of the prime class in `C_K / H` is equivalent to
membership of its prime ideal in the ideal Artin kernel. -/
theorem subgroupQuotientPrimeClass_eq_one_iff_primeIdeal_mem_idealArtinKernel
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ H.narrowFiniteConductor.support) :
    subgroupQuotientPrimeClass H.1 v = 1 ↔
      RayClass.primeToModulusIdeal
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)
          v hv ∈
        IdealClassFieldTheory.idealArtinKernel
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) H.1
          H.narrowFiniteConductor_isDefiningModulus := by
  rw [← H.narrowFiniteConductorIdealFrobeniusClass_eq_quotientPrimeClass v hv]
  rfl

/-- The order of the prime class in `C_K / H` is the order of its prime
ideal modulo the ideal Artin kernel. -/
theorem orderOf_subgroupQuotientPrimeClass_eq_orderOf_idealArtinPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ H.narrowFiniteConductor.support) :
    orderOf (subgroupQuotientPrimeClass H.1 v) =
      orderOf
        (QuotientGroup.mk'
          (IdealClassFieldTheory.idealArtinKernel
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) H.1
            H.narrowFiniteConductor_isDefiningModulus)
          (RayClass.primeToModulusIdeal
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)
            v hv)) := by
  rw [← H.narrowFiniteConductorIdealFrobeniusClass_eq_quotientPrimeClass v hv]
  exact
    IdealClassFieldTheory.orderOf_idealFrobeniusClass
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) H.1
      H.narrowFiniteConductor_isDefiningModulus
      v hv

/-- The order of the prime class in `C_K / H` divides the order of its
lift to the exact narrow finite conductor ray class group. -/
theorem orderOf_subgroupQuotientPrimeClass_dvd_orderOf_narrowFiniteConductorRayPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf (subgroupQuotientPrimeClass H.1 v) ∣
      orderOf (H.narrowFiniteConductorRayPrimeClass v) := by
  rw [← H.narrowFiniteConductorRayClassGroupToQuotient_rayPrimeClass v]
  exact
    orderOf_map_dvd H.narrowFiniteConductorRayClassGroupToQuotient
      (H.narrowFiniteConductorRayPrimeClass v)

/-- Under maximal exact narrow finite conductor ray-class cardinality,
triviality of the ray prime class is equivalent to triviality of its class
in `C_K / H`. -/
theorem narrowFiniteConductorRayPrimeClass_eq_one_iff_quotientPrimeClass_eq_one
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorRayPrimeClass v = 1 ↔
      subgroupQuotientPrimeClass H.1 v = 1 := by
  let f := H.narrowFiniteConductorRayClassGroupToQuotient
  have hfInjective : Function.Injective f :=
    H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
      hcard
  constructor
  · intro hprime
    calc
      subgroupQuotientPrimeClass H.1 v =
          f (H.narrowFiniteConductorRayPrimeClass v) := by
        rw [H.narrowFiniteConductorRayClassGroupToQuotient_rayPrimeClass]
      _ = f 1 := congrArg f hprime
      _ = 1 := map_one f
  · intro hquotient
    apply hfInjective
    rw [H.narrowFiniteConductorRayClassGroupToQuotient_rayPrimeClass,
      hquotient, map_one]

/-- Under maximal exact narrow finite conductor ray-class cardinality, the
ray prime class and its image in `C_K / H` have the same order. -/
theorem orderOf_narrowFiniteConductorRayPrimeClass_eq_orderOf_quotientPrimeClass
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf (H.narrowFiniteConductorRayPrimeClass v) =
      orderOf (subgroupQuotientPrimeClass H.1 v) := by
  let f := H.narrowFiniteConductorRayClassGroupToQuotient
  have hfInjective : Function.Injective f :=
    H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
      hcard
  have horder :=
    orderOf_injective f hfInjective
      (H.narrowFiniteConductorRayPrimeClass v)
  rw [H.narrowFiniteConductorRayClassGroupToQuotient_rayPrimeClass v] at horder
  exact horder.symm

/-- Under maximal exact narrow finite conductor ray-class cardinality,
triviality of the ray prime class is equivalent to membership of the
corresponding prime ideal in the ideal Artin kernel. -/
theorem narrowFiniteConductorRayPrimeClass_eq_one_iff_primeIdeal_mem_idealArtinKernel
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ H.narrowFiniteConductor.support) :
    H.narrowFiniteConductorRayPrimeClass v = 1 ↔
      RayClass.primeToModulusIdeal
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)
          v hv ∈
        IdealClassFieldTheory.idealArtinKernel
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) H.1
          H.narrowFiniteConductor_isDefiningModulus := by
  rw [H.narrowFiniteConductorRayPrimeClass_eq_one_iff_quotientPrimeClass_eq_one
      hcard v,
    H.subgroupQuotientPrimeClass_eq_one_iff_primeIdeal_mem_idealArtinKernel v hv]

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory

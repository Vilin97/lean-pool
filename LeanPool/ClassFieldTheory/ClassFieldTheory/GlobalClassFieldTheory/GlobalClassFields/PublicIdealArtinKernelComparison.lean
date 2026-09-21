/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap
/-!
# Comparing the public and ideal-theoretic Artin kernels

The public finite ray-class Artin map is normalized on all primes away from
its modulus.  Frobenius rigidity identifies its kernel with the genuine
idèle-class norm kernel.  We then compare that kernel with the established
ideal-theoretic Artin map on the same ray modulus.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

private theorem finiteAbelianReciprocity_primeArtin_eq_original
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ D.modulus.finitePart.support) :
    D.artin (rayClassOfFinitePrime D.modulus v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v := by
  let w₀ := _root_.chosenFinitePlaceExtension (L := L) v
  let w := _root_.finitePlaceExtensionCentre (K := K) (L := L) v w₀
  have hw : w.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w₀
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (D.unramifiedOutsideModulus.1 v hv) w.asIdeal inferInstance hw
  calc
    D.artin (rayClassOfFinitePrime D.modulus v hv) =
        arithmeticFrobeniusAt (K := K) w :=
      D.artin_frobenius v hv w hw
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v :=
      (arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := L) v w hw hunram).symm

private theorem finiteAbelianReciprocity_originalPrimeNormalization
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    let m := rayClassModulusToOriginal K D.modulus
    let e := rayClassGroupEquivOriginalIdele K D.modulus
    let a : RayClass.RayClassGroup m →* (L ≃ₐ[K] L) :=
      D.artin.comp e.symm.toMonoidHom
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (_hv : v ∉ m.finitePart.support),
      a (QuotientGroup.mk' m.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v))) =
        GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v := by
  intro m e a v hv
  have hvm : v ∉ D.modulus.finitePart.support := hv
  change D.artin (e.symm (QuotientGroup.mk' m.congruenceSubgroup
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.finitePrimeIdele v)))) = _
  rw [← rayClassGroupEquivOriginalIdele_prime K D.modulus v hvm]
  simpa only [e, MulEquiv.symm_apply_apply] using
    finiteAbelianReciprocity_primeArtin_eq_original K L D v hvm

/-- The modulus of public finite abelian reciprocity data defines the
extension's genuine idèle-class norm subgroup.  This follows from prime
normalization, rather than being an additional field of the data. -/
theorem finiteAbelianReciprocity_modulus_isDefining
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    (rayClassModulusToOriginal K D.modulus).congruenceSubgroup ≤
      (_root_.ideleClassNorm K L).range := by
  let m := rayClassModulusToOriginal K D.modulus
  let e := rayClassGroupEquivOriginalIdele K D.modulus
  let a : RayClass.RayClassGroup m →* (L ≃ₐ[K] L) :=
    D.artin.comp e.symm.toMonoidHom
  have hprime := finiteAbelianReciprocity_originalPrimeNormalization K L D
  have hnorm :=
    GlobalClassFieldTheory.GlobalClassFields.rayModulus_normSubgroup_eq_artinKer_preimage
      m a hprime
  intro x hx
  rw [hnorm]
  change a (QuotientGroup.mk' m.congruenceSubgroup x) = 1
  have hmk : QuotientGroup.mk' m.congruenceSubgroup x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  rw [hmk, map_one]

/-- On a fractional ideal prime to the modulus, the public Artin map is
trivial exactly when the original ideal Artin map is trivial. -/
theorem publicArtinKer_iff_idealArtinKernel
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (I : rayClassPrimeToIdeals D.modulus) :
    (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) ∈
        D.artin.ker ↔
      I ∈ GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinKernel
        (rayClassModulusToOriginal K D.modulus)
        (_root_.ideleClassNorm K L).range
        (finiteAbelianReciprocity_modulus_isDefining K L D) := by
  let : IsMulCommutative (IdeleClassGroup K) :=
    ⟨⟨fun x y => mul_comm x y⟩⟩
  let : ((_root_.ideleClassNorm K L).range).Normal :=
    Subgroup.normal_of_isMulCommutative _
  let m := rayClassModulusToOriginal K D.modulus
  let G := RayClass.primeToModulusIdeals m
  let hComm : IsMulCommutative G :=
    IsMulCommutative.of_comm (fun x y => Subtype.ext (mul_comm x.1 y.1))
  let M : Subgroup G := rayPrincipalIdealSubgroupInPrimeTo D.modulus
  let N : Subgroup G := RayClass.principalRayIdealSubgroup m
  let hMN : M = N := rayPrincipalIdealSubgroup_eq K D.modulus
  let hM : M.Normal :=
    @Subgroup.normal_of_isMulCommutative G _ hComm M
  let hN : N.Normal :=
    @Subgroup.normal_of_isMulCommutative G _ hComm N
  let e := rayClassGroupEquivOriginalIdele K D.modulus
  let a : RayClass.RayClassGroup m →* (L ≃ₐ[K] L) :=
    D.artin.comp e.symm.toMonoidHom
  have hprime := finiteAbelianReciprocity_originalPrimeNormalization K L D
  have hnorm :=
    GlobalClassFieldTheory.GlobalClassFields.rayModulus_normSubgroup_eq_artinKer_preimage
      m a hprime
  let q : RayClass.RayClassGroup m :=
    (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm
      (QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup m) I)
  have he : e (QuotientGroup.mk'
      (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) = q := by
    change (rayClassGroupEquivOriginal K D.modulus).trans
      (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm
        (QuotientGroup.mk'
          (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) = q
    rw [MulEquiv.trans_apply]
    change (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm
      ((rayClassGroupEquivOriginal K D.modulus)
        (QuotientGroup.mk'
          (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I)) = q
    have hideal : (rayClassGroupEquivOriginal K D.modulus)
        (QuotientGroup.mk'
          (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) =
        QuotientGroup.mk'
          (RayClass.principalRayIdealSubgroup m) I := by
      change (@QuotientGroup.quotientMulEquivOfEq G _ M N
        hM hN hMN) (QuotientGroup.mk' M I) =
          QuotientGroup.mk' N I
      rfl
    rw [hideal]
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective m.congruenceSubgroup q
  have hArtin : D.artin (QuotientGroup.mk'
      (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) = 1 ↔
      x ∈ (_root_.ideleClassNorm K L).range := by
    rw [hnorm]
    change _ ↔ a (QuotientGroup.mk' m.congruenceSubgroup x) = 1
    rw [hx, ← he]
    change _ ↔ D.artin
      (e.symm (e (QuotientGroup.mk'
        (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I))) = 1
    rw [e.symm_apply_apply]
  have hIdealArtin :
      GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinMap m
        (_root_.ideleClassNorm K L).range
        (finiteAbelianReciprocity_modulus_isDefining K L D) I =
      QuotientGroup.mk' (_root_.ideleClassNorm K L).range x := by
    change GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient
      m (_root_.ideleClassNorm K L).range
      (finiteAbelianReciprocity_modulus_isDefining K L D) q = _
    rw [← hx]
    rfl
  change D.artin (QuotientGroup.mk'
      (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) = 1 ↔
    GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinMap m
      (_root_.ideleClassNorm K L).range
      (finiteAbelianReciprocity_modulus_isDefining K L D) I = 1
  rw [hIdealArtin]
  exact hArtin.trans (QuotientGroup.eq_one_iff x).symm

end ClassFieldTheory.GlobalClassFieldComparison

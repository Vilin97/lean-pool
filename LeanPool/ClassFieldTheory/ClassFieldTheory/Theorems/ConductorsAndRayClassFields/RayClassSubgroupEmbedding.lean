/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupHomExtFinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
/-!
# Antitone class fields of ray-class subgroups

For a fixed modulus, inclusion of ray-class subgroups reverses inclusion of
their finite abelian class fields.  The embedding between arbitrary
Frobenius-normalized realizations intertwines both Artin actions.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

private theorem subgroupArtin_prime_eq_arithmeticPrimeArtin
    {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {H : Subgroup (RayClassGroup m)}
    (R : RayClassSubgroupRealization K m H)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    R.artin (rayClassOfFinitePrime m v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := R.extension) v := by
  let w₀ := _root_.chosenFinitePlaceExtension (L := R.extension) v
  let w := _root_.finitePlaceExtensionCentre (K := K) (L := R.extension) v w₀
  have hw : w.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := R.extension) v w₀
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (R.unramifiedOutsideModulus.1 v hv) w.asIdeal inferInstance hw
  calc
    R.artin (rayClassOfFinitePrime m v hv) =
        arithmeticFrobeniusAt (K := K) w := R.artin_frobenius v hv w hw
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v :=
      (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := R.extension) v w hw hunram).symm

private theorem subgroupRealization_mem_norm_range_iff
    {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {H : Subgroup (RayClassGroup m)}
    (R : RayClassSubgroupRealization K m H)
    (x : IdeleClassGroup K) :
    x ∈ (_root_.ideleClassNorm K R.extension).range ↔
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (QuotientGroup.mk'
          (GlobalClassFieldComparison.rayClassModulusToOriginal K m).congruenceSubgroup
          x) ∈ H := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
  let a : RayClass.RayClassGroup m' →* (R.extension ≃ₐ[K] R.extension) :=
    R.artin.comp e.symm.toMonoidHom
  have hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m'.finitePart.support),
      a (QuotientGroup.mk' m'.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v))) =
        GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v := by
    intro v hv
    have hvm : v ∉ m.finitePart.support := hv
    change R.artin (e.symm (QuotientGroup.mk' m'.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v)))) = _
    rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
      K m v hvm]
    simpa only [e, MulEquiv.symm_apply_apply] using
      subgroupArtin_prime_eq_arithmeticPrimeArtin R v hvm
  have hnorm :=
    GlobalClassFieldTheory.GlobalClassFields.rayModulus_normSubgroup_eq_artinKer_preimage
      m' a hprime
  rw [hnorm]
  change a (QuotientGroup.mk' m'.congruenceSubgroup x) = 1 ↔ _
  change R.artin (e.symm (QuotientGroup.mk' m'.congruenceSubgroup x)) = 1 ↔ _
  rw [← MonoidHom.mem_ker, R.artin_ker]

private theorem arithmeticPrimeArtin_restrict_tower
    {K E L : Type}
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Field L] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    AlgEquiv.restrictNormalHom E
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := E) v := by
  open GlobalClassFieldTheory.GlobalClassFields in
  rw [arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := L) v,
    arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := E) v, map_inv]
  simpa only [GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin,
    MonoidHom.comp_apply] using
    congrArg Inv.inv
      (DFunLike.congr_fun
        (GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E))
        (IdeleGroup.finitePrimeIdele v))

/-- If `H ≤ J`, every Frobenius-normalized realization of the class field
of `J` embeds into every such realization for `H`; the embedding commutes
with their Artin actions. -/
theorem exists_rayClassSubgroupEmbedding_artinNaturality
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K)
    {H J : Subgroup (RayClassGroup m)} (hHJ : H ≤ J)
    (RH : RayClassSubgroupRealization K m H)
    (RJ : RayClassSubgroupRealization K m J) :
    ∃ f : RJ.extension →ₐ[K] RH.extension,
      ∀ (x : RayClassGroup m) (y : RJ.extension),
        RH.artin x (f y) = f (RJ.artin x y) := by
  have hnorm : (_root_.ideleClassNorm K RH.extension).range ≤
      (_root_.ideleClassNorm K RJ.extension).range := by
    intro c hc
    apply (subgroupRealization_mem_norm_range_iff RJ c).2
    exact hHJ ((subgroupRealization_mem_norm_range_iff RH c).1 hc)
  obtain ⟨f⟩ :=
    GlobalClassFieldTheory.GlobalClassFields.finiteAbelianExtension_nonempty_algHom_of_normRange_le
      (K := K) RJ.extension RH.extension hnorm
  let : Algebra RJ.extension RH.extension := f.toRingHom.toAlgebra
  let : IsScalarTower K RJ.extension RH.extension :=
    IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  let : CommGroup (RJ.extension ≃ₐ[K] RJ.extension) :=
    { (inferInstance : Group (RJ.extension ≃ₐ[K] RJ.extension)) with
      mul_comm := mul_comm' }
  have hnat :
      (AlgEquiv.restrictNormalHom RJ.extension).comp RH.artin = RJ.artin := by
    apply rayClassGroup_hom_ext_finitePrime K m
    intro v hv
    change AlgEquiv.restrictNormalHom RJ.extension
      (RH.artin (rayClassOfFinitePrime m v hv)) =
        RJ.artin (rayClassOfFinitePrime m v hv)
    rw [subgroupArtin_prime_eq_arithmeticPrimeArtin RH v hv,
      subgroupArtin_prime_eq_arithmeticPrimeArtin RJ v hv]
    exact arithmeticPrimeArtin_restrict_tower v
  refine ⟨f, ?_⟩
  intro x y
  have hx := DFunLike.congr_fun hnat x
  change AlgEquiv.restrictNormalHom RJ.extension (RH.artin x) = RJ.artin x at hx
  have hy := congrArg (fun σ : RJ.extension ≃ₐ[K] RJ.extension => f (σ y)) hx
  exact (AlgEquiv.restrictNormal_commutes (RH.artin x) RJ.extension y).symm.trans hy

end ClassFieldTheory

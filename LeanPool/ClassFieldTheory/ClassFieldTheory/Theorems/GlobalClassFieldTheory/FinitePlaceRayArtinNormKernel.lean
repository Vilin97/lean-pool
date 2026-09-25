/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
/-!
# The local kernel of a ray-class Artin map

The local-to-ray map is constructed from a one-place idèle class.  This
statement compares the kernel of the resulting ray-class Artin map with the
determinant norm of the entire local tensor algebra, at every finite place,
including places in the modulus.  It is a kernel comparison; the stronger
equality of the Artin values is a separate normalization question.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

open GlobalClassFieldTheory.Reciprocity renaming
  chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm →
    chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm in
/-- At every finite place, including a ramified place, the ray-class Artin
map has the local tensor-norm subgroup as its kernel after the canonical
one-place map into the ray class group. -/
theorem exists_finitePlaceRayArtin_normKernel
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus,
      (D.artin.comp ι).ker = finitePlaceTensorNormSubgroup K L v := by
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal K D.modulus
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K D.modulus
  let a : RayClass.RayClassGroup m →* (L ≃ₐ[K] L) :=
    D.artin.comp e.symm.toMonoidHom
  have hprime :
      ∀ (p : HeightOneSpectrum (𝓞 K))
        (_hp : p ∉ m.finitePart.support),
        a (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele p))) =
          GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := L) p := by
    intro p hp
    have hpD : p ∉ D.modulus.finitePart.support := hp
    change D.artin (e.symm (QuotientGroup.mk' m.congruenceSubgroup
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
        (IdeleGroup.finitePrimeIdele p)))) = _
    rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
      K D.modulus p hpD]
    have hFrob :
        D.artin (rayClassOfFinitePrime D.modulus p hpD) =
          GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := L) p := by
      let w₀ := _root_.chosenFinitePlaceExtension (L := L) p
      let w := _root_.finitePlaceExtensionCentre (K := K) (L := L) p w₀
      have hw : w.asIdeal.LiesOver p.asIdeal :=
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) p w₀
      have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
        (D.unramifiedOutsideModulus.1 p hpD) w.asIdeal inferInstance hw
      calc
        D.artin (rayClassOfFinitePrime D.modulus p hpD) =
            arithmeticFrobeniusAt (K := K) w :=
          D.artin_frobenius p hpD w hw
        _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
              (K := K) (L := L) p :=
          (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
            (K := K) (L := L) p w hw hunram).symm
    simpa only [e, MulEquiv.symm_apply_apply] using hFrob
  have hNorm :=
    GlobalClassFieldTheory.GlobalClassFields.rayModulus_normSubgroup_eq_artinKer_preimage
      m a hprime
  let ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' m.congruenceSubgroup).comp
        (IdeleGroup.finitePlaceIdeleClass v))
  refine ⟨ι, ?_⟩
  ext x
  change D.artin
      (e.symm (QuotientGroup.mk' m.congruenceSubgroup
        (IdeleGroup.finitePlaceIdeleClass v x))) = 1 ↔
    x ∈ finitePlaceTensorNormSubgroup K L v
  have hRay :
      D.artin
          (e.symm (QuotientGroup.mk' m.congruenceSubgroup
            (IdeleGroup.finitePlaceIdeleClass v x))) = 1 ↔
        IdeleGroup.finitePlaceIdeleClass v x ∈
          (_root_.ideleClassNorm K L).range := by
    rw [hNorm]
    change a (QuotientGroup.mk' m.congruenceSubgroup
      (IdeleGroup.finitePlaceIdeleClass v x)) = 1 ↔ _
    rfl
  have hLocal :
      IdeleGroup.finitePlaceIdeleClass v x ∈
          (_root_.ideleClassNorm K L).range ↔
        x ∈ finitePlaceTensorNormSubgroup K L v := by
    rw [← GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_ker]
    change GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v x) = 1 ↔ _
    have hcompat := DFunLike.congr_fun
      (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
        (K := K) (L := L) v) x
    rw [show GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v x) =
          GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v x from hcompat]
    rw [chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
      ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := L) v]
    change x ∈ (localTensorNorm (K := K) (L := L) v).range ↔
      x ∈ finitePlaceTensorNormSubgroup K L v
    rfl
  exact hRay.trans hLocal

end ClassFieldTheory

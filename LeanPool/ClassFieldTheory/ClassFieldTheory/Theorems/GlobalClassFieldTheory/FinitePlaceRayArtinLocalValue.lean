/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.ExtendingAbsoluteValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
/-!
# The finite-place ray Artin value diagram

The ray map comes from the one-place idèle class, while the local Artin map
comes from local reciprocity on the completed extension. The transport from
local automorphisms to the global Galois group is characterized on the dense
copy of `L`. Arithmetic ray values are inverse to the geometric local Artin
values under this transport.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- At every finite place, including those in the modulus, the
Frobenius-normalized ray Artin value equals the transported inverse of the
independently constructed local Artin value. The transport is injective and
has its standard action on the canonical copy of `L`; the local and ray
kernels are the actual local tensor-norm subgroup. -/
theorem exists_finitePlaceRayArtin_localValueDiagram
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    ∃ (w : ExtendingAbsoluteValue vK L)
      (halg : Algebra vK.Completion w.1.Completion),
      letI := halg
      ∃ (ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus)
        (localArtin : (v.adicCompletion K)ˣ →*
          (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion))
        (transport : (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) →*
          (L ≃ₐ[K] L)),
        Continuous localArtin ∧
        Function.Surjective localArtin ∧
        Function.Injective transport ∧
        (∀ γ : L ≃ₐ[K] L,
          (∃ σ, transport σ = γ) ↔
            ∀ y : L, w.1 (γ y) < 1 ↔ w.1 y < 1) ∧
        localArtin.ker = finitePlaceTensorNormSubgroup K L v ∧
        (D.artin.comp ι).ker = finitePlaceTensorNormSubgroup K L v ∧
        (∀ (σ : w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) (y : L),
          algebraMap L w.1.Completion ((transport σ) y) =
            σ (algebraMap L w.1.Completion y)) ∧
        ∀ x : (v.adicCompletion K)ˣ,
          D.artin (ι x) = (transport (localArtin x))⁻¹ := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let w : ExtendingAbsoluteValue vK L :=
    _root_.chosenFinitePlaceExtension (L := L) v
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let halg : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Algebra vK.Completion w.1.Completion := halg
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra v w
  let eC : E ≃ₐ[vK.Completion] w.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion vK hvK w
  let eAut : (E ≃ₐ[vK.Completion] E) ≃*
      (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) :=
    AlgEquiv.autCongr eC
  let localE : (v.adicCompletion K)ˣ →* (E ≃ₐ[vK.Completion] E) :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinMonoidHom v w
  let localArtin : (v.adicCompletion K)ˣ →*
      (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) :=
    eAut.toMonoidHom.comp localE
  let S := HilbertRamification.absoluteValueDecompositionGroup K w.1
  let eD : S ≃* (E ≃ₐ[vK.Completion] E) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let transport : (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) →*
      (L ≃ₐ[K] L) :=
    S.subtype.comp (eD.symm.toMonoidHom.comp eAut.symm.toMonoidHom)
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
      let w' := _root_.finitePlaceExtensionCentre (K := K) (L := L) p w₀
      have hw : w'.asIdeal.LiesOver p.asIdeal :=
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) p w₀
      have hunram : Algebra.IsUnramifiedAt (𝓞 K) w'.asIdeal :=
        (D.unramifiedOutsideModulus.1 p hpD) w'.asIdeal inferInstance hw
      calc
        D.artin (rayClassOfFinitePrime D.modulus p hpD) =
            arithmeticFrobeniusAt (K := K) w' :=
          D.artin_frobenius p hpD w' hw
        _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
              (K := K) (L := L) p :=
          (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
            (K := K) (L := L) p w' hw hunram).symm
    simpa only [e, MulEquiv.symm_apply_apply] using hFrob
  let ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' m.congruenceSubgroup).comp
        (IdeleGroup.finitePlaceIdeleClass v))
  have hvalue (x : (v.adicCompletion K)ˣ) :
      D.artin (ι x) =
        GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
          K L v x := by
    calc
      D.artin (ι x) =
          GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
            K L (IdeleGroup.finitePlaceIdeleClass v x) :=
        GlobalClassFieldTheory.GlobalClassFields.rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue
          m a hprime (IdeleGroup.finitePlaceIdeleClass v x)
      _ = GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
            K L v x := by
        exact DFunLike.congr_fun
          (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
            (K := K) (L := L) v) x
  have hfactor (x : (v.adicCompletion K)ˣ) :
      GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x = S.subtype (eD.symm (localE x)) := by
    change GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension
      (K := K) (L := L) v w x = _
    rw [GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor,
      MonoidHom.comp_apply]
    rfl
  have hLocalESurj : Function.Surjective localE := by
    intro τ
    let δ := eD.symm τ
    have hδ : (δ : L ≃ₐ[K] L) ∈
        (GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range := by
      rw [GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_range]
      exact δ.property
    obtain ⟨x, hx⟩ := hδ
    refine ⟨x, ?_⟩
    have hxD : eD.symm (localE x) = δ := by
      apply Subtype.coe_injective
      calc
        ((eD.symm (localE x) : S) : L ≃ₐ[K] L) =
            GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v x := (hfactor x).symm
        _ = (δ : L ≃ₐ[K] L) := hx
    change eD.symm (localE x) = eD.symm τ at hxD
    exact eD.symm.injective hxD
  have hTransportInj : Function.Injective transport := by
    intro σ τ hστ
    have hD : eD.symm (eAut.symm σ) = eD.symm (eAut.symm τ) := by
      apply Subtype.coe_injective
      exact hστ
    exact eAut.symm.injective (eD.symm.injective hD)
  have hTransportRange (γ : L ≃ₐ[K] L) :
      (∃ σ, transport σ = γ) ↔
        ∀ y : L, w.1 (γ y) < 1 ↔ w.1 y < 1 := by
    constructor
    · rintro ⟨σ, rfl⟩
      exact (eD.symm (eAut.symm σ)).property
    · intro hγ
      let δ : S := ⟨γ, hγ⟩
      refine ⟨eAut (eD δ), ?_⟩
      change S.subtype (eD.symm (eAut.symm (eAut (eD δ)))) = γ
      rw [eAut.symm_apply_apply, eD.symm_apply_apply]
      change (δ : L ≃ₐ[K] L) = γ
      rfl
  let j : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  have hemb (y : L) : eC (j y) = algebraMap L w.1.Completion y := by
    calc
      eC (j y) = ((j y : E) : w.1.Completion) :=
        AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe
          vK hvK w (j y)
      _ = AbsoluteValue.toCompletion w.1 y :=
        AbsoluteValue.toAlgebraicLocalization_apply vK w.1 w.2 y
      _ = algebraMap L w.1.Completion y :=
        AbsoluteValue.toCompletion_eq_algebraMap w.1 y
  have hTransportEval
      (σ : w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) (y : L) :
      algebraMap L w.1.Completion ((transport σ) y) =
        σ (algebraMap L w.1.Completion y) := by
    let δ : S := eD.symm (eAut.symm σ)
    have hloc : eD δ (j y) = j ((δ : L ≃ₐ[K] L) y) :=
      HilbertRamification.localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        vK hvK w δ y
    calc
      algebraMap L w.1.Completion ((transport σ) y) =
          eC (j ((δ : L ≃ₐ[K] L) y)) := by
        change algebraMap L w.1.Completion ((δ : L ≃ₐ[K] L) y) = _
        exact (hemb _).symm
      _ = eC (eD δ (j y)) := congrArg eC hloc.symm
      _ = σ (eC (j y)) := by
        have hδ : eD δ = eAut.symm σ :=
          eD.apply_symm_apply _
        rw [hδ]
        change eC (eC.symm (σ (eC (j y)))) = _
        exact eC.apply_symm_apply _
      _ = σ (algebraMap L w.1.Completion y) := congrArg σ (hemb y)
  have hDiagram (x : (v.adicCompletion K)ˣ) :
      D.artin (ι x) = (transport (localArtin x))⁻¹ := by
    calc
      D.artin (ι x) =
          GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
            K L v x := hvalue x
      _ = (GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v x)⁻¹ :=
        GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply
          K L v x
      _ = (transport (localArtin x))⁻¹ := by
        congr 1
  have hRayKer : (D.artin.comp ι).ker = finitePlaceTensorNormSubgroup K L v := by
    ext x
    change D.artin (ι x) = 1 ↔ x ∈ finitePlaceTensorNormSubgroup K L v
    rw [hvalue x,
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply,
      inv_eq_one,
      GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
      ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := L) v]
    rfl
  have hLocalKer : localArtin.ker = finitePlaceTensorNormSubgroup K L v := by
    ext x
    change localArtin x = 1 ↔ x ∈ finitePlaceTensorNormSubgroup K L v
    calc
      localArtin x = 1 ↔ transport (localArtin x) = 1 := by
        constructor
        · intro hx
          rw [hx, map_one]
        · intro hx
          apply hTransportInj
          simpa only [map_one] using hx
      _ ↔ D.artin (ι x) = 1 := by
        rw [hDiagram x, inv_eq_one]
      _ ↔ x ∈ finitePlaceTensorNormSubgroup K L v := by
        change x ∈ (D.artin.comp ι).ker ↔
          x ∈ finitePlaceTensorNormSubgroup K L v
        rw [hRayKer]
  have hLocalKerOpen : IsOpen (localArtin.ker : Set (v.adicCompletion K)ˣ) := by
    rw [hLocalKer]
    change IsOpen ((_root_.localTensorNorm (K := K) (L := L) v).range :
      Set (v.adicCompletion K)ˣ)
    rw [finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v]
    exact _root_.chosenFinitePlaceLocalNormSubgroup_isOpen
      (K := K) (L := L) v
  have hLocalContinuous : Continuous localArtin := by
    apply continuous_of_continuousAt_one localArtin
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hLocalKerOpen.mem_nhds (by simp)] with x hx
    change localArtin x = 1 at hx
    simpa only [map_one] using hx
  exact ⟨w, halg, ι, localArtin, transport,
    hLocalContinuous, eAut.surjective.comp hLocalESurj, hTransportInj,
    hTransportRange, hLocalKer, hRayKer, hTransportEval, hDiagram⟩

end ClassFieldTheory

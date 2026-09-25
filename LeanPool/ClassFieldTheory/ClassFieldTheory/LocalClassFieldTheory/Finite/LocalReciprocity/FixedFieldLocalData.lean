/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalHenselianValuation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport
/-!
# Canonical local data on finite fixed fields

This file compares the normalized valuation induced on a finite abstract
field by the local class formation with the ordinary normalized valuation
of its concrete fixed field.  The concrete field is equipped with the
canonical spectral extension of the topology on the original local field.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  hasExtension_valuation_of_valuationSubring_pullback →
    hasExtension_valuation_of_valuationSubring_pullback

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_pullback_of_hasExtension_valuation →
    valuationSubring_pullback_of_hasExtension_valuation


noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal Pointwise ValuativeRel
open ClassFormation LocalFieldTheory RamificationTheory CyclicCohomology
open RamificationTheory.HilbertRamification.ValuationSubring

private abbrev finiteFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K))) :
    Type :=
  abstractFixedField K (SeparableClosure K) H.field

/-- The separable closure of a finite fixed field is an algebra over that fixed field. -/
local instance finiteFixedFieldSeparableClosureAlgebra
    (K : Type) [Field K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K))) :
    Algebra (finiteFixedField K H)
      (SeparableClosure (finiteFixedField K H)) :=
  (separableClosure (finiteFixedField K H)
    (AlgebraicClosure (finiteFixedField K H))).algebra

@[reducible]
private def valuationSubringEquivOfComapEq
    {L M : Type} [Field L] [Field M]
    (A : ValuationSubring M) (B : ValuationSubring L)
    (e : L ≃+* M) (h : B = A.comap e.toRingHom) :
    B ≃+* A where
  toFun x := ⟨e x, by
    change (x : L) ∈ A.comap e.toRingHom
    rw [← h]
    exact x.property⟩
  invFun y := ⟨e.symm y, by
    rw [h]
    change e (e.symm y) ∈ A
    simp⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_add' x y := by
    ext
    simp

private theorem semilinearConjugate_commutes
    {k k' Omega Omega' : Type}
    [Field k] [Field k'] [Field Omega] [Field Omega']
    [Algebra k Omega] [Algebra k' Omega']
    (tau : k ≃+* k') (e : Omega ≃+* Omega')
    (he :
      ∀ x : k,
        e (algebraMap k Omega x) =
          algebraMap k' Omega' (tau x))
    (sigma : Omega ≃ₐ[k] Omega) (x : k') :
    e (sigma (e.symm (algebraMap k' Omega' x))) =
      algebraMap k' Omega' x := by
  have hpre :
      e.symm (algebraMap k' Omega' x) =
        algebraMap k Omega (tau.symm x) := by
    apply e.injective
    rw [e.apply_symm_apply, he, tau.apply_symm_apply]
  rw [hpre, sigma.commutes, he, tau.apply_symm_apply]

/-- On a finite fixed field, the normalized valuation induced by the local
class formation is the ordinary normalized local-field valuation. -/
theorem localHenselianValuation_valuationAt_abstractFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K)))
    (x : (abstractFixedField K (SeparableClosure K) H.field)ˣ) :
    letI : FiniteDimensional K
        (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (abstractFixedField K (SeparableClosure K) H.field) :=
      finiteExtensionSpectralNormedField K
        (abstractFixedField K (SeparableClosure K) H.field)
    letI : ValuativeRel
        (abstractFixedField K (SeparableClosure K) H.field) :=
      finiteExtensionSpectralValuativeRel K
        (abstractFixedField K (SeparableClosure K) H.field)
    letI : IsNonarchimedeanLocalField
        (abstractFixedField K (SeparableClosure K) H.field) :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K
        (abstractFixedField K (SeparableClosure K) H.field)
    ((((localHenselianValuation K).valuationAt H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field (Additive.ofMul x))) :
        (localHenselianValuation K).valueGroup) : ZHat) =
      Int.castRingHom ZHat
        (IsNonarchimedeanLocalField.valuationMap
          (abstractFixedField K (SeparableClosure K) H.field)
          (Additive.ofMul x)) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let hIntegralClosure : IsIntegralClosure 𝒪[F] 𝒪[K] F :=
    localCompleteDVF_integerRing_isIntegralClosure K F
  let a :=
    abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H.field (Additive.ofMul x)
  let f := Module.finrank 𝓀[K] 𝓀[F]
  let z :=
    Int.castRingHom ZHat
      (IsNonarchimedeanLocalField.valuationMap F (Additive.ofMul x))
  have hdegree :
      (H.residueDegree (localResidueDatum K) : ℕ) = f := by
    have hdegreeRaw :=
      localResidueDatum_residueDegree_eq_residueFinrank K H
    exact hdegreeRaw.trans (by
        apply Nat.pow_right_injective
          (Finite.one_lt_card : 2 ≤ Nat.card 𝓀[K])
        calc
          _ = Nat.card 𝓀[F] := by
            symm
            refine @Module.natCard_eq_pow_finrank 𝓀[K] 𝓀[F] _ _ ?_ ?_
            refine @Module.Finite.of_finite 𝓀[K] 𝓀[F] _ _ ?_ ?_
            infer_instance
          _ = Nat.card 𝓀[F] := rfl
          _ = _ := by
            dsimp only [f]
            refine @Module.natCard_eq_pow_finrank 𝓀[K] 𝓀[F] _ _ ?_ ?_
            refine @Module.Finite.of_finite 𝓀[K] 𝓀[F] _ _ ?_ ?_
            infer_instance)
  have hnorm :
      (localHenselianValuation K).normCompositeAt H a =
        f • z := by
    change localBaseValuation K
        (normToBase
          (galoisAmbientUnitsRep K (SeparableClosure K)) H.field a) =
      f • z
    rw [show a =
      abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H.field (Additive.ofMul x) from rfl]
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    change Int.castRingHom ZHat
        (IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul (normUnits K F x))) =
      f • Int.castRingHom ZHat
        (IsNonarchimedeanLocalField.valuationMap F
          (Additive.ofMul x))
    have hnormInt :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K F _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure x
    change IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul (normUnits K F x)) =
      (f : Int) *
        IsNonarchimedeanLocalField.valuationMap F
          (Additive.ofMul x) at hnormInt
    rw [hnormInt, ← map_nsmul]
    rfl
  have hnorm' :
      (localHenselianValuation K).normCompositeAt H a =
        (H.residueDegree (localResidueDatum K) : ℕ) • z := by
    rw [hdegree]
    exact hnorm
  rw [(localHenselianValuation K).valuationAt_coe]
  change zHatDivide (H.residueDegree (localResidueDatum K) : ℕ)
      (H.residueDegree (localResidueDatum K)).pos
      ((localHenselianValuation K).normCompositeAtInResidueImage H a) = z
  have hsub :
      (localHenselianValuation K).normCompositeAtInResidueImage H a =
        ⟨zHatMulNat (H.residueDegree (localResidueDatum K) : ℕ) z,
          ⟨z, rfl⟩⟩ := by
    apply Subtype.ext
    change (localHenselianValuation K).normCompositeAt H a =
      zHatMulNat (H.residueDegree (localResidueDatum K) : ℕ) z
    simpa only [zHatMulNat_apply] using hnorm'
  exact (congrArg (zHatDivide (H.residueDegree (localResidueDatum K) : ℕ)
      (H.residueDegree (localResidueDatum K)).pos) hsub).trans
    (zHatDivide_zHatMulNat (H.residueDegree (localResidueDatum K) : ℕ)
      (H.residueDegree (localResidueDatum K)).pos z)

/-- A separable-closure equivalence extending an embedding of a finite
separable local extension identifies the two uniquely extended local
valuation rings. -/
theorem localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap e.toRingHom := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e
  let A := localSeparableValuationSubring K
  let B := A.comap e.toRingHom
  have hcomap :
      A.comap i.toRingHom =
        (ValuativeRel.valuation F).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K F i
  have hBext :
      (localCompleteDVF F).valuation.HasExtension B.valuation := by
    apply
      hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change e (algebraMap F (SeparableClosure F) x) ∈ A ↔
      x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [e.commutes]
    change x ∈ A.comap i.toRingHom ↔
      x ∈ (ValuativeRel.valuation F).valuationSubring
    rw [hcomap]
  let : (localCompleteDVF F).valuation.HasExtension B.valuation :=
    hBext
  exact localSeparableValuationSubring_eq_of_hasExtension F B

/-- After identifying separable closures over a finite separable local
extension, the ambient selected valuation ring is stabilized by the whole
absolute Galois group of the extension field. -/
theorem localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      decompositionGroup F (localSeparableValuationSubring K) = ⊤ := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e
  let A := localSeparableValuationSubring K
  let AF := localSeparableValuationSubring F
  have hAF :
      AF = A.comap e.toRingHom :=
    localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
      K F i e
  have hAFtop :
      decompositionGroup F AF = ⊤ :=
    localSeparableDecompositionGroup_eq_top F
  apply top_unique
  intro sigma _hsigma
  let sigmaF : Gal(SeparableClosure F/F) :=
    AlgEquiv.autCongr e.symm sigma
  have hsigmaF :
      sigmaF • AF = AF := by
    have :
        sigmaF ∈ decompositionGroup F AF := by
      rw [hAFtop]
      trivial
    change sigmaF • AF = AF at this
    exact this
  change sigma • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hmem (z : SeparableClosure K) :
      e.symm z ∈ AF ↔ z ∈ A := by
    rw [hAF]
    change e (e.symm z) ∈ A ↔ z ∈ A
    rw [e.apply_symm_apply]
  rw [← hmem (sigma⁻¹ • x), ← hmem x]
  have hx :=
    congrArg
      (fun B : ValuationSubring (SeparableClosure F) =>
        e.symm x ∈ B)
      hsigmaF
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [sigmaF, AlgEquiv.autCongr_apply] using hx.to_iff

@[implicit_reducible]
private noncomputable def finiteExtensionDecompositionResidueFintype
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      Fintype (decompositionResidueField F
        (localSeparableValuationSubring K)) := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  letI : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  letI : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro _e
  let A := localSeparableValuationSubring K
  let C := (ValuativeRel.valuation F).valuationSubring
  have hcomap :
      A.comap (algebraMap F (SeparableClosure K)) = C := by
    change A.comap i.toRingHom =
      (ValuativeRel.valuation F).valuationSubring
    exact localSeparableValuationSubring_comap_embedding K F i
  have htop : decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F i _e
  let residueEquiv :
      IsLocalRing.ResidueField C ≃+*
        decompositionResidueField F A :=
    residueFieldEquivDecompositionResidueOfEqTop A C hcomap htop
  letI : Finite (IsLocalRing.ResidueField C) := by
    change Finite 𝓀[F]
    infer_instance
  letI : Fintype (IsLocalRing.ResidueField C) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _ residueEquiv.toEquiv

/-- The intrinsic residue degree of a finite separable local extension is
unchanged after moving its separable closure into the ambient separable
closure of the base field. -/
theorem
    localResidueDegree_eq_residueAbsoluteDegreeIn_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (sigma : Gal(SeparableClosure F/F)),
      letI : Fintype (decompositionResidueField F
          (localSeparableValuationSubring K)) :=
        finiteExtensionDecompositionResidueFintype K F i e
      localResidueDegree F sigma =
        residueAbsoluteDegreeIn
          (decompositionResidueField F
            (localSeparableValuationSubring K))
          (selectedResidueField
            (localSeparableValuationSubring K))
          (residueAlgActionOfEqTop F
            (localSeparableValuationSubring K)
            (localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
              K F i e)
            (AlgEquiv.autCongr e sigma)) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e sigma
  let : Fintype (decompositionResidueField F
      (localSeparableValuationSubring K)) :=
    finiteExtensionDecompositionResidueFintype K F i e
  let A := localSeparableValuationSubring K
  let AF := localSeparableValuationSubring F
  let C := (ValuativeRel.valuation F).valuationSubring
  let kF := IsLocalRing.ResidueField C
  let kA := decompositionResidueField F A
  let kAF := decompositionResidueField F AF
  let OmegaA := selectedResidueField A
  let OmegaF := selectedResidueField AF
  have hAcomap :
      A.comap (algebraMap F (SeparableClosure K)) = C := by
    change A.comap i.toRingHom =
      (ValuativeRel.valuation F).valuationSubring
    exact localSeparableValuationSubring_comap_embedding K F i
  have hAFcomap :
      AF.comap (algebraMap F (SeparableClosure F)) = C := by
    ext x
    exact localSeparableValuationSubring_pullback F x
  have hAtop :
      decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F i e
  have hAFtop :
      decompositionGroup F AF = ⊤ :=
    localSeparableDecompositionGroup_eq_top F
  let eA : kF ≃+* kA :=
    residueFieldEquivDecompositionResidueOfEqTop
      A C hAcomap hAtop
  let eAF : kF ≃+* kAF :=
    residueFieldEquivDecompositionResidueOfEqTop
      AF C hAFcomap hAFtop
  let tau : kAF ≃+* kA :=
    eAF.symm.trans eA
  have hAF :
      AF = A.comap e.toRingHom :=
    localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
      K F i e
  let r : AF ≃+* A :=
    valuationSubringEquivOfComapEq A AF e.toRingEquiv hAF
  let eResidue : OmegaF ≃+* OmegaA :=
    IsLocalRing.ResidueField.mapEquiv r
  have hr (x : AF) :
      ((r x : A) : SeparableClosure K) =
        e (x : SeparableClosure F) := by
    rfl
  have heResidue (x : kAF) :
      eResidue (algebraMap kAF OmegaF x) =
        algebraMap kA OmegaA (tau x) := by
    obtain ⟨y, rfl⟩ := eAF.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have htau :
        tau (eAF (IsLocalRing.residue C a)) =
          eA (IsLocalRing.residue C a) := by
      simp [tau]
    rw [htau]
    change IsLocalRing.ResidueField.map r
        (IsLocalRing.residue AF _) =
      algebraMap kA OmegaA
        (eA (IsLocalRing.residue C a))
    rw [IsLocalRing.ResidueField.map_residue,
      residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    congr 1
    apply Subtype.ext
    exact (hr _).trans (e.commutes (a : F))
  let rhoF : OmegaF ≃ₐ[kAF] OmegaF :=
    localSeparableResidueAlgAction F sigma
  let rhoA : OmegaA ≃ₐ[kA] OmegaA :=
    residueAlgActionOfEqTop F A hAtop
      (AlgEquiv.autCongr e sigma)
  let conjugate : OmegaA ≃ₐ[kA] OmegaA :=
    { eResidue.symm.trans (rhoF.toRingEquiv.trans eResidue) with
      commutes' := fun x => by
        change eResidue
            (rhoF (eResidue.symm (algebraMap kA OmegaA x))) =
          algebraMap kA OmegaA x
        have hpre :
            eResidue.symm (algebraMap kA OmegaA x) =
              algebraMap kAF OmegaF (tau.symm x) := by
          apply eResidue.injective
          rw [eResidue.apply_symm_apply, heResidue,
            tau.apply_symm_apply]
        rw [hpre, rhoF.commutes, heResidue,
          tau.apply_symm_apply] }
  have hconjugate : conjugate = rhoA := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eResidue.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change eResidue
        (rhoF (eResidue.symm
          (eResidue (IsLocalRing.residue AF a)))) =
      rhoA (eResidue (IsLocalRing.residue AF a))
    rw [eResidue.symm_apply_apply]
    change IsLocalRing.ResidueField.map r
        (residueAlgActionOfEqTop F AF hAFtop sigma
          (IsLocalRing.residue AF a)) =
      residueAlgActionOfEqTop F A hAtop
        (AlgEquiv.autCongr e sigma)
        (IsLocalRing.ResidueField.map r
          (IsLocalRing.residue AF a))
    dsimp only [residueAlgActionOfEqTop]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      decompositionGroupResidueAction_residue,
      IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      decompositionGroupResidueAction_residue]
    congr 1
    apply Subtype.ext
    change e (sigma (a : SeparableClosure F)) =
      AlgEquiv.autCongr e sigma (e (a : SeparableClosure F))
    simp [AlgEquiv.autCongr_apply]
  change residueAbsoluteDegreeIn kAF OmegaF rhoF =
    residueAbsoluteDegreeIn kA OmegaA rhoA
  rw [← hconjugate]
  exact
    (residueAbsoluteDegreeIn_semilinear_conjugation
      kAF OmegaF tau eResidue heResidue rhoF).symm

/-- Local residue degree is invariant under a semilinear equivalence of
local fields and separable closures that carries the selected extension
valuation ring to the selected extension valuation ring. -/
theorem localResidueDegree_semilinear_conjugation
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (phi : K ≃+* F)
    (e : SeparableClosure K ≃+* SeparableClosure F)
    (he : ∀ x : K,
      e (algebraMap K (SeparableClosure K) x) =
        algebraMap F (SeparableClosure F) (phi x))
    (hvaluation :
      localSeparableValuationSubring K =
        (localSeparableValuationSubring F).comap e.toRingHom)
    (sigma : Gal(SeparableClosure K/K)) :
    let sigmaF : Gal(SeparableClosure F/F) :=
      { e.symm.trans (sigma.toRingEquiv.trans e) with
        commutes' := fun x => by
          change e (sigma (e.symm
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          have hpre :
              e.symm (algebraMap F (SeparableClosure F) x) =
                algebraMap K (SeparableClosure K) (phi.symm x) := by
            apply e.injective
            rw [e.apply_symm_apply, he, phi.apply_symm_apply]
          rw [hpre, sigma.commutes, he, phi.apply_symm_apply] }
    localResidueDegree F sigmaF =
      localResidueDegree K sigma := by
  dsimp only
  let AK := localSeparableValuationSubring K
  let AF := localSeparableValuationSubring F
  let CK := (localCompleteDVF K).valuation.valuationSubring
  let CF := (localCompleteDVF F).valuation.valuationSubring
  let kK := IsLocalRing.ResidueField CK
  let kF := IsLocalRing.ResidueField CF
  let kAK := decompositionResidueField K AK
  let kAF := decompositionResidueField F AF
  let OmegaK := selectedResidueField AK
  let OmegaF := selectedResidueField AF
  have hbase (x : K) :
      x ∈ CK ↔ phi x ∈ CF := by
    change
      x ∈ (localCompleteDVF K).valuation.valuationSubring ↔
        phi x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [← localSeparableValuationSubring_pullback K x,
      ← localSeparableValuationSubring_pullback F (phi x)]
    rw [hvaluation]
    change
      e (algebraMap K (SeparableClosure K) x) ∈ AF ↔
        algebraMap F (SeparableClosure F) (phi x) ∈ AF
    rw [he]
  let rBase : CK ≃+* CF := {
    toFun := fun x =>
      ⟨phi (x : K), (hbase (x : K)).1 x.property⟩
    invFun := fun y =>
      ⟨phi.symm (y : F), (hbase (phi.symm (y : F))).2 (by
        simpa only [phi.apply_symm_apply] using y.property)⟩
    left_inv := fun x => by
      ext
      simp
    right_inv := fun y => by
      ext
      simp
    map_mul' := fun x y => by
      ext
      simp
    map_add' := fun x y => by
      ext
      simp }
  let eBaseResidue : kK ≃+* kF :=
    IsLocalRing.ResidueField.mapEquiv rBase
  let r : AK ≃+* AF :=
    valuationSubringEquivOfComapEq AF AK e hvaluation
  let eResidue : OmegaK ≃+* OmegaF :=
    IsLocalRing.ResidueField.mapEquiv r
  have hr (x : AK) :
      ((r x : AF) : SeparableClosure F) =
        e (x : SeparableClosure K) := by
    rfl
  let bK : kK ≃+* kAK :=
    localBaseResidueEquivDecompositionResidue K
  let bF : kF ≃+* kAF :=
    localBaseResidueEquivDecompositionResidue F
  let tau : kAK ≃+* kAF :=
    bK.symm.trans (eBaseResidue.trans bF)
  have heResidue (x : kAK) :
      eResidue (algebraMap kAK OmegaK x) =
        algebraMap kAF OmegaF (tau x) := by
    obtain ⟨y, rfl⟩ := bK.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [localBaseResidueEquivDecompositionResidue_algebraMap]
    have htau :
        tau (bK (IsLocalRing.residue CK a)) =
          bF (eBaseResidue (IsLocalRing.residue CK a)) := by
      simp [tau]
    rw [htau]
    change IsLocalRing.ResidueField.map r
        (IsLocalRing.residue AK _) =
      algebraMap kAF OmegaF
        (bF (IsLocalRing.ResidueField.map rBase
          (IsLocalRing.residue CK a)))
    rw [IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      localBaseResidueEquivDecompositionResidue_algebraMap]
    congr 1
    apply Subtype.ext
    exact (hr _).trans (he (a : K))
  let sigmaF : Gal(SeparableClosure F/F) :=
    { e.symm.trans (sigma.toRingEquiv.trans e) with
      commutes' := fun x => by
        change e (sigma (e.symm
          (algebraMap F (SeparableClosure F) x))) =
            algebraMap F (SeparableClosure F) x
        have hpre :
            e.symm (algebraMap F (SeparableClosure F) x) =
              algebraMap K (SeparableClosure K) (phi.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, he, phi.apply_symm_apply]
        rw [hpre, sigma.commutes, he, phi.apply_symm_apply] }
  let rhoK : OmegaK ≃ₐ[kAK] OmegaK :=
    localSeparableResidueAlgAction K sigma
  let rhoF : OmegaF ≃ₐ[kAF] OmegaF :=
    localSeparableResidueAlgAction F sigmaF
  let conjugate : OmegaF ≃ₐ[kAF] OmegaF :=
    { eResidue.symm.trans (rhoK.toRingEquiv.trans eResidue) with
      commutes' := fun x => by
        change eResidue
            (rhoK (eResidue.symm (algebraMap kAF OmegaF x))) =
          algebraMap kAF OmegaF x
        have hpre :
            eResidue.symm (algebraMap kAF OmegaF x) =
              algebraMap kAK OmegaK (tau.symm x) := by
          apply eResidue.injective
          rw [eResidue.apply_symm_apply, heResidue,
            tau.apply_symm_apply]
        rw [hpre, rhoK.commutes, heResidue,
          tau.apply_symm_apply] }
  have hconjugate : conjugate = rhoF := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eResidue.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change eResidue
        (rhoK (eResidue.symm
          (eResidue (IsLocalRing.residue AK a)))) =
      rhoF (eResidue (IsLocalRing.residue AK a))
    rw [eResidue.symm_apply_apply]
    change IsLocalRing.ResidueField.map r
        (residueAlgActionOfEqTop K AK
          (localSeparableDecompositionGroup_eq_top K) sigma
          (IsLocalRing.residue AK a)) =
      residueAlgActionOfEqTop F AF
        (localSeparableDecompositionGroup_eq_top F) sigmaF
        (IsLocalRing.ResidueField.map r
          (IsLocalRing.residue AK a))
    dsimp only [residueAlgActionOfEqTop]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      decompositionGroupResidueAction_residue,
      IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      decompositionGroupResidueAction_residue]
    congr 1
    apply Subtype.ext
    change e (sigma (a : SeparableClosure K)) =
      sigmaF (e (a : SeparableClosure K))
    simp [sigmaF]
  change residueAbsoluteDegreeIn kAF OmegaF rhoF =
    residueAbsoluteDegreeIn kAK OmegaK rhoK
  rw [← hconjugate]
  exact
    residueAbsoluteDegreeIn_semilinear_conjugation
      kAK OmegaK tau eResidue heResidue rhoK

/-- Every `F`-algebra equivalence from the standard separable closure of a
finite fixed field `F` to the original ambient separable closure identifies
the two uniquely extended local valuation rings. -/
theorem localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K)))
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[finiteFixedField K H] SeparableClosure K) :
    letI : FiniteDimensional K
        (finiteFixedField K H) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (finiteFixedField K H) :=
      finiteExtensionSpectralNormedField K
        (finiteFixedField K H)
    letI : ValuativeRel
        (finiteFixedField K H) :=
      finiteExtensionSpectralValuativeRel K
        (finiteFixedField K H)
    letI : IsNonarchimedeanLocalField
        (finiteFixedField K H) :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K
        (finiteFixedField K H)
    localSeparableValuationSubring (finiteFixedField K H) =
        (localSeparableValuationSubring K).comap e.toRingHom := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let A := localSeparableValuationSubring K
  let B := A.comap e.toRingHom
  have hcomap :
      A.comap
          (abstractFixedField K (SeparableClosure K) H.field).val.toRingHom =
        (ValuativeRel.valuation F).valuationSubring := by
    exact localSeparableValuationSubring_comap_embedding K F
      (abstractFixedField K (SeparableClosure K) H.field).val
  have hBext :
      (localCompleteDVF F).valuation.HasExtension B.valuation := by
    apply
      hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change e (algebraMap F (SeparableClosure F) x) ∈ A ↔
      x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [e.commutes]
    change x ∈
        A.comap
          (abstractFixedField K (SeparableClosure K) H.field).val.toRingHom ↔
      x ∈ (ValuativeRel.valuation F).valuationSubring
    rw [hcomap]
  let : (localCompleteDVF F).valuation.HasExtension B.valuation := hBext
  exact localSeparableValuationSubring_eq_of_hasExtension F B

/-- The residue field presented through the ambient separable closure is
canonically equivalent to the residue intermediate field attached to the
finite fixing subgroup, compatibly with their embeddings into the selected
residue field. -/
private theorem exists_abstractFixedFieldResidueEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K)))
    [FiniteDimensional K (finiteFixedField K H)]
    [NontriviallyNormedField (finiteFixedField K H)]
    [ValuativeRel (finiteFixedField K H)]
    [IsNonarchimedeanLocalField (finiteFixedField K H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (finiteFixedField K H))]
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[finiteFixedField K H] SeparableClosure K) :
    ∃ tau :
        decompositionResidueField (finiteFixedField K H)
            (localSeparableValuationSubring K) ≃+*
          localAbstractFixedResidueIntermediateField K H.field,
      ∀ x : decompositionResidueField (finiteFixedField K H)
          (localSeparableValuationSubring K),
        algebraMap
            (decompositionResidueField (finiteFixedField K H)
              (localSeparableValuationSubring K))
            (selectedResidueField (localSeparableValuationSubring K)) x =
          algebraMap
            (localAbstractFixedResidueIntermediateField K H.field)
            (selectedResidueField (localSeparableValuationSubring K))
            (tau x) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let A := localSeparableValuationSubring K
  let C := (ValuativeRel.valuation F).valuationSubring
  let V := (localCompleteDVF K).valuation.valuationSubring
  let kK := IsLocalRing.ResidueField V
  let kF := IsLocalRing.ResidueField C
  let k₀ := decompositionResidueField K A
  let kA := decompositionResidueField F A
  let Omega := selectedResidueField A
  let R := localAbstractFixedResidueIntermediateField K H.field
  let j : F →ₐ[K] SeparableClosure K :=
    (abstractFixedField K (SeparableClosure K) H.field).val
  let : (localCompleteDVF K).valuation.HasExtension C.valuation := by
    apply
      hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change ValuativeRel.valuation F (algebraMap K F x) ≤ 1 ↔
      (localCompleteDVF K).valuation x ≤ 1
    rw [_root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    rfl
  have hVC : V.valuation.HasExtension C.valuation := by
    apply
      hasExtension_valuation_of_valuationSubring_pullback
    intro x
    simpa only [V, ValuationSubring.valuationSubring_valuation] using
      (valuationSubring_pullback_of_hasExtension_valuation
        (localCompleteDVF K).valuation C x)
  have hC : A.comap (algebraMap F (SeparableClosure K)) = C := by
    simpa only [
      RamificationTheory.ValuationSubring.restrictIntermediateField_eq_comap] using
      (ValuationSubring.restrictIntermediateField_eq_of_finite_separable
        (localCompleteDVF K) A
        (abstractFixedField K (SeparableClosure K) H.field) C)
  have htop : decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F j e
  let eK : kK ≃+* k₀ :=
    localBaseResidueEquivDecompositionResidue K
  let eA : kF ≃+* kA :=
    residueFieldEquivDecompositionResidueOfEqTop A C hC htop
  let i : V →+* C :=
    ValuationTheory.Valuations.valuationSubringMapOfHasExtension V C hVC
  let bar : kF →+* Omega :=
    (algebraMap kA Omega).comp eA.toRingHom
  let : Algebra kK kF := by
    change Algebra 𝓀[K] 𝓀[F]
    exact IsLocalRing.ResidueField.instAlgebra
  have hbar_base (x : kK) :
      bar (algebraMap kK kF x) =
        algebraMap k₀ Omega (eK x) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have hres :
        algebraMap kK kF (IsLocalRing.residue V a) =
          IsLocalRing.residue C (i a) := by
      change algebraMap 𝓀[K] 𝓀[F]
          (IsLocalRing.residue 𝒪[K] a) =
        IsLocalRing.residue 𝒪[F] (algebraMap 𝒪[K] 𝒪[F] a)
      exact residueField_algebraMap_residue K F a
    rw [hres]
    change algebraMap kA Omega
        (eA (IsLocalRing.residue C (i a))) =
      algebraMap k₀ Omega
        (eK (IsLocalRing.residue V a))
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have hbase :=
      localBaseResidueEquivDecompositionResidue_algebraMap K a
    change algebraMap k₀ Omega
      (eK (IsLocalRing.residue V a)) = _ at hbase
    rw [hbase]
    congr 1
  let : Algebra k₀ kF :=
    ((algebraMap kK kF).comp eK.symm.toRingHom).toAlgebra
  let barAlg : kF →ₐ[k₀] Omega :=
    { bar with
      commutes' := fun z => by
        change bar (algebraMap kK kF (eK.symm z)) =
          algebraMap k₀ Omega z
        simpa using hbar_base (eK.symm z) }
  have hR : R = barAlg.fieldRange := by
    change IntermediateField.adjoin k₀
        (Set.range (algebraMap kA Omega)) = barAlg.fieldRange
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := eA.surjective z
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨eA x, rfl⟩
  let eRange : kF ≃+* barAlg.fieldRange :=
    (AlgEquiv.ofInjectiveField barAlg).toRingEquiv
  let eTop : kF ≃+* R :=
    eRange.trans
      (IntermediateField.equivOfEq hR.symm).toRingEquiv
  have heTop (x : kF) :
      algebraMap R Omega (eTop x) = bar x := by
    rfl
  let tau : kA ≃+* R := eA.symm.trans eTop
  refine ⟨tau, ?_⟩
  intro x
  change algebraMap kA Omega x =
    algebraMap R Omega (eTop (eA.symm x))
  rw [heTop]
  simp [bar]

private theorem residueAbsoluteDegreeIn_eq_normalizedDegree_abstractFixedFieldEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K)))
    [FiniteDimensional K (finiteFixedField K H)]
    [NontriviallyNormedField (finiteFixedField K H)]
    [ValuativeRel (finiteFixedField K H)]
    [IsNonarchimedeanLocalField (finiteFixedField K H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (finiteFixedField K H))]
    [Fintype (decompositionResidueField (finiteFixedField K H)
      (localSeparableValuationSubring K))]
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[finiteFixedField K H] SeparableClosure K)
    (sigma : Gal(SeparableClosure (finiteFixedField K H)/finiteFixedField K H))
    (htop : decompositionGroup (finiteFixedField K H)
      (localSeparableValuationSubring K) = ⊤)
    (tau : decompositionResidueField (finiteFixedField K H)
        (localSeparableValuationSubring K) ≃+*
      localAbstractFixedResidueIntermediateField K H.field)
    (hTau : ∀ x : decompositionResidueField (finiteFixedField K H)
        (localSeparableValuationSubring K),
      algebraMap
          (decompositionResidueField (finiteFixedField K H)
            (localSeparableValuationSubring K))
          (selectedResidueField (localSeparableValuationSubring K)) x =
        algebraMap
          (localAbstractFixedResidueIntermediateField K H.field)
          (selectedResidueField (localSeparableValuationSubring K))
          (tau x)) :
    residueAbsoluteDegreeIn
        (decompositionResidueField (finiteFixedField K H)
          (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (residueAlgActionOfEqTop (finiteFixedField K H)
          (localSeparableValuationSubring K) htop
          (AlgEquiv.autCongr e sigma)) =
      (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        ((abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field).symm
            (AlgEquiv.autCongr e sigma)) := by
  let F := finiteFixedField K H
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let A := localSeparableValuationSubring K
  let k₀ := decompositionResidueField K A
  let kA := decompositionResidueField F A
  let Omega := selectedResidueField A
  let R := localAbstractFixedResidueIntermediateField K H.field
  let eOmega : Omega ≃+* Omega := RingEquiv.refl Omega
  have heOmega (x : kA) :
      eOmega (algebraMap kA Omega x) =
        algebraMap R Omega (tau x) := by
    simpa [F, A, kA, Omega, R, eOmega] using hTau x
  let sigmaH : H.field.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup
      K (SeparableClosure K) H.field).symm
        (AlgEquiv.autCongr e sigma)
  let rhoA : Omega ≃ₐ[kA] Omega :=
    residueAlgActionOfEqTop F A htop
      (AlgEquiv.autCongr e sigma)
  let rhoH : Omega ≃ₐ[R] Omega :=
    localAbstractFixedResidueActionOverIntermediateField
      K H.field sigmaH
  let conjugate : Omega ≃ₐ[R] Omega :=
    { eOmega.symm.trans (rhoA.toRingEquiv.trans eOmega) with
      commutes' :=
        semilinearConjugate_commutes
          tau eOmega heOmega rhoA }
  have hconjugate : conjugate = rhoH := by
    apply AlgEquiv.ext
    intro x
    change residueAlgActionOfEqTop F A htop
        (AlgEquiv.autCongr e sigma) x =
      localSeparableResidueAlgAction K sigmaH.1 x
    have hsigmaH :
        abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H.field sigmaH =
          AlgEquiv.autCongr e sigma :=
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).apply_symm_apply
          (AlgEquiv.autCongr e sigma)
    rw [localAbstractFixedResidueAction_apply K H.field sigmaH]
    rw [hsigmaH]
  let : Algebra k₀ R := R.algebra
  let : FiniteDimensional k₀ R :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
  let : Finite R := Module.finite_of_finite k₀
  let : Fintype R := Fintype.ofFinite R
  rw [localResidueDatum_normalizedDegree_eq_residueAbsoluteDegreeIn]
  change residueAbsoluteDegreeIn kA Omega rhoA =
    residueAbsoluteDegreeIn R Omega rhoH
  rw [← hconjugate]
  exact
    (residueAbsoluteDegreeIn_semilinear_conjugation
      kA Omega tau eOmega heOmega rhoA).symm

/-- Changing from the canonical separable closure of a finite fixed field to
the original ambient separable closure identifies its intrinsic local
residue degree with the normalized degree on the corresponding abstract
field. -/
theorem localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K/K)))
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[finiteFixedField K H] SeparableClosure K)
    (sigma : Gal(SeparableClosure (finiteFixedField K H)/finiteFixedField K H)) :
    letI : FiniteDimensional K
        (finiteFixedField K H) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (finiteFixedField K H) :=
      finiteExtensionSpectralNormedField K
        (finiteFixedField K H)
    letI : ValuativeRel
        (finiteFixedField K H) :=
      finiteExtensionSpectralValuativeRel K
        (finiteFixedField K H)
    letI : IsNonarchimedeanLocalField
        (finiteFixedField K H) :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K
        (finiteFixedField K H)
    localResidueDegree (finiteFixedField K H) sigma =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          ((abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H.field).symm
              (AlgEquiv.autCongr e sigma)) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let A := localSeparableValuationSubring K
  let kA := decompositionResidueField F A
  let j : F →ₐ[K] SeparableClosure K :=
    (abstractFixedField K (SeparableClosure K) H.field).val
  have htop : decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F j e
  obtain ⟨tau, hTau⟩ := exists_abstractFixedFieldResidueEquiv K H e
  let : Fintype kA :=
    finiteExtensionDecompositionResidueFintype K F j e
  have hlocal :
      localResidueDegree F sigma =
        residueAbsoluteDegreeIn kA (selectedResidueField A)
          (residueAlgActionOfEqTop F A htop
            (AlgEquiv.autCongr e sigma)) :=
    localResidueDegree_eq_residueAbsoluteDegreeIn_finiteExtensionEquiv
      K F j e sigma
  rw [hlocal]
  exact
    residueAbsoluteDegreeIn_eq_normalizedDegree_abstractFixedFieldEquiv
      K H e sigma htop tau hTau

/-- A finite field embedded in the separable closure has a fixing subgroup of finite index. -/
private theorem finite_absoluteFixingQuotient_fieldRange
    (K F : Type) [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (i : F →ₐ[K] SeparableClosure K) :
    Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K)))
        (closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i))
        (le_baseField _)) := by
  let H₀ := closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)
  let : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let G := Gal(SeparableClosure K/K)
  let Bases := { B : ClosedSubgroup G //
    H₀.toSubgroup ≤ B.toSubgroup }
  let Bfix : Bases :=
    ⟨closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)),
      fixingSubgroupLeBase K (SeparableClosure K)
        (AlgHom.fieldRange i)⟩
  let Bbase : Bases :=
    ⟨baseField G, le_baseField H₀⟩
  let Q : Bases → Type := fun B =>
    B.1.toSubgroup ⧸ extensionSubgroup B.1 H₀ B.2
  have hBase : Bfix = Bbase := by
    apply Subtype.ext
    exact closedFixingSubgroup_bot_eq_baseField
      K (SeparableClosure K)
  let : Finite (Q Bfix) := by
    change Finite
      ((closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K)))
          H₀
          (fixingSubgroupLeBase K (SeparableClosure K)
            (AlgHom.fieldRange i)))
    infer_instance
  change Finite (Q Bbase)
  exact Finite.of_equiv (Q Bfix)
    (Equiv.cast (congrArg Q hBase))

/-- A semilinear equivalence transports automorphisms fixing the corresponding base fields. -/
private def semilinearGaloisTransport
    {k f Ω Ω' : Type} [Field k] [Field f] [Field Ω] [Field Ω']
    [Algebra k Ω] [Algebra f Ω'] (phi : k ≃+* f) (c : Ω ≃+* Ω')
    (hc : ∀ x : k, c (algebraMap k Ω x) = algebraMap f Ω' (phi x))
    (sigma : Gal(Ω/k)) : Gal(Ω'/f) :=
  { c.symm.trans (sigma.toRingEquiv.trans c) with
    commutes' := fun x => by
      change c (sigma (c.symm (algebraMap f Ω' x))) = algebraMap f Ω' x
      have hc' : c.symm (algebraMap f Ω' x) = algebraMap k Ω (phi.symm x) := by
        apply c.injective
        rw [c.apply_symm_apply, hc, phi.apply_symm_apply]
      rw [hc', sigma.commutes, hc, phi.apply_symm_apply] }

/-- The intrinsic residue degree of an arbitrary finite separable local
extension agrees with the normalized degree on the ambient fixing subgroup
cut out by an embedding into the base separable closure.  Thus the
fixed-field comparison does not require the extension field itself to be
definitionally a fixed-field subtype. -/
theorem
    localResidueDegree_eq_normalizedDegree_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (sigma : Gal(SeparableClosure F/F)),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      letI hHabsolute : Finite
          ((baseField
            (Gal(SeparableClosure K/K))).toSubgroup ⧸
            extensionSubgroup
              (baseField (Gal(SeparableClosure K/K)))
              H₀ (le_baseField H₀)) :=
        finite_absoluteFixingQuotient_fieldRange K F i
      let H : FiniteAbstractField
          (Gal(SeparableClosure K/K)) :=
        ⟨H₀, hHabsolute⟩
      let F₀ :=
        abstractFixedField K (SeparableClosure K) H₀
      let hfixed :
          F₀ = AlgHom.fieldRange i :=
        InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)
      let phi : F ≃+* F₀ :=
        ((i.equivFieldRange).trans
          (IntermediateField.equivOfEq hfixed.symm)).toRingEquiv
      let rho : Gal(SeparableClosure K/F₀) :=
        semilinearGaloisTransport phi e.toRingEquiv (fun x => by
          change e (algebraMap F (SeparableClosure F) x) =
            algebraMap F₀ (SeparableClosure K) (phi x)
          rw [e.commutes]
          rfl) sigma
      localResidueDegree F sigma =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField
            (localResidueDatum K))
          ((abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H₀).symm
              rho) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e sigma
  dsimp only
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        (Gal(SeparableClosure K/K))).toSubgroup ⧸
        extensionSubgroup
          (baseField (Gal(SeparableClosure K/K)))
          H₀ (le_baseField H₀)) :=
    finite_absoluteFixingQuotient_fieldRange K F i
  let H : FiniteAbstractField
      (Gal(SeparableClosure K/K)) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  let : NontriviallyNormedField F₀ :=
    finiteExtensionSpectralNormedField K F₀
  let : ValuativeRel F₀ :=
    finiteExtensionSpectralValuativeRel K F₀
  let : IsNonarchimedeanLocalField F₀ :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F₀
  let : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  let : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  have hvaluation :
      localSeparableValuationSubring F =
        (localSeparableValuationSubring F₀).comap
          c.toRingHom := by
    have hF :=
      localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
        K F i e
    have hF₀ :=
      localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv
        K H e₀
    rw [hF, hF₀]
    ext x
    change
      e x ∈ localSeparableValuationSubring K ↔
        e₀ (c x) ∈ localSeparableValuationSubring K
    change
      e x ∈ localSeparableValuationSubring K ↔
        e₀ (e₀.symm (e x)) ∈ localSeparableValuationSubring K
    rw [e₀.apply_symm_apply]
  let sigma₀ : Gal(SeparableClosure F₀/F₀) :=
    semilinearGaloisTransport phi c hc sigma
  let rho : Gal(SeparableClosure K/F₀) :=
    semilinearGaloisTransport phi e.toRingEquiv (fun x => by
      change e (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure K) (phi x)
      rw [e.commutes]
      rfl) sigma
  have hrho :
      AlgEquiv.autCongr e₀ sigma₀ = rho := by
    apply AlgEquiv.ext
    intro x
    simp only [AlgEquiv.autCongr_apply]
    change
      e₀
          (c (sigma (c.symm (e₀.symm x)))) =
        e (sigma (e.symm x))
    rw [show c.symm (e₀.symm x) = e.symm x by
      apply c.injective
      rw [c.apply_symm_apply]
      change e₀.symm x = e₀.symm (e (e.symm x))
      rw [e.apply_symm_apply]]
    change e₀ (e₀.symm (e (sigma (e.symm x)))) =
      e (sigma (e.symm x))
    rw [e₀.apply_symm_apply]
  have hdegree :
      localResidueDegree F₀ sigma₀ =
        localResidueDegree F sigma := by
    simpa only [sigma₀, semilinearGaloisTransport] using
      localResidueDegree_semilinear_conjugation
        F F₀ phi c hc hvaluation sigma
  have hfixedDegree :
      localResidueDegree F₀ sigma₀ =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField
            (localResidueDatum K))
          ((abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H₀).symm
              (AlgEquiv.autCongr e₀ sigma₀)) := by
    exact
      localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv
        K H e₀ sigma₀
  rw [hrho] at hfixedDegree
  change
    localResidueDegree F sigma =
      (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField
          (localResidueDatum K))
        ((abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H₀).symm rho)
  exact hdegree.symm.trans hfixedDegree


end LocalClassFieldTheory

/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueValuationComparison
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.UniqueRing

/-! # Finite Residue Finrank Transfer -/
namespace LocalClassFieldTheory
open CyclicCohomology RamificationTheory ClassFormation

open LocalFieldTheory ValuationTheory

/-!
# Finite local reciprocity: comparison of the two finite residue-field models

The residue-action exact sequence presents the residue field of a
finite fixed field intrinsically, inside the selected residue algebraic
closure.  The norm formula uses the literal residue field of the spectral
valuation on that fixed field.  This file compares those presentations by
the uniqueness of the finite extension valuation.
-/

noncomputable section

open scoped ValuativeRel
open HilbertRamification.ValuationSubring

universe u v

/-- If the decomposition group of an ambient valuation ring is the whole
Galois group, its decomposition-field valuation ring is canonically
equivalent to the given valuation ring on the ground field. -/
noncomputable def valuationSubringEquivDecompositionFieldOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    C ≃+* decompositionFieldValuationSubring F A := by
  let Z := decompositionField F A
  have hZ : Z = ⊥ := by
    change IntermediateField.fixedField (decompositionGroup F A) = ⊥
    rw [hA]
    simpa using
      (InfiniteGalois.fixedField_fixingSubgroup
        (⊥ : IntermediateField F Omega))
  let eFZ : F ≃ₐ[F] Z :=
    (IntermediateField.botEquiv F Omega).symm.trans
      (IntermediateField.equivOfEq hZ.symm)
  refine
    { toFun := fun x => ⟨eFZ (x : F), ?_⟩
      invFun := fun z => ⟨eFZ.symm (z : Z), ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact eFZ.symm_apply_apply (x : F)
      right_inv := fun z => by
        apply Subtype.ext
        exact eFZ.apply_symm_apply (z : Z)
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add eFZ (x : F) (y : F)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul eFZ (x : F) (y : F) }
  · change ((eFZ x : Z) : Omega) ∈ A
    have he : ((eFZ x : Z) : Omega) =
        algebraMap F Omega (x : F) := by
      rfl
    rw [he]
    have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
      rw [hC]
      exact x.property
    exact hx
  · have hz : eFZ.symm (z : Z) ∈ A.comap (algebraMap F Omega) := by
      change algebraMap F Omega (eFZ.symm (z : Z)) ∈ A
      have he : algebraMap F Omega (eFZ.symm (z : Z)) =
          ((z : Z) : Omega) := by
        exact congrArg Subtype.val (eFZ.apply_symm_apply (z : Z))
      rw [he]
      exact z.property
    rw [hC] at hz
    exact hz

/-- The corresponding equivalence between literal and intrinsic residue
fields. -/
noncomputable def residueFieldEquivDecompositionResidueOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    IsLocalRing.ResidueField C ≃+* decompositionResidueField F A :=
  (IsLocalRing.ResidueField.mapEquiv
      (valuationSubringEquivDecompositionFieldOfEqTop A C hC hA)).trans
    (decompositionFieldResidueEquiv (K := F) A)

/-- Naturality of the preceding residue equivalence with reduction into the
selected residue field. -/
theorem residueFieldEquivDecompositionResidueOfEqTop_algebraMap
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) (x : C) :
    algebraMap (decompositionResidueField F A) (selectedResidueField A)
        (residueFieldEquivDecompositionResidueOfEqTop A C hC hA
          (IsLocalRing.residue C x)) =
      IsLocalRing.residue A
        (⟨algebraMap F Omega (x : F), by
          have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
            rw [hC]
            exact x.property
          exact hx⟩ : A) := by
  rfl

/-! ## The finite fixed-field comparison -/

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Finite local reciprocity, residue-degree comparison.**  For an arbitrary finite
closed subgroup field (not necessarily normal over `K`), the residue degree
defined by the absolute residue action is the degree of the literal residue
field of the unique finite extension valuation. -/
theorem localResidueDatum_residueDegree_eq_residueFinrank
    (H : FiniteAbstractField (Gal(SeparableClosure K/K)))
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H.field)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H.field)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H.field)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H.field)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H.field))] :
    (H.residueDegree (localResidueDatum K) : ℕ) =
      @Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (SeparableClosure K) H.field] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[abstractFixedField K (SeparableClosure K) H.field])) := by
  let E := abstractFixedField K (SeparableClosure K) H.field
  let A := localSeparableValuationSubring K
  let C := (ValuativeRel.valuation E).valuationSubring
  let V := (localCompleteDVF K).valuation.valuationSubring
  let kK := IsLocalRing.ResidueField
    V
  let kE := IsLocalRing.ResidueField C
  let k₀ := decompositionResidueField K A
  let kE' := decompositionResidueField E A
  let Omega := selectedResidueField A
  let F := localAbstractFixedResidueIntermediateField K H.field
  let : Algebra kK kE := by
    change Algebra 𝓀[K] 𝓀[E]
    exact IsLocalRing.ResidueField.instAlgebra
  let : Module kK kE := by
    change Module 𝓀[K] 𝓀[E]
    exact IsLocalRing.ResidueField.instModule
  change (H.residueDegree (localResidueDatum K) : ℕ) =
    Module.finrank kK kE

  have hExtC : (localCompleteDVF K).valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change ValuativeRel.valuation E (algebraMap K E x) ≤ 1 ↔
      (localCompleteDVF K).valuation x ≤ 1
    rw [_root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    rfl
  let : (localCompleteDVF K).valuation.HasExtension C.valuation := hExtC
  have hVC : V.valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    simpa only [V, ValuationSubring.valuationSubring_valuation] using
      (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
        (localCompleteDVF K).valuation C x)
  have hC : A.comap (algebraMap E (SeparableClosure K)) = C := by
    simpa only [RamificationTheory.ValuationSubring.restrictIntermediateField_eq_comap] using
      (ValuationSubring.restrictIntermediateField_eq_of_finite_separable
        (localCompleteDVF K) A
        (abstractFixedField K (SeparableClosure K) H.field) C)
  have htop : decompositionGroup E A = ⊤ :=
    localAbstractFixedDecompositionGroup_eq_top K H.field

  let eK : kK ≃+* k₀ :=
    localBaseResidueEquivDecompositionResidue K
  let eE : kE ≃+* kE' :=
    residueFieldEquivDecompositionResidueOfEqTop A C hC htop
  let i : V →+* C :=
    ValuationTheory.Valuations.valuationSubringMapOfHasExtension V C hVC
  let bar : kE →+* Omega :=
    (algebraMap kE' Omega).comp eE.toRingHom

  have hbar_base (x : kK) :
      bar (algebraMap kK kE x) =
        algebraMap k₀ Omega (eK x) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have hres :
        algebraMap kK kE
            (IsLocalRing.residue V a) =
          IsLocalRing.residue C
            (i a) := by
      change algebraMap 𝓀[K] 𝓀[E]
          (IsLocalRing.residue 𝒪[K] a) =
        IsLocalRing.residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] a)
      exact residueField_algebraMap_residue K E a
    rw [hres]
    change algebraMap kE' Omega
        (eE (IsLocalRing.residue C
          (i a))) =
      algebraMap k₀ Omega
        (eK (IsLocalRing.residue V a))
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have hbase :=
      localBaseResidueEquivDecompositionResidue_algebraMap K a
    change algebraMap k₀ Omega
      (eK (IsLocalRing.residue V a)) = _ at hbase
    rw [hbase]
    congr 1

  let : Algebra k₀ kE :=
    ((algebraMap kK kE).comp eK.symm.toRingHom).toAlgebra
  let barAlg : kE →ₐ[k₀] Omega :=
    { bar with
      commutes' := fun z => by
        change bar (algebraMap kK kE (eK.symm z)) =
          algebraMap k₀ Omega z
        simpa using hbar_base (eK.symm z) }

  have hF : F = barAlg.fieldRange := by
    change IntermediateField.adjoin k₀
        (Set.range (algebraMap kE' Omega)) = barAlg.fieldRange
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := eE.surjective z
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨eE x, rfl⟩

  let eRange : kE ≃+* barAlg.fieldRange :=
    (AlgEquiv.ofInjectiveField barAlg).toRingEquiv
  let : Algebra k₀ barAlg.fieldRange := barAlg.fieldRange.algebra
  let : Algebra k₀ F :=
    localAbstractFixedResidueIntermediateFieldAlgebra K H.field
  let eTop : kE ≃+* F :=
    eRange.trans
      (IntermediateField.equivOfEq hF.symm).toRingEquiv
  have hcomm :
      (algebraMap k₀ F).comp eK.toRingHom =
        eTop.toRingHom.comp (algebraMap kK kE) := by
    ext x
    change algebraMap k₀ Omega (eK x) =
      bar (algebraMap kK kE x)
    exact (hbar_base x).symm
  have hfinrankRaw :
      Module.finrank kK kE = Module.finrank k₀ F :=
    Algebra.finrank_eq_of_equiv_equiv eK eTop hcomm
  exact
    (localResidueDatum_residueDegree_eq_selectedResidueFinrank K H).trans
      hfinrankRaw.symm

end
end LocalClassFieldTheory

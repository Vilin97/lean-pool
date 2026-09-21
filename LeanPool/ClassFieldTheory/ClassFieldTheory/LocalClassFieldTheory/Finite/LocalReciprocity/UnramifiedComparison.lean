/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Abstract and concrete unramified Frobenius

This module compares the residue-degree construction on a fixed separable
closure with the ordinary unramified valuation extension and its arithmetic
Frobenius.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open RamificationTheory.HilbertRamification.ValuationSubring


private abbrev absoluteGalois (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev abstractBase (K : Type) [Field K] :
    ClosedSubgroup (absoluteGalois K) :=
  intrinsicAbstractBase K

private noncomputable def finiteResidueAbstractBase
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    DegreeData.FiniteResidueAbstractField (localResidueDatum K) :=
  (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField (localResidueDatum K)

section BaseResidueDegree

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The intrinsic finite abstract base has residue degree one for the local
datum. -/
theorem intrinsicFiniteAbstractBase_residueDegree_eq_one :
    ((intrinsicFiniteAbstractBase K).residueDegree (localResidueDatum K) : ℕ) = 1 := by
  rw [intrinsicFiniteAbstractBase_eq_base,
    FiniteAbstractField.base_residueDegree]
  rfl

private theorem finiteResidueAbstractBase_residueDegree_eq_one :
    ((finiteResidueAbstractBase K).residueDegree : ℕ) = 1 := by
  change ((intrinsicFiniteAbstractBase K).residueDegree (localResidueDatum K) : ℕ) = 1
  exact intrinsicFiniteAbstractBase_residueDegree_eq_one K

end BaseResidueDegree

section BaseFrobeniusLift

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The chosen degree-one lift used in the abstract unramified Frobenius. -/
private noncomputable def abstractBaseFrobeniusLift :
    (abstractBase K).toSubgroup :=
  Classical.choose
    ((localResidueDatum K).normalizedDegree_surjective
      (finiteResidueAbstractBase K)
      (Multiplicative.ofAdd (1 : ZHat)))

private theorem abstractBaseFrobeniusLift_normalizedDegree :
    (localResidueDatum K).normalizedDegree
        (finiteResidueAbstractBase K)
        (abstractBaseFrobeniusLift K) =
      Multiplicative.ofAdd (1 : ZHat) :=
  Classical.choose_spec
    ((localResidueDatum K).normalizedDegree_surjective
      (finiteResidueAbstractBase K)
      (Multiplicative.ofAdd (1 : ZHat)))

private theorem abstractBaseFrobeniusLift_degree :
    localResidueDegree K (abstractBaseFrobeniusLift K).1 =
      Multiplicative.ofAdd (1 : ZHat) := by
  apply Multiplicative.ext
  have h :=
    (localResidueDatum K).residueDegree_nsmul_normalizedDegree
      (finiteResidueAbstractBase K)
      (abstractBaseFrobeniusLift K)
  rw [finiteResidueAbstractBase_residueDegree_eq_one K, one_nsmul,
    abstractBaseFrobeniusLift_normalizedDegree K] at h
  exact h.symm

/-- A degree-one element of the local absolute Galois group acts by the
arithmetic Frobenius on the selected residue algebraic closure. -/
private theorem localSeparableResidueAlgAction_eq_frobenius_of_degree_one
    (sigma : Gal((SeparableClosure K) / K))
    (hsigma : localResidueDegree K sigma =
      Multiplicative.ofAdd (1 : ZHat)) :
    localSeparableResidueAlgAction K sigma =
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K)) := by
  let k := decompositionResidueField K (localSeparableValuationSubring K)
  let Omega := selectedResidueField (localSeparableValuationSubring K)
  let rho := localSeparableResidueAlgAction K sigma
  change residueAbsoluteDegreeIn k Omega rho =
      Multiplicative.ofAdd (1 : ZHat) at hsigma
  calc
    rho = residueAbsoluteFrobenius k Omega
        (residueAbsoluteDegreeIn k Omega rho) :=
      ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply rho).symm
    _ = residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat)) := by rw [hsigma]
    _ = FiniteField.frobeniusAlgEquivOfAlgebraic k Omega :=
      residueAbsoluteFrobenius_one k Omega

end BaseFrobeniusLift

section

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

private noncomputable instance comparisonIntegerRingIsIntegralClosure :
    IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  localCompleteDVF_integerRing_isIntegralClosure K L

/-- A finite Galois extension of nonarchimedean local fields has a finite
extension of valuation integer rings.  The integral-closure proof is derived
from the chosen valuation extension, rather than exposed as an assumption. -/
noncomputable instance finiteGaloisLocalField_integerRing_moduleFinite :
    Module.Finite 𝒪[K] 𝒪[L] :=
  localCompleteDVF_integerRing_moduleFinite K L

variable
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

variable (i : L →ₐ[K] SeparableClosure K)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- Pulling the selected extension valuation on `Kˢᵉᵖ` back along a finite
separable embedding gives the given local valuation on the source field. -/
theorem localSeparableValuationSubring_comap_embedding
    [Algebra.IsSeparable K L] :
    (localSeparableValuationSubring K).comap i.toRingHom =
      (ValuativeRel.valuation L).valuationSubring := by
  let A := localSeparableValuationSubring K
  let B := A.comap i.toRingHom
  let C := (ValuativeRel.valuation L).valuationSubring
  have hBext : (localCompleteDVF K).valuation.HasExtension B.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change i (algebraMap K L x) ∈ A ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring
    rw [i.commutes]
    exact localSeparableValuationSubring_pullback K x
  have hCext : (localCompleteDVF K).valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      (localCompleteDVF K).valuation x ≤ 1
    rw [_root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    rfl
  obtain ⟨target, htarget, _hintegral, _hFundamental⟩ :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := K) (L := L) (localCompleteDVF K)
  let : IsScalarTower (localCompleteDVF K).valuationSubring
      target.valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isScalarTower_of_hasExtension
      (localCompleteDVF K).valuation target.valuation
  have hB : target.valuation.valuationSubring = B :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target B
  have hC : target.valuation.valuationSubring = C :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target C
  exact hB.symm.trans hC

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- Reduction of an embedded finite extension into the selected residue
algebraic closure used by `localResidueDatum`. -/
noncomputable def finiteGaloisResidueEmbeddingOfEmbedding :
    𝓀[L] →+*
      selectedResidueField (localSeparableValuationSubring K) := by
  letI : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  have h := congrArg ValuationSubring.toSubring
    (localSeparableValuationSubring_comap_embedding K L i)
  change ((localSeparableValuationSubring K).comap i.toRingHom).toSubring =
    (ValuativeRel.valuation L).integer at h
  letI : IsLocalRing ((localSeparableValuationSubring K).comap i.toRingHom).toSubring := by
    change IsLocalRing ((localSeparableValuationSubring K).comap i.toRingHom)
    infer_instance
  let e : (ValuativeRel.valuation L).integer ≃+*
      ((localSeparableValuationSubring K).comap i.toRingHom).toSubring :=
    RingEquiv.subringCongr h.symm
  exact (valuationSubringComapResidueMap
      (F := L) (localSeparableValuationSubring K)).comp
    (IsLocalRing.ResidueField.mapEquiv e).toRingHom

omit [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- The residue embedding is reduction of the original field embedding. -/
@[simp] theorem finiteGaloisResidueEmbeddingOfEmbedding_residue
    (x : 𝒪[L]) :
    finiteGaloisResidueEmbeddingOfEmbedding K L i
        (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨i (x : L), by
          have hx : (x : L) ∈
              (localSeparableValuationSubring K).comap i.toRingHom := by
            rw [localSeparableValuationSubring_comap_embedding K L i]
            exact x.property
          exact hx⟩ : localSeparableValuationSubring K) := by
  simp only [finiteGaloisResidueEmbeddingOfEmbedding]
  rfl

omit [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- The concrete residue action is the restriction of the selected absolute
residue action along the chosen finite Galois embedding. -/
theorem finiteGaloisResidueEmbeddingOfEmbedding_equivariant
    (τ : (abstractBase K).toSubgroup) (x : 𝓀[L]) :
    finiteGaloisResidueEmbeddingOfEmbedding K L i
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
            (QuotientGroup.mk τ)) x) =
      localSeparableResidueAlgAction K τ.1
        (finiteGaloisResidueEmbeddingOfEmbedding K L i x) := by
  let A := localSeparableValuationSubring K
  let σ : Gal(L / K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  let jO : 𝒪[L] → A := fun y =>
    ⟨i (y : L), by
      have hy : (y : L) ∈ A.comap i.toRingHom := by
        rw [localSeparableValuationSubring_comap_embedding K L i]
        exact y.property
      exact hy⟩
  let σa : 𝒪[L] :=
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a
  let aA : A := jO a
  let σaA : A := jO σa
  let τD : decompositionGroup K A :=
    toDecompositionGroupOfEqTop K A
      (localSeparableDecompositionGroup_eq_top K) τ.1
  have hσaA : σaA = τD • aA := by
    apply Subtype.ext
    exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      K L i τ (a : L)
  calc
    finiteGaloisResidueEmbeddingOfEmbedding K L i
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ
          (IsLocalRing.residue 𝒪[L] a)) =
      finiteGaloisResidueEmbeddingOfEmbedding K L i
        (IsLocalRing.residue 𝒪[L] σa) := by
          congr 1
    _ = IsLocalRing.residue A σaA := by
      simpa only [jO, σaA] using
        finiteGaloisResidueEmbeddingOfEmbedding_residue K L i σa
    _ = IsLocalRing.residue A (τD • aA) := by rw [hσaA]
    _ = localSeparableResidueAlgAction K τ.1
        (IsLocalRing.residue A aA) := by
      change IsLocalRing.residue A (τD • aA) =
        residueAlgActionOfEqTop K A
          (localSeparableDecompositionGroup_eq_top K) τ.1
            (IsLocalRing.residue A aA)
      exact (decompositionGroupResidueAction_residue
        (K := K) A τD aA).symm
    _ = localSeparableResidueAlgAction K τ.1
        (finiteGaloisResidueEmbeddingOfEmbedding K L i
          (IsLocalRing.residue 𝒪[L] a)) := by
      rw [finiteGaloisResidueEmbeddingOfEmbedding_residue]

/-! ## Comparison of unramifiedness -/

/-- An actually unramified finite Galois extension gives an unramified
extension for the abstract local residue datum. -/
theorem finiteGaloisAbstractExtensionOfEmbedding_isUnramified :
    (finiteGaloisAbstractExtensionOfEmbedding K L i).IsUnramified
      (localResidueDatum K) := by
  apply ((finiteGaloisAbstractExtensionOfEmbedding K L i).isUnramified_iff_inertia_le
    (localResidueDatum K)).2
  intro g hg
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let τ : (abstractBase K).toSubgroup := ⟨g, hg.1⟩
  let q : Gal(L / K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)
  have hdegree : localResidueDegree K g = 1 := hg.2
  have hdegree' :
      residueAbsoluteDegreeIn k Omega
        (localSeparableResidueAlgAction K g) = 1 := hdegree
  have hlocal :
      localSeparableResidueAlgAction K g = 1 := by
    calc
      localSeparableResidueAlgAction K g =
          residueAbsoluteFrobenius k Omega
            (residueAbsoluteDegreeIn k Omega
              (localSeparableResidueAlgAction K g)) :=
        ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply
          (localSeparableResidueAlgAction K g)).symm
      _ = residueAbsoluteFrobenius k Omega 1 := by rw [hdegree']
      _ = 1 := map_one _
  have hresidue :
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L q = 1 := by
    apply AlgEquiv.ext
    intro x
    apply (finiteGaloisResidueEmbeddingOfEmbedding K L i).injective
    rw [finiteGaloisResidueEmbeddingOfEmbedding_equivariant K L i τ x]
    change localSeparableResidueAlgAction K g
        (finiteGaloisResidueEmbeddingOfEmbedding K L i x) =
      finiteGaloisResidueEmbeddingOfEmbedding K L i x
    rw [hlocal]
    rfl
  have hq : q = 1 := by
    apply
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
        K L
    rw [map_one]
    exact hresidue
  change g ∈
    (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  rcases hz with ⟨x, rfl⟩
  have hrestrict :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      K L i τ x
  change i (q x) = g (i x) at hrestrict
  rw [hq] at hrestrict
  exact hrestrict.symm

/-! ## Frobenius normalization -/

section AbstractUnramifiedFrobenius

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
private theorem finiteGaloisResidueBaseExtension_normal :
    (extensionSubgroup (finiteResidueAbstractBase K).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below).Normal :=
  (finiteGaloisAbstractExtensionOfEmbedding K L i).normal

attribute [local instance] finiteGaloisResidueBaseExtension_normal

/-- Under the field-facing quotient equivalence, the abstract degree-one
unramified Frobenius is the actual arithmetic Frobenius of the unramified
valuation extension. -/
theorem finiteGaloisAbstractUnramifiedFrobenius_eq_arithmeticFrobenius :
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
        ((localResidueDatum K).unramifiedFrobenius
          (finiteResidueAbstractBase K)
          (finiteGaloisAbstractExtensionOfEmbedding K L i).field
          (finiteGaloisAbstractExtensionOfEmbedding K L i).below) =
      arithmeticFrobeniusOfUnramifiedValuation K L := by
  let phi := abstractBaseFrobeniusLift K
  let q : Gal(L / K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk phi)
  have hselected :
      localSeparableResidueAlgAction K phi.1 =
        FiniteField.frobeniusAlgEquivOfAlgebraic
          (decompositionResidueField K
            (localSeparableValuationSubring K))
          (selectedResidueField
            (localSeparableValuationSubring K)) :=
    localSeparableResidueAlgAction_eq_frobenius_of_degree_one K phi.1
      (abstractBaseFrobeniusLift_degree K)
  have hcard :
      Nat.card
          (decompositionResidueField K
            (localSeparableValuationSubring K)) =
        Nat.card 𝓀[K] :=
    (Nat.card_congr
      (localBaseResidueEquivDecompositionResidue K).toEquiv).symm
  have hresidue :
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L q =
        galoisGroupResidueAlgEquivOfIsIntegralClosure K L
          (arithmeticFrobeniusOfUnramifiedValuation K L) := by
    apply AlgEquiv.ext
    intro x
    apply (finiteGaloisResidueEmbeddingOfEmbedding K L i).injective
    rw [finiteGaloisResidueEmbeddingOfEmbedding_equivariant K L i phi x,
      hselected]
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply,
      map_pow, ← Nat.card_eq_fintype_card, hcard]
  have hq : q = arithmeticFrobeniusOfUnramifiedValuation K L := by
    apply
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
        K L
    exact hresidue
  change q = arithmeticFrobeniusOfUnramifiedValuation K L
  exact hq

end AbstractUnramifiedFrobenius

end

end LocalClassFieldTheory

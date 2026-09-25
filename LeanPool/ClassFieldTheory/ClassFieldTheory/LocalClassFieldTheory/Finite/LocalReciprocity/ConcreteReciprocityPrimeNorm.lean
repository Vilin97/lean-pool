/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Concrete prime-norm evaluation

The abstract prime-norm formula is transported through an explicit
separable-closure realization. The resulting concrete norm-residue symbol
sends the transported base-field norm to the represented Galois automorphism.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable (i : L →ₐ[K] SeparableClosure K)

local notation "Eᵢ" => finiteGaloisAbstractExtensionOfEmbedding K L i

/-- The concrete local norm-residue symbol evaluated on the norm of a prime
element in the fixed field of a positive Frobenius lift.

The hypothesis on `x` identifies its image in the base fixed coefficient
group with the abstract relative norm, so the statement is independent of a
particular presentation of that norm. The right side is the abelianization
class of the actual `K`-automorphism of `L` represented by `q`. -/
theorem concreteNormResidueSymbolOfEmbedding_apply_primeNorm
    (D : DegreeData (intrinsicAbsoluteGalois K)) (v : ValuationData D (intrinsicAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K))
    (q : (Eᵢ).extensionQuotient)
    (sigma : D.FrobeniusElements
      ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D) (Eᵢ).field (Eᵢ).below)
    (hsigma : D.frobeniusRestriction
      ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D) (Eᵢ).field (Eᵢ).below
        sigma = q)
    (pi : ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
      (D.frobeniusFixedField ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D)
        (Eᵢ).field (Eᵢ).below sigma))
    (hpi :
      letI : Finite ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
          extensionSubgroup (intrinsicFiniteAbstractBase K).field (Eᵢ).field (Eᵢ).below) := by
        change Finite ((intrinsicAbstractBase K).toSubgroup ⧸
          extensionSubgroup (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below)
        exact (Eᵢ).finite
      let KR := (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D
      let S := D.frobeniusFixedField KR (Eᵢ).field (Eᵢ).below sigma
      letI : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
          extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) S (le_baseField S)) :=
        D.frobeniusFixedField_absoluteFinite
          (intrinsicFiniteAbstractBase K) (Eᵢ).field (Eᵢ).below sigma
      let Sigma : FiniteAbstractField (intrinsicAbsoluteGalois K) := ⟨S, inferInstance⟩
      v.IsPrimeElement Sigma pi)
    (x : Kˣ)
    (hx :
      let KR := (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D
      let S := D.frobeniusFixedField KR (Eᵢ).field (Eᵢ).below sigma
      let hSB := D.frobeniusFixedField_le KR (Eᵢ).field (Eᵢ).below sigma
      letI : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
          extensionSubgroup (intrinsicAbstractBase K) S hSB) :=
        D.frobeniusFixedField_finite
          KR (Eᵢ).field (Eᵢ).below sigma
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x) =
        relativeNorm
          (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) S hSB pi) :
    concreteNormResidueSymbolOfEmbedding K L i D v hcf x =
      Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q) := by
  dsimp only at hx
  let BK := intrinsicFiniteAbstractBase K
  let hEfinite : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below) :=
    (Eᵢ).finite
  let hBKEfinite : Finite (BK.field.toSubgroup ⧸
      extensionSubgroup BK.field (Eᵢ).field (Eᵢ).below) := by
    change Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below)
    exact hEfinite
  let KR := BK.toFiniteResidueAbstractField D
  let S := D.frobeniusFixedField KR (Eᵢ).field (Eᵢ).below sigma
  let hSB := D.frobeniusFixedField_le
    KR (Eᵢ).field (Eᵢ).below sigma
  let hSBfinite : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) S hSB) :=
    D.frobeniusFixedField_finite
      KR (Eᵢ).field (Eᵢ).below sigma
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let a := relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) S hSB pi
  have hbase : e (Additive.ofMul x) = a := by
    simpa only [BK, KR, S, hSB, e, a] using hx
  have hprimeNorm :
      D.finiteReciprocityHom (intrinsicAbsoluteUnits K) v
        (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          BK (Eᵢ).field (Eᵢ).below (Additive.ofMul q) =
        finiteNormClass (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) (Eᵢ).field
          (Eᵢ).below a := by
    simpa only [BK, KR, S, hSB, a] using
      D.finiteReciprocityHom_apply_eq_primeNormClass
        (intrinsicAbsoluteUnits K) v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        BK (Eᵢ).field (Eᵢ).below
        (Additive.ofMul q) sigma hsigma pi hpi
  have hreciprocity :
      D.abstractReciprocityEquiv (intrinsicAbsoluteUnits K) v hcf BK Eᵢ
          (Additive.ofMul (Abelianization.of q)) =
        finiteNormClass (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) (Eᵢ).field
          (Eᵢ).below a := by
    rw [D.abstractReciprocityEquiv_apply_of (intrinsicAbsoluteUnits K) v hcf BK Eᵢ q]
    exact hprimeNorm
  have hnormTransport :
      finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i
          (finiteNormClass (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) (Eᵢ).field
            (Eᵢ).below a) =
        Additive.ofMul (normClass K L x) := by
    rw [← hbase]
    convert
      finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
        K L i x using 1 <;>
      rfl
  have hsource :
      MulEquiv.toAdditive
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L i).abelianizationCongr.symm)
          (Additive.ofMul (Abelianization.of
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q))) =
        Additive.ofMul (Abelianization.of q) := by
    change
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L i).abelianizationCongr.symm
          (Abelianization.of
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q)) =
        Abelianization.of q
    rw [← abelianizationCongr_of
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i) q]
    exact
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).abelianizationCongr.symm_apply_apply _
  have hforward :
      concreteReciprocityAddEquivOfEmbedding K L i D v hcf
          (Additive.ofMul (Abelianization.of
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q))) =
        Additive.ofMul (normClass K L x) := by
    change
      finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i
          (D.abstractReciprocityEquiv (intrinsicAbsoluteUnits K) v hcf BK Eᵢ
            (MulEquiv.toAdditive
              ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                K L i).abelianizationCongr.symm)
              (Additive.ofMul (Abelianization.of
                (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                  K L i q))))) =
        Additive.ofMul (normClass K L x)
    rw [hsource, hreciprocity, hnormTransport]
  change
    (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm
        (normClass K L x) =
      Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q)
  apply (concreteReciprocityEquivOfEmbedding K L i D v hcf).injective
  rw [(concreteReciprocityEquivOfEmbedding K L i D v hcf).apply_symm_apply]
  exact (congrArg Additive.toMul hforward).symm

end LocalClassFieldTheory

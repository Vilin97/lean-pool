/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.Abelianization.Defs
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
/-!
# Restriction naturality in an arbitrary finite abelian tower

The fixed-separable-closure form of finite local reciprocity naturality is
transported here to an arbitrary tower `K ⊂ E ⊂ L`.  The two extensions are
realized compatibly in the chosen separable closure by first embedding `L`
and then restricting that embedding to `E`.  Abstract norm--residue
naturality then becomes the actual restriction homomorphism
`Gal(L/K) → Gal(E/K)`.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

private abbrev towerAbsoluteGalois (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev towerAbsoluteUnits (K : Type) [Field K] :
    Rep ℤ (towerAbsoluteGalois K) :=
  intrinsicAbsoluteUnits K

private abbrev towerAbstractBase (K : Type) [Field K] :
    ClosedSubgroup (towerAbsoluteGalois K) :=
  intrinsicAbstractBase K

private def towerLowerEmbedding
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    E →ₐ[K] SeparableClosure K :=
  iL.comp (IsScalarTower.toAlgHom K E L)

private def towerEmbeddedBaseNormClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    FiniteNormQuotient (towerAbsoluteUnits K) (towerAbstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below :=
  finiteNormClass (towerAbsoluteUnits K) (towerAbstractBase K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul a))

private theorem towerEmbeddedFieldRange_le
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    AlgHom.fieldRange (towerLowerEmbedding K E L iL) ≤
      AlgHom.fieldRange iL := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap E L y, rfl⟩

private theorem towerEmbeddedAbstractExtension_field_le
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsGalois K E] [IsGalois K L]
    (iL : L →ₐ[K] SeparableClosure K) :
    (finiteGaloisAbstractExtensionOfEmbedding K L iL).field.toSubgroup ≤
      (finiteGaloisAbstractExtensionOfEmbedding K E
        (towerLowerEmbedding K E L iL)).field.toSubgroup := by
  change
    (closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange iL)).toSubgroup ≤
    (closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange (towerLowerEmbedding K E L iL))).toSubgroup
  change
    (AlgHom.fieldRange iL).fixingSubgroup ≤
      (AlgHom.fieldRange (towerLowerEmbedding K E L iL)).fixingSubgroup
  exact
    (AlgHom.fieldRange (towerLowerEmbedding K E L iL)).fixingSubgroup_le
      (towerEmbeddedFieldRange_le K E L iL)

private theorem towerRestrict_abstractQuotient_mk
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsGalois K E] [IsGalois K L]
    (iL : L →ₐ[K] SeparableClosure K)
    (sigma : (towerAbstractBase K).toSubgroup) :
    AlgEquiv.restrictNormalHom E
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L iL (QuotientGroup.mk sigma)) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K E (towerLowerEmbedding K E L iL)
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) := by
  let iE := towerLowerEmbedding K E L iL
  apply AlgEquiv.ext
  intro x
  apply iE.injective
  calc
    iE ((AlgEquiv.restrictNormalHom E
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L iL (QuotientGroup.mk sigma))) x) =
        iL ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L iL (QuotientGroup.mk sigma)) (algebraMap E L x)) := by
      change
        iL (algebraMap E L
          ((AlgEquiv.restrictNormalHom E
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
              K L iL (QuotientGroup.mk sigma))) x)) =
          iL ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L iL (QuotientGroup.mk sigma)) (algebraMap E L x))
      exact congrArg iL
        (AlgEquiv.restrictNormal_commutes
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L iL (QuotientGroup.mk sigma)) E x)
    _ = sigma.1 (iL (algebraMap E L x)) := by
      exact
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          K L iL sigma (algebraMap E L x)
    _ = sigma.1 (iE x) := rfl
    _ = iE
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E iE
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))) x) := by
      exact
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          K E iE (Subgroup.inclusion le_rfl sigma) x).symm

private theorem towerRestrict_abstractAbelianization
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (iL : L →ₐ[K] SeparableClosure K)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L iL).extensionQuotient) :
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L/K))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L iL).abelianizationCongr z)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E (towerLowerEmbedding K E L iL)).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            (towerAbstractBase K) (towerAbstractBase K)
            (finiteGaloisAbstractExtensionOfEmbedding
              K E (towerLowerEmbedding K E L iL)).field
            (finiteGaloisAbstractExtensionOfEmbedding K L iL).field
            (finiteGaloisAbstractExtensionOfEmbedding
              K E (towerLowerEmbedding K E L iL)).below
            (finiteGaloisAbstractExtensionOfEmbedding K L iL).below
            le_rfl (towerEmbeddedAbstractExtension_field_le K E L iL) z)) := by
  let B := towerAbstractBase K
  let EE :=
    finiteGaloisAbstractExtensionOfEmbedding K E
      (towerLowerEmbedding K E L iL)
  let EL := finiteGaloisAbstractExtensionOfEmbedding K L iL
  let qE :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      K E (towerLowerEmbedding K E L iL)
  let qL :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L iL
  let : (extensionSubgroup B EE.field EE.below).Normal := EE.normal
  let : (extensionSubgroup B EL.field EL.below).Normal := EL.normal
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  change
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L/K))).symm
          (qL.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EL.field EE.below EL.below le_rfl
            (towerEmbeddedAbstractExtension_field_le K E L iL)
            (Abelianization.of (QuotientGroup.mk sigma))))
  rw [abelianizationCongr_of]
  change
    AlgEquiv.restrictNormalHom E
        (qL (QuotientGroup.mk sigma)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EL.field EE.below EL.below le_rfl
            (towerEmbeddedAbstractExtension_field_le K E L iL)
            (Abelianization.of (QuotientGroup.mk sigma))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk]
  change
    AlgEquiv.restrictNormalHom E
        (qL (QuotientGroup.mk sigma)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))))
  rw [abelianizationCongr_of]
  change
    AlgEquiv.restrictNormalHom E
        (qL (QuotientGroup.mk sigma)) =
      qE (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))
  exact towerRestrict_abstractQuotient_mk K E L iL sigma

/-- Before specializing the local class-formation structures, compatible
embeddings of an arbitrary finite abelian tower identify abstract
norm--residue restriction with the actual Galois restriction map. -/
theorem concreteNormResidueAutomorphism_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (iL : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (towerAbsoluteGalois K))
    (v : ValuationData D (towerAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (towerAbsoluteUnits K))
    (a : Kˣ) :
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L/K))).symm
          (concreteNormResidueSymbolOfEmbedding
            K L iL D v hcf a)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (concreteNormResidueSymbolOfEmbedding
          K E (towerLowerEmbedding K E L iL) D v hcf a) := by
  let B := towerAbstractBase K
  let BF := intrinsicFiniteAbstractBase K
  let EE :=
    finiteGaloisAbstractExtensionOfEmbedding K E
      (towerLowerEmbedding K E L iL)
  let EL := finiteGaloisAbstractExtensionOfEmbedding K L iL
  let qE :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      K E (towerLowerEmbedding K E L iL)
  let qL :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L iL
  let xE :=
    towerEmbeddedBaseNormClass K E
      (towerLowerEmbedding K E L iL) a
  let xL := towerEmbeddedBaseNormClass K L iL a
  have hLE : EL.field.toSubgroup ≤ EE.field.toSubgroup :=
    towerEmbeddedAbstractExtension_field_le K E L iL
  let hEENormal : (extensionSubgroup B EE.field EE.below).Normal :=
    EE.normal
  let hELNormal : (extensionSubgroup B EL.field EL.below).Normal :=
    EL.normal
  let hEEFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below) :=
    EE.finite
  let hELFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EL.field EL.below) :=
    EL.finite
  let hBBFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B B le_rfl) := by
    have htop : extensionSubgroup B B le_rfl = ⊤ := by
      ext sigma
      constructor
      · intro _
        trivial
      · intro _
        exact sigma.2
    rw [htop]
    infer_instance
  let T : FiniteAbstractFieldExtension (towerAbsoluteGalois K) := {
    field := BF
    base := BF
    below := le_rfl
    finiteQuotient := hBBFinite }
  let : (extensionSubgroup T.base.field EE.field EE.below).Normal := by
    change (extensionSubgroup B EE.field EE.below).Normal
    exact hEENormal
  let : (extensionSubgroup T.field.field EL.field EL.below).Normal := by
    change (extensionSubgroup B EL.field EL.below).Normal
    exact hELNormal
  let : Finite
      (T.base.field.toSubgroup ⧸
        extensionSubgroup T.base.field EE.field EE.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below)
    exact hEEFinite
  let : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field EL.field EL.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EL.field EL.below)
    exact hELFinite
  have hnorm : finiteReciprocityNaturalityNormMap (towerAbsoluteUnits K)
        B B EE.field EL.field EE.below EL.below le_rfl hLE xL = xE := by
    dsimp only [xL, xE, towerEmbeddedBaseNormClass]
    rw [finiteReciprocityNaturalityNormMap_finiteNormClass,
      relativeNorm_self]
  have hraw := D.normResidueNaturality_norm_restriction
    (towerAbsoluteUnits K) v hcf
    T EE.field EL.field EE.below EL.below hLE
  have hrawa := DFunLike.congr_fun hraw xL
  change _ =
    D.normResidueSymbol (towerAbsoluteUnits K) v hcf BF EE
      (finiteReciprocityNaturalityNormMap (towerAbsoluteUnits K)
        B B EE.field EL.field EE.below EL.below le_rfl hLE xL) at hrawa
  rw [hnorm] at hrawa
  let zL :=
    D.normResidueSymbol (towerAbsoluteUnits K) v hcf BF EL xL
  let zE :=
    D.normResidueSymbol (towerAbsoluteUnits K) v hcf BF EE xE
  have hz : normResidueNaturalityAbelianizedRestriction
        B B EE.field EL.field EE.below EL.below le_rfl hLE
        (Additive.toMul zL) = Additive.toMul zE := by
    exact congrArg Additive.toMul hrawa
  rw [concreteNormResidueSymbolOfEmbedding_eq_abstract
      K L iL D v hcf a,
    concreteNormResidueSymbolOfEmbedding_eq_abstract
      K E (towerLowerEmbedding K E L iL) D v hcf a]
  change
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L/K))).symm
          (qL.abelianizationCongr (Additive.toMul zL))) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr (Additive.toMul zE))
  calc
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L/K))).symm
          (qL.abelianizationCongr (Additive.toMul zL))) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EL.field EE.below EL.below le_rfl hLE
            (Additive.toMul zL))) :=
      towerRestrict_abstractAbelianization
        K E L iL (Additive.toMul zL)
    _ = (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr (Additive.toMul zE)) :=
      congrArg
        (fun w => (Abelianization.equivOfComm (H := Gal(E/K))).symm
          (qE.abelianizationCongr w)) hz

/-- Pointwise restriction naturality for the canonical local Artin
automorphism in an arbitrary finite abelian tower. -/
theorem localArtinAutomorphism_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (a : Kˣ) :
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L/K))).symm
          (localArtinMonoidHom K L a)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (localArtinMonoidHom K E a) := by
  let iL := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  rw [localArtinMonoidHom_eq_of_embedding K L iL,
    localArtinMonoidHom_eq_of_embedding K E
      (towerLowerEmbedding K E L iL)]
  exact
    concreteNormResidueAutomorphism_restrict_tower
      K E L iL
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) a

/-- The actual finite abelian local Artin maps commute with the genuine
restriction homomorphism in every finite abelian tower `K ⊂ E ⊂ L`. -/
theorem abelianLocalArtinMonoidHom_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L] :
    (AlgEquiv.restrictNormalHom E).comp
        (abelianLocalArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K E := by
  apply MonoidHom.ext
  intro a
  exact localArtinAutomorphism_restrict_tower K E L a

/-- When `L` is regarded as an `M`-algebra through the inverse of a
`K`-algebra equivalence, restriction from `L` to `M` is conjugation by that
equivalence. -/
theorem restrictNormalHom_eq_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) :
    letI : Algebra M L := e.symm.toRingHom.toAlgebra
    letI : IsScalarTower K M L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (e.symm.commutes x).symm)
    (AlgEquiv.restrictNormalHom M :
        Gal(L/K) →* Gal(M/K)) =
      (AlgEquiv.autCongr e).toMonoidHom := by
  let : Algebra M L := e.symm.toRingHom.toAlgebra
  let : IsScalarTower K M L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.symm.commutes x).symm)
  apply MonoidHom.ext
  intro sigma
  apply AlgEquiv.ext
  intro x
  apply e.symm.injective
  calc
    e.symm ((AlgEquiv.restrictNormalHom M sigma) x) =
        sigma (e.symm x) := by
      exact AlgEquiv.restrictNormal_commutes sigma M x
    _ = e.symm ((AlgEquiv.autCongr e sigma) x) := by
      simp [AlgEquiv.autCongr_apply]

/-- Finite local Artin maps are natural under a `K`-algebra equivalence of
finite abelian extensions.  The Galois groups are identified by conjugating
automorphisms with that equivalence. -/
theorem abelianLocalArtinMonoidHom_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    (e : L ≃ₐ[K] M) :
    (AlgEquiv.autCongr e).toMonoidHom.comp
        (abelianLocalArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K M := by
  let : Algebra M L := e.symm.toRingHom.toAlgebra
  let : IsScalarTower K M L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.symm.commutes x).symm)
  rw [← restrictNormalHom_eq_autCongr K L M e]
  exact abelianLocalArtinMonoidHom_restrict_tower K M L

end LocalClassFieldTheory

namespace ClassFieldTheory

/-- Restriction of the canonical Artin map at the upper level is exactly the
canonical Artin map at the lower level of a finite abelian tower. -/
theorem finiteAbelianLocalArtinMap_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (AlgEquiv.restrictNormalHom E).comp
        (LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom =
      (LocalClassFieldTheory.abelianLocalArtinMap K E).toMonoidHom := by
  rw [LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K L,
    LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K E]
  exact LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower K E L

end ClassFieldTheory

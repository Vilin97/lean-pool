/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.Abelianization.Defs
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
/-!
# Restriction naturality for the concrete local norm-residue symbol

The abstract class formation supplies restriction naturality.  This file
constructs the field-facing restriction map for two finite Galois intermediate
fields in the fixed separable closure and transports the naturality identity
to the concrete local norm-residue symbol.

The intermediate-field restriction is packaged here so callers do not have
to install the auxiliary `Algebra E F` and scalar-tower instances attached
to an inclusion `E ≤ F`.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

private abbrev absoluteGalois (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev absoluteUnits (K : Type) [Field K] :
    Rep ℤ (absoluteGalois K) :=
  intrinsicAbsoluteUnits K

private abbrev abstractBase (K : Type) [Field K] :
    ClosedSubgroup (absoluteGalois K) :=
  intrinsicAbstractBase K

section AbstractToConcrete

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The finite abstract norm class represented by a base-field unit in an
explicit separable-closure realization. -/
private def embeddedBaseNormClass
    (i : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    FiniteNormQuotient (absoluteUnits K) (abstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below :=
  finiteNormClass (absoluteUnits K) (abstractBase K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul a))

/-- Before specializing the local datum, the concrete norm-residue symbol is
the abstract norm-residue class transported through the canonical quotient
equivalence.  This pointwise transport formula expresses abstract
restriction naturality as a statement about actual field automorphisms. -/
theorem concreteNormResidueSymbolOfEmbedding_eq_abstract
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (absoluteGalois K))
    (v : ValuationData D (absoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (absoluteUnits K)) (a : Kˣ) :
    concreteNormResidueSymbolOfEmbedding K L i D v hcf a =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).abelianizationCongr
        (Additive.toMul
          (D.normResidueSymbol (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K)
            (finiteGaloisAbstractExtensionOfEmbedding K L i)
            (embeddedBaseNormClass K L i a))) := by
  let Eabs := finiteGaloisAbstractExtensionOfEmbedding K L i
  let q := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
  let xabs := embeddedBaseNormClass K L i a
  let z := D.normResidueSymbol (absoluteUnits K) v hcf
    (intrinsicFiniteAbstractBase K) Eabs xabs
  have hnorm :
      finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i xabs =
        Additive.ofMul
          (normClass K L a) := by
    convert
      finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
        K L i a using 1 <;> rfl
  have hsource :
      MulEquiv.toAdditive q.abelianizationCongr.symm
          (Additive.ofMul (q.abelianizationCongr (Additive.toMul z))) = z := by
    apply Additive.toMul.injective
    exact q.abelianizationCongr.symm_apply_apply (Additive.toMul z)
  have hforward :
      concreteReciprocityAddEquivOfEmbedding K L i D v hcf
          (Additive.ofMul (q.abelianizationCongr (Additive.toMul z))) =
        Additive.ofMul
          (normClass K L a) := by
    change finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (D.abstractReciprocityEquiv (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs
          (MulEquiv.toAdditive q.abelianizationCongr.symm
            (Additive.ofMul
              (q.abelianizationCongr (Additive.toMul z))))) = _
    rw [hsource]
    change finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (D.abstractReciprocityEquiv (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs
          ((D.abstractReciprocityEquiv
            (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs).symm xabs)) = _
    rw [(D.abstractReciprocityEquiv
      (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs).apply_symm_apply,
      hnorm]
  change (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm
      (normClass K L a) =
    q.abelianizationCongr (Additive.toMul z)
  apply (concreteReciprocityEquivOfEmbedding K L i D v hcf).injective
  rw [(concreteReciprocityEquivOfEmbedding
    K L i D v hcf).apply_symm_apply]
  exact (congrArg Additive.toMul hforward).symm

end AbstractToConcrete

section IntermediateRestriction

variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem commGroup_abelianizationCongr_of
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) :
    (Abelianization.equivOfComm (H := H)).symm
        (q.abelianizationCongr (Abelianization.of x)) =
      q x := by
  exact
    (congrArg (Abelianization.equivOfComm (H := H)).symm
      (abelianizationCongr_of q x)).trans
      ((Abelianization.equivOfComm (H := H)).symm_apply_apply (q x))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem intermediateFieldRestrict_abstractQuotient_mk
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F]
    (sigma : (abstractBase K).toSubgroup) :
    intermediateFieldRestrictNormalHom E F hEF
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
          (QuotientGroup.mk sigma)) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) := by
  apply AlgEquiv.ext
  intro x
  apply E.val.injective
  calc
    E.val ((intermediateFieldRestrictNormalHom E F hEF)
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
          (QuotientGroup.mk sigma)) x) =
      F.val
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
            (QuotientGroup.mk sigma))
          (IntermediateField.inclusion hEF x)) :=
            intermediateFieldRestrictNormalHom_apply_val E F hEF _ x
    _ = sigma.1 (F.val (IntermediateField.inclusion hEF x)) := by
      exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
        K F F.val sigma (IntermediateField.inclusion hEF x)
    _ = (Subgroup.inclusion le_rfl sigma).1 (E.val x) := rfl
    _ = E.val
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))) x) := by
      exact (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
        K E E.val (Subgroup.inclusion le_rfl sigma) x).symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedAbstractExtension_field_le
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F] :
    (finiteGaloisAbstractExtensionOfEmbedding K F F.val).field.toSubgroup ≤
      (finiteGaloisAbstractExtensionOfEmbedding K E E.val).field.toSubgroup := by
  change
    (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange F.val)).toSubgroup ≤
      (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange E.val)).toSubgroup
  simp only [IntermediateField.fieldRange_val]
  change F.fixingSubgroup ≤ E.fixingSubgroup
  exact E.fixingSubgroup_le hEF

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem intermediateFieldRestrict_abstractAbelianization_of_mk
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (sigma : (abstractBase K).toSubgroup) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := Gal(F/K))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K F F.val).abelianizationCongr
              (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E E.val).abelianizationCongr
            (normResidueNaturalityAbelianizedRestriction
              (abstractBase K) (abstractBase K)
              (finiteGaloisAbstractExtensionOfEmbedding K E E.val).field
              (finiteGaloisAbstractExtensionOfEmbedding K F F.val).field
              (finiteGaloisAbstractExtensionOfEmbedding K E E.val).below
              (finiteGaloisAbstractExtensionOfEmbedding K F F.val).below
              le_rfl (embeddedAbstractExtension_field_le K E F hEF)
              (Abelianization.of (QuotientGroup.mk sigma)))) := by
  let B := abstractBase K
  let EE := finiteGaloisAbstractExtensionOfEmbedding K E E.val
  let EF := finiteGaloisAbstractExtensionOfEmbedding K F F.val
  let qE := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
  let qF := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
  have hrestriction :
      normResidueNaturalityAbelianizedRestriction
          B B EE.field EF.field EE.below EF.below le_rfl
          (embeddedAbstractExtension_field_le K E F hEF)
          (Abelianization.of (QuotientGroup.mk sigma)) =
        Abelianization.of
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) :=
    normResidueNaturalityAbelianizedRestriction_of_mk
      B B EE.field EF.field EE.below EF.below le_rfl
      (embeddedAbstractExtension_field_le K E F hEF) sigma
  calc
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := Gal(F/K))).symm
          (qF.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      intermediateFieldRestrictNormalHom E F hEF
        (qF (QuotientGroup.mk sigma)) :=
      congrArg (intermediateFieldRestrictNormalHom E F hEF)
        (commGroup_abelianizationCongr_of
          qF (QuotientGroup.mk sigma))
    _ = qE (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) :=
      intermediateFieldRestrict_abstractQuotient_mk K E F hEF sigma
    _ = (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)))) :=
      (commGroup_abelianizationCongr_of qE
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))).symm
    _ = (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field EE.below EF.below le_rfl
            (embeddedAbstractExtension_field_le K E F hEF)
            (Abelianization.of (QuotientGroup.mk sigma)))) :=
      congrArg
        (fun w => (Abelianization.equivOfComm
          (H := Gal(E/K))).symm (qE.abelianizationCongr w))
        hrestriction.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem intermediateFieldRestrict_abstractAbelianization
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K F F.val).extensionQuotient) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := Gal(F/K))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val).abelianizationCongr
            z)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            (abstractBase K) (abstractBase K)
            (finiteGaloisAbstractExtensionOfEmbedding K E E.val).field
            (finiteGaloisAbstractExtensionOfEmbedding K F F.val).field
            (finiteGaloisAbstractExtensionOfEmbedding K E E.val).below
            (finiteGaloisAbstractExtensionOfEmbedding K F F.val).below
            le_rfl (embeddedAbstractExtension_field_le K E F hEF) z)) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  exact
    intermediateFieldRestrict_abstractAbelianization_of_mk
      K E F hEF sigma

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Restriction naturality for the concrete norm-residue symbol, before
specializing the three structures of the local class formation.  Both
extensions are literal intermediate fields of the fixed separable closure,
so the vertical Galois map is the actual restriction map above. -/
theorem concreteNormResidueAutomorphism_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (D : DegreeData (absoluteGalois K))
    (v : ValuationData D (absoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (absoluteUnits K)) (a : Kˣ) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := Gal(F/K))).symm
          (concreteNormResidueSymbolOfEmbedding
            K F F.val D v hcf a)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (concreteNormResidueSymbolOfEmbedding
          K E E.val D v hcf a) := by
  let B := abstractBase K
  let BF := intrinsicFiniteAbstractBase K
  let EE := finiteGaloisAbstractExtensionOfEmbedding K E E.val
  let EF := finiteGaloisAbstractExtensionOfEmbedding K F F.val
  let qE := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
  let qF := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
  let xE := embeddedBaseNormClass K E E.val a
  let xF := embeddedBaseNormClass K F F.val a
  have hFE : EF.field.toSubgroup ≤ EE.field.toSubgroup :=
    embeddedAbstractExtension_field_le K E F hEF
  let hEENormal : (extensionSubgroup B EE.field EE.below).Normal :=
    EE.normal
  let hEFNormal : (extensionSubgroup B EF.field EF.below).Normal :=
    EF.normal
  let hEEFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below) :=
    EE.finite
  let hEFFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EF.field EF.below) :=
    EF.finite
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
  let T : FiniteAbstractFieldExtension (absoluteGalois K) := {
    field := BF
    base := BF
    below := le_rfl
    finiteQuotient := hBBFinite }
  let : (extensionSubgroup T.base.field EE.field EE.below).Normal := by
    change (extensionSubgroup B EE.field EE.below).Normal
    exact hEENormal
  let : (extensionSubgroup T.field.field EF.field EF.below).Normal := by
    change (extensionSubgroup B EF.field EF.below).Normal
    exact hEFNormal
  let : Finite
      (T.base.field.toSubgroup ⧸
        extensionSubgroup T.base.field EE.field EE.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below)
    exact hEEFinite
  let : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field EF.field EF.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EF.field EF.below)
    exact hEFFinite
  have hnorm : finiteReciprocityNaturalityNormMap (absoluteUnits K)
        B B EE.field EF.field EE.below EF.below le_rfl hFE xF = xE := by
    let aB := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul a)
    have hmap := finiteReciprocityNaturalityNormMap_finiteNormClass
      (absoluteUnits K) B B EE.field EF.field EE.below EF.below le_rfl hFE aB
    exact hmap.trans (congrArg
      (finiteNormClass (absoluteUnits K) B EE.field EE.below)
      (relativeNorm_self (absoluteUnits K) B aB))
  have hraw := D.normResidueNaturality_norm_restriction
    (absoluteUnits K) v hcf
    T EE.field EF.field EE.below EF.below hFE
  have hrawa := DFunLike.congr_fun hraw xF
  change _ =
    D.normResidueSymbol (absoluteUnits K) v hcf BF EE
      (finiteReciprocityNaturalityNormMap (absoluteUnits K) B B EE.field EF.field EE.below
        EF.below le_rfl hFE xF) at hrawa
  rw [hnorm] at hrawa
  let zF := D.normResidueSymbol (absoluteUnits K) v hcf BF EF xF
  let zE := D.normResidueSymbol (absoluteUnits K) v hcf BF EE xE
  have hz : normResidueNaturalityAbelianizedRestriction
        B B EE.field EF.field EE.below EF.below le_rfl hFE
        (Additive.toMul zF) = Additive.toMul zE := by
    exact congrArg Additive.toMul hrawa
  rw [concreteNormResidueSymbolOfEmbedding_eq_abstract
      K F F.val D v hcf a,
    concreteNormResidueSymbolOfEmbedding_eq_abstract
      K E E.val D v hcf a]
  change intermediateFieldRestrictNormalHom E F hEF
      ((Abelianization.equivOfComm (H := Gal(F/K))).symm
        (qF.abelianizationCongr (Additive.toMul zF))) =
    (Abelianization.equivOfComm (H := Gal(E/K))).symm
      (qE.abelianizationCongr (Additive.toMul zE))
  calc
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := Gal(F/K))).symm
          (qF.abelianizationCongr (Additive.toMul zF))) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field EE.below EF.below le_rfl hFE
            (Additive.toMul zF))) :=
      intermediateFieldRestrict_abstractAbelianization
        K E F hEF (Additive.toMul zF)
    _ = (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (qE.abelianizationCongr (Additive.toMul zE)) :=
      congrArg
        (fun w => (Abelianization.equivOfComm
          (H := Gal(E/K))).symm (qE.abelianizationCongr w)) hz

/-- Restriction naturality for the canonical local norm-residue symbol,
expressed through automorphisms of finite abelian intermediate fields. -/
theorem localArtinAutomorphism_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] (a : Kˣ) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := Gal(F/K))).symm
          (localArtinMonoidHom K F a)) =
      (Abelianization.equivOfComm (H := Gal(E/K))).symm
        (localArtinMonoidHom K E a) := by
  rw [localArtinMonoidHom_eq_of_embedding K F F.val,
    localArtinMonoidHom_eq_of_embedding K E E.val]
  exact concreteNormResidueAutomorphism_restrict
    K E F hEF
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K) a

end IntermediateRestriction

end LocalClassFieldTheory

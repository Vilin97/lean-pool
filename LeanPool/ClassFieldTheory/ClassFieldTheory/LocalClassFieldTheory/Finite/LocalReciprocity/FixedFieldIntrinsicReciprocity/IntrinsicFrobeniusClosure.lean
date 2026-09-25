/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusQuotientTransport
/-!
# Intrinsic Frobenius closure comparison

This module compares the intrinsic and ambient Frobenius closures after
the quotient transport has been constructed.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Membership in the intrinsic Frobenius closure, expressed either with the
residue datum's carrier or with the canonical fixed-field quotient. -/
theorem intrinsicFixedFieldFrobeniusClosure_mem_iff
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    let E := abstractRelativeFixedField K (SeparableClosure K) hJH
    letI : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField F :=
      finiteExtensionSpectralNormedField K F
    letI : ValuativeRel F :=
      finiteExtensionSpectralValuativeRel K F
    letI : IsNonarchimedeanLocalField F :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K F
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        K (SeparableClosure K) H.field J hJH H.finite hJfinite
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        K (SeparableClosure K) H.field J hJH hJnormal
    let i : E →ₐ[F] SeparableClosure F :=
      e.symm.toAlgHom.comp E.val
    let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
    let RF :=
      (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)
    ∀ τ : (intrinsicAbstractBase F).toSubgroup,
      let τRF : RF.field.toSubgroup :=
        ⟨τ.1, by
          simpa only [RF, intrinsicFiniteAbstractBase,
            FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
      QuotientGroup.mk τRF ∈
          ((localResidueDatum F).frobeniusClosure
            RF EI.field EI.below σ).toSubgroup ↔
        (QuotientGroup.mk τ :
            intrinsicFixedFieldFrobeniusQuotient K H J hJH e) ∈
          (closedSubgroupGenerated
            ({σ.1} : Set
              (intrinsicFixedFieldFrobeniusQuotient
                K H J hJH e)) : Subgroup _) := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J hJH H.finite hJfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J hJH hJnormal
  let i : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp E.val
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  intro τ
  let τRF : RF.field.toSubgroup :=
    ⟨τ.1, by
      simpa only [RF, intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
  constructor
  · intro h
    convert h using 1
    all_goals
      simp only [DegreeData.frobeniusClosure, Set.range_unique,
        intrinsicFixedFieldFrobeniusQuotient,
        intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField]
  · intro h
    convert h using 1
    all_goals
      simp only [DegreeData.frobeniusClosure, Set.range_unique,
        intrinsicFixedFieldFrobeniusQuotient,
        intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField]

/-- Membership in the ambient Frobenius closure, expressed either with the
residue datum's carrier or with the canonical ambient quotient. -/
theorem ambientFixedFieldFrobeniusClosure_mem_iff
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    let E := abstractRelativeFixedField K (SeparableClosure K) hJH
    letI : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField F :=
      finiteExtensionSpectralNormedField K F
    letI : ValuativeRel F :=
      finiteExtensionSpectralValuativeRel K F
    letI : IsNonarchimedeanLocalField F :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K F
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        K (SeparableClosure K) H.field J hJH H.finite hJfinite
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        K (SeparableClosure K) H.field J hJH hJnormal
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    let ψ := intrinsicBaseEquivAmbientFixedField K H e
    ∀ τ : (intrinsicAbstractBase F).toSubgroup,
      let ψτRH : RH.field.toSubgroup :=
        ⟨(ψ τ).1, by
          simpa only [RH,
            FiniteAbstractField.toFiniteResidueAbstractField] using
              (ψ τ).2⟩
      QuotientGroup.mk ψτRH ∈
          ((localResidueDatum K).frobeniusClosure
            RH J hJH σH).toSubgroup ↔
        (QuotientGroup.mk (ψ τ) :
            ambientFixedFieldFrobeniusQuotient K H J hJH) ∈
          (closedSubgroupGenerated
            ({σH.1} : Set
              (ambientFixedFieldFrobeniusQuotient
                K H J hJH)) : Subgroup _) := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J hJH H.finite hJfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J hJH hJnormal
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  intro τ
  let ψτRH : RH.field.toSubgroup :=
    ⟨(ψ τ).1, by
      simpa only [RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
          (ψ τ).2⟩
  constructor
  · intro h
    simpa only [DegreeData.frobeniusClosure, Set.range_unique,
      ambientFixedFieldFrobeniusQuotient,
      FiniteAbstractField.toFiniteResidueAbstractField] using h
  · intro h
    simpa only [DegreeData.frobeniusClosure, Set.range_unique,
      ambientFixedFieldFrobeniusQuotient,
      FiniteAbstractField.toFiniteResidueAbstractField] using h

/-- The canonical fixed-field quotient equivalence maps the intrinsic
Frobenius closure into the ambient Frobenius closure. -/
theorem intrinsicFixedFieldFrobeniusClosure_le_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)
    (q : intrinsicFixedFieldFrobeniusQuotient K H J hJH e)
    (hq : q ∈
      (closedSubgroupGenerated
        ({σ.1} : Set
          (intrinsicFixedFieldFrobeniusQuotient
            K H J hJH e)) : Subgroup _)) :
    intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
        K H J hJH e q ∈
      (closedSubgroupGenerated
        ({(intrinsicFrobeniusElementToAmbientFixedField
            K H J hJH e σ).1} : Set
          (ambientFixedFieldFrobeniusQuotient
            K H J hJH)) : Subgroup _) := by
  let ξ :=
    intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
      K H J hJH e
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  let ξHom :=
    ContinuousMonoidHom.toContinuousMonoidHom ξ
  have hmap :=
    map_mem_closedSubgroupGenerated_singleton
      ξHom σ.1 hq
  change
    ξ q ∈
      (closedSubgroupGenerated
        ({ξ σ.1} : Set
          (ambientFixedFieldFrobeniusQuotient
            K H J hJH)) : Subgroup _) at hmap
  have hξσ : ξ σ.1 = σH.1 :=
    (intrinsicFrobeniusElementToAmbientFixedField_val
      K H J hJH e σ).symm
  simpa only [hξσ] using hmap

/-- A continuous multiplicative equivalence reflects membership in the closed
subgroup generated by a singleton, after identifying both the generator and
the tested element. -/
theorem
    continuousMulEquiv_preimage_mem_closedSubgroupGenerated_singleton_of_eq
    {G₁ G₂ : Type*}
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    (ξ : G₁ ≃ₜ* G₂) (x q : G₁) (x' q' : G₂)
    (hx : ξ x = x') (hq : ξ q = q')
    (h : q' ∈
      (closedSubgroupGenerated ({x'} : Set G₂) : Subgroup G₂)) :
    q ∈
      (closedSubgroupGenerated ({x} : Set G₁) : Subgroup G₁) := by
  subst x'
  subst q'
  have hmap :=
    map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom ξ.symm)
      (ξ x) h
  change
    ξ.symm (ξ q) ∈
      (closedSubgroupGenerated
        ({ξ.symm (ξ x)} : Set G₁) : Subgroup G₁) at hmap
  simpa only [ξ.symm_apply_apply] using hmap

/-- The canonical fixed-field quotient equivalence pulls the ambient
Frobenius closure back into the intrinsic Frobenius closure. -/
theorem ambientFixedFieldFrobeniusClosure_le_intrinsicFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)
    (q : intrinsicFixedFieldFrobeniusQuotient K H J hJH e)
    (hq :
      intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
          K H J hJH e q ∈
        (closedSubgroupGenerated
          ({(intrinsicFrobeniusElementToAmbientFixedField
              K H J hJH e σ).1} : Set
            (ambientFixedFieldFrobeniusQuotient
              K H J hJH)) : Subgroup _)) :
    q ∈
      (closedSubgroupGenerated
        ({σ.1} : Set _) : Subgroup _) := by
  let ξ :=
    intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
      K H J hJH e
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  have hξσ : ξ σ.1 = σH.1 :=
    (intrinsicFrobeniusElementToAmbientFixedField_val
      K H J hJH e σ).symm
  have hξq : ξ q = ξ q := rfl
  exact
    continuousMulEquiv_preimage_mem_closedSubgroupGenerated_singleton_of_eq
      ξ σ.1 q σH.1 (ξ q) hξσ hξq hq

/-- The canonical fixed-field quotient equivalence identifies the intrinsic
and ambient Frobenius closures. -/
theorem intrinsicFrobeniusClosure_iff_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)
    (q : intrinsicFixedFieldFrobeniusQuotient K H J hJH e) :
    q ∈
        (closedSubgroupGenerated
          ({σ.1} : Set
            (intrinsicFixedFieldFrobeniusQuotient
              K H J hJH e)) : Subgroup _) ↔
      intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
          K H J hJH e q ∈
        (closedSubgroupGenerated
          ({(intrinsicFrobeniusElementToAmbientFixedField
              K H J hJH e σ).1} : Set
            (ambientFixedFieldFrobeniusQuotient
              K H J hJH)) : Subgroup _) := by
  exact
    ⟨intrinsicFixedFieldFrobeniusClosure_le_ambientFixedField
        K H J hJH e σ q,
      ambientFixedFieldFrobeniusClosure_le_intrinsicFixedField
        K H J hJH e σ q⟩

end LocalClassFieldTheory

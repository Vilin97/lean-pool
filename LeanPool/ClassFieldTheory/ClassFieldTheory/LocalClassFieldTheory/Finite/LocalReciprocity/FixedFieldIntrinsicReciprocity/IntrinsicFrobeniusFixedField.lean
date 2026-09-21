/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusClosure
/-!
# Intrinsic Frobenius fixed-field transport

This module transports Frobenius-fixed subgroups and fixed fields through
the intrinsic-to-ambient closure equivalence.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Intrinsic Frobenius-fixed elements map to ambient Frobenius-fixed
elements under the fixed-field Galois-group equivalence. -/
theorem intrinsicFrobeniusFixedSubgroup_le_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    ∀ τ : (intrinsicAbstractBase F).toSubgroup,
      let τRF : RF.field.toSubgroup :=
        ⟨τ.1, by
          simpa only [RF, intrinsicFiniteAbstractBase,
            FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
      let ψ := intrinsicBaseEquivAmbientFixedField K H e
      let ψτRH : RH.field.toSubgroup :=
        ⟨(ψ τ).1, by
          simpa only [RH,
            FiniteAbstractField.toFiniteResidueAbstractField] using
              (ψ τ).2⟩
      τRF ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
          RF EI.field EI.below σ →
        ψτRH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
          RH J hJH σH := by
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
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  intro τ
  let τRF : RF.field.toSubgroup :=
    ⟨τ.1, by
      simpa only [RF, intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  let ψτRH : RH.field.toSubgroup :=
    ⟨(ψ τ).1, by
      simpa only [RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
          (ψ τ).2⟩
  intro hτ
  have hτclosureRF :
      QuotientGroup.mk τRF ∈
        ((localResidueDatum F).frobeniusClosure
          RF EI.field EI.below σ).toSubgroup :=
    ((localResidueDatum F).mem_frobeniusFixedSubgroupWithin_iff
      RF EI.field EI.below σ τRF).1 hτ
  let ξ :=
    intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
      K H J hJH e
  let qτ : intrinsicFixedFieldFrobeniusQuotient K H J hJH e :=
    QuotientGroup.mk τ
  let qH : ambientFixedFieldFrobeniusQuotient K H J hJH :=
    QuotientGroup.mk (ψ τ)
  have hτclosure :
      qτ ∈
        (closedSubgroupGenerated
          ({σ.1} : Set
            (intrinsicFixedFieldFrobeniusQuotient
              K H J hJH e)) : Subgroup _) := by
    exact
      (intrinsicFixedFieldFrobeniusClosure_mem_iff
        K H J hJH e σ τ).1 hτclosureRF
  have hξq : ξ qτ = qH := by
    rfl
  have htransport :
      qH ∈
        (closedSubgroupGenerated
          ({σH.1} : Set
            (ambientFixedFieldFrobeniusQuotient
              K H J hJH)) : Subgroup _) := by
    rw [← hξq]
    exact
      intrinsicFixedFieldFrobeniusClosure_le_ambientFixedField
        K H J hJH e σ qτ hτclosure
  have hψclosureRH :
      QuotientGroup.mk ψτRH ∈
          ((localResidueDatum K).frobeniusClosure
            RH J hJH σH).toSubgroup := by
    exact
      (ambientFixedFieldFrobeniusClosure_mem_iff
        K H J hJH e σ τ).2 htransport
  exact
    ((localResidueDatum K).mem_frobeniusFixedSubgroupWithin_iff
      RH J hJH σH ψτRH).2 hψclosureRH

/-- Ambient Frobenius-fixed elements pull back to intrinsic Frobenius-fixed
elements under the fixed-field Galois-group equivalence. -/
theorem ambientFixedFieldFrobeniusFixedSubgroup_le_intrinsic
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    ∀ τ : (intrinsicAbstractBase F).toSubgroup,
      let τRF : RF.field.toSubgroup :=
        ⟨τ.1, by
          simpa only [RF, intrinsicFiniteAbstractBase,
            FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
      let ψ := intrinsicBaseEquivAmbientFixedField K H e
      let ψτRH : RH.field.toSubgroup :=
        ⟨(ψ τ).1, by
          simpa only [RH,
            FiniteAbstractField.toFiniteResidueAbstractField] using
              (ψ τ).2⟩
      ψτRH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
          RH J hJH σH →
        τRF ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
          RF EI.field EI.below σ := by
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
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  intro τ
  let τRF : RF.field.toSubgroup :=
    ⟨τ.1, by
      simpa only [RF, intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  let ψτRH : RH.field.toSubgroup :=
    ⟨(ψ τ).1, by
      simpa only [RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
          (ψ τ).2⟩
  intro hψτ
  have hψclosureRH :
      QuotientGroup.mk ψτRH ∈
        ((localResidueDatum K).frobeniusClosure
          RH J hJH σH).toSubgroup :=
    ((localResidueDatum K).mem_frobeniusFixedSubgroupWithin_iff
      RH J hJH σH ψτRH).1 hψτ
  let ξ :=
    intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
      K H J hJH e
  let qτ : intrinsicFixedFieldFrobeniusQuotient K H J hJH e :=
    QuotientGroup.mk τ
  let qH : ambientFixedFieldFrobeniusQuotient K H J hJH :=
    QuotientGroup.mk (ψ τ)
  have hqHclosure :
      qH ∈
        (closedSubgroupGenerated
          ({σH.1} : Set
            (ambientFixedFieldFrobeniusQuotient
              K H J hJH)) : Subgroup _) := by
    exact
      (ambientFixedFieldFrobeniusClosure_mem_iff
        K H J hJH e σ τ).1 hψclosureRH
  have hξq : ξ qτ = qH := by
    rfl
  have hqHclosure' :
      ξ qτ ∈
        (closedSubgroupGenerated
          ({σH.1} : Set
            (ambientFixedFieldFrobeniusQuotient
              K H J hJH)) : Subgroup _) := by
    rw [hξq]
    exact hqHclosure
  have htransport :
      qτ ∈
        (closedSubgroupGenerated
          ({σ.1} : Set
            (intrinsicFixedFieldFrobeniusQuotient
              K H J hJH e)) : Subgroup _) := by
    exact
      ambientFixedFieldFrobeniusClosure_le_intrinsicFixedField
        K H J hJH e σ qτ hqHclosure'
  have hτclosureRF :
      QuotientGroup.mk τRF ∈
          ((localResidueDatum F).frobeniusClosure
            RF EI.field EI.below σ).toSubgroup := by
    exact
      (intrinsicFixedFieldFrobeniusClosure_mem_iff
        K H J hJH e σ τ).2 htransport
  exact
    ((localResidueDatum F).mem_frobeniusFixedSubgroupWithin_iff
      RF EI.field EI.below σ τRF).2 hτclosureRF

/-- The image of the intrinsic Frobenius fixed field is contained in the
ambient Frobenius fixed field. -/
theorem map_intrinsicFrobeniusFixedField_le_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    let SF :=
      (localResidueDatum F).frobeniusFixedField
        RF EI.field EI.below σ
    let SH :=
      (localResidueDatum K).frobeniusFixedField
        RH J hJH σH
    let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
      simpa only [SH, RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        (localResidueDatum K).frobeniusFixedField_le
          RH J hJH σH
    (abstractFixedField F (SeparableClosure F) SF).map e.toAlgHom ≤
      abstractRelativeFixedField K (SeparableClosure K) hSHH := by
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
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below σ
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J hJH σH
  let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
    simpa only [SH, RH,
      FiniteAbstractField.toFiniteResidueAbstractField] using
      (localResidueDatum K).frobeniusFixedField_le
        RH J hJH σH
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  intro x hx
  rw [IntermediateField.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩
  change e y ∈ IntermediateField.fixedField SH.toSubgroup
  rw [IntermediateField.mem_fixedField_iff]
  intro ρ hρ
  let ρH : H.field.toSubgroup := ⟨ρ, hSHH hρ⟩
  let ρRH : RH.field.toSubgroup :=
    ⟨ρ, by
      simpa only [RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
          hSHH hρ⟩
  have hρinternalRH :
      ρRH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
        RH J hJH σH := by
    rcases
        ((localResidueDatum K).mem_frobeniusFixedField_iff
          RH J hJH σH ρ).1 hρ with
      ⟨k, hk, hkρ⟩
    have hkeq : k = ρRH := by
      apply Subtype.ext
      exact hkρ
    simpa only [hkeq] using hk
  let τ :
      (intrinsicAbstractBase F).toSubgroup :=
    ψ.symm ρH
  have hψ : ψ τ = ρH :=
    ψ.apply_symm_apply ρH
  let τRF : RF.field.toSubgroup :=
    ⟨τ.1, by
      simpa only [RF, intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
  let ψτRH : RH.field.toSubgroup :=
    ⟨(ψ τ).1, by
      simpa only [RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
          (ψ τ).2⟩
  have hψτRH : ψτRH = ρRH := by
    apply Subtype.ext
    exact congrArg Subtype.val hψ
  have hψinternalRH :
      ψτRH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
        RH J hJH σH := by
    rw [hψτRH]
    exact hρinternalRH
  have hτinternalRF :
      τRF ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
        RF EI.field EI.below σ :=
    ambientFixedFieldFrobeniusFixedSubgroup_le_intrinsic
      K H J hJH e σ τ hψinternalRH
  have hτSF : τ.1 ∈ SF.toSubgroup := by
    exact
      ((localResidueDatum F).mem_frobeniusFixedField_iff
        RF EI.field EI.below σ τ.1).2
          ⟨τRF, hτinternalRF, rfl⟩
  have hyfix : τ.1 y = y :=
    (IntermediateField.mem_fixedField_iff SF.toSubgroup y).1
      hy τ.1 hτSF
  have hρeq : (ψ τ).1 = ρ :=
    congrArg Subtype.val hψ
  calc
    ρ (e y) = (ψ τ).1 (e y) := by rw [hρeq]
    _ = e (τ.1 y) := by
      change e (τ.1 (e.symm (e y))) = e (τ.1 y)
      exact
        congrArg (fun z => e (τ.1 z))
          (e.symm_apply_apply y)
    _ = e y := congrArg e hyfix
/-- The ambient Frobenius fixed field is contained in the image of the
intrinsic Frobenius fixed field. -/
theorem ambientFixedField_le_map_intrinsicFrobeniusFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    let SF :=
      (localResidueDatum F).frobeniusFixedField
        RF EI.field EI.below σ
    let SH :=
      (localResidueDatum K).frobeniusFixedField
        RH J hJH σH
    let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
      simpa only [SH, RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        (localResidueDatum K).frobeniusFixedField_le
          RH J hJH σH
    abstractRelativeFixedField K (SeparableClosure K) hSHH ≤
      (abstractFixedField F (SeparableClosure F) SF).map e.toAlgHom := by
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
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below σ
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J hJH σH
  let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
    simpa only [SH, RH,
      FiniteAbstractField.toFiniteResidueAbstractField] using
      (localResidueDatum K).frobeniusFixedField_le
        RH J hJH σH
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  intro x hx
  change
    ∃ y ∈ abstractFixedField F (SeparableClosure F) SF,
      e y = x
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  change e.symm x ∈ IntermediateField.fixedField SF.toSubgroup
  refine
    (IntermediateField.mem_fixedField_iff
      SF.toSubgroup (e.symm x)).2 ?_
  intro τ₀ hτ₀
  let τ :
      (intrinsicAbstractBase F).toSubgroup :=
    (intrinsicAbstractBaseEquivAbsolute F).symm τ₀
  let τRF : RF.field.toSubgroup :=
    ⟨τ.1, by
      simpa only [RF, intrinsicFiniteAbstractBase,
        FiniteAbstractField.toFiniteResidueAbstractField] using τ.2⟩
  have hτinternalRF :
      τRF ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
        RF EI.field EI.below σ := by
    have hτSF : τRF.1 ∈ SF.toSubgroup := by
      simpa only [τRF, τ,
        intrinsicAbstractBaseEquivAbsolute_symm_apply_val] using hτ₀
    have hτsub :
        τRF ∈ extensionSubgroup RF.field
          ((localResidueDatum F).frobeniusFixedField
            RF EI.field EI.below σ)
          ((localResidueDatum F).frobeniusFixedField_le
            RF EI.field EI.below σ) := hτSF
    simpa only [(localResidueDatum F).extensionSubgroup_frobeniusFixedField
      RF EI.field EI.below σ] using hτsub
  let ρRH : RH.field.toSubgroup :=
    ⟨(ψ τ).1, by
      simpa only [RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
          (ψ τ).2⟩
  have hρinternalRH :
      ρRH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
        RH J hJH σH := by
    exact
      intrinsicFrobeniusFixedSubgroup_le_ambientFixedField
        K H J hJH e σ τ hτinternalRF
  have hρSH : (ψ τ).1 ∈ SH.toSubgroup := by
    exact
      ((localResidueDatum K).mem_frobeniusFixedField_iff
        RH J hJH σH ρRH.1).2
          ⟨ρRH, hρinternalRH, rfl⟩
  have hxfix : (ψ τ).1 x = x :=
    (IntermediateField.mem_fixedField_iff SH.toSubgroup x).1
      hx (ψ τ).1 hρSH
  apply e.injective
  calc
    e (τ₀ (e.symm x)) = e (τ.1 (e.symm x)) := by
      simp only [τ,
        intrinsicAbstractBaseEquivAbsolute_symm_apply_val]
    _ = (ψ τ).1 x := by
      change e (τ.1 (e.symm x)) =
        e (τ.1 (e.symm x))
      rfl
    _ = x := hxfix
    _ = e (e.symm x) := (e.apply_symm_apply x).symm

/-- The image of the intrinsic Frobenius fixed field is exactly the ambient
Frobenius fixed field. -/
theorem map_intrinsicFrobeniusFixedField_eq_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    let SF :=
      (localResidueDatum F).frobeniusFixedField
        RF EI.field EI.below σ
    let SH :=
      (localResidueDatum K).frobeniusFixedField
        RH J hJH σH
    let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
      simpa only [SH, RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        (localResidueDatum K).frobeniusFixedField_le
          RH J hJH σH
    (abstractFixedField F (SeparableClosure F) SF).map e.toAlgHom =
      abstractRelativeFixedField K (SeparableClosure K) hSHH := by
  exact le_antisymm
    (map_intrinsicFrobeniusFixedField_le_ambientFixedField
      K H J hJH e σ)
    (ambientFixedField_le_map_intrinsicFrobeniusFixedField
      K H J hJH e σ)

/-- The intrinsic Frobenius fixed field is canonically equivalent, over the
intrinsic base field, to the corresponding ambient Frobenius fixed field. -/
noncomputable def
    intrinsicFrobeniusFixedFieldEquivAmbientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    let SF :=
      (localResidueDatum F).frobeniusFixedField
        RF EI.field EI.below σ
    let SH :=
      (localResidueDatum K).frobeniusFixedField
        RH J hJH σH
    let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
      simpa only [SH, RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        (localResidueDatum K).frobeniusFixedField_le
          RH J hJH σH
    @AlgEquiv F
      (abstractFixedField F (SeparableClosure F) SF)
      (abstractRelativeFixedField K (SeparableClosure K) hSHH)
      _ _ _
      (abstractFixedField F (SeparableClosure F) SF).algebra
      (abstractRelativeFixedField K (SeparableClosure K) hSHH).algebra := by
  dsimp only
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
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below σ
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J hJH σH
  let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
    simpa only [SH, RH,
      FiniteAbstractField.toFiniteResidueAbstractField] using
      (localResidueDatum K).frobeniusFixedField_le
        RH J hJH σH
  let SFI := abstractFixedField F (SeparableClosure F) SF
  let SHI := abstractRelativeFixedField K (SeparableClosure K) hSHH
  let eSF :
      @AlgEquiv F SFI (SFI.map e.toAlgHom)
        _ _ _ SFI.algebra (SFI.map e.toAlgHom).algebra :=
    IntermediateField.equivMap SFI e.toAlgHom
  let eMap :
      @AlgEquiv F (SFI.map e.toAlgHom) SHI
        _ _ _ (SFI.map e.toAlgHom).algebra SHI.algebra :=
    IntermediateField.equivOfEq
      (map_intrinsicFrobeniusFixedField_eq_ambientFixedField
        K H J hJH e σ)
  exact
    @AlgEquiv.trans F SFI (SFI.map e.toAlgHom) SHI
      _ _ _ _
      SFI.algebra
      (SFI.map e.toAlgHom).algebra
      SHI.algebra
      eSF eMap

/-- On underlying elements, the canonical Frobenius fixed-field equivalence
is the restriction of the chosen separable-closure equivalence. -/
@[simp]
theorem
    intrinsicFrobeniusFixedFieldEquivAmbientFixedField_apply_val
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)
    (x :
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
      let SF :=
        (localResidueDatum F).frobeniusFixedField
          RF EI.field EI.below σ
      abstractFixedField F (SeparableClosure F) SF) :
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
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let σH :=
      intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ
    let _SF :=
      (localResidueDatum F).frobeniusFixedField
        RF EI.field EI.below σ
    let SH :=
      (localResidueDatum K).frobeniusFixedField
        RH J hJH σH
    let hSHH : SH.toSubgroup ≤ H.field.toSubgroup := by
      simpa only [SH, RH,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        (localResidueDatum K).frobeniusFixedField_le
          RH J hJH σH
    ((intrinsicFrobeniusFixedFieldEquivAmbientFixedField
      K H J hJH e σ x :
        abstractRelativeFixedField K (SeparableClosure K) hSHH) :
      SeparableClosure K) =
      e (x : SeparableClosure F) := by
  rfl

end LocalClassFieldTheory

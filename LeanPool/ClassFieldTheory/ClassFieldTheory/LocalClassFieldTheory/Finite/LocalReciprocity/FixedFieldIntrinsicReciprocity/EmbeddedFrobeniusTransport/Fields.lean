/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.Groups

/-!
# Embedded Frobenius fixed fields

The transported Frobenius subgroups determine equivalent fixed fields.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

section EmbeddedFrobeniusTransport

variable (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]

/-- Restricting the ambient separable-closure equivalence gives an
`F`-algebra equivalence between the intrinsic and ambient Frobenius fixed
fields. -/
noncomputable def
    intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      letI _hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hSourceFinite : Finite
          ((intrinsicAbstractBase F).toSubgroup ⧸
            extensionSubgroup
              (intrinsicAbstractBase F) EI.field EI.below) :=
        EI.finite
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      letI _hTargetFinite : Finite
          (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
        ambientEmbeddedExtensionQuotient_finite K F E j e
      let RF :=
        (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
          (localResidueDatum F)
      let hHabsolute : Finite
          ((baseField
            Gal(SeparableClosure K/K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K/K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K/K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      ∀ sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below,
        let sigmaH :=
          intrinsicFrobeniusElementToAmbientEmbeddedField
            K F E j e sigma
        let SF :=
          (localResidueDatum F).frobeniusFixedField
            RF EI.field EI.below sigma
        let SH :=
          (localResidueDatum K).frobeniusFixedField
            RH J₀ hJH sigmaH
        let hSHH :=
          (localResidueDatum K).frobeniusFixedField_le
            RH J₀ hJH sigmaH
        let LH :=
          abstractRelativeFixedField K (SeparableClosure K) hSHH
        let iLH : F →ₐ[K] LH :=
          i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
            change
              i x ∈ IntermediateField.fixedField SH.toSubgroup
            rw [IntermediateField.mem_fixedField_iff]
            intro rho hrho
            have hrhoH : rho ∈ H₀.toSubgroup :=
              hSHH hrho
            change rho (i x) = i x
            change
              rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
            rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
            exact hrhoH (i x) ⟨x, rfl⟩)
        letI : Algebra F LH :=
          iLH.toRingHom.toAlgebra
        abstractFixedField F (SeparableClosure F) SF ≃ₐ[F] LH := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K/K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  intro sigma
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J₀ hJH sigmaH
  let hSFB :=
    (localResidueDatum F).frobeniusFixedField_le
      RF EI.field EI.below sigma
  let hSHH :=
    (localResidueDatum K).frobeniusFixedField_le
      RH J₀ hJH sigmaH
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSHH
  let iLH : F →ₐ[K] LH :=
    i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
      change i x ∈ IntermediateField.fixedField SH.toSubgroup
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      have hrhoH : rho ∈ H₀.toSubgroup :=
        hSHH hrho
      change rho (i x) = i x
      change
        rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
      rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
      exact hrhoH (i x) ⟨x, rfl⟩)
  letI : Algebra F LH :=
    iLH.toRingHom.toAlgebra
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hmem (x : SeparableClosure F) :
      x ∈ IntermediateField.fixedField SF.toSubgroup ↔
        e x ∈ IntermediateField.fixedField SH.toSubgroup := by
    apply mem_fixedField_iff_of_equivariant
      (intrinsicAbstractBase F).toSubgroup SF.toSubgroup H₀.toSubgroup SH.toSubgroup
      hSFB hSHH e.toRingEquiv psi
    · intro tau y
      change (intrinsicBaseEquivAmbientEmbeddedField K F i e tau).val.toEquiv (e y) =
        e (tau.val y)
      rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val, e.symm_apply_apply]
    · intro tau
      change tau ∈ extensionSubgroup RF.field SF hSFB ↔
        psi tau ∈ extensionSubgroup RH.field SH hSHH
      rw [(localResidueDatum F).extensionSubgroup_frobeniusFixedField,
        (localResidueDatum K).extensionSubgroup_frobeniusFixedField]
      exact intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField K F E j e sigma tau
  exact {
    toFun := fun x =>
      ⟨e (x : SeparableClosure F),
        (hmem (x : SeparableClosure F)).1 x.property⟩
    invFun := fun y =>
      ⟨e.symm (y : SeparableClosure K),
        (hmem (e.symm (y : SeparableClosure K))).2
          (by
            rw [e.apply_symm_apply]
            exact y.property)⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact e.symm_apply_apply (x : SeparableClosure F)
    right_inv := fun y => by
      apply Subtype.ext
      exact e.apply_symm_apply (y : SeparableClosure K)
    map_mul' := fun x y => by
      apply Subtype.ext
      exact e.map_mul (x : SeparableClosure F) (y : SeparableClosure F)
    map_add' := fun x y => by
      apply Subtype.ext
      exact e.map_add (x : SeparableClosure F) (y : SeparableClosure F)
    commutes' := fun x => by
      apply Subtype.ext
      exact e.commutes x }

/-- After coercion to `SeparableClosure K`, the Frobenius fixed-field
equivalence acts as the original separable-closure equivalence. -/
theorem
    intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (sigma :
        let jF : E →ₐ[F] SeparableClosure K :=
          { j with commutes' := fun x => rfl }
        let jI : E →ₐ[F] SeparableClosure F :=
          e.symm.toAlgHom.comp jF
        let EI :=
          finiteGaloisAbstractExtensionOfEmbedding F E jI
        let RF :=
          (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (localResidueDatum F)
        (localResidueDatum F).FrobeniusElements
          RF EI.field EI.below)
      (x :
        let jF : E →ₐ[F] SeparableClosure K :=
          { j with commutes' := fun x => rfl }
        let jI : E →ₐ[F] SeparableClosure F :=
          e.symm.toAlgHom.comp jF
        let EI :=
          finiteGaloisAbstractExtensionOfEmbedding F E jI
        let RF :=
          (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (localResidueDatum F)
        let SF :=
          (localResidueDatum F).frobeniusFixedField
            RF EI.field EI.below sigma
        abstractFixedField F (SeparableClosure F) SF),
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro y hy
        rcases hy with ⟨z, rfl⟩
        exact ⟨algebraMap F E z, rfl⟩
      letI _hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hSourceFinite : Finite
          ((intrinsicAbstractBase F).toSubgroup ⧸
            extensionSubgroup
              (intrinsicAbstractBase F) EI.field EI.below) :=
        EI.finite
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      letI _hTargetFinite : Finite
          (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
        ambientEmbeddedExtensionQuotient_finite K F E j e
      let _RF :=
        (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
          (localResidueDatum F)
      let hHabsolute : Finite
          ((baseField
            Gal(SeparableClosure K/K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K/K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K/K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      let sigmaH :=
        intrinsicFrobeniusElementToAmbientEmbeddedField
          K F E j e sigma
      let SH :=
        (localResidueDatum K).frobeniusFixedField
          RH J₀ hJH sigmaH
      let hSHH :=
        (localResidueDatum K).frobeniusFixedField_le
          RH J₀ hJH sigmaH
      let LH :=
        abstractRelativeFixedField K (SeparableClosure K) hSHH
      let iLH : F →ₐ[K] LH :=
        i.codRestrict (LH.restrictScalars K).toSubalgebra (fun y => by
          change
            i y ∈ IntermediateField.fixedField SH.toSubgroup
          rw [IntermediateField.mem_fixedField_iff]
          intro rho hrho
          have hrhoH : rho ∈ H₀.toSubgroup :=
            hSHH hrho
          change rho (i y) = i y
          change
            rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
          rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
          exact hrhoH (i y) ⟨y, rfl⟩)
      letI : Algebra F LH :=
        iLH.toRingHom.toAlgebra
      ((intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
        K F E j e sigma x : LH) : SeparableClosure K) =
        e (x : SeparableClosure F) := by
  dsimp only
  intro e sigma x
  rfl

end EmbeddedFrobeniusTransport

end LocalClassFieldTheory

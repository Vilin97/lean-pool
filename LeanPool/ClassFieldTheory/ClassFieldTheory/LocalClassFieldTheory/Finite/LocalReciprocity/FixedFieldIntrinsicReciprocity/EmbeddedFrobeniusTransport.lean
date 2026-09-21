/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedInertiaComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldNormQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldSpecialization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv
/-!
# Embedded Frobenius transport

This module transports inertia, Frobenius elements, and fixed fields across an explicit equivalence of separable closures.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The separable-closure equivalence identifies the intrinsic extension
inertia subgroup of a fixed field with its ambient extension inertia
subgroup. -/
theorem map_intrinsicExtensionInertia_eq_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K),
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
    let ψ := intrinsicBaseEquivAmbientFixedField K H e
    ((localResidueDatum F).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below).map
        ψ.toMonoidHom =
      (localResidueDatum K).extensionInertiaWithin
        H.field J hJH := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
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
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact
      (intrinsicExtensionInertia_iff_ambientFixedField
        K H J hJH e τ).1 hτ
  · intro hσ
    let τ :
        (intrinsicAbstractBase F).toSubgroup :=
      ψ.symm σ
    refine ⟨τ, ?_, ψ.apply_symm_apply σ⟩
    apply
      (intrinsicExtensionInertia_iff_ambientFixedField
        K H J hJH e τ).2
    change
      ψ τ ∈
        (localResidueDatum K).extensionInertiaWithin
          H.field J hJH
    have hτImage : ψ τ = σ :=
      ψ.apply_symm_apply σ
    rw [hτImage]
    exact hσ

/-- The equivalence on absolute Galois base subgroups induced by a fixed-field
separable-closure equivalence is continuous. -/
theorem intrinsicBaseEquivAmbientFixedField_continuous
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K),
      Continuous (intrinsicBaseEquivAmbientFixedField K H e) := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  apply continuous_induced_rng.mpr
  change Continuous fun τ :
      (intrinsicAbstractBase F).toSubgroup =>
    (AlgEquiv.autCongr e τ.1).restrictScalars K
  exact
    (Field.absoluteGaloisGroup.ofIntermediateFieldInExtension_continuous
      F).comp
      ((Field.absoluteGaloisGroup.algEquiv_autCongr_continuous e).comp
        continuous_subtype_val)

/-- The intrinsic absolute Galois equivalence induced by an embedding into the
ambient separable closure is continuous. -/
theorem
    intrinsicBaseEquivAmbientEmbeddedField_continuous
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      Continuous
        (intrinsicBaseEquivAmbientEmbeddedField K F i e) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
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
  let theta :
      Gal(SeparableClosure F / F) ≃*
        Gal(SeparableClosure F₀ / F₀) := {
    toFun := fun sigma =>
      { c.symm.trans (sigma.toRingEquiv.trans c) with
        commutes' := fun x => by
          change c (sigma (c.symm
            (algebraMap F₀ (SeparableClosure F₀) x))) =
              algebraMap F₀ (SeparableClosure F₀) x
          have hpre :
              c.symm
                  (algebraMap F₀ (SeparableClosure F₀) x) =
                algebraMap F (SeparableClosure F) (phi.symm x) := by
            apply c.injective
            rw [c.apply_symm_apply, hc, phi.apply_symm_apply]
          rw [hpre, sigma.commutes, hc, phi.apply_symm_apply] }
    invFun := fun tau =>
      { c.trans (tau.toRingEquiv.trans c.symm) with
        commutes' := fun x => by
          change c.symm (tau (c
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          rw [hc, tau.commutes]
          apply c.injective
          rw [c.apply_symm_apply, hc] }
    left_inv := fun sigma => by
      apply AlgEquiv.ext
      intro x
      change c.symm
          (c (sigma (c.symm (c x)))) = sigma x
      rw [c.symm_apply_apply, c.symm_apply_apply]
    right_inv := fun tau => by
      apply AlgEquiv.ext
      intro x
      change c
          (c.symm (tau (c (c.symm x)))) = tau x
      rw [c.apply_symm_apply, c.apply_symm_apply]
    map_mul' := fun sigma tau => by
      apply AlgEquiv.ext
      intro x
      change c (sigma (tau (c.symm x))) =
        c (sigma (c.symm (c (tau (c.symm x)))))
      rw [c.symm_apply_apply] }
  have htheta : Continuous theta := by
    apply
      RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
        phi c hc theta.toMonoidHom
    intro sigma
    rfl
  let psi₀ :=
    intrinsicBaseEquivAmbientFixedField K H e₀
  have hpsi₀ : Continuous psi₀ :=
    intrinsicBaseEquivAmbientFixedField_continuous K H e₀
  have hlift : Continuous
      (fun sigma : Gal(SeparableClosure F₀ / F₀) =>
        (⟨sigma, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          trivial⟩ :
          (intrinsicAbstractBase F₀).toSubgroup)) := by
    apply continuous_induced_rng.mpr
    exact continuous_id
  change Continuous
    (fun tau : (intrinsicAbstractBase F).toSubgroup =>
      psi₀
        ⟨theta tau.1, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          trivial⟩)
  exact hpsi₀.comp
    (hlift.comp (htheta.comp continuous_subtype_val))

/-- Bundles the intrinsic-to-ambient absolute Galois equivalence as a continuous
multiplicative equivalence. -/
noncomputable def
    intrinsicBaseContinuousEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃ₜ*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hpsi : Continuous psi :=
    intrinsicBaseEquivAmbientEmbeddedField_continuous
      K F i e
  letI : CompactSpace (intrinsicAbstractBase F).toSubgroup :=
    isCompact_iff_compactSpace.mp
      ((intrinsicAbstractBase F).isClosed'.isCompact)
  exact
    { toMulEquiv := psi
      continuous_toFun := hpsi
      continuous_invFun :=
        hpsi.continuous_symm_of_equiv_compact_to_t2 }

/-- Descends the intrinsic-to-ambient Galois equivalence to a continuous
multiplicative equivalence between the quotients by extension inertia. -/
noncomputable def
    intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
    (K F E : Type)
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
      let _psi :=
        intrinsicBaseEquivAmbientEmbeddedField K F i e
      letI hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hSourceFinite : Finite
          ((intrinsicAbstractBase F).toSubgroup ⧸
            extensionSubgroup
              (intrinsicAbstractBase F) EI.field EI.below) :=
        EI.finite
      letI hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      letI _hTargetFinite : Finite
          (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
        ambientEmbeddedExtensionQuotient_finite K F E j e
      ((intrinsicAbstractBase F).toSubgroup ⧸
          (localResidueDatum F).extensionInertiaWithin
            (intrinsicAbstractBase F) EI.field EI.below) ≃ₜ*
        (H₀.toSubgroup ⧸
          (localResidueDatum K).extensionInertiaWithin
            H₀ J₀ hJH) := by
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let psiC :=
    intrinsicBaseContinuousEquivAmbientEmbeddedField K F i e
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  have hmapExtension :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
        K F E j e
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI :
      ((localResidueDatum F).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    inferInstance
  letI :
      ((localResidueDatum K).extensionInertiaWithin
        H₀ J₀ hJH).Normal :=
    inferInstance
  have hmapInertia :
      ((localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        (localResidueDatum K).extensionInertiaWithin
          H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionInertia_eq_ambientEmbeddedField
        K F E j e
  exact
    LocalFieldTheory.QuotientGroup.continuousCongr
      ((localResidueDatum F).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below)
      ((localResidueDatum K).extensionInertiaWithin
        H₀ J₀ hJH)
      psiC
      (by
        change
          ((localResidueDatum F).extensionInertiaWithin
              (intrinsicAbstractBase F) EI.field EI.below).map
              psi.toMonoidHom =
            (localResidueDatum K).extensionInertiaWithin
              H₀ J₀ hJH
        exact hmapInertia)

/-- The intrinsic-to-ambient quotient equivalence preserves the normalized
degree of extension Frobenius classes. -/
theorem
    intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField_normalizedDegree
    (K F E : Type)
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
      letI hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      letI _hTargetFinite : Finite
          (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
        ambientEmbeddedExtensionQuotient_finite K F E j e
      ∀ q :
          (intrinsicAbstractBase F).toSubgroup ⧸
            (localResidueDatum F).extensionInertiaWithin
              (intrinsicAbstractBase F) EI.field EI.below,
        let RF :=
          (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (localResidueDatum F)
        let hHabsolute : Finite
            ((baseField
              Gal(SeparableClosure K / K)).toSubgroup ⧸
              extensionSubgroup
                (baseField Gal(SeparableClosure K / K))
                H₀ (le_baseField H₀)) := by
          exact ambientEmbeddedAbsoluteQuotientFinite K F i
        let H : FiniteAbstractField
            Gal(SeparableClosure K / K) :=
          ⟨H₀, hHabsolute⟩
        let RH :=
          H.toFiniteResidueAbstractField (localResidueDatum K)
        (localResidueDatum K).extensionNormalizedDegree
            RH J₀ hJH
            (intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
              K F E j e q) =
          (localResidueDatum F).extensionNormalizedDegree
            RF EI.field EI.below q := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  intro q
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  refine Quotient.inductionOn' q ?_
  intro tau
  have hquotientMk :
      intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
          K F E j e (QuotientGroup.mk tau) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) := by
    exact
      LocalFieldTheory.QuotientGroup.continuousCongr_mk
        _ _ _ _ tau
  rw [hquotientMk,
    (localResidueDatum K).extensionNormalizedDegree_mk,
    (localResidueDatum F).extensionNormalizedDegree_mk]
  simpa only [RF, RH, H] using
    (intrinsicBase_normalizedDegree_eq_ambientEmbeddedField
      K F i e tau).symm

/-- Transports a positive Frobenius lift for an embedded extension from the
intrinsic separable closure of `F` to the ambient separable closure of `K`. -/
noncomputable def
    intrinsicFrobeniusElementToAmbientEmbeddedField
    (K F E : Type)
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
      letI hTargetNormal :
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
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      (localResidueDatum F).FrobeniusElements
          RF EI.field EI.below →
        (localResidueDatum K).FrobeniusElements
          RH J₀ hJH := by
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
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
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  intro sigma
  refine
    ⟨intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
        K F E j e sigma.1, ?_⟩
  rcases sigma.2 with ⟨n, hn, hdegree⟩
  refine ⟨n, hn, ?_⟩
  rw [
    intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField_normalizedDegree]
  exact hdegree

/-- Extension restriction commutes with the intrinsic-to-ambient quotient
equivalence and the corresponding quotient-to-Galois equivalences. -/
theorem
    intrinsicExtensionRestriction_compatibility_ambientEmbeddedField
    (K F E : Type)
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
      letI hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hSourceFinite : Finite
          ((intrinsicAbstractBase F).toSubgroup ⧸
            extensionSubgroup
              (intrinsicAbstractBase F) EI.field EI.below) :=
        EI.finite
      letI hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      letI _hTargetFinite : Finite
          (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
        ambientEmbeddedExtensionQuotient_finite K F E j e
      ∀ q :
          (intrinsicAbstractBase F).toSubgroup ⧸
            (localResidueDatum F).extensionInertiaWithin
              (intrinsicAbstractBase F) EI.field EI.below,
        ambientEmbeddedExtensionQuotientEquivGaloisGroup
            K F E j e
            ((localResidueDatum K).extensionRestriction
              H₀ J₀ hJH
              (intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
                K F E j e q)) =
          finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            F E jI
            ((localResidueDatum F).extensionRestriction
              (intrinsicAbstractBase F) EI.field EI.below q) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  intro q
  refine Quotient.inductionOn' q ?_
  intro tau
  have hquotientMk :
      intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
          K F E j e (QuotientGroup.mk tau) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) := by
    exact
      LocalFieldTheory.QuotientGroup.continuousCongr_mk
        _ _ _ _ tau
  have hAmbientRestriction :
      (localResidueDatum K).extensionRestriction
          H₀ J₀ hJH
          (intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
            K F E j e (QuotientGroup.mk tau)) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) := by
    calc
      _ =
          (localResidueDatum K).extensionRestriction
            H₀ J₀ hJH
            (QuotientGroup.mk
              (intrinsicBaseEquivAmbientEmbeddedField K F i e tau)) :=
        congrArg
          ((localResidueDatum K).extensionRestriction H₀ J₀ hJH)
          hquotientMk
      _ = _ :=
        (localResidueDatum K).extensionRestriction_mk
          H₀ J₀ hJH
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau)
  have hSourceRestriction :
      (localResidueDatum F).extensionRestriction
          (intrinsicAbstractBase F) EI.field EI.below
          (QuotientGroup.mk tau) =
        QuotientGroup.mk tau :=
    (localResidueDatum F).extensionRestriction_mk
      (intrinsicAbstractBase F) EI.field EI.below tau
  calc
    _ =
        ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e
          (QuotientGroup.mk
            (intrinsicBaseEquivAmbientEmbeddedField K F i e tau)) :=
      congrArg
        (ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e)
        hAmbientRestriction
    _ =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) :=
      ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk
        K F E j e tau
    _ = _ :=
      congrArg
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI)
        hSourceRestriction.symm

/-- Restriction of a transported Frobenius lift agrees, under the intrinsic
and ambient quotient--Galois equivalences, with restriction of the original
intrinsic lift. -/
theorem
    intrinsicFrobeniusRestriction_compatibility_ambientEmbeddedField
    (K F E : Type)
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
      letI hTargetNormal :
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
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      ∀ sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below,
        ambientEmbeddedExtensionQuotientEquivGaloisGroup
            K F E j e
            ((localResidueDatum K).frobeniusRestriction
              RH J₀ hJH
              (intrinsicFrobeniusElementToAmbientEmbeddedField
                K F E j e sigma)) =
          finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            F E jI
            ((localResidueDatum F).frobeniusRestriction
              RF EI.field EI.below sigma) := by
  dsimp only
  intro e sigma
  exact
    intrinsicExtensionRestriction_compatibility_ambientEmbeddedField
      K F E j e sigma.1

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

/-- The intrinsic-to-ambient quotient equivalence preserves and reflects
membership in the Frobenius closure generated by a Frobenius element. -/
theorem
    intrinsicFrobeniusClosure_iff_ambientEmbeddedField
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
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      ∀ (sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below)
        (q :
          (intrinsicAbstractBase F).toSubgroup ⧸
            (localResidueDatum F).extensionInertiaWithin
              (intrinsicAbstractBase F) EI.field EI.below),
        q ∈ ((localResidueDatum F).frobeniusClosure
            RF EI.field EI.below sigma).toSubgroup ↔
          intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
              K F E j e q ∈
            ((localResidueDatum K).frobeniusClosure
              RH J₀ hJH
              (intrinsicFrobeniusElementToAmbientEmbeddedField
                K F E j e sigma)).toSubgroup := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  intro sigma q
  let xi :=
    intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
      K F E j e
  let xiHom :=
    ContinuousMonoidHom.toContinuousMonoidHom xi
  let xiInvHom :=
    ContinuousMonoidHom.toContinuousMonoidHom xi.symm
  constructor
  · intro hq
    change
      q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => sigma.1) : Set
            ((intrinsicAbstractBase F).toSubgroup ⧸
              (localResidueDatum F).extensionInertiaWithin
                (intrinsicAbstractBase F) EI.field EI.below)) :
          Subgroup _) at hq
    have hmap :=
      map_mem_closedSubgroupGenerated_image
        xiHom
        hq
    have hgenerators :
        xiHom ''
            Set.range (fun _ : Unit => sigma.1) =
          Set.range (fun _ : Unit => xiHom sigma.1) := by
      ext y
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨sigma.1, ⟨u, rfl⟩, rfl⟩
    rw [hgenerators] at hmap
    change
      xiHom q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => xiHom sigma.1) : Set
            (H₀.toSubgroup ⧸
              (localResidueDatum K).extensionInertiaWithin
                H₀ J₀ hJH)) :
          Subgroup _)
    exact hmap
  · intro hq
    change
      xiHom q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => xiHom sigma.1) : Set
            (H₀.toSubgroup ⧸
              (localResidueDatum K).extensionInertiaWithin
                H₀ J₀ hJH)) :
          Subgroup _) at hq
    have hmap :=
      map_mem_closedSubgroupGenerated_image
        xiInvHom
        hq
    have hgenerators :
        xiInvHom ''
            Set.range (fun _ : Unit => xiHom sigma.1) =
          Set.range (fun _ : Unit => sigma.1) := by
      ext y
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, (xi.symm_apply_apply sigma.1).symm⟩
      · rintro ⟨u, rfl⟩
        exact
          ⟨xiHom sigma.1, ⟨u, rfl⟩,
            xi.symm_apply_apply sigma.1⟩
    rw [hgenerators] at hmap
    have hvalue : xiInvHom (xiHom q) = q :=
      xi.symm_apply_apply q
    rw [hvalue] at hmap
    change
      q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => sigma.1) : Set
            ((intrinsicAbstractBase F).toSubgroup ⧸
              (localResidueDatum F).extensionInertiaWithin
                (intrinsicAbstractBase F) EI.field EI.below)) :
          Subgroup _)
    exact hmap

/-- The intrinsic-to-ambient absolute Galois equivalence preserves and reflects
membership in the Frobenius fixed subgroup. -/
theorem
    intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField
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
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      ∀ (sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below)
        (tau : (intrinsicAbstractBase F).toSubgroup),
        tau ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
            RF EI.field EI.below sigma ↔
          intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
            (localResidueDatum K).frobeniusFixedSubgroupWithin
              RH J₀ hJH
              (intrinsicFrobeniusElementToAmbientEmbeddedField
                K F E j e sigma) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
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
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  intro sigma tau
  have htransport :=
    intrinsicFrobeniusClosure_iff_ambientEmbeddedField
      K F E j e sigma (QuotientGroup.mk tau)
  have hquotientMk :
      intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
          K F E j e (QuotientGroup.mk tau) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) := by
    exact
      LocalFieldTheory.QuotientGroup.continuousCongr_mk
        _ _ _ _ tau
  rw [hquotientMk] at htransport
  change
    QuotientGroup.mk tau ∈
        ((localResidueDatum F).frobeniusClosure
          RF EI.field EI.below sigma).toSubgroup ↔
      QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) ∈
        ((localResidueDatum K).frobeniusClosure
          RH J₀ hJH
          (intrinsicFrobeniusElementToAmbientEmbeddedField
            K F E j e sigma)).toSubgroup
  convert htransport using 1 <;>
    simp only [
      i, jF, jI, EI, H₀, J₀, RF, H, RH]
  · rfl
  · rfl

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
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
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
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
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
    constructor
    · intro hx
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      let rhoH : H₀.toSubgroup := ⟨rho, hSHH hrho⟩
      have hrhoExtension :
          rhoH ∈ extensionSubgroup RH.field SH hSHH := by
        exact hrho
      have hrhoInternal :
          rhoH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
            RH J₀ hJH sigmaH := by
        rw [← (localResidueDatum K).extensionSubgroup_frobeniusFixedField
          RH J₀ hJH sigmaH]
        exact hrhoExtension
      let tau :
          (intrinsicAbstractBase F).toSubgroup :=
        psi.symm rhoH
      have htauInternal :
          tau ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
            RF EI.field EI.below sigma :=
        (intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField
          K F E j e sigma tau).2 (by
            have hpsiApply :
                intrinsicBaseEquivAmbientEmbeddedField K F i e tau =
                  rhoH :=
              psi.apply_symm_apply rhoH
            rw [hpsiApply]
            simpa only [
              i, jF, jI, EI, H₀, J₀, hJH, RF, hHabsolute, H, RH,
              sigmaH] using hrhoInternal)
      have htauExtension :
          tau ∈ extensionSubgroup
            RF.field SF hSFB := by
        rw [(localResidueDatum F).extensionSubgroup_frobeniusFixedField
          RF EI.field EI.below sigma]
        exact htauInternal
      have hxfix : tau.1 x = x :=
        (IntermediateField.mem_fixedField_iff SF.toSubgroup x).1
          hx tau.1 htauExtension
      have hpsi : psi tau = rhoH :=
        psi.apply_symm_apply rhoH
      have hrhoeq : (psi tau).1 = rho :=
        congrArg Subtype.val hpsi
      calc
        rho (e x) = (psi tau).1.1 (e x) := by
          exact congrArg
            (fun g : Gal(SeparableClosure K / K) => g (e x))
            hrhoeq.symm
        _ = e (tau.1 x) := by
          rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val,
            e.symm_apply_apply]
        _ = e x := congrArg e hxfix
    · intro hx
      rw [IntermediateField.mem_fixedField_iff]
      intro tau₀ htau₀
      let tau :
          (intrinsicAbstractBase F).toSubgroup :=
        ⟨tau₀, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          exact Subgroup.mem_top _⟩
      have htauExtension :
          tau ∈ extensionSubgroup
            RF.field SF hSFB := by
        exact htau₀
      have htauInternal :
          tau ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
            RF EI.field EI.below sigma := by
        rw [← (localResidueDatum F).extensionSubgroup_frobeniusFixedField
          RF EI.field EI.below sigma]
        exact htauExtension
      have hrhoInternal :
          psi tau ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
            RH J₀ hJH sigmaH :=
        (intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField
          K F E j e sigma tau).1 htauInternal
      have hrhoExtension :
          psi tau ∈ extensionSubgroup RH.field SH hSHH := by
        rw [(localResidueDatum K).extensionSubgroup_frobeniusFixedField
          RH J₀ hJH sigmaH]
        exact hrhoInternal
      have hxfix : (psi tau).1.1 (e x) = e x :=
        (IntermediateField.mem_fixedField_iff SH.toSubgroup (e x)).1
          hx (psi tau).1 hrhoExtension
      apply e.injective
      calc
        e (tau₀ x) = e (tau.1 x) := rfl
        _ = (psi tau).1.1 (e x) := by
          rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val,
            e.symm_apply_apply]
        _ = e x := hxfix
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
@[simp]
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
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
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

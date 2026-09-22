/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient
/-!
# Embedded inertia comparison

This module transports extension inertia between an intrinsic finite extension and its
  realization inside an ambient separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Under the embedded-field base equivalence, membership in intrinsic
extension inertia for `E / F` is equivalent to membership in the corresponding
ambient extension-inertia subgroup. -/
theorem
    intrinsicExtensionInertia_iff_ambientEmbeddedField
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
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
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
      tau ∈ (localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below ↔
        intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
          (localResidueDatum K).extensionInertiaWithin
            H₀ J₀ hJH := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
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
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let tauRF : RF.field.toSubgroup :=
    ⟨tau.1, tau.2⟩
  let psiTauRH : RH.field.toSubgroup :=
    ⟨(psi tau).1, (psi tau).2⟩
  have hdegree :
      (localResidueDatum F).normalizedDegree RF tauRF =
        (localResidueDatum K).normalizedDegree RH psiTauRH := by
    simpa [RF, RH, psi, tauRF, psiTauRH] using
      intrinsicBase_normalizedDegree_eq_ambientEmbeddedField
        K F i e tau
  change
    (tau ∈ extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below ∧
      tau ∈ (localResidueDatum F).fieldInertiaWithin
        (intrinsicAbstractBase F)) ↔
    (psi tau ∈ extensionSubgroup H₀ J₀ hJH ∧
      psi tau ∈ (localResidueDatum K).fieldInertiaWithin H₀)
  constructor
  · rintro ⟨htauExtension, htauInertia⟩
    refine
      ⟨(intrinsicExtensionSubgroup_iff_ambientEmbeddedField
        K F E j e tau).1 htauExtension, ?_⟩
    have htauRF :
        tauRF ∈
          (localResidueDatum F).fieldInertiaWithin RF.field := by
      exact htauInertia
    have hnormalizedRF :
        (localResidueDatum F).normalizedDegree RF tauRF = 1 := by
      change
        tauRF ∈
          ((localResidueDatum F).normalizedDegree RF).toMonoidHom.ker
      rw [(localResidueDatum F).normalizedDegree_ker RF]
      exact htauRF
    have hnormalizedRH :
        (localResidueDatum K).normalizedDegree RH psiTauRH = 1 :=
      hdegree.symm.trans hnormalizedRF
    change
      psiTauRH ∈
        (localResidueDatum K).fieldInertiaWithin RH.field
    rw [← (localResidueDatum K).normalizedDegree_ker RH]
    exact hnormalizedRH
  · rintro ⟨hpsiExtension, hpsiInertia⟩
    refine
      ⟨(intrinsicExtensionSubgroup_iff_ambientEmbeddedField
        K F E j e tau).2 hpsiExtension, ?_⟩
    have hpsiTauRH :
        psiTauRH ∈
          (localResidueDatum K).fieldInertiaWithin RH.field := by
      exact hpsiInertia
    have hnormalizedRH :
        (localResidueDatum K).normalizedDegree RH psiTauRH = 1 := by
      change
        psiTauRH ∈
          ((localResidueDatum K).normalizedDegree RH).toMonoidHom.ker
      rw [(localResidueDatum K).normalizedDegree_ker RH]
      exact hpsiTauRH
    have hnormalizedRF :
        (localResidueDatum F).normalizedDegree RF tauRF = 1 :=
      hdegree.trans hnormalizedRH
    change
      tauRF ∈
        (localResidueDatum F).fieldInertiaWithin RF.field
    rw [← (localResidueDatum F).normalizedDegree_ker RF]
    exact hnormalizedRF

/-- The embedded-field base equivalence maps the intrinsic extension-inertia
subgroup for `E / F` onto the corresponding ambient extension-inertia subgroup. -/
theorem
    map_intrinsicExtensionInertia_eq_ambientEmbeddedField
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
      let psi :=
        intrinsicBaseEquivAmbientEmbeddedField K F i e
      ((localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        (localResidueDatum K).extensionInertiaWithin
          H₀ J₀ hJH := by
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
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  ext sigma
  constructor
  · rintro ⟨tau, htau, rfl⟩
    exact
      (intrinsicExtensionInertia_iff_ambientEmbeddedField
        K F E j e tau).1 htau
  · intro hsigma
    let tau :
        (intrinsicAbstractBase F).toSubgroup :=
      psi.symm sigma
    refine ⟨tau, ?_, psi.apply_symm_apply sigma⟩
    apply
      (intrinsicExtensionInertia_iff_ambientEmbeddedField
        K F E j e tau).2
    have htauImage : psi tau = sigma :=
      psi.apply_symm_apply sigma
    rw [htauImage]
    exact hsigma

end LocalClassFieldTheory

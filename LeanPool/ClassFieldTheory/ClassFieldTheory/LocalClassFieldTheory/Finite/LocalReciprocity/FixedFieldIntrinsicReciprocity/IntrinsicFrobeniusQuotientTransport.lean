/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport
/-!
# Intrinsic Frobenius quotient transport

This module constructs the intrinsic-to-ambient quotient transport and
maps Frobenius elements before the closure comparisons.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The chosen equivalence of separable closures induces a continuous
multiplicative equivalence from the intrinsic absolute-base subgroup of the
finite fixed field to its ambient fixed subgroup. -/
noncomputable def
    intrinsicBaseContinuousEquivAmbientFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (e : intrinsicFixedFieldSeparableClosureEquiv K H) :
    (intrinsicAbstractBase
      (abstractFixedField K (SeparableClosure K) H.field)).toSubgroup ≃ₜ*
      H.field.toSubgroup := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  letI : CompactSpace (intrinsicAbstractBase F).toSubgroup :=
    isCompact_iff_compactSpace.mp
      (intrinsicAbstractBase F).isClosed'.isCompact
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  have hψ : Continuous ψ :=
    intrinsicBaseEquivAmbientFixedField_continuous K H e
  exact
    { toMulEquiv := ψ
      continuous_toFun := hψ
      continuous_invFun :=
        hψ.continuous_symm_of_equiv_compact_to_t2 }

/-- Descend the continuous intrinsic-to-ambient base equivalence to the
quotients by the corresponding extension-inertia subgroups. -/
noncomputable def
    intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
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
    ((intrinsicAbstractBase F).toSubgroup ⧸
        (localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below) ≃ₜ*
      (H.field.toSubgroup ⧸
        (localResidueDatum K).extensionInertiaWithin
          H.field J hJH) := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
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
  let ψ := intrinsicBaseContinuousEquivAmbientFixedField K H e
  letI :
      ((localResidueDatum F).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    inferInstance
  letI :
      ((localResidueDatum K).extensionInertiaWithin
        H.field J hJH).Normal :=
    inferInstance
  exact
    LocalFieldTheory.QuotientGroup.continuousCongr
      ((localResidueDatum F).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below)
      ((localResidueDatum K).extensionInertiaWithin
        H.field J hJH)
      ψ
      (map_intrinsicExtensionInertia_eq_ambientFixedField
        K H J hJH e)

/-- The multiplicative equivalence from the intrinsic extension-inertia
quotient of a finite fixed field to the corresponding quotient inside the
ambient absolute Galois group, induced by the chosen equivalence of separable
closures. -/
noncomputable def intrinsicFrobeniusQuotientEquivAmbientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
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
    ((intrinsicAbstractBase F).toSubgroup ⧸
        (localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below) ≃*
      (H.field.toSubgroup ⧸
        (localResidueDatum K).extensionInertiaWithin
          H.field J hJH) := by
  dsimp only
  intro e
  exact
    (intrinsicFrobeniusQuotientContinuousEquivAmbientFixedField
      K H J hJH e).toMulEquiv

/-- The fixed-field quotient equivalence sends the class of an intrinsic
automorphism to the class of the corresponding ambient automorphism. -/
@[simp]
theorem intrinsicFrobeniusQuotientEquivAmbientFixedField_mk
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
    intrinsicFrobeniusQuotientEquivAmbientFixedField
        K H J hJH e (QuotientGroup.mk τ) =
      QuotientGroup.mk
        (intrinsicBaseEquivAmbientFixedField K H e τ) := by
  dsimp only
  rintro e τ
  exact LocalFieldTheory.QuotientGroup.continuousCongr_mk _ _ _ _ _

/-- The intrinsic-to-ambient Frobenius quotient equivalence preserves the
normalized extension degree of every quotient class. -/
theorem
    intrinsicFrobeniusQuotientEquivAmbientFixedField_normalizedDegree
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
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
    ∀ (q :
      (intrinsicAbstractBase F).toSubgroup ⧸
        (localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below),
    let RF :=
      (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    (localResidueDatum K).extensionNormalizedDegree
        RH J hJH
        (intrinsicFrobeniusQuotientEquivAmbientFixedField
          K H J hJH e q) =
      (localResidueDatum F).extensionNormalizedDegree
        RF EI.field EI.below q := by
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
  intro q
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  refine Quotient.inductionOn' q ?_
  intro τ
  let τRF : RF.field.toSubgroup :=
    ⟨τ.1, τ.2⟩
  let ψτRH : RH.field.toSubgroup :=
    ⟨(intrinsicBaseEquivAmbientFixedField K H e τ).1,
      (intrinsicBaseEquivAmbientFixedField K H e τ).2⟩
  change
    (localResidueDatum K).normalizedDegree RH ψτRH =
      (localResidueDatum F).normalizedDegree RF τRF
  have hψτRH :
      ψτRH =
        (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field).symm
            (AlgEquiv.autCongr e τ.1) := by
    apply Subtype.ext
    exact
      intrinsicBaseEquivAmbientFixedField_apply_val
        K H e τ
  rw [hψτRH]
  exact
    (intrinsicBase_normalizedDegree_eq_ambientFixedField
      K H e τ).symm

/-- Intrinsic extension-inertia quotient classes whose normalized degree is a
strictly positive power of the canonical Frobenius degree. -/
abbrev intrinsicFixedFieldFrobeniusElements
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H) :=
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
  {q :
      (intrinsicAbstractBase F).toSubgroup ⧸
        (localResidueDatum F).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below //
    ∃ n : ℕ, 0 < n ∧
      (localResidueDatum F).extensionNormalizedDegree
          RF EI.field EI.below q =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n}

/-- The ambient fixed subgroup modulo the extension-inertia subgroup attached
to the given finite Galois extension. -/
abbrev ambientFixedFieldFrobeniusQuotient
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [_hJnormal : (extensionSubgroup H.field J hJH).Normal] :=
  H.field.toSubgroup ⧸
    (localResidueDatum K).extensionInertiaWithin
      H.field J hJH

/-- The property that an ambient quotient class has normalized degree equal to
a strictly positive power of the canonical Frobenius degree. -/
abbrev ambientFixedFieldFrobeniusProperty
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    (q : ambientFixedFieldFrobeniusQuotient K H J hJH) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    (localResidueDatum K).extensionNormalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH q =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n

/-- Ambient extension-inertia quotient classes satisfying the positive
Frobenius-degree property. -/
abbrev ambientFixedFieldFrobeniusElements
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal] :=
  {q : ambientFixedFieldFrobeniusQuotient K H J hJH //
    ambientFixedFieldFrobeniusProperty K H J hJH q}

/-- Transporting an intrinsic Frobenius element to the ambient quotient
preserves its positive Frobenius-degree property. -/
theorem
    intrinsicFrobeniusElementToAmbientFixedField_property
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
    ambientFixedFieldFrobeniusProperty K H J hJH
      (intrinsicFrobeniusQuotientEquivAmbientFixedField
        K H J hJH e σ.1) := by
  change ∃ n : ℕ, 0 < n ∧
    (localResidueDatum K).extensionNormalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH
        (intrinsicFrobeniusQuotientEquivAmbientFixedField
          K H J hJH e σ.1) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n
  rw [intrinsicFrobeniusQuotientEquivAmbientFixedField_normalizedDegree
    K H J hJH e σ.1]
  exact σ.2

/-- Transport an intrinsic fixed-field Frobenius element to the ambient
extension-inertia quotient, together with its positive Frobenius-degree
property. -/
noncomputable def
    intrinsicFrobeniusElementToAmbientFixedField
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
    ambientFixedFieldFrobeniusElements K H J hJH := by
  exact
    ⟨intrinsicFrobeniusQuotientEquivAmbientFixedField
        K H J hJH e σ.1,
      intrinsicFrobeniusElementToAmbientFixedField_property
        K H J hJH e σ⟩

/-- The quotient class underlying a transported intrinsic Frobenius element is
the image under the intrinsic-to-ambient quotient equivalence. -/
@[simp]
theorem intrinsicFrobeniusElementToAmbientFixedField_val
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
    (intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ).1 =
      intrinsicFrobeniusQuotientEquivAmbientFixedField
        K H J hJH e σ.1 := by
  rfl

end LocalClassFieldTheory

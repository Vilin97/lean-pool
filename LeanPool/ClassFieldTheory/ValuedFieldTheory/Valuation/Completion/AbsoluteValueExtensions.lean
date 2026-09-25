/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
/-!
# Extension of valuations to finite field extensions

The setup uses nontrivial real-valued absolute values throughout.  For an
absolute value `v` on `K`, we use mathlib's completion `v.Completion` and its
concrete algebraic closure.  The absolute value `bar v` on that algebraic
closure is produced by the unique-extension unique extension theorem, not supplied as an
extra hypothesis.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- Absolute values on `L` which extend `v` pointwise.  This is the common
index type for the valuation-extension theorem and the factor correspondence in the
  extension-factor correspondence. -/
abbrev AbsoluteValueExtension
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (L : Type v) [Field L] [Algebra K L] :=
  {w : AbsoluteValue L ℝ // AbsoluteValue.Extends vK w}

/-- An exact extension of a nontrivial absolute value is nontrivial. -/
theorem AbsoluteValueExtension.isNontrivial
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    {vK : AbsoluteValue K ℝ}
    (u : AbsoluteValueExtension vK L)
    (hvK : vK.IsNontrivial) :
    u.1.IsNontrivial := by
  rcases hvK with ⟨a, ha, hva⟩
  refine
    ⟨algebraMap K L a,
      (map_ne_zero (algebraMap K L)).2 ha, ?_⟩
  simpa only [u.2 a] using hva

/-- The concrete algebraic closure `\bar K_v` used in the valuation-extension theorem. -/
abbrev absoluteValueExtensionAlgebraicCompletionClosure
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :=
  AlgebraicClosure vK.Completion

/-- The unique extension `\bar v` of the completion absolute value to
`\bar K_v`. -/
noncomputable def absoluteValueExtensionAlgebraicClosureAbsoluteValue
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    AbsoluteValue (absoluteValueExtensionAlgebraicCompletionClosure vK) ℝ :=
  (AbsoluteValue.uniqueAlgebraicExtension
    (AbsoluteValue.completionAbsoluteValue vK)
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)).extension

@[simp]
theorem absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) (x : vK.Completion) :
    absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtensionAlgebraicCompletionClosure vK) x) =
      AbsoluteValue.completionAbsoluteValue vK x := by
  exact
    (AbsoluteValue.uniqueAlgebraicExtension
      (AbsoluteValue.completionAbsoluteValue vK)
      (AbsoluteValue.completionAbsoluteValue_complete vK)
      (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)).isExtension x


/-- A `K_v`-embedding of the algebraic localization into `\bar K_v`. -/
noncomputable def absoluteValueExtensionLocalizationEmbedding
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 →ₐ[vK.Completion]
      absoluteValueExtensionAlgebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  letI : Module.IsTorsionFree vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap vK.Completion
        (AbsoluteValue.algebraicLocalization vK w.1 w.2)).injective
  letI : Module.IsTorsionFree vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap vK.Completion
        (absoluteValueExtensionAlgebraicCompletionClosure vK)).injective
  exact IsAlgClosed.lift

/-- The localization absolute value is the pullback of `\bar v` along the
chosen localization embedding. -/
theorem absoluteValueExtension_localizationAbsoluteValue_eq_pullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 =
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).comp
        (absoluteValueExtensionLocalizationEmbedding vK w).injective := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion) (L := AbsoluteValue.algebraicLocalization vK w.1 w.2)
    (AbsoluteValue.completionAbsoluteValue vK)
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  have hleft : AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 = R.extension :=
    R.unique _ (AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2)
  have hright :
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).comp
          (absoluteValueExtensionLocalizationEmbedding vK w).injective = R.extension := by
    apply R.unique
    intro x
    change absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK
      (absoluteValueExtensionLocalizationEmbedding vK w
        (algebraMap vK.Completion (AbsoluteValue.algebraicLocalization vK w.1 w.2) x)) = _
    rw [(absoluteValueExtensionLocalizationEmbedding vK w).commutes]
    exact absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap vK hvK x
  exact hleft.trans hright.symm

/-- Pull `\bar v` back along a `K`-embedding of `L` into `\bar K_v`. -/
noncomputable def absoluteValueExtensionPullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    AbsoluteValue L ℝ :=
  (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).comp tau.injective

/-- Every pullback along a `K`-embedding is an exact extension of `v`. -/
theorem absoluteValueExtension_pullback_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    AbsoluteValue.Extends vK (absoluteValueExtensionPullback vK hvK tau) := by
  intro x
  change absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK
    (tau (algebraMap K L x)) = vK x
  rw [tau.commutes,
    IsScalarTower.algebraMap_apply K vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK),
    absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap]
  exact AbsoluteValue.completionAbsoluteValue_coe vK x

/-- Extend an exact nontrivial absolute value through an algebraic
tower to an algebraically closed overfield.

The construction pulls the canonical absolute value on the algebraic
closure of the completion back along an actual embedding of the
overfield.  Unlike the finite normal-closure specialization, this
statement does not impose a finite-dimensional hypothesis. -/
noncomputable def AbsoluteValueExtension.extendToAlgebraicallyClosed
    {K : Type u} {L : Type v} {Ω : Type*}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω]
    [Algebra.IsAlgebraic L Ω]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (u : AbsoluteValueExtension vK L) :
    AbsoluteValueExtension vK Ω := by
  let τ :
      Ω →ₐ[L]
        absoluteValueExtensionAlgebraicCompletionClosure u.1 :=
    IsAlgClosed.lift
  let wΩ : AbsoluteValue Ω ℝ :=
    absoluteValueExtensionPullback
      u.1 (u.isNontrivial hvK) τ
  have hwΩ :
      AbsoluteValue.Extends u.1 wΩ :=
    absoluteValueExtension_pullback_extends
      u.1 (u.isNontrivial hvK) τ
  exact
    { val := wΩ
      property := by
        intro x
        rw [IsScalarTower.algebraMap_apply K L Ω,
          hwΩ, u.2] }

/-- The extension to an algebraically closed overfield restricts to
the original exact absolute value on the intermediate field. -/
@[simp]
theorem AbsoluteValueExtension.extendToAlgebraicallyClosed_algebraMap
    {K : Type u} {L : Type v} {Ω : Type*}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω]
    [Algebra.IsAlgebraic L Ω] [IsAlgClosed Ω]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (u : AbsoluteValueExtension vK L)
    (x : L) :
    (u.extendToAlgebraicallyClosed vK hvK :
        AbsoluteValueExtension vK Ω).1
        (algebraMap L Ω x) =
      u.1 x := by
  change
    absoluteValueExtensionPullback
        u.1 (u.isNontrivial hvK) IsAlgClosed.lift
        (algebraMap L Ω x) =
      u.1 x
  exact
    absoluteValueExtension_pullback_extends
      u.1 (u.isNontrivial hvK) IsAlgClosed.lift x

/-- The `K`-embedding attached to an exact extension `w | v`. -/
noncomputable def absoluteValueExtensionEmbeddingOfExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) :
    L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let phi := absoluteValueExtensionLocalizationEmbedding vK w
  refine
    { __ := phi.toRingHom.comp (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
      commutes' := ?_ }
  intro x
  change phi (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
    (algebraMap K L x)) = algebraMap K
      (absoluteValueExtensionAlgebraicCompletionClosure vK) x
  rw [AbsoluteValue.toAlgebraicLocalization_algebraMap,
    phi.commutes]
  rfl

@[simp]
theorem absoluteValueExtension_embeddingOfExtension_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (x : L) :
    absoluteValueExtensionEmbeddingOfExtension vK w x =
      absoluteValueExtensionLocalizationEmbedding vK w
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) :=
  rfl

/-- The canonical embedding attached to `w` pulls `\bar v` back to `w`.
This is the witness equality used in the valuation-extension theorem(i). -/
theorem absoluteValueExtension_extension_eq_pullback_embeddingOfExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    w.1 = absoluteValueExtensionPullback vK hvK
      (absoluteValueExtensionEmbeddingOfExtension vK w) := by
  ext x
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  have h := congrArg
    (fun a : AbsoluteValue (AbsoluteValue.algebraicLocalization vK w.1 w.2) ℝ =>
      a (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x))
    (absoluteValueExtension_localizationAbsoluteValue_eq_pullback vK hvK w)
  calc
    w.1 x = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) :=
      (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 x).symm
    _ = absoluteValueExtensionPullback vK hvK
        (absoluteValueExtensionEmbeddingOfExtension vK w) x := by
      change AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
        (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).comp
          (absoluteValueExtensionLocalizationEmbedding vK w).injective
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)
      exact h

/-- Clause (i) of the valuation-extension theorem: every exact extension of `v` to an algebraic
extension
`L / K` is the pullback of `\bar v` along a `K`-embedding into `\bar K_v`. -/
theorem absoluteValueExtension_extension_exists_embedding
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    ∃ tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK,
      w.1 = absoluteValueExtensionPullback vK hvK tau := by
  exact ⟨absoluteValueExtensionEmbeddingOfExtension vK w,
    absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w⟩

/-- Conjugacy of two `K`-embeddings over the completion `K_v`. -/
def AbsoluteValueExtensionConjugateOverCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ)
    (tau tau' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) : Prop :=
  ∃ sigma : absoluteValueExtensionAlgebraicCompletionClosure vK ≃ₐ[vK.Completion]
      absoluteValueExtensionAlgebraicCompletionClosure vK,
    ∀ x : L, tau' x = sigma (tau x)

/-- The unique extension `\bar v` is invariant under every automorphism over
`K_v`. -/
theorem absoluteValueExtension_algebraicClosureAbsoluteValue_algEquiv
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (sigma : absoluteValueExtensionAlgebraicCompletionClosure vK
      ≃ₐ[vK.Completion] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (x : absoluteValueExtensionAlgebraicCompletionClosure vK) :
    absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK (sigma x) =
      absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK x := by
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion)
    (L := absoluteValueExtensionAlgebraicCompletionClosure vK)
    (AbsoluteValue.completionAbsoluteValue vK)
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  let a : AbsoluteValue (absoluteValueExtensionAlgebraicCompletionClosure vK) ℝ :=
    (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).comp
      (f := sigma.toRingHom) sigma.injective
  have ha : a = absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK := by
    change a = R.extension
    apply R.unique
    intro y
    change absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK
      (sigma (algebraMap vK.Completion
        (absoluteValueExtensionAlgebraicCompletionClosure vK) y)) = _
    rw [sigma.commutes]
    exact absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap vK hvK y
  exact congrArg (fun b : AbsoluteValue _ ℝ => b x) ha

/-- Conjugate embeddings induce the same extension of `v`. -/
theorem absoluteValueExtension_pullback_eq_of_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {tau tau' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK}
    (hconj : AbsoluteValueExtensionConjugateOverCompletion vK tau tau') :
    absoluteValueExtensionPullback vK hvK tau =
      absoluteValueExtensionPullback vK hvK tau' := by
  rcases hconj with ⟨sigma, hsigma⟩
  ext x
  change absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK (tau x) =
    absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK (tau' x)
  rw [hsigma x, absoluteValueExtension_algebraicClosureAbsoluteValue_algEquiv]

/-- The dense embedding of `\bar K_v` into its metric completion. -/
noncomputable def absoluteValueExtensionAlgebraicClosureToCompletionRingHom
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    absoluteValueExtensionAlgebraicCompletionClosure vK →+*
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK)).symm.toRingHom

@[simp]
theorem absoluteValueExtension_algebraicClosureToCompletionRingHom_apply
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (x : absoluteValueExtensionAlgebraicCompletionClosure vK) :
    absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK x =
      ((WithAbs.equiv
        (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK)).symm x :
          (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion) :=
  rfl

/-- The `K_v`-algebra structure on the completion of `\bar K_v` induced by
the dense algebraic closure. -/
@[implicit_reducible]
noncomputable def absoluteValueExtensionAlgebraicClosureCompletionAlgebra
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    Algebra vK.Completion
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion :=
  ((absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK).comp
    (algebraMap vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK))).toAlgebra

/-- The dense algebraic-closure map as a `K_v`-algebra homomorphism. -/
noncomputable def absoluteValueExtensionAlgebraicClosureToCompletionAlgHom
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    letI := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
    absoluteValueExtensionAlgebraicCompletionClosure vK →ₐ[vK.Completion]
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion := by
  letI := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
  exact
    { __ := absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
      commutes' _ := rfl }

/-- A valuation-preserving `K`-embedding `tau` extends isometrically from
`L` to a map between metric completions. -/
noncomputable def absoluteValueExtensionEmbeddingToAlgebraicClosureCompletionRingHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    WithAbs w.1 →+*
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion :=
  (absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK).comp
    (tau.toRingHom.comp (WithAbs.equiv w.1).toRingHom)

theorem absoluteValueExtension_embeddingToAlgebraicClosureCompletion_norm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau)
    (x : WithAbs w.1) :
    ‖absoluteValueExtensionEmbeddingToAlgebraicClosureCompletionRingHom
        vK hvK w tau x‖ = ‖x‖ := by
  change ‖absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
    (tau (WithAbs.equiv w.1 x))‖ = ‖x‖
  rw [absoluteValueExtension_algebraicClosureToCompletionRingHom_apply,
    UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.norm_eq_apply_ofAbs]
  have h := congrArg (fun a : AbsoluteValue L ℝ =>
    a (WithAbs.equiv w.1 x)) htau
  exact h.symm

/-- The isometry on the dense field underlying the preceding completion
map. -/
theorem absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau) :
    Isometry (absoluteValueExtensionEmbeddingToAlgebraicClosureCompletionRingHom
      vK hvK w tau) :=
  AddMonoidHomClass.isometry_of_norm _
    (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_norm
      vK hvK w tau htau)

/-- Extension of `tau` to the completion `L_w`. -/
noncomputable def absoluteValueExtensionEmbeddingCompletionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau) :
    w.1.Completion →+*
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion :=
  UniformSpace.Completion.extensionHom
    (absoluteValueExtensionEmbeddingToAlgebraicClosureCompletionRingHom
      vK hvK w tau)
    (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
      vK hvK w tau htau).continuous

@[simp]
theorem absoluteValueExtension_embeddingCompletionMap_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau)
    (x : WithAbs w.1) :
    absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
        (x : w.1.Completion) =
      absoluteValueExtensionEmbeddingToAlgebraicClosureCompletionRingHom
        vK hvK w tau x :=
  UniformSpace.Completion.extensionHom_coe
    (absoluteValueExtensionEmbeddingToAlgebraicClosureCompletionRingHom
      vK hvK w tau)
    (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
      vK hvK w tau htau).continuous x

/-- The extended completion map is still an isometry. -/
theorem absoluteValueExtension_embeddingCompletionMap_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau) :
    Isometry (absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau) :=
  (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
    vK hvK w tau htau).completion_extension

/-- The map `K_v → \widehat{\bar K_v}` through the dense algebraic closure
is an isometry. -/
theorem absoluteValueExtension_completionToAlgebraicClosureCompletion_isometry
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    Isometry ((absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK).comp
      (algebraMap vK.Completion
        (absoluteValueExtensionAlgebraicCompletionClosure vK))) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change ‖absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
    (algebraMap vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK) x)‖ = ‖x‖
  rw [absoluteValueExtension_algebraicClosureToCompletionRingHom_apply,
    UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]
  change absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK
    (algebraMap vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK) x) = ‖x‖
  rw [absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap]
  rfl

/-- On `K_v`, the completion extension of `tau` agrees with the canonical
map through `\bar K_v`.  Equality on the dense copy of `K` is extended by
continuity. -/
theorem absoluteValueExtension_embeddingCompletionMap_completionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau)
    (x : vK.Completion) :
    absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
        (AbsoluteValue.completionMap vK w.1 w.2 x) =
      absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtensionAlgebraicCompletionClosure vK) x) := by
  let f := (absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau).comp
    (AbsoluteValue.completionMap vK w.1 w.2)
  let g := (absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK).comp
    (algebraMap vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK))
  change f x = g x
  refine UniformSpace.Completion.induction_on (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      ((absoluteValueExtension_embeddingCompletionMap_isometry
          vK hvK w tau htau).continuous.comp
        (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous)
      (absoluteValueExtension_completionToAlgebraicClosureCompletion_isometry
        vK hvK).continuous
  · intro a
    dsimp [f, g]
    change absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
        (AbsoluteValue.completionMap vK w.1 w.2
          (algebraMap K vK.Completion (WithAbs.equiv vK a))) =
      absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtensionAlgebraicCompletionClosure vK)
          (algebraMap K vK.Completion (WithAbs.equiv vK a)))
    rw [AbsoluteValue.completionMap_coe]
    change absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
        (((algebraMap (WithAbs vK) (WithAbs w.1)) a : WithAbs w.1) :
          w.1.Completion) =
      absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtensionAlgebraicCompletionClosure vK)
            (a : vK.Completion))
    rw [absoluteValueExtension_embeddingCompletionMap_coe]
    change absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
        (tau (algebraMap K L (WithAbs.equiv vK a))) =
      absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtensionAlgebraicCompletionClosure vK)
            (algebraMap K vK.Completion (WithAbs.equiv vK a)))
    congr 1
    rw [tau.commutes,
      IsScalarTower.algebraMap_apply K vK.Completion
        (absoluteValueExtensionAlgebraicCompletionClosure vK)]

/-- The completion extension of `tau`, bundled over `K_v`. -/
noncomputable def absoluteValueExtensionEmbeddingCompletionAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
    w.1.Completion →ₐ[vK.Completion]
      (absoluteValueExtensionAlgebraicClosureAbsoluteValue vK hvK).Completion := by
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
  exact
    { __ := absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
      commutes' x :=
        absoluteValueExtension_embeddingCompletionMap_completionMap
          vK hvK w tau htau x }

/-- The image of the localization under the completed embedding lies in the
dense algebraic closure inside its completion. -/
theorem absoluteValueExtension_embeddingCompletionAlgHom_mem_range
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau)
    (z : AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
    absoluteValueExtensionEmbeddingCompletionAlgHom vK hvK w tau htau (z : w.1.Completion)
      ∈ (absoluteValueExtensionAlgebraicClosureToCompletionAlgHom vK hvK).range := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtensionEmbeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtensionAlgebraicClosureToCompletionAlgHom vK hvK
  change F (z : w.1.Completion) ∈ j.range
  apply IntermediateField.adjoin_induction
      (F := vK.Completion)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
      (p := fun x _ => F x ∈ j.range)
      (x := (z : w.1.Completion))
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨tau y, ?_⟩
    symm
    change absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
      (AbsoluteValue.toCompletion w.1 y) =
        absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK (tau y)
    change absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
      (((WithAbs.equiv w.1).symm y : WithAbs w.1) : w.1.Completion) = _
    rw [absoluteValueExtension_embeddingCompletionMap_coe]
    rfl
  · intro x
    refine ⟨algebraMap vK.Completion
      (absoluteValueExtensionAlgebraicCompletionClosure vK) x, ?_⟩
    exact (absoluteValueExtension_embeddingCompletionMap_completionMap
      vK hvK w tau htau x).symm
  · intro x y _ _ hx hy
    simpa only [map_add] using j.range.add_mem hx hy
  · intro x _ hx
    rcases hx with ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    simpa only [map_inv₀] using congrArg Inv.inv ha
  · intro x y _ _ hx hy
    simpa only [map_mul] using j.range.mul_mem hx hy
  · exact z.property

/-- A valuation-preserving embedding `tau : L → \bar K_v` extends to a
`K_v`-embedding of the common localization.  The construction first extends
to metric completions and then factors through the actual dense copy of
`\bar K_v`; no completeness of the algebraic closure is assumed. -/
noncomputable def absoluteValueExtensionLocalizationEmbeddingOfPullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 →ₐ[vK.Completion]
      absoluteValueExtensionAlgebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtensionEmbeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtensionAlgebraicClosureToCompletionAlgHom vK hvK
  let f : E →ₐ[vK.Completion] j.range :=
    (F.comp E.val).codRestrict j.range
      (absoluteValueExtension_embeddingCompletionAlgHom_mem_range
        vK hvK w tau htau)
  exact (AlgEquiv.ofInjectiveField j).symm.toAlgHom.comp f

/-- The extended localization embedding restricts to the original `tau` on
the dense copy of `L`. -/
theorem absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtensionPullback vK hvK tau)
    (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    absoluteValueExtensionLocalizationEmbeddingOfPullback vK hvK w tau htau
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) = tau x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let := absoluteValueExtensionAlgebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtensionEmbeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtensionAlgebraicClosureToCompletionAlgHom vK hvK
  apply j.injective
  change j ((AlgEquiv.ofInjectiveField j).symm
      ⟨F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x),
        absoluteValueExtension_embeddingCompletionAlgHom_mem_range
          vK hvK w tau htau _⟩) = j (tau x)
  rw [show j ((AlgEquiv.ofInjectiveField j).symm
      ⟨F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x),
        absoluteValueExtension_embeddingCompletionAlgHom_mem_range
          vK hvK w tau htau _⟩) =
      F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) by
        exact congrArg Subtype.val
          ((AlgEquiv.ofInjectiveField j).apply_symm_apply _)]
  change absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
      (AbsoluteValue.toCompletion w.1 x) =
    absoluteValueExtensionAlgebraicClosureToCompletionRingHom vK hvK (tau x)
  change absoluteValueExtensionEmbeddingCompletionMap vK hvK w tau htau
      (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.1.Completion) = _
  rw [absoluteValueExtension_embeddingCompletionMap_coe]
  rfl

/-- Two embeddings of an algebraic extension into an algebraic closure are
conjugate by an automorphism of that algebraic closure.  The algebra structure
on the closure over `E` is induced by the first embedding. -/
theorem absoluteValueExtension_algHom_conjugate_in_algClosure
    {F E A : Type*} [Field F] [Field E] [Field A]
    [Algebra F E] [Algebra F A]
    [IsAlgClosure F A]
    (phi phi' : E →ₐ[F] A) :
    ∃ sigma : A ≃ₐ[F] A, ∀ x : E, sigma (phi x) = phi' x := by
  let : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  let : Algebra E A := phi.toRingHom.toAlgebra
  let : IsScalarTower F E A :=
    IsScalarTower.of_algebraMap_eq' phi.comp_algebraMap.symm
  let : Algebra.IsAlgebraic E A :=
    Algebra.IsAlgebraic.tower_top (K := F) E
  obtain ⟨psi, hpsi⟩ :=
    IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := F) (L := E) (M := A) (E := A) phi'
  let sigma : A ≃ₐ[F] A := AlgEquiv.ofBijective psi
    (Algebra.IsAlgebraic.algHom_bijective psi)
  refine ⟨sigma, fun x => ?_⟩
  have hx := DFunLike.congr_fun hpsi x
  change psi (phi x) = phi' x
  change psi (algebraMap E A x) = phi' x at hx
  rw [RingHom.algebraMap_toAlgebra] at hx
  have hphi : phi.toRingHom x = phi x :=
    congrFun (AlgHom.coe_toRingHom phi) x
  rw [hphi] at hx
  exact hx

/-- The difficult direction of clause (ii) of the valuation-extension theorem: equality of
pullback absolute
values forces conjugacy over `K_v`. -/
theorem absoluteValueExtension_conjugate_of_pullback_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {tau tau' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK}
    (h : absoluteValueExtensionPullback vK hvK tau =
      absoluteValueExtensionPullback vK hvK tau') :
    AbsoluteValueExtensionConjugateOverCompletion vK tau tau' := by
  let w : AbsoluteValueExtension vK L :=
    ⟨absoluteValueExtensionPullback vK hvK tau,
      absoluteValueExtension_pullback_extends vK hvK tau⟩
  have htau : w.1 = absoluteValueExtensionPullback vK hvK tau := rfl
  have htau' : w.1 = absoluteValueExtensionPullback vK hvK tau' := h
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let phi := absoluteValueExtensionLocalizationEmbeddingOfPullback
    vK hvK w tau htau
  let phi' := absoluteValueExtensionLocalizationEmbeddingOfPullback
    vK hvK w tau' htau'
  let : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  obtain ⟨sigma, hsigma⟩ :=
    absoluteValueExtension_algHom_conjugate_in_algClosure phi phi'
  refine ⟨sigma, fun x => ?_⟩
  rw [← absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vK hvK w tau htau x,
    ← absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vK hvK w tau' htau' x]
  exact (hsigma (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)).symm

/-- Clause (ii) of the valuation-extension theorem: two embeddings induce the same extension
exactly when
they are conjugate by an automorphism over the completion `K_v`. -/
theorem absoluteValueExtension_pullback_eq_iff_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau tau' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    absoluteValueExtensionPullback vK hvK tau =
        absoluteValueExtensionPullback vK hvK tau' ↔
      AbsoluteValueExtensionConjugateOverCompletion vK tau tau' := by
  constructor
  · exact absoluteValueExtension_conjugate_of_pullback_eq vK hvK
  · exact absoluteValueExtension_pullback_eq_of_conjugate vK hvK

/-- The valuation-extension theorem, with its two clauses packaged together.
The only global side condition is that the base absolute value is
nontrivial. -/
theorem absoluteValueExtension_extension_theorem
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    (∀ w : AbsoluteValueExtension vK L,
      ∃ tau : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK,
        w.1 = absoluteValueExtensionPullback vK hvK tau) ∧
    (∀ tau tau' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK,
      absoluteValueExtensionPullback vK hvK tau =
          absoluteValueExtensionPullback vK hvK tau' ↔
        AbsoluteValueExtensionConjugateOverCompletion vK tau tau') := by
  exact ⟨absoluteValueExtension_extension_exists_embedding vK hvK,
    absoluteValueExtension_pullback_eq_iff_conjugate vK hvK⟩

end Valuations
end AlgebraicNumberTheory

end

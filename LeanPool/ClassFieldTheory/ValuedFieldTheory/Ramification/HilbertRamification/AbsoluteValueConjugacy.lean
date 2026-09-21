/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.AbsoluteValueExtensions
/-!
# Valuation conjugacy

For a possibly infinite Galois extension `L/K`, the Galois group acts
transitively on the extensions to `L` of a nontrivial absolute value of `K`.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- Pull an absolute value back by a field automorphism.  This is the canonical
right action `w ↦ w ∘ σ`. -/
def absoluteValueConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) : AbsoluteValue L ℝ :=
  w.comp (f := σ.toRingEquiv.toRingHom) σ.injective

@[simp] theorem absoluteValueConjugate_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) (x : L) :
    absoluteValueConjugate w σ x = w (σ x) :=
  rfl

/-- Conjugating an extension by a ground-field automorphism gives another
exact extension of the same base absolute value. -/
theorem absoluteValueConjugate_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) :
    AbsoluteValue.Extends vK (absoluteValueConjugate w.1 σ) := by
  intro x
  rw [absoluteValueConjugate_apply, σ.commutes, w.2 x]

/-- The conjugated extension as an element of the exact-extension type. -/
def absoluteValueExtensionConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) : AbsoluteValueExtension vK L :=
  ⟨absoluteValueConjugate w.1 σ,
    absoluteValueConjugate_extends vK w σ⟩

/-- Equivalent exact extensions of a nontrivial base absolute value are equal.
Thus `AbsoluteValueExtension vK L` is a faithful normalized model for the
absolute-value classes lying over the class of `vK`. -/
theorem equivalent_exactExtensions_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L)
    (h : LubinTate.Valuations.EquivalentAbsoluteValues w.1 w'.1) :
    w = w' := by
  rcases (LubinTate.Valuations.equivalentAbsoluteValues_iff_exists_rpow_eq w.1 w'.1).mp h with
    ⟨s, hs, hpow⟩
  rcases hvK with ⟨a, ha, hva⟩
  have hbase : vK a ^ s = vK a := by
    have hpoint := congrFun hpow (algebraMap K L a)
    simpa [w.2 a, w'.2 a] using hpoint
  have hs_one : s = 1 :=
    (Real.rpow_right_inj (vK.pos ha) hva).mp (by simpa using hbase)
  apply Subtype.ext
  ext x
  have hpoint := congrFun hpow x
  simpa [hs_one] using hpoint

/-- Normality descent for the embeddings supplied by the valuation-extension theorem: two exact
extensions differ by an actual `K`-automorphism of `L`, not merely by an
automorphism of the ambient algebraic closure. -/
theorem absoluteValueConjugacy_exists_conjugatingAlgEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L, w'.1 = absoluteValueConjugate w.1 σ := by
  let A := absoluteValueExtension_algebraicCompletionClosure vK
  let τ : L →ₐ[K] A := absoluteValueExtension_embeddingOfExtension vK w
  let τ' : L →ₐ[K] A := absoluteValueExtension_embeddingOfExtension vK w'
  let : Algebra L A := τ.toRingHom.toAlgebra
  let : IsScalarTower K L A :=
    IsScalarTower.of_algebraMap_eq' τ.comp_algebraMap.symm
  let σ : L ≃ₐ[K] L := Normal.algHomEquivAut K A L τ'
  refine ⟨σ, ?_⟩
  rw [absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w',
    absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w]
  ext x
  change
    absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (τ' x) =
      absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (τ (σ x))
  congr 1
  simpa [σ, τ, AlgHom.restrictNormal', RingHom.algebraMap_toAlgebra] using
    (τ'.restrictNormal_commutes L x).symm

/-- The valuation-conjugacy theorem: the Galois group acts transitively
on the exact extensions of a nontrivial valuation.  This statement covers
finite and infinite Galois extensions and both archimedean and
nonarchimedean absolute values. -/
theorem absoluteValueConjugacy
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L,
      w' = absoluteValueExtensionConjugate vK w σ := by
  rcases absoluteValueConjugacy_exists_conjugatingAlgEquiv vK hvK w w' with
    ⟨σ, hσ⟩
  exact ⟨σ, Subtype.ext hσ⟩

/-- Class-level form of the valuation-conjugacy theorem.  The exact-representative equality
above in particular gives equality of the corresponding absolute value
classes. -/
theorem absoluteValueConjugacy_valuationClass
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L,
      LubinTate.Valuations.EquivalentAbsoluteValues w'.1
        (absoluteValueExtensionConjugate vK w σ).1 := by
  rcases absoluteValueConjugacy vK hvK w w' with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  rw [← hσ]
  exact LubinTate.Valuations.equivalentAbsoluteValues_refl w'.1

end Valuations
end AlgebraicNumberTheory

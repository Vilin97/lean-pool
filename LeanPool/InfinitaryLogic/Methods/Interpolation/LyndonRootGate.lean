/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.RootGate
import LeanPool.InfinitaryLogic.Methods.PolarityCalculus
/-!
# The signed root gate (issue #14, Unit 5, commit 1)

The polarity-refined twin of `base_interpolant_of_empty_support_separator`: at the root of the
argument the allowed constant support is empty, so any separator is constant-free and strips to a
base-language sentence — and the strip carries **all three** occurrence bounds, the two signed
relation bounds included.

No new semantics: the entailment transport is the existing `entails_reduct_of_entails_map`, and the
signed bound is the Unit-0 calculus lemma `relationsInSigned_stripConsts`.  Nothing here inducts
over formulas.

The file is deliberately **neutral**: it imports only the unsigned root gate and the signed
occurrence calculus, so the paired/countable-completion machinery enters the Lyndon development
only at the countable core (`LyndonRelational.lean`), which is its first semantic consumer.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-- **The signed root gate**: an empty-support `L[[ℕ]]`-separator of the `mapLanguage`-images of
`(Γ₀, Δ₀)` strips to a genuine base-language interpolant whose function symbols, **positive**
relation occurrences, and **negative** relation occurrences are each bounded by the separator's
corresponding base sets. -/
theorem base_lyndon_interpolant_of_empty_support_separator {Γ₀ Δ₀ : Set L.Sentenceω}
    (σ : L[[ℕ]].Sentenceω)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅)
    (hΓ : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Γ₀) σ)
    (hΔ : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Δ₀) σ.not) :
    ∃ θ₀ : L.Sentenceω,
      θ₀.functionsIn ⊆ σ.baseFunctionsIn ∧
      θ₀.positiveRelationsIn ⊆ σ.basePositiveRelations ∧
      θ₀.negativeRelationsIn ⊆ σ.baseNegativeRelations ∧
      Theoryω.Entails Γ₀ θ₀ ∧ Theoryω.Entails Δ₀ θ₀.not := by
  refine ⟨σ.stripConsts hsupp, BoundedFormulaω.functionsIn_stripConsts σ hsupp,
    relationsInSigned_stripConsts true σ hsupp, relationsInSigned_stripConsts false σ hsupp,
    ?_, ?_⟩
  · apply entails_reduct_of_entails_map
    rw [BoundedFormulaω.mapLanguage_stripConsts σ hsupp]
    exact hΓ
  · apply entails_reduct_of_entails_map
    rw [BoundedFormulaω.mapLanguage_not, BoundedFormulaω.mapLanguage_stripConsts σ hsupp]
    exact hΔ

end FirstOrder.Language

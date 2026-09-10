/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.RootGate
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# The Malitz root gate (issue #15)

Neutral companion to `LyndonRootGate.lean`.  Where the Lyndon gate carries *signed relation*
occurrences through the strip, this one carries the *quantifier class*: an empty-support universal
`L[[ℕ]]`-separator strips to a genuine **universal** base-language interpolant.

Nothing here is new semantics.  The entailment transport is the existing reduct bridge
(`entails_reduct_of_entails_map`), the occurrence bounds are the existing `stripConsts` lemmas, and
universality is the class-preservation lemma proved alongside `stripConsts` itself.  This file is
composition only.
-/

namespace FirstOrder.Language

open FirstOrder BoundedFormulaω

variable {L : Language.{0, 0}}

/-- **The Malitz root gate**: an empty-support *universal* `L[[ℕ]]`-separator of the
`mapLanguage`-images of `(Γ₀, Δ₀)` strips to a base-language interpolant that is still universal and
whose function and relation occurrences are bounded by the separator's base sets.

Constant-freeness has done its work by this point and disappears from the conclusion, which is what
lets the public theorem avoid exposing any Henkin bookkeeping. -/
theorem base_malitz_interpolant_of_empty_support_separator {Γ₀ Δ₀ : Set L.Sentenceω}
    (σ : L[[ℕ]].Sentenceω)
    (hσU : IsUniversal σ)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅)
    (hΓ : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Γ₀) σ)
    (hΔ : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Δ₀) σ.not) :
    ∃ θ₀ : L.Sentenceω,
      IsUniversal θ₀ ∧
      θ₀.functionsIn ⊆ σ.baseFunctionsIn ∧
      θ₀.relationsIn ⊆ σ.baseRelationsIn ∧
      Theoryω.Entails Γ₀ θ₀ ∧ Theoryω.Entails Δ₀ θ₀.not := by
  refine ⟨σ.stripConsts hsupp,
    (BoundedFormulaω.universalSigned_stripConsts true σ hsupp).mpr hσU,
    BoundedFormulaω.functionsIn_stripConsts σ hsupp,
    BoundedFormulaω.relationsIn_stripConsts σ hsupp, ?_, ?_⟩
  · apply entails_reduct_of_entails_map
    rw [BoundedFormulaω.mapLanguage_stripConsts σ hsupp]
    exact hΓ
  · apply entails_reduct_of_entails_map
    rw [BoundedFormulaω.mapLanguage_not, BoundedFormulaω.mapLanguage_stripConsts σ hsupp]
    exact hΔ

end FirstOrder.Language

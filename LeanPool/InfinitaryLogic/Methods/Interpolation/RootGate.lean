/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.Inseparability
/-!
# The semantic root gate (issue #8 tranche 1.5 item 2)

At the root of the interpolation argument the allowed constant support is empty, so any
separator is constant-free and strips to a base-language sentence (`stripConsts`). This file
turns that *syntactic* left inverse into the *semantic* bridge the argument needs:

* `entails_reduct_of_entails_map` — a cross-language entailment bridge: an `L[[ℕ]]`-entailment
  between `mapLanguage`-images descends to the base `L`-entailment (lift every base structure
  by dummy constants; realization of a `mapLanguage`-image is realization in the reduct);
* `base_interpolant_of_empty_support_separator` — an empty-support `L[[ℕ]]`-separator strips to
  an actual base-language interpolant with the correct symbol-occurrence bounds and both
  `L`-entailments. This makes "`InsepAt ∅` yields no base interpolant" a theorem, not a
  documented future composition.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {α : Type}

/-- **Cross-language entailment bridge**: if the `mapLanguage`-images of `Γ₀` entail the
`mapLanguage`-image of `φ` over `L[[ℕ]]`, then `Γ₀` entails `φ` over `L`. Proof: lift an
arbitrary base model by interpreting every fresh constant as a fixed element; realization of a
`mapLanguage`-image equals realization in the reduct (`realize_mapLanguage`). -/
theorem entails_reduct_of_entails_map {Γ₀ : Set L.Sentenceω} {φ : L.Sentenceω}
    (hE : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Γ₀)
            (φ.mapLanguage (L.lhomWithConstants ℕ))) :
    Theoryω.Entails Γ₀ φ := by
  intro M instM neM hmodel
  let : L[[ℕ]].Structure M := wc instM (fun _ => Classical.arbitrary M)
  have hmodel' : Theoryω.Model
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Γ₀) M := by
    intro ψ hψ
    obtain ⟨γ, hγ, rfl⟩ := hψ
    exact (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) γ
      (Empty.elim : Empty → M) Fin.elim0).mpr (hmodel γ hγ)
  exact (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) φ
    (Empty.elim : Empty → M) Fin.elim0).mp (hE M hmodel')

/-- **The root gate**: an empty-support `L[[ℕ]]`-separator of the `mapLanguage`-images of
`(Γ₀, Δ₀)` strips to a genuine base-language interpolant — a sentence with symbols bounded by
the separator's base symbols, entailed by `Γ₀` and refuting `Δ₀`. -/
theorem base_interpolant_of_empty_support_separator {Γ₀ Δ₀ : Set L.Sentenceω}
    (σ : L[[ℕ]].Sentenceω)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅)
    (hΓ : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Γ₀) σ)
    (hΔ : Theoryω.Entails (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' Δ₀) σ.not) :
    ∃ θ₀ : L.Sentenceω,
      θ₀.functionsIn ⊆ σ.baseFunctionsIn ∧ θ₀.relationsIn ⊆ σ.baseRelationsIn ∧
      Theoryω.Entails Γ₀ θ₀ ∧ Theoryω.Entails Δ₀ θ₀.not := by
  refine ⟨σ.stripConsts hsupp, BoundedFormulaω.functionsIn_stripConsts σ hsupp,
    BoundedFormulaω.relationsIn_stripConsts σ hsupp, ?_, ?_⟩
  · apply entails_reduct_of_entails_map
    rw [BoundedFormulaω.mapLanguage_stripConsts σ hsupp]
    exact hΓ
  · apply entails_reduct_of_entails_map
    rw [BoundedFormulaω.mapLanguage_not, BoundedFormulaω.mapLanguage_stripConsts σ hsupp]
    exact hΔ

/-! ## The semantic contraposition / singleton bridge -/

/-- **Semantic contraposition (singleton form)**: `{r₂.not} ⊨ θ.not` is `{θ} ⊨ r₂`. -/
theorem entails_singleton_of_neg_entails_neg {r₂ θ : L.Sentenceω}
    (hE : Theoryω.Entails {r₂.not} θ.not) : Theoryω.Entails {θ} r₂ := by
  intro M _ _ hmodel
  by_contra hr₂
  have hnr₂ : Theoryω.Model {r₂.not} M := by
    intro ψ hψ; rw [Set.mem_singleton_iff] at hψ; subst hψ
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hr₂
  have := hE M hnr₂
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this
  exact this (hmodel θ (Set.mem_singleton _))

end FirstOrder.Language

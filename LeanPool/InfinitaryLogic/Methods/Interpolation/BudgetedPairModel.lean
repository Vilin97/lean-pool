/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.BudgetedPairCompletion
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTruthLemma
/-!
# The budgeted labelled pair's countermodel (issue #15)

Turns the completion of the labelled root pair into an actual model: from budgeted inseparability of
`({r₁}, {r₂.not})` — which by `budgetedPairInsep_root_of_no_interpolant` follows from *absence of an
admissible interpolant* — a structure satisfying `r₁` and refuting `r₂`.

This is the countermodel that contradicts `r₁ ⊨ r₂` in the final interpolation argument.

## Boundaries

* `[L.IsRelational]` enters **here**, as the quotient term model requires it; the completion step
  does not.
* Relation-symbol countability is inherited from the completion step and is consumed only there.
* Both labelled roots are read off with the **positive** truth direction, matching how the family was
  seeded; the negative direction of the truth lemma is discarded, so no polarity argument is needed.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}

/-- **The model endpoint.**  A labelled root member yields a model of `r₁` refuting `r₂`. -/
theorem exists_budgetedPair_model {r₁ r₂ : L[[ℕ]].Sentenceω}
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hroot : BudgetedPairMem r₁ r₂.not F₁ R₁ F₂ R₂ ({r₁} ∪ {r₂.not})) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      Sentenceω.Realize r₁ M ∧ ¬ Sentenceω.Realize r₂ M := by
  obtain ⟨Sstar, hsub, hcomplete⟩ :=
    exists_henkinComplete_budgetedPairRoot (F₁ := F₁) (R₁ := R₁) (F₂ := F₂) (R₂ := R₂)
      hr₁ hr₂ hroot
  obtain ⟨M, instM, neM, hpos, -⟩ := exists_model_of_henkinComplete hcomplete
  have h₁ : r₁ ∈ Sstar := hsub (Or.inl rfl)
  have h₂ : r₂.not ∈ Sstar := hsub (Or.inr rfl)
  refine ⟨M, instM, neM, hpos _ h₁, ?_⟩
  have := hpos _ h₂
  rwa [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this

end FirstOrder.Language

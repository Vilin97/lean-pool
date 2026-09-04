/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.BudgetedPair
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.FairEnumeration
/-!
# Completing the budgeted labelled pair (issue #15)

The first consumer of `budgetedPairConsistencyProperty`.  It does one thing: run the fair Henkin
completion on the labelled root member and expose the result **opaquely**, as containment plus
`HenkinComplete`.

The internal `S* ⊆ GenU` fact is deliberately dropped.  The model endpoint should consume a
completion, not a subset of a particular universe, so that swapping the completion strategy cannot
ripple outward.

## Boundaries

* Countability of the generated universe is *derived*, not assumed: `genU_countable` needs only
  `[Countable (Σ l, L.Relations l)]`, which is the honest boundary here.
* **No `L.IsRelational`.**  Relationality is a requirement of the quotient term model, so it belongs
  to the model endpoint, not to completion.
* Finite constant support is accepted for `r₂` rather than for the labelled right root `r₂.not`, and
  converted locally — the interpolation consumer holds the former.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} [Countable (Σ l, L.Relations l)]
variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}

/-- **The completion endpoint.**  From a labelled root member, a Henkin-complete superset of the
root pair.

Stated with finite support of `r₂` rather than of `r₂.not`; the two are equal, but the former is what
an interpolation consumer has to hand. -/
theorem exists_henkinComplete_budgetedPairRoot {r₁ r₂ : L[[ℕ]].Sentenceω}
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hroot : BudgetedPairMem r₁ r₂.not F₁ R₁ F₂ R₂ ({r₁} ∪ {r₂.not})) :
    ∃ Sstar : Set L[[ℕ]].Sentenceω,
      ({r₁} ∪ {r₂.not} : Set L[[ℕ]].Sentenceω) ⊆ Sstar ∧
        HenkinComplete (GenU r₁ r₂.not) Sstar := by
  have hr₂' : (sentenceJConsts (L' := L) (J := ℕ) r₂.not).Finite := by
    rwa [sentenceJConsts_not]
  have : Countable ↥(GenU (L := L) r₁ r₂.not) := genU_countable.to_subtype
  obtain ⟨Sstar, hsub, -, hcomplete⟩ :=
    exists_henkinComplete (U := GenU r₁ r₂.not)
      (P := budgetedPairConsistencyProperty F₁ R₁ F₂ R₂ r₁ r₂.not hr₁ hr₂')
      (S₀ := ⟨({r₁} ∪ {r₂.not} : Set L[[ℕ]].Sentenceω), hroot⟩)
  exact ⟨Sstar, hsub, hcomplete⟩

end FirstOrder.Language

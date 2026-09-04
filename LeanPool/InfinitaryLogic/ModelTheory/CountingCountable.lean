/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.CountingModels
import LeanPool.InfinitaryLogic.Descriptive.FiniteCarrier
/-!
# Counting Theorem for All Countable Models

This file provides the user-facing counting theorem for all countable models
of an Lω₁ω sentence with bounded Scott height. It combines the ℕ-coded
result (via BF-equivalence Borelness) with finite-carrier results (via
permutation orbits) from `FiniteCarrier.lean`.

The type `AllCodedIsoClasses φ` faithfully represents all isomorphism classes
of countable models of φ, as established by the bridge theorems:
- `codeModel`: maps any countable model to a coded iso class
- `codeModel_eq_of_iso`: L-isomorphic models yield the same class
- `iso_of_codeModel_eq`: same class implies L-isomorphic
- `codeModel_surjective`: every class is realized

## Main Result

- `counting_countable_models_bounded_scottHeight`: The number of isomorphism
  classes of countable models (with bounded Scott height) is ≤ ℵ₀ or = 2^ℵ₀.

The stronger unconditional-height version (≤ ℵ₁ or 2^ℵ₀) is
`FirstOrder.Language.morley_counting` in `ModelTheory/MorleyCounting.lean`.
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- Bounded-Scott-height counting theorem for all countable models.
The total number of isomorphism classes of countable models of φ
(with bounded Scott height) is either ≤ ℵ₀ or exactly 2^ℵ₀.

This combines ℕ-coded models (BF-equivalence Borelness, `counting_coded_models_dichotomy`)
with finite-carrier models (permutation orbits, `counting_fin_models_dichotomy`).
`AllCodedIsoClasses φ` faithfully represents all iso classes of countable models
(by `codeModel`, `codeModel_eq_of_iso`, `iso_of_codeModel_eq`, `codeModel_surjective`). -/
theorem counting_countable_models_bounded_scottHeight
    (silver : SilverBurgessDichotomy.{v})
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    (#(AllCodedIsoClasses φ) ≤ ℵ₀) ∨
    (#(AllCodedIsoClasses φ) = Cardinal.continuum) :=
  allCodedIsoClasses_dichotomy silver hα hbound

end Language

end FirstOrder

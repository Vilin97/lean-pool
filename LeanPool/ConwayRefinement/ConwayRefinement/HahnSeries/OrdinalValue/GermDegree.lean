/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

/-!
# Degree bounds for translated truncations

Translated closed truncation at a real exponent does not increase Hahn-series degree. Since
Berarducci's ordinal-value degree is bounded by Hahn-series degree, the same bound holds for the
ordinal-value degree of every translated truncation.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- Translated closed truncation does not increase Hahn-series degree. -/
theorem degree_translatedTruncation_le (b : K⟦ℝ⟧) (γ : ℝ) :
    ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).degree ≤ b.degree := by
  rw [coe_translatedTruncation, HahnSeries.degree_translate]
  exact HahnSeries.degree_truncLE_le γ b

/-- The ordinal-value degree of a translated closed truncation is bounded by the degree of the
original Hahn series. -/
theorem ordinalValueDegree_translatedTruncation_le_degree (b : K⟦ℝ⟧) (γ : ℝ) :
    ordinalValueDegree (translatedTruncation b γ) ≤ b.degree :=
  (ordinalValueDegree_le_degree (translatedTruncation b γ)).trans
    (degree_translatedTruncation_le b γ)

end Berarducci

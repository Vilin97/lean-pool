/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.IntegerApproximation
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalCoefficients

/-!
# The balanced-combination lemma

The positive rational barycenter is chosen at the largest centrality.
Bounded integer correction then supplies every sufficiently large weight,
with its lower fraction and threshold independent of centrality.
-/

namespace EGZ

/-- The balanced-combination lemma, with the uniform quantifier order in
the statement `BalancedCombinationLemma`. -/
theorem balanced_combination_lemma : BalancedCombinationLemma := by
  intro d D ε hε
  obtain ⟨β, hβ, hsum, hvec, hcap⟩ :=
    D.positive_rational_capped_barycenter_exists (η := ε / 2) (by positivity)
  exact D.exists_coefficients_of_rational ε hε β hβ hsum hvec hcap

end EGZ

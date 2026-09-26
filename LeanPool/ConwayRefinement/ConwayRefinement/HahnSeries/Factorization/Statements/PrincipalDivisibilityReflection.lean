/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.PrincipalScalarRedistribution

/-!
# Divisibility reflection over the principal graded fraction field

This module states LM24, Remark 6.3.5. Under the identification from Remark 6.1.3, coefficient
extension embeds `K(ℝ^{≤0})` in `Frac(P̂)(ℝ^{≤0})`. An extended finite-support series
divides another extended series if and only if the corresponding divisibility already holds over
`K`.

The reverse implication uses Lemma 6.3.4 to redistribute a nonzero fraction-field scalar. A
nonzero coefficient of the first factor then forces that scalar to belong to `K`.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- LM24, Remark 6.3.5: coefficient extension from `K(ℝ^{≤0})` to
`Frac(P̂)(ℝ^{≤0})` reflects divisibility. -/
theorem principalSubringFractionScalarExtension_dvd_iff
    (p q : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) :
    principalSubringFractionScalarExtension K p ∣
        principalSubringFractionScalarExtension K q ↔
      p ∣ q := by
  apply principalSubringFractionScalarExtension_dvd_iff_of_scalarRedistribution ?_ p q
  intro p₁ p₂ hp₁ hp₂ hprod
  exact principalSubringFraction_exists_scalarRedistribution hp₁ hp₂ hprod

end

end Berarducci

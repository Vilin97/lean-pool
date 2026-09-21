/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringScalarRedistributionProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.PrincipalSubringFraction

/-!
# Scalar redistribution over the principal graded fraction field

This module states LM24, Lemma 6.3.4. For nonzero finite-support series `p₁` and `p₂` over
`Frac(P̂)` whose product has coefficients in `K`, a nonzero coefficient `B ∈ Frac(P̂)` can be
moved from one factor to the other so that both resulting series have coefficients in `K`.

The rendered statement writes `B⁻¹`, which conventionally presupposes `B ≠ 0`. Because
inversion is total in Lean, the theorem records that condition explicitly. The final theorem proves
that the formula without this condition is satisfied by `B = 0` for arbitrary inputs; it is a
regression theorem, not the mathematical content of Lemma 6.3.4.
-/

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- LM24, Lemma 6.3.4, with the conventional nonzeroness of the inverted coefficient made
explicit. -/
theorem principalSubringFraction_exists_scalarRedistribution
    {p₁ p₂ : PrincipalSubringFractionFiniteSupportRing K}
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hprod : p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K) :
    ∃ B : PrincipalSubringFractionField K,
      B ≠ 0 ∧
        p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
          principalSubringFractionCoefficientSubring K ∧
        p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
          principalSubringFractionCoefficientSubring K := by
  apply principalSubringFraction_exists_scalarRedistribution_of_isRelativelyAlgebraicallyClosed
    (isRelativelyAlgebraicallyClosed_principalGradedFractionField K)
    hp₁ hp₂ hprod

/-- If the nonzeroness of the inverted coefficient is omitted, Lean's total inverse makes the
displayed conclusion hold for arbitrary factors by taking the coefficient to be zero. -/
theorem principalSubringFraction_exists_literalTotalInverseScalarRedistribution
    (p₁ p₂ : PrincipalSubringFractionFiniteSupportRing K) :
    ∃ B : PrincipalSubringFractionField K,
      p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
          principalSubringFractionCoefficientSubring K ∧
        p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
          principalSubringFractionCoefficientSubring K := by
  refine ⟨0, ?_, ?_⟩ <;> simp

end

end Berarducci

/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction
public import LeanPool.ConwayRefinement.ConwayRefinement.FieldTheory.RelativeAlgebraicClosure

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFractionAlgebraic

/-!
# Relative algebraic closure in the principal graded fraction field

This module states LM24, Lemma 6.3.3: the coefficient field is relatively algebraically closed in
the fraction field of `P̂`. Equivalently, every element of `Frac(P̂)` that is
algebraic over `K` already belongs to the image of `K`. The coefficient field has characteristic
zero, which supplies the ordinal-value multiplicativity behind the ring structure on the intrinsic
ring `P̂`.

The proof reduces to the minimal-polynomial bound for a nonzero algebraic fraction, which is
established in the Berarducci development.
-/

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

variable (K) in
/-- LM24, Lemma 6.3.3: `K` is relatively algebraically closed in `Frac(P̂)`. -/
theorem isRelativelyAlgebraicallyClosed_principalGradedFractionField :
    @Algebra.IsRelativelyAlgebraicallyClosed K
      (PrincipalSubringFractionField K) _ _
      (principalSubringFractionAlgebra K) := by
  let := principalSubringFractionAlgebra K
  apply Algebra.isRelativelyAlgebraicallyClosed_of_minpoly_natDegree_le_one
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp
  · exact principalSubringFraction_minpoly_natDegree_le_one_of_ne_zero x hx hx0

end

end Berarducci

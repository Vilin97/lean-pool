/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedIrreducibility

/-!
# Exact bidegree of the weighted middle-game trace curve

Corvaja--Zannier Corollary 2 uses the two coordinate degrees of the affine
torus curve.  This module computes those degrees for the actual reduced
weighted trace closure.  The two-variable polynomial is transported through
the explicit `Fin 2` multivariate-to-iterated-polynomial equivalence already
used in the irreducibility proof; swapping the two polynomial variables
computes the second coordinate degree.
-/

namespace BGS.Markoff

open Polynomial

variable {K : Type*} [Field K]

/-- The weighted trace closure has degree two in the right trace coordinate. -/
theorem weightedTraceIteratedPolynomial_right_natDegree (alpha beta : K) :
    (weightedTraceIteratedPolynomial alpha beta).natDegree = 2 := by
  apply Nat.le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hn0 : N ≠ 0 := by omega
    have h1 : 1 ≠ N := by omega
    have h2 : 2 ≠ N := by omega
    simp [weightedTraceIteratedPolynomial, coeff_monomial, h1, h2,
      coeff_C_of_ne_zero hn0]
  · apply le_natDegree_of_ne_zero
    simp [weightedTraceIteratedPolynomial, coeff_monomial]

/-- The weighted trace closure has degree two in the left weighted coordinate
when its leading weight is nonzero. -/
theorem weightedTraceIteratedPolynomial_left_natDegree
    (alpha beta : K) (halpha : alpha ≠ 0) :
    (Polynomial.Bivariate.swap
      (weightedTraceIteratedPolynomial alpha beta)).natDegree = 2 := by
  have hswap :
      Polynomial.Bivariate.swap (weightedTraceIteratedPolynomial alpha beta) =
        monomial 2 (C alpha * X) +
          monomial 1 (-(X ^ 2 + 1)) + C (C beta * X) := by
    simp [weightedTraceIteratedPolynomial, Polynomial.Bivariate.swap_apply,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    ring
  rw [hswap]
  apply Nat.le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hn0 : N ≠ 0 := by omega
    have h1 : 1 ≠ N := by omega
    have h2 : 2 ≠ N := by omega
    simp [coeff_monomial, h1, h2, coeff_C_of_ne_zero hn0]
  · apply le_natDegree_of_ne_zero
    simp [coeff_monomial, halpha]

/-- In the nonzero-weight branch used by the Markoff middle game, the reduced
torus closure has exact bidegree `(2, 2)`.  The pair is expressed through the
explicit iterated-polynomial presentation, so no informal support convention
is hidden in the statement. -/
theorem weightedTraceTorusClosurePolynomial_iteratedBidegree
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    let p := finTwoToIteratedPolynomial (K := K)
      (weightedTraceTorusClosurePolynomial alpha beta)
    (p.natDegree, (Polynomial.Bivariate.swap p).natDegree) = (2, 2) := by
  rw [finTwoToIteratedPolynomial_weightedTraceTorusClosurePolynomial
    alpha beta hbeta]
  exact Prod.ext
    (weightedTraceIteratedPolynomial_right_natDegree alpha beta)
    (weightedTraceIteratedPolynomial_left_natDegree alpha beta halpha)

end BGS.Markoff

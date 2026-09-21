/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.PrincipalMaximalFinite
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof

/-!
# LM24 principal-factor invariance statements

This module states LM24, Lemmas 6.3.1--6.3.2. The first lemma concerns the multiplicative RV
quotient and the paper's set `P` of principal RV classes. The second concerns the full
degree-graded ring `RV̂` and the principal graded subring `P̂`. In both cases multiplication
by a nonzero principal factor preserves the normalized maximal finite-support divisor.

The RV notation `p(B)` is represented by applying the full graded normalization to the canonical
graded image of `B`. The proofs use Berarducci multiplicativity and finite-support
greatest-common divisors.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- LM24, Lemma 6.3.1: multiplying an RV class by a nonzero principal RV class does not change
its normalized maximal finite-support divisor. -/
theorem maximalFiniteSupportDivisor_rv_mul_principal (B C : HahnDegreeRV K)
    (hC : IsPrincipalRV C) (hC0 : C ≠ 0) :
    gradedNormalizedMaximalFiniteSupportDivisor
        ((degreeValuation K).rvInitialFormHom (B * C)) =
      gradedNormalizedMaximalFiniteSupportDivisor
        ((degreeValuation K).rvInitialFormHom B) := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  exact
    gradedNormalizedMaximalFiniteSupportDivisor_rv_mul_principal_eq_of_exists_gcd hgcd B hC hC0

/-- LM24, Lemma 6.3.2: multiplying a full graded element by a nonzero element of the principal
graded subring does not change its normalized maximal finite-support divisor. -/
theorem maximalFiniteSupportDivisor_mul_principal (B C : DegreeGraded K)
    (hC : IsPrincipalGraded C) (hC0 : C ≠ 0) :
    gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
      gradedNormalizedMaximalFiniteSupportDivisor B := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  exact gradedNormalizedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd hgcd B hC hC0

end

end Berarducci

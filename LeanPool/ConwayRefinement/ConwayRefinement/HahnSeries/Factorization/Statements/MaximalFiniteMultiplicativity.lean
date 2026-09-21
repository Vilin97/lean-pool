/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.MaximalFiniteMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.SeriesMaximalMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.PrincipalSubringPrimality

/-!
# LM24 multiplicativity of maximal finite-support divisors

This module states LM24, Corollary 6.3.7. The normalized maximal finite-support divisor of a
product in `RV̂` is the product of the two normalized maximal finite-support divisors.

The proof applies the finite-support factor witness from Corollary 6.3.6 to the generic
normalization argument.

Both statements assume only that the coefficient field has characteristic zero; Proposition
6.3.8 below has the printed signature on Hahn series.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [hchar : CharZero K]

include hchar in
/-- LM24, Corollary 6.3.7: the normalized maximal finite-support divisor is multiplicative on
the degree-graded ring `RV̂`. -/
theorem maximalFiniteSupportDivisor_mul (B C : DegreeGraded K) :
    gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
      gradedNormalizedMaximalFiniteSupportDivisor B *
        gradedNormalizedMaximalFiniteSupportDivisor C := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  let hunits := HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
    (G := ℝ) (K := K)
  apply gradedNormalizedMaximalFiniteSupportDivisor_mul_of_factorization hgcd hunits
  intro p X Y hp
  exact finiteSupportGradedEmbedding_exists_factor_dvd p X Y hp

include hchar in
/-- LM24, Proposition 6.3.8: the normalized maximal finite-support divisor is multiplicative on
the Hahn-series ring `K((ℝ^{≤ 0}))`. -/
theorem seriesMaximalFiniteSupportDivisor_mul (b c : Series K) :
    seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
      seriesNormalizedMaximalFiniteSupportDivisor b *
        seriesNormalizedMaximalFiniteSupportDivisor c := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  let hunits := HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
    (G := ℝ) (K := K)
  exact seriesNormalizedMaximalFiniteSupportDivisor_mul_of_graded hgcd hunits
    maximalFiniteSupportDivisor_mul b c

end

end Berarducci

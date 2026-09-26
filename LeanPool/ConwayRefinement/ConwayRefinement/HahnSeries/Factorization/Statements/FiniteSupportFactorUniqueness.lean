/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.FiniteSupportFactorUniqueness

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.MaximalFiniteMultiplicativity

/-!
# LM24 uniqueness of the finite-support factor

This module states LM24, Theorem 6.4.1. For each nonzero series, it gives one finite-support
factor and finitely many irreducible infinite-support factors. The number of infinite-support
factors is bounded by the number of terms in the Cantor normal form of the degree. Only the
finite-support factor is asserted to be unique, and only up to multiplication by a nonzero
coefficient scalar.

The list represents the source sequence `c₁, …, cₙ`; its length is the source natural number
`n`. The proof combines LM24, Proposition 5.6.1 and Proposition 6.3.8.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- LM24, Theorem 6.4.1: every nonzero series factors into one finite-support factor and a
bounded finite list of irreducible infinite-support factors, and the finite-support factor is
unique up to multiplication by a nonzero coefficient scalar. -/
theorem series_factorization_with_unique_finiteSupportFactor {b : Series K} (hb : b ≠ 0) :
    ∃ (p : FiniteSupportRing (K := K)) (factors : List (Series K)),
      IsInfiniteSupportIrreducibleFactorization b p factors ∧
        factors.length ≤ HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) ∧
        IsUniqueFiniteSupportFactorUpToScalar b p := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  let hunits := HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
    (G := ℝ) (K := K)
  exact exists_factorization_with_unique_finiteSupportFactor hgcd hunits
    (seriesMaximalFiniteSupportDivisor_mul (K := K)) hb

end

end Berarducci

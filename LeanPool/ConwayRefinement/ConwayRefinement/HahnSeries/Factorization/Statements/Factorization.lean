/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DegreeTermCount

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.InfiniteSupport
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree

/-!
# LM24 factorisation statement

This module gives the exact public signature of LM24, Proposition 5.6.1 for `K((ℝ^{≤ 0}))`.
A list represents the finite sequence `c₁, …, cₙ` from the paper, and its length is `n`. Every
list member is irreducible and has infinite support. The list length is bounded by the number of
terms in the uncompressed Cantor normal form of the degree.

The first theorem retains the derived fact that the coefficient scalar is nonzero. The second
theorem has exactly the conclusion printed in Proposition 5.6.1. Both retain the normalized
maximal finite-support divisor `p(b)` from LM24, Notation 5.5.2.

The proofs combine Berarducci multiplicativity, the finite-support greatest-common-divisor and
unit-classification theorems, Cantor-term arithmetic, residual reduction, and factorisation
induction.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [hchar : CharZero K]

include hchar in
/-- Strengthened form of LM24, Proposition 5.6.1, recording that the coefficient scalar is
nonzero. -/
theorem series_infinite_support_factorization_with_nonzero_scalar {b : Series K} (hb : b ≠ 0) :
    ∃ (factors : List (Series K)) (k : K),
      k ≠ 0 ∧
        b = HahnSeries.Nonpositive.C k *
          (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) *
            factors.prod ∧
        (∀ c ∈ factors,
          Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
        factors.length ≤ HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) := by
  obtain ⟨k, factors, hk, hfactor, hfactors, hbound⟩ :=
    exists_series_infinite_support_factorization_of_exists_gcd
      (HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
        (G := ℝ) (K := K))
      (HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
        (G := ℝ) (K := K)) hb
  exact ⟨factors, k, hk, hfactor, hfactors, hbound⟩

include hchar in
/-- LM24, Proposition 5.6.1: every nonzero series is a scalar times its normalized maximal
finite-support divisor and finitely many irreducible infinite-support series, with the number of
such factors bounded by the Cantor term count of its degree. -/
theorem series_infinite_support_factorization {b : Series K} (hb : b ≠ 0) :
    ∃ (factors : List (Series K)) (k : K),
      b = HahnSeries.Nonpositive.C k *
        (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) *
          factors.prod ∧
        (∀ c ∈ factors,
          Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
        factors.length ≤ HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) := by
  obtain ⟨factors, k, _, hfactor, hfactors, hbound⟩ :=
    series_infinite_support_factorization_with_nonzero_scalar hb
  exact ⟨factors, k, hfactor, hfactors, hbound⟩

end

end Berarducci

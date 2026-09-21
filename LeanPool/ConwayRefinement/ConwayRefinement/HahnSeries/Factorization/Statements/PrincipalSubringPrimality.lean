/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.PrincipalSubringPrimality
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.PrincipalScalarRedistribution

/-!
# LM24 primality in the degree-graded ring

This module states LM24, Corollary 6.3.6. In the degree-graded ring `RV̂`, every
finite-support series is primal. The stronger witness theorem retains the two primal factors as
elements of `K(ℝ^{≤0})`; the source-level primality statement is derived from it.

The proof depends only on the finite-support greatest-common-divisor and scalar-redistribution
prerequisites, both proved over the real exponents, and on the characteristic-zero hypothesis
that supplies ordinal-value and degree multiplicativity.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [hchar : CharZero K]

include hchar in
/-- The factor-witness form of LM24, Corollary 6.3.6: the two factors of `p` remain
finite-support series over `K`. -/
theorem finiteSupportGradedEmbedding_exists_factor_dvd (p : FiniteSupportRing (K := K))
    (B C : DegreeGraded K)
    (hp : finiteSupportGradedEmbedding K p ∣ B * C) :
    ∃ p₁ p₂ : FiniteSupportRing (K := K),
      p = p₁ * p₂ ∧
        finiteSupportGradedEmbedding K p₁ ∣ B ∧
        finiteSupportGradedEmbedding K p₂ ∣ C := by
  let hgcdK := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  let hgcdL := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := PrincipalSubringFractionField K)
  let hredistribute : PrincipalSubringFractionScalarRedistribution K :=
    ⟨fun hp₁ hp₂ hprod ↦
      principalSubringFraction_exists_scalarRedistribution hp₁ hp₂ hprod⟩
  exact finiteSupportGradedEmbedding_exists_factor_dvd_of_scalarRedistribution hgcdK hgcdL
    hredistribute p B C hp

include hchar in
/-- LM24, Corollary 6.3.6: every finite-support series is primal in `RV̂`. -/
theorem finiteSupportGradedEmbedding_isPrimal (p : FiniteSupportRing (K := K)) :
    IsPrimal (finiteSupportGradedEmbedding K p) := by
  intro B C hp
  obtain ⟨p₁, p₂, hpFactors, hp₁, hp₂⟩ :=
    finiteSupportGradedEmbedding_exists_factor_dvd p B C hp
  refine ⟨finiteSupportGradedEmbedding K p₁,
    finiteSupportGradedEmbedding K p₂, hp₁, hp₂, ?_⟩
  rw [hpFactors, map_mul]

end

end Berarducci

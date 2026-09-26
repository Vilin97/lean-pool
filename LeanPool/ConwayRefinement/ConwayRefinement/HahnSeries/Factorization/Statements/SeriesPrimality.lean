/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentTensor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Divisibility.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.SeriesPrimality
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.MaximalFiniteMultiplicativity

/-!
# LM24 primality in the Hahn-series ring

This module states LM24, Corollary 6.3.9. The stronger witness theorem retains the factors of the
finite-support divisor as elements of `K(ℝ^{≤ 0})`; primality of every element of the
finite-support subring is derived from it.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [hchar : CharZero K]

include hchar in
/-- The factor-witness form of LM24, Corollary 6.3.9: both factors remain elements of the
finite-support subring `K(ℝ^{≤ 0})`. -/
theorem finiteSupportSeries_exists_factor_dvd (p : FiniteSupportRing (K := K)) (b c : Series K)
    (hp : (p : Series K) ∣ b * c) :
    ∃ p₁ p₂ : FiniteSupportRing (K := K),
      (p : Series K) = (p₁ : Series K) * (p₂ : Series K) ∧
        (p₁ : Series K) ∣ b ∧ (p₂ : Series K) ∣ c := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  obtain ⟨p₁, p₂, hpFactor, hp₁, hp₂⟩ :=
    finiteSupportSeries_exists_factor_dvd_of_maximalMultiplicative hgcd
      (seriesMaximalFiniteSupportDivisor_mul (K := K))
        p b c hp
  refine ⟨p₁, p₂, ?_, hp₁, hp₂⟩
  exact congrArg
    (HahnSeries.Nonpositive.finiteSupportSubring
      (G := ℝ) (K := K)).subtype hpFactor

end

end Berarducci

namespace HahnSeries.Nonpositive

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- Strengthened form of LM24, Corollary 6.3.9: a finite-support divisor `p` of `b * c`
has a factorisation `p = p₁ * p₂` into finite-support series with `p₁ ∣ b` and
`p₂ ∣ c`. -/
theorem exists_finiteSupport_split_of_dvd_mul
    {p b c : Nonpositive ℝ K} (hp : p ∈ finiteSupportSubring)
    (hdiv : p ∣ b * c) :
    ∃ p₁ p₂ : Nonpositive ℝ K,
      p₁ ∈ finiteSupportSubring ∧ p₂ ∈ finiteSupportSubring ∧
        p = p₁ * p₂ ∧ p₁ ∣ b ∧ p₂ ∣ c := by
  let p' : Berarducci.FiniteSupportRing (K := K) := ⟨p, hp⟩
  obtain ⟨p₁, p₂, hpFactor, hp₁, hp₂⟩ :=
    Berarducci.finiteSupportSeries_exists_factor_dvd p' b c hdiv
  exact ⟨p₁, p₂, p₁.property, p₂.property, hpFactor, hp₁, hp₂⟩

/-- LM24, Corollary 6.3.9: every finite-support nonpositive real Hahn series is primal. -/
theorem isPrimal_of_mem_finiteSupportSubring
    {p : Nonpositive ℝ K} (hp : p ∈ finiteSupportSubring) : IsPrimal p := by
  intro b c hdiv
  obtain ⟨p₁, p₂, -, -, hpFactor, hp₁, hp₂⟩ := exists_finiteSupport_split_of_dvd_mul hp hdiv
  exact ⟨p₁, p₂, hp₁, hp₂, hpFactor⟩

end

end HahnSeries.Nonpositive

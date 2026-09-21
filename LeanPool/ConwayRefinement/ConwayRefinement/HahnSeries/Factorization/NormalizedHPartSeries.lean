/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedHPartMultiplicativity
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite

/-!
# Normalized exponent-subgroup parts of Hahn-series maximal divisors

LM24, Corollary 6.5.3 combines two intrinsic divisor characterizations. The real finite-support
series `p(b)` has exactly the finite-support divisors of `b`, while its normalized `H`-part has
exactly its normalized finite-support `H`-divisors.

The theorem below proves this composition for arbitrary representatives satisfying those two
predicates. It therefore needs no Ritt-factorisation or Berarducci input; the corresponding source
theorem reduces to the two existence results.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable (H : AddSubgroup ℝ) {K : Type v} [Field K]

/-- Relational form of LM24, Corollary 6.5.3: normalized finite-support `H`-divisors of a Hahn
series are exactly the divisors of the normalized `H`-part of its maximal finite-support
divisor. -/
theorem normalizedHPart_dvd_iff_dvd_series
    {b : Nonpositive ℝ K} {p : FiniteSupportRing (G := ℝ) (K := K)}
    {pH : ConstantTermOneFiniteSupport (G := H) (K := K)}
    (hmax : Berarducci.IsNormalizedSeriesMaximalFiniteSupportDivisor b p)
    (hpH : IsNormalizedHPart H p pH)
    (q : ConstantTermOneFiniteSupport (G := H) (K := K)) :
    mapDomainToReal H
        ((q : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) ∣ b ↔
      (q : FiniteSupportRing (G := H) (K := K)) ∣
        (pH : FiniteSupportRing (G := H) (K := K)) := by
  have hmax' :=
    (Berarducci.isNormalizedSeriesMaximalFiniteSupportDivisor_iff b p).mp hmax
  have hpH' := (isNormalizedHPart_iff H p pH).mp hpH
  calc
    mapDomainToReal H
          ((q : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) ∣ b ↔
        ((finiteSupportToReal H
          (q : FiniteSupportRing (G := H) (K := K)) :
            FiniteSupportRing (G := ℝ) (K := K)) : Nonpositive ℝ K) ∣ b := by
      rw [coe_finiteSupportToReal]
    _ ↔ finiteSupportToReal H
        (q : FiniteSupportRing (G := H) (K := K)) ∣ p :=
      hmax'.1 _
    _ ↔ (q : FiniteSupportRing (G := H) (K := K)) ∣
        (pH : FiniteSupportRing (G := H) (K := K)) := hpH' q

/-- Relational reduction underlying LM24, Corollary 6.5.5: multiplicativity of the real
series-level maximal finite-support divisor and normalized-divisor refinement imply
multiplicativity of its normalized `H`-part. -/
theorem normalizedHPart_seriesMaximal_mul_eq
    (hrefine : HasNormalizedHDivisorRefinement H (K := K))
    {b c : Nonpositive ℝ K}
    {bH cH bcH : ConstantTermOneFiniteSupport (G := H) (K := K)}
    (hbH : IsNormalizedHPart H
      (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b) bH)
    (hcH : IsNormalizedHPart H
      (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c) cH)
    (hbcH : IsNormalizedHPart H
      (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c)) bcH)
    (hmaxMul : Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b *
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c) :
    bcH = bH * cH := by
  apply hbcH.eq H
  rw [hmaxMul]
  exact isNormalizedHPart_mul H hrefine hbH hcH

end HahnSeries.Nonpositive

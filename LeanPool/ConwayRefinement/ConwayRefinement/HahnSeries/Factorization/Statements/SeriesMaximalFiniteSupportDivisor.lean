/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof

/-!
# LM24 series-level maximal finite-support divisor statements

This module states LM24, Proposition 5.5.1, Notation 5.5.2, Remark 5.5.3, and Proposition 5.5.5
for the ring `K((ℝ^{≤ 0}))`. Proposition 5.5.1 is the bidirectional assertion

`(q : K((ℝ^{≤ 0}))) ∣ b ↔ q ∣ p`

for every finite-support `q`; its uniqueness clause is multiplication by a nonzero coefficient.
The notation is represented by the monic finite-support series
`seriesNormalizedMaximalFiniteSupportDivisor b`, with zero fixed separately.

The theorem proofs use LM24, Fact 2.5.2 and Berarducci ordinal-value multiplicativity; the
coefficient field has characteristic zero.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

omit [CharZero K] in
private theorem series_representative_spec_and_uniqueness
    (b : Series K) (p : FiniteSupportRing (K := K))
    (hp : IsSeriesMaximalFiniteSupportDivisor b (Associates.mk p)) :
    (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p) ∧
      ∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  have hpSpec := (isSeriesMaximalFiniteSupportDivisor_mk_iff b p).mp hp
  refine ⟨hpSpec, ?_⟩
  intro p' hp'Spec
  have hp' := (isSeriesMaximalFiniteSupportDivisor_mk_iff b p').mpr hp'Spec
  exact HahnSeries.Nonpositive.exists_nonzero_scalar_mul_of_mk_eq_mk
    (HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
      (G := ℝ) (K := K))
    (hp.eq hp')

/-- LM24, Proposition 5.5.1: every Hahn series has a finite-support series with exactly the same
finite-support divisors, unique up to multiplication by a nonzero coefficient. -/
theorem series_maximal_finite_support_divisor (b : Series K) :
    ∃ p : FiniteSupportRing (K := K),
      (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p) ∧
      ∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isSeriesMaximalFiniteSupportDivisor_of_exists_gcd hgcd b
  induction a using Quotient.inductionOn with
  | _ p =>
      obtain ⟨hpSpec, hpUnique⟩ :=
        series_representative_spec_and_uniqueness b p ha
      exact ⟨p, hpSpec, hpUnique⟩

/-- LM24, Notation 5.5.2: the maximal finite-support divisor has a unique representative that is
zero at zero and monic otherwise. -/
theorem existsUnique_normalized_series_maximal_finite_support_divisor (b : Series K) :
    ∃! p : FiniteSupportRing (K := K),
      IsNormalizedSeriesMaximalFiniteSupportDivisor b p := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  let hunits := HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
    (G := ℝ) (K := K)
  refine ⟨seriesNormalizedMaximalFiniteSupportDivisor b, ?_, ?_⟩
  · exact seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b
  · intro p hp
    exact (seriesNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits hp).symm

/-- The representative fixed by LM24, Notation 5.5.2 satisfies its defining predicate. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_is (b : Series K) :
    IsNormalizedSeriesMaximalFiniteSupportDivisor b
      (seriesNormalizedMaximalFiniteSupportDivisor b) := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  exact seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b

/-- LM24, Remark 5.5.3: the normalized maximal finite-support divisor divides the Hahn series. -/
theorem seriesMaximalFiniteSupportDivisor_dvd (b : Series K) :
    (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) ∣ b := by
  have h := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    b (seriesNormalizedMaximalFiniteSupportDivisor b)).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is b)
  exact (h.1 (seriesNormalizedMaximalFiniteSupportDivisor b)).mpr dvd_rfl

variable (K) in
/-- The series-level maximal finite-support divisor of zero is zero. -/
theorem seriesMaximalFiniteSupportDivisor_zero :
    seriesNormalizedMaximalFiniteSupportDivisor (0 : Series K) = 0 := by
  have h := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    (0 : Series K) (seriesNormalizedMaximalFiniteSupportDivisor 0)).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is 0)
  rcases h.2 with hzero | hnonzero
  · exact hzero.2
  · exact (hnonzero.1 rfl).elim
/-- LM24, Remark 5.5.3: on a finite-support input, the normalized maximal divisor is a nonzero
scalar multiple of that input. -/
theorem exists_scalar_seriesMaximalFiniteSupportDivisor_coe (p : FiniteSupportRing (K := K)) :
    ∃ k : K, k ≠ 0 ∧
      seriesNormalizedMaximalFiniteSupportDivisor (p : Series K) =
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  exact exists_scalar_seriesNormalizedMaximalFiniteSupportDivisor_coe
    (HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
      (G := ℝ) (K := K)) p

/-- LM24, Remark 5.5.3: on a finite-support input, the series-level normalized divisor
coincides with the normalized divisor from LM24, Notation 5.4.5. -/
theorem seriesMaximalFiniteSupportDivisor_coe_eq_graded (p : FiniteSupportRing (K := K)) :
    seriesNormalizedMaximalFiniteSupportDivisor (p : Series K) =
      gradedNormalizedMaximalFiniteSupportDivisor
        (finiteSupportGradedEmbedding K p) := by
  exact seriesNormalizedMaximalFiniteSupportDivisor_coe_eq_graded p

/-- LM24, Remark 5.5.3: the normalized maximal finite-support divisor of a principal Hahn series
is one. -/
theorem seriesMaximalFiniteSupportDivisor_principal_eq_one
    {b : Series K} (hb : HahnSeries.Nonpositive.IsPrincipal b) :
    seriesNormalizedMaximalFiniteSupportDivisor b = 1 := by
  exact seriesNormalizedMaximalFiniteSupportDivisor_eq_one_of_isPrincipal
      (HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
        (G := ℝ) (K := K)) hb

/-- LM24, Proposition 5.5.5: the product of the two normalized maximal finite-support divisors
divides the normalized maximal finite-support divisor of the product. -/
theorem seriesMaximalFiniteSupportDivisor_mul_dvd (b c : Series K) :
    seriesNormalizedMaximalFiniteSupportDivisor b *
        seriesNormalizedMaximalFiniteSupportDivisor c ∣
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) := by
  exact seriesNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd
      (HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
        (G := ℝ) (K := K)) b c

end

end Berarducci

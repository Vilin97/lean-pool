/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc
-/
import LeanPool.Erdos1196.Preliminaries
import LeanPool.Erdos1196.FirstEntryRowTerm
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Core definitions for the normalization constant

This file contains the shared decomposition of the entry weights and normalization constant into
their small-prime and first-entry pieces, together with the structural reindexing lemmas used by
the two separate estimate files.

## Main definitions

* `entryWeightFactor`
* `smallPrimeDivisorSum`
* `firstEntryDivisorSum`
* `normalizationSmallPrimePart`
* `normalizationFirstEntryPart`
-/

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/-- The common prefactor `1 / (n log^2 n)` in the entry weights. -/
noncomputable def entryWeightFactor (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)

/-- The small-prime-power divisor sum appearing in `b_x(n)`. -/
noncomputable def smallPrimeDivisorSum (Y n : ℕ) : ℝ :=
  (n.divisors.filter (fun q => q < Y)).sum fun q => Λ q

/-- The first-entry divisor sum appearing in `b_x(n)`. -/
noncomputable def firstEntryDivisorSum (x Y n : ℕ) : ℝ :=
  (n.divisors.filter (fun q => Y ≤ q ∧ n / q < x)).sum fun q => Λ q

/-- The contribution to `b_x(n)` from divisors `q < Y`. -/
noncomputable def smallPrimeEntryWeight (Y n : ℕ) : ℝ :=
  entryWeightFactor n * smallPrimeDivisorSum Y n

/-- The contribution to `b_x(n)` from divisors `q ≥ Y` with `n / q < x`. -/
noncomputable def firstEntryEntryWeight (x Y n : ℕ) : ℝ :=
  entryWeightFactor n * firstEntryDivisorSum x Y n

/-- The small-prime-power summand in the normalization constant `B_x`. -/
noncomputable def normalizationSmallPrimePart (x Y n : ℕ) : ℝ :=
  if x ≤ n then smallPrimeEntryWeight Y n else 0

/-- The first-entry summand in the normalization constant `B_x`. -/
noncomputable def normalizationFirstEntryPart (x Y n : ℕ) : ℝ :=
  if x ≤ n then firstEntryEntryWeight x Y n else 0

/-- `b_x(n)` splits into the small-prime-power and first-entry contributions. -/
lemma entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight (x Y n : ℕ) :
    entryWeight x Y n = smallPrimeEntryWeight Y n + firstEntryEntryWeight x Y n := by
  rw [entryWeight, smallPrimeEntryWeight, firstEntryEntryWeight, entryWeightFactor,
    smallPrimeDivisorSum, firstEntryDivisorSum, mul_add]

/--
Adding the remaining divisor contribution to `b_x(n)` recovers the full weighted divisor sum.
-/
lemma entryWeight_add_filtered_vonMangoldt_eq_entryWeightFactor_sum_divisors (x Y n : ℕ) :
    entryWeight x Y n +
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then entryWeightFactor n * Λ q else 0) =
      entryWeightFactor n * (n.divisors.sum fun q => Λ q) := by
  calc
    entryWeight x Y n +
        n.divisors.sum (fun q =>
          if Y ≤ q ∧ x ≤ n / q then entryWeightFactor n * Λ q else 0)
      = entryWeight x Y n +
          entryWeightFactor n *
            ((n.divisors.filter fun q => Y ≤ q ∧ x ≤ n / q).sum fun q => Λ q) := by
          rw [← Finset.sum_filter, Finset.mul_sum]
    _ = entryWeightFactor n *
          (((n.divisors.filter fun q => q < Y).sum fun q => Λ q) +
            ((n.divisors.filter fun q => Y ≤ q ∧ n / q < x).sum fun q => Λ q) +
            ((n.divisors.filter fun q => Y ≤ q ∧ x ≤ n / q).sum fun q => Λ q)) := by
          simp [entryWeight, entryWeightFactor]
          ring_nf
    _ = entryWeightFactor n * (n.divisors.sum fun q => Λ q) := by
          congr 1
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun q _ => by grind only

/-- The small-prime contribution to `b_x(n)` is nonnegative. -/
lemma smallPrimeEntryWeight_nonneg (Y n : ℕ) : 0 ≤ smallPrimeEntryWeight Y n := by
  unfold smallPrimeEntryWeight entryWeightFactor smallPrimeDivisorSum
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- The first-entry contribution to `b_x(n)` is nonnegative. -/
lemma firstEntryEntryWeight_nonneg (x Y n : ℕ) : 0 ≤ firstEntryEntryWeight x Y n := by
  unfold firstEntryEntryWeight entryWeightFactor firstEntryDivisorSum
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ => ArithmeticFunction.vonMangoldt_nonneg)

/--
The first-entry threshold always lands in the admissible range `x ≤ m * q`, since it dominates the
ceiling quotient `x ⌈/⌉ m`.
-/
lemma le_mul_entryThreshold (x Y m : ℕ) (hm : 0 < m) :
    x ≤ m * entryThreshold x Y m :=
  (le_smul_ceilDiv hm).trans (Nat.mul_le_mul_left _ (le_max_right _ _))

/--
For `m < x`, the ceiling-quotient part of the first-entry threshold overshoots `x / m` by less than
one step, so `m * (x ⌈/⌉ m)` stays below `2x`.
-/
private lemma mul_ceilDiv_lt_two_mul (x m : ℕ) (hm : 0 < m) (hmx : m < x) :
    m * (x ⌈/⌉ m) < 2 * x := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hmul_div : m * ((x + m - 1) / m) ≤ x + m - 1 := Nat.mul_div_le _ _
  omega

/--
Under the standing regime `Y ≥ 2`, the first-entry threshold satisfies the upper bound
`m * entryThreshold x Y m ≤ xY` whenever `m < x`.
-/
private lemma mul_entryThreshold_le (x Y m : ℕ) (hY : 2 ≤ Y) (hm : 0 < m) (hmx : m < x) :
    m * entryThreshold x Y m ≤ x * Y := by
  rcases le_total Y (x ⌈/⌉ m) with hcase | hcase
  · rw [entryThreshold, max_eq_right hcase]
    exact (mul_ceilDiv_lt_two_mul x m hm hmx).le.trans
      (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left x hY)
  · rw [entryThreshold, max_eq_left hcase]
    exact Nat.mul_le_mul_right Y hmx.le

/--
If `n ∈ [x, xY]` and `x ≥ 2`, then the reciprocal logarithm at `n` differs from the reciprocal
logarithm at `x` by at most `log Y / log(x)^2`.
-/
private lemma abs_inv_log_sub_inv_log_le (x Y n : ℕ) (hx : 2 ≤ x) (hY : 1 ≤ Y)
    (hxn : x ≤ n) (hnY : n ≤ x * Y) :
    |1 / Real.log (n : ℝ) - 1 / Real.log (x : ℝ)| ≤
      Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hlog_le : Real.log (x : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hxn)
  rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hxlog hlog_le)),
    show -(1 / Real.log (n : ℝ) - 1 / Real.log (x : ℝ)) =
      (Real.log (n : ℝ) - Real.log (x : ℝ)) / (Real.log (x : ℝ) * Real.log (n : ℝ)) by
        grind only]
  have hnum_nonneg : 0 ≤ Real.log (n : ℝ) - Real.log (x : ℝ) := sub_nonneg.mpr hlog_le
  have hlog_upper : Real.log (n : ℝ) ≤ Real.log (x : ℝ) + Real.log (Y : ℝ) := by
    calc Real.log (n : ℝ) ≤ Real.log ((x * Y : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnY)
      _ = Real.log (x : ℝ) + Real.log (Y : ℝ) := by
          rw [Nat.cast_mul, Real.log_mul
            (by exact_mod_cast (show x ≠ 0 by omega))
            (by exact_mod_cast (show Y ≠ 0 by omega))]
  calc
    (Real.log (n : ℝ) - Real.log (x : ℝ)) / (Real.log (x : ℝ) * Real.log (n : ℝ))
      ≤ (Real.log (n : ℝ) - Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_left hnum_nonneg (sq_pos_of_pos hxlog) (by nlinarith)
    _ ≤ Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hxlog)).2 (by linarith)

/--
Specializing the interval estimate to the first-entry threshold gives a uniform logarithmic error
bound along the initial-entry contribution.
-/
private lemma abs_inv_log_entryThreshold_sub_inv_log_le (x Y m : ℕ)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hm : 0 < m) (hmx : m < x) :
    |1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ) - 1 / Real.log (x : ℝ)| ≤
      Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 :=
  abs_inv_log_sub_inv_log_le x Y (m * entryThreshold x Y m) hx (le_of_lt hY)
    (le_mul_entryThreshold x Y m hm) (mul_entryThreshold_le x Y m hY hm hmx)

/--
For fixed `Y ≥ 2`, the first-entry tail at the faithful cutoff `entryThreshold x Y m`
approximates `1 / log x` with a uniform `log⁻² x` error, uniformly for all parent states
`1 ≤ m < x`.
-/
lemma firstEntryTailApproximation {Y : ℕ} (hY : 2 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {x m : ℕ}, 2 ≤ x → 1 ≤ m → m < x →
        |firstEntryTail x Y m - 1 / Real.log (x : ℝ)| ≤
          C / (Real.log (x : ℝ)) ^ 2 := by
  rcases tailEstimate with ⟨C0, hC0pos, hC0⟩
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hY))
  refine ⟨C0 + Real.log (Y : ℝ), by linarith, ?_⟩
  intro x m hx hm hmx
  have hthreshold : 2 ≤ entryThreshold x Y m := le_trans hY (le_max_left _ _)
  have htail :
      |firstEntryTail x Y m - 1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)| ≤
        C0 / (Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)) ^ 2 := by
    simpa [firstEntryTail, tailSum] using hC0 hm hthreshold
  have hmul_lower : x ≤ m * entryThreshold x Y m := le_mul_entryThreshold x Y m hm
  have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hmul_log : Real.log (x : ℝ) ≤ Real.log ((m * entryThreshold x Y m : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmul_lower)
  have hlogsq : C0 / (Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)) ^ 2 ≤
      C0 / (Real.log (x : ℝ)) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hxlog) (by nlinarith)
  calc
    |firstEntryTail x Y m - 1 / Real.log (x : ℝ)|
      ≤ |firstEntryTail x Y m - 1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)| +
          |1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ) - 1 / Real.log (x : ℝ)| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              abs_sub_le (firstEntryTail x Y m)
                (1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)) (1 / Real.log (x : ℝ))
    _ ≤ C0 / (Real.log (x : ℝ)) ^ 2 + Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
          gcongr
          · exact htail.trans hlogsq
          · exact abs_inv_log_entryThreshold_sub_inv_log_le x Y m hx hY hm hmx
    _ = (C0 + Real.log (Y : ℝ)) / (Real.log (x : ℝ)) ^ 2 := by ring

/--
The reciprocal sum up to `x - 1` differs from `log x` by at most `1`, which is the `O(1)` input
used in the normalization argument.
-/
private lemma abs_harmonic_pred_sub_log_le_one (x : ℕ) (hx : 1 ≤ x) :
    |(harmonic (x - 1) : ℝ) - Real.log (x : ℝ)| ≤ 1 := by
  by_cases hx1 : x = 1
  · subst hx1
    norm_num [harmonic_zero]
  have hlower : Real.log (x : ℝ) ≤ (harmonic (x - 1) : ℝ) :=
    by simpa [Nat.sub_add_cancel hx] using log_add_one_le_harmonic (x - 1)
  have hupper0 : (harmonic (x - 1) : ℝ) ≤ 1 + Real.log ((x - 1 : ℕ) : ℝ) :=
    by exact_mod_cast harmonic_le_one_add_log (x - 1)
  have hlog_mono : Real.log ((x - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by exact_mod_cast show 0 < x - 1 by omega)
      (by exact_mod_cast Nat.sub_le x 1)
  grind only [= abs.eq_1, = max_def]

/-- Equivalently, the finite reciprocal sum `∑_{m < x} 1 / m` is within `1` of `log x`. -/
lemma abs_sum_Icc_inv_sub_log_le_one (x : ℕ) (hx : 1 ≤ x) :
    |(∑ m ∈ Finset.Icc 1 (x - 1), (1 : ℝ) / m) - Real.log (x : ℝ)| ≤ 1 := by
  simpa [one_div, harmonic_eq_sum_Icc] using abs_harmonic_pred_sub_log_le_one x hx

/--
Reindexing the finite union of the divisor antidiagonals for `n < N` gives the finite product set
of positive pairs with product `< N`.
-/
private lemma sum_sigma_divisorsAntidiagonal_eq_sum_product
    (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ z ∈ (Finset.range N).sigma (fun n => n.divisorsAntidiagonal), F z.2.1 z.2.2 =
      ∑ p ∈ (((Finset.range N).product (Finset.range N)).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 < N)), F p.1 p.2 := by
  refine Finset.sum_bij' (i := fun z _ => z.2) (j := fun p _ => ⟨p.1 * p.2, p⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rcases Finset.mem_sigma.1 hz with ⟨hzN, hzdiv⟩
    rcases Nat.mem_divisorsAntidiagonal.1 hzdiv with ⟨hmul, _⟩
    have hzN' : z.1 < N := Finset.mem_range.1 hzN
    have hz1pos : 0 < z.2.1 :=
      Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hzdiv)
    have hz2pos : 0 < z.2.2 :=
      Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hzdiv)
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_mul_of_pos_right z.2.1 hz2pos) (hmul ▸ hzN')),
       Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_mul_of_pos_left z.2.2 hz1pos) (hmul ▸ hzN'))⟩,
      ⟨hz1pos, hz2pos, hmul ▸ hzN'⟩⟩
  · intro p hp
    rcases Finset.mem_filter.1 hp with ⟨hpprod, hp1pos, hp2pos, hplt⟩
    refine Finset.mem_sigma.2 ⟨Finset.mem_range.2 hplt,
      Nat.mem_divisorsAntidiagonal.2 ⟨rfl, mul_ne_zero hp1pos.ne' hp2pos.ne'⟩⟩
  · intro z hz
    rcases z with ⟨n, q, m⟩
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact (Nat.mem_divisorsAntidiagonal.1 (Finset.mem_sigma.1 hz).2).1
  · intro p hp
    simp
  · intro z hz
    rfl

/-- The small-prime divisor sum can be rewritten over the divisor antidiagonal. -/
private lemma smallPrimeDivisorSum_eq_sum_divisorsAntidiagonal (Y n : ℕ) :
    smallPrimeDivisorSum Y n =
      ∑ p ∈ n.divisorsAntidiagonal, if p.1 < Y then Λ p.1 else 0 := by
  symm
  simpa [smallPrimeDivisorSum, Finset.sum_filter] using
    (Nat.sum_divisorsAntidiagonal (n := n) (f := fun q _ => if q < Y then Λ q else 0))

/-- Splitting `1 / ((mq) log^2(mq))` at the factor `q` produces the small-prime tail. -/
private lemma entryWeightFactor_mul_vonMangoldt_eq_smallFactor (q m : ℕ) :
    entryWeightFactor (m * q) * Λ q =
      (Λ q / (q : ℝ)) *
        (1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)) := by
  rw [entryWeightFactor, Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
  ring_nf

/--
The finite prefix of the small-prime contribution reindexes as a sum over `q < Y` and inner
`m`-tails, with the exact lower cutoff `x ⌈/⌉ q`.
-/
lemma sum_range_normalizationSmallPrimePart_eq
    (N x Y : ℕ) :
    ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n =
      ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
        if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
          (Λ q / (q : ℝ)) *
            (1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2))
        else 0 := by
  let F : ℕ → ℕ → ℝ := fun q m =>
    if x ≤ q * m then entryWeightFactor (q * m) * (if q < Y then Λ q else 0) else 0
  calc
    ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n
      = ∑ n ∈ Finset.range N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          by_cases hx : x ≤ n
          · rw [normalizationSmallPrimePart, if_pos hx, smallPrimeEntryWeight,
              smallPrimeDivisorSum_eq_sum_divisorsAntidiagonal, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p hp => ?_
            rcases Nat.mem_divisorsAntidiagonal.1 hp with ⟨hp_mul, _⟩
            simp [F, hp_mul, hx]
          · have hzero : ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 = 0 :=
              Finset.sum_eq_zero fun p hp => by
                rcases Nat.mem_divisorsAntidiagonal.1 hp with ⟨hp_mul, _⟩
                simp [F, hp_mul, hx]
            simp [normalizationSmallPrimePart, hx, hzero]
    _ = ∑ z ∈ (Finset.range N).sigma (fun n => n.divisorsAntidiagonal), F z.2.1 z.2.2 :=
          Finset.sum_sigma' (Finset.range N) Nat.divisorsAntidiagonal fun _ p => F p.1 p.2
    _ = ∑ p ∈ (((Finset.range N).product (Finset.range N)).filter
          (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 < N)), F p.1 p.2 := by
          simpa [F] using sum_sigma_divisorsAntidiagonal_eq_sum_product N F
    _ = ∑ p ∈ (Finset.range N).product (Finset.range N),
          if 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 < N then F p.1 p.2 else 0 :=
          Finset.sum_filter _ _
    _ = ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
          if 0 < q ∧ 0 < m ∧ q * m < N then F q m else 0 := by
          simpa [F] using
            (Finset.sum_product' (Finset.range N) (Finset.range N)
              (fun q m => if 0 < q ∧ 0 < m ∧ q * m < N then F q m else 0))
    _ = ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
          if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
            (Λ q / (q : ℝ)) *
              (1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2))
          else 0 := by
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun m _ => ?_
          by_cases hbase : 0 < q ∧ 0 < m ∧ q * m < N
          · rcases hbase with ⟨hqpos, hmpos, hqmN⟩
            by_cases hxqm : x ≤ q * m <;> by_cases hqY : q < Y <;>
              simp [F, hqpos, hmpos, hqmN, hxqm, hqY, ceilDiv_le_iff_le_mul hqpos]
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Nat.mul_comm] using
              (entryWeightFactor_mul_vonMangoldt_eq_smallFactor q m)
          · simp [F, hbase, show ¬ (0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m) from
              fun h => hbase ⟨h.1, h.2.1, h.2.2.1⟩]

/-- Reindexing the product fiber of `firstEntryPairWeight` recovers the first-entry normalization
summand, including the zero fiber. -/
lemma tsum_firstEntryPairWeight_fiber_prod {x Y n : ℕ} (hx : 1 ≤ x) :
    ∑' p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' {n}, firstEntryPairWeight x Y p =
      normalizationFirstEntryPart x Y n := by
  by_cases hn : n = 0
  · subst hn
    have hzero :
        ∀ p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' ({0} : Set ℕ),
          firstEntryPairWeight x Y p = 0 := by
      rintro ⟨⟨m, q⟩, hp⟩
      by_cases hmq : 1 ≤ m ∧ m < x ∧ entryThreshold x Y m ≤ q
      · have hm_pos : 0 < m := by omega
        have hxle : x ≤ m * q := (entryThreshold_le_iff x Y m q hm_pos).1 hmq.2.2 |>.2
        have : m * q = 0 := by simpa using hp
        omega
      · simp [firstEntryPairWeight, hmq]
    simpa [normalizationFirstEntryPart, show ¬ x ≤ 0 from by omega] using tsum_congr hzero
  · rw [show (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' {n} = n.divisorsAntidiagonal by
      ext mq; simp [Nat.mem_divisorsAntidiagonal, hn],
      Finset.tsum_subtype' n.divisorsAntidiagonal fun mq => firstEntryPairWeight x Y mq,
      Nat.sum_divisorsAntidiagonal' (f := fun m q => firstEntryPairWeight x Y (m, q))]
    by_cases hxn : x ≤ n
    · rw [normalizationFirstEntryPart, if_pos hxn, firstEntryEntryWeight, firstEntryDivisorSum]
      calc
        ∑ q ∈ n.divisors, firstEntryPairWeight x Y (n / q, q) =
            ∑ q ∈ n.divisors,
              entryWeightFactor n * (if Y ≤ q ∧ n / q < x then Λ q else 0) := by
              refine Finset.sum_congr rfl fun q hq => ?_
              have hq_dvd : q ∣ n := (Nat.mem_divisors.mp hq).1
              have hmq_pos : 0 < n / q :=
                Nat.pos_of_dvd_of_pos ⟨q, by simpa using (Nat.div_mul_cancel hq_dvd).symm⟩
                  (Nat.pos_iff_ne_zero.mpr hn)
              have hmul : (n / q) * q = n := Nat.div_mul_cancel hq_dvd
              have hiff : entryThreshold x Y (n / q) ≤ q ↔ Y ≤ q :=
                ⟨fun hle => (entryThreshold_le_iff x Y (n / q) q hmq_pos).1 hle |>.1,
                 fun hYq => (entryThreshold_le_iff x Y (n / q) q hmq_pos).2
                   ⟨hYq, by simpa [hmul] using hxn⟩⟩
              have hmq_ge : 1 ≤ n / q := Nat.succ_le_of_lt hmq_pos
              by_cases hcond : Y ≤ q ∧ n / q < x
              · rw [firstEntryPairWeight_eq (x := x) (Y := Y) hmq_ge hcond.2, if_pos hcond,
                  if_pos (hiff.2 hcond.1)]
                have hmul' : q * (n / q) = n := (mul_comm q (n / q)).trans hmul
                simpa [div_eq_mul_inv, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc, hmul']
                  using (entryWeightFactor_mul_vonMangoldt_eq_smallFactor q (n / q)).symm
              · simp [firstEntryPairWeight, hiff, hmq_ge, hcond, and_comm]
        _ = entryWeightFactor n *
              ∑ q ∈ n.divisors.filter (fun q => Y ≤ q ∧ n / q < x), Λ q := by
              rw [← Finset.mul_sum, ← Finset.sum_filter]
        _ = entryWeightFactor n * firstEntryDivisorSum x Y n := by simp [firstEntryDivisorSum]
    · rw [normalizationFirstEntryPart, if_neg hxn]
      refine Finset.sum_eq_zero fun q hq => ?_
      have hq_dvd : q ∣ n := (Nat.mem_divisors.mp hq).1
      have hmq_pos : 0 < n / q :=
        Nat.pos_of_dvd_of_pos ⟨q, by simpa using (Nat.div_mul_cancel hq_dvd).symm⟩
          (Nat.pos_iff_ne_zero.mpr hn)
      simp [firstEntryPairWeight, Nat.succ_le_of_lt hmq_pos,
        show ¬ entryThreshold x Y (n / q) ≤ q from fun hle =>
          hxn ((entryThreshold_le_iff x Y (n / q) q hmq_pos).1 hle |>.2.trans_eq
            (Nat.div_mul_cancel hq_dvd))]

/-- The normalization constant `B_x` is exactly the sum of its small-prime and first-entry
contributions. -/
lemma normalizationConstant_eq_tsum_parts (x Y : ℕ) :
    normalizationConstant x Y =
      ∑' n : ℕ, (normalizationSmallPrimePart x Y n + normalizationFirstEntryPart x Y n) := by
  refine tsum_congr fun n => ?_
  by_cases hn : x ≤ n
  · simp [normalizationSmallPrimePart, normalizationFirstEntryPart, hn,
      entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight]
  · simp [normalizationSmallPrimePart, normalizationFirstEntryPart, hn]

end PrimitiveSetsAboveX

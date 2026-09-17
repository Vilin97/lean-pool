/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import LeanPool.MooreBound.DegreeDiameter.MooreBound
import LeanPool.MooreBound.DegreeDiameter.Proposition31
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Polynomial.Basic

/-!
# The graph-family asymptotics in Proposition 3.1

This file proves equation (9) for the actual halved flag graphs, indexed by
`PrimePowerIndex`.  Thus `atTop` means that the field cardinality tends to
infinity through all prime powers, as proved by
`tendsto_primePowerIndex_val`.

The proof follows the write-up.  Exact flag enumeration first shows that the
order divided by the `k`-th power of the displayed degree cap tends to one.
The Moore bound and regularity then squeeze the actual common degree against
that cap.  Substitution gives the second displayed asymptotic.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Filter Finset Polynomial Topology
open scoped BigOperators

namespace DegreeDiameter

noncomputable section

/-- The factor `A_q = (q+1)^k` in Proposition 3.1. -/
def proposition31Amplitude (q k : ℕ) : ℕ :=
  (q + 1) ^ k

/-- The sharp displayed degree cap
`K_q = (q+1)^k ((q+1)^k-1)`. -/
def proposition31DegreeCap (q k : ℕ) : ℕ :=
  proposition31Amplitude q k * (proposition31Amplitude q k - 1)

/-- The order of the concrete graph over the chosen field of order `q`. -/
abbrev proposition31PrimePowerOrder (k : ℕ) (q : PrimePowerIndex) : ℕ :=
  Nat.card (Proposition31Vertex (PrimePowerField q) k)

/-- The actual common degree of the concrete graph over the chosen field of
order `q`. -/
abbrev proposition31PrimePowerDegree (k : ℕ) (q : PrimePowerIndex) : ℕ :=
  proposition31Degree (PrimePowerField q) k

/-! ## Polynomial form of exact flag enumeration -/

/-- The real polynomial `1 + X + ... + X^(n-1)`. -/
def proposition31QIntegerPolynomial (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range n, X ^ i

/-- The real polynomial whose value at a natural number `q` is
`qFactorial q n`. -/
def proposition31QFactorialPolynomial (n : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range n, proposition31QIntegerPolynomial (i + 1)

/-- The polynomial `(X+1)^k`. -/
def proposition31AmplitudePolynomial (k : ℕ) : ℝ[X] :=
  (X + 1) ^ k

/-- The polynomial version of the sharp degree cap. -/
def proposition31CapPolynomial (k : ℕ) : ℝ[X] :=
  proposition31AmplitudePolynomial k *
    (proposition31AmplitudePolynomial k - 1)

/-- The denominator polynomial `A_q K_q^k` occurring after the exact
multiplication count is substituted into `N_q / K_q^k`. -/
def proposition31DenominatorPolynomial (k : ℕ) : ℝ[X] :=
  proposition31AmplitudePolynomial k * proposition31CapPolynomial k ^ k

@[simp]
theorem proposition31_eval_qIntegerPolynomial (x : ℝ) (n : ℕ) :
    eval x (proposition31QIntegerPolynomial n) =
      ∑ i ∈ Finset.range n, x ^ i := by
  simp [proposition31QIntegerPolynomial]

theorem proposition31_eval_qIntegerPolynomial_nat (q n : ℕ) :
    eval (q : ℝ) (proposition31QIntegerPolynomial n) =
      (qInteger q n : ℝ) := by
  simp [proposition31QIntegerPolynomial, qInteger]

theorem proposition31_qIntegerPolynomial_monic {n : ℕ} (hn : n ≠ 0) :
    (proposition31QIntegerPolynomial n).Monic := by
  simpa only [proposition31QIntegerPolynomial] using
    (Polynomial.monic_geom_sum_X (R := ℝ) hn)

theorem proposition31_qIntegerPolynomial_natDegree_succ (n : ℕ) :
    (proposition31QIntegerPolynomial (n + 1)).natDegree = n := by
  induction n with
  | zero => simp [proposition31QIntegerPolynomial]
  | succ n ih =>
      change
        (∑ i ∈ Finset.range ((n + 1) + 1), (X : ℝ[X]) ^ i).natDegree = n + 1
      rw [Finset.sum_range_succ]
      change
        (proposition31QIntegerPolynomial (n + 1) + (X : ℝ[X]) ^ (n + 1)).natDegree =
          n + 1
      have hlt :
          (proposition31QIntegerPolynomial (n + 1)).natDegree <
            ((X : ℝ[X]) ^ (n + 1)).natDegree := by
        rw [ih, Polynomial.natDegree_X_pow]
        exact Nat.lt_succ_self n
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt,
        Polynomial.natDegree_X_pow]

@[simp]
theorem proposition31_eval_qFactorialPolynomial_nat (q n : ℕ) :
    eval (q : ℝ) (proposition31QFactorialPolynomial n) =
      (qFactorial q n : ℝ) := by
  rw [qFactorial_eq_prod_range, proposition31QFactorialPolynomial,
    Polynomial.eval_prod]
  simp_rw [proposition31_eval_qIntegerPolynomial_nat]
  push_cast
  rfl

theorem proposition31_qFactorialPolynomial_monic (n : ℕ) :
    (proposition31QFactorialPolynomial n).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact proposition31_qIntegerPolynomial_monic (by omega)

theorem proposition31_qFactorialPolynomial_natDegree_eq_sum (n : ℕ) :
    (proposition31QFactorialPolynomial n).natDegree =
      ∑ i ∈ Finset.range n, i := by
  rw [proposition31QFactorialPolynomial,
    Polynomial.natDegree_prod_of_monic]
  · exact Finset.sum_congr rfl fun i hi ↦
      proposition31_qIntegerPolynomial_natDegree_succ i
  · intro i hi
    exact proposition31_qIntegerPolynomial_monic (by omega)

theorem proposition31_qFactorialPolynomial_natDegree_odd (k : ℕ) :
    (proposition31QFactorialPolynomial (2 * k + 1)).natDegree =
      2 * k * k + k := by
  rw [proposition31_qFactorialPolynomial_natDegree_eq_sum]
  refine Nat.mul_right_cancel (m := 2) (by omega) ?_
  rw [Finset.sum_range_id_mul_two]
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hsub]
  ring

theorem proposition31_amplitudePolynomial_monic (k : ℕ) :
    (proposition31AmplitudePolynomial k).Monic := by
  simpa only [proposition31AmplitudePolynomial, Polynomial.C_1] using
    (Polynomial.monic_X_add_C (1 : ℝ)).pow k

@[simp]
theorem proposition31_amplitudePolynomial_natDegree (k : ℕ) :
    (proposition31AmplitudePolynomial k).natDegree = k := by
  rw [proposition31AmplitudePolynomial, ← Polynomial.C_1,
    (Polynomial.monic_X_add_C (1 : ℝ)).natDegree_pow,
    Polynomial.natDegree_X_add_C, Nat.mul_one]

private theorem proposition31_degree_one_lt_amplitudePolynomial_degree
    {k : ℕ} (hk : 0 < k) :
    degree (1 : ℝ[X]) < degree (proposition31AmplitudePolynomial k) := by
  rw [Polynomial.degree_one,
    Polynomial.degree_eq_natDegree (proposition31_amplitudePolynomial_monic k).ne_zero,
    proposition31_amplitudePolynomial_natDegree]
  exact_mod_cast hk

theorem proposition31_amplitudePolynomial_sub_one_monic
    {k : ℕ} (hk : 0 < k) :
    (proposition31AmplitudePolynomial k - 1).Monic :=
  (proposition31_amplitudePolynomial_monic k).sub_of_left
    (proposition31_degree_one_lt_amplitudePolynomial_degree hk)

@[simp]
theorem proposition31_amplitudePolynomial_sub_one_natDegree
    {k : ℕ} (hk : 0 < k) :
    (proposition31AmplitudePolynomial k - 1).natDegree = k := by
  rw [Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_sub_eq_left_of_degree_lt
      (proposition31_degree_one_lt_amplitudePolynomial_degree hk)),
    proposition31_amplitudePolynomial_natDegree]

theorem proposition31_capPolynomial_monic {k : ℕ} (hk : 0 < k) :
    (proposition31CapPolynomial k).Monic := by
  exact (proposition31_amplitudePolynomial_monic k).mul
    (proposition31_amplitudePolynomial_sub_one_monic hk)

@[simp]
theorem proposition31_capPolynomial_natDegree {k : ℕ} (hk : 0 < k) :
    (proposition31CapPolynomial k).natDegree = 2 * k := by
  rw [proposition31CapPolynomial,
    (proposition31_amplitudePolynomial_monic k).natDegree_mul
      (proposition31_amplitudePolynomial_sub_one_monic hk),
    proposition31_amplitudePolynomial_natDegree,
    proposition31_amplitudePolynomial_sub_one_natDegree hk]
  omega

theorem proposition31_denominatorPolynomial_monic {k : ℕ} (hk : 0 < k) :
    (proposition31DenominatorPolynomial k).Monic := by
  exact (proposition31_amplitudePolynomial_monic k).mul
    ((proposition31_capPolynomial_monic hk).pow k)

@[simp]
theorem proposition31_denominatorPolynomial_natDegree {k : ℕ} (hk : 0 < k) :
    (proposition31DenominatorPolynomial k).natDegree = 2 * k * k + k := by
  rw [proposition31DenominatorPolynomial,
    (proposition31_amplitudePolynomial_monic k).natDegree_mul
      ((proposition31_capPolynomial_monic hk).pow k),
    (proposition31_capPolynomial_monic hk).natDegree_pow,
    proposition31_amplitudePolynomial_natDegree,
    proposition31_capPolynomial_natDegree hk]
  ring

@[simp]
theorem proposition31_eval_amplitudePolynomial_nat (q k : ℕ) :
    eval (q : ℝ) (proposition31AmplitudePolynomial k) =
      (proposition31Amplitude q k : ℝ) := by
  simp [proposition31AmplitudePolynomial, proposition31Amplitude]

@[simp]
theorem proposition31_eval_capPolynomial_nat (q k : ℕ) :
    eval (q : ℝ) (proposition31CapPolynomial k) =
      (proposition31DegreeCap q k : ℝ) := by
  have hA : 1 ≤ proposition31Amplitude q k := by
    exact Nat.one_le_pow' k q
  rw [proposition31CapPolynomial, eval_mul, eval_sub, eval_one,
    proposition31_eval_amplitudePolynomial_nat,
    proposition31DegreeCap, Nat.cast_mul, Nat.cast_sub hA, Nat.cast_one]

@[simp]
theorem proposition31_eval_denominatorPolynomial_nat (q k : ℕ) :
    eval (q : ℝ) (proposition31DenominatorPolynomial k) =
      (proposition31Amplitude q k * proposition31DegreeCap q k ^ k : ℕ) := by
  simp [proposition31DenominatorPolynomial]

/-- Exact q-factorial enumeration and the cap have the same monic leading
term after the multiplication count is substituted. -/
theorem proposition31_qFactorial_div_denominator_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ ↦
        eval x (proposition31QFactorialPolynomial (2 * k + 1)) /
          eval x (proposition31DenominatorPolynomial k))
      atTop (nhds 1) := by
  have hdegree :
      (proposition31QFactorialPolynomial (2 * k + 1)).degree =
        (proposition31DenominatorPolynomial k).degree := by
    rw [Polynomial.degree_eq_natDegree
        (proposition31_qFactorialPolynomial_monic (2 * k + 1)).ne_zero,
      Polynomial.degree_eq_natDegree
        (proposition31_denominatorPolynomial_monic hk).ne_zero,
      proposition31_qFactorialPolynomial_natDegree_odd,
      proposition31_denominatorPolynomial_natDegree hk]
  have h := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (proposition31QFactorialPolynomial (2 * k + 1))
    (proposition31DenominatorPolynomial k) hdegree
  simpa only [
      (proposition31_qFactorialPolynomial_monic (2 * k + 1)).leadingCoeff,
      (proposition31_denominatorPolynomial_monic hk).leadingCoeff,
      div_one] using h

/-- The purely algebraic ratio, restricted from all real `q` to prime-power
cardinalities. -/
theorem proposition31_qFactorial_div_capDenominator_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (qFactorial q.1 (2 * k + 1) : ℝ) /
          (proposition31Amplitude q.1 k *
            proposition31DegreeCap q.1 k ^ k : ℕ))
      atTop (nhds 1) := by
  have hreal := proposition31_qFactorial_div_denominator_tendsto_one k hk
  have hcast : Tendsto (fun q : PrimePowerIndex ↦ (q.1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_primePowerIndex_val
  have hcomp := hreal.comp hcast
  change Tendsto
    (fun q : PrimePowerIndex ↦
      eval (q.1 : ℝ) (proposition31QFactorialPolynomial (2 * k + 1)) /
        eval (q.1 : ℝ) (proposition31DenominatorPolynomial k))
    atTop (nhds 1) at hcomp
  simpa only [
    proposition31_eval_qFactorialPolynomial_nat,
    proposition31_eval_denominatorPolynomial_nat] using hcomp

/-! ## Exact order versus the cap -/
private theorem proposition31_amplitude_pos (q k : ℕ) :
    0 < proposition31Amplitude q k := by
  exact pow_pos (Nat.succ_pos q) k

private theorem proposition31_cap_pos (q : PrimePowerIndex)
    {k : ℕ} (hk : 0 < k) :
    0 < proposition31DegreeCap q.1 k := by
  have hbase : 1 < q.1 + 1 := by
    have hq := q.2.two_le
    omega
  have hpow : q.1 + 1 ≤ proposition31Amplitude q.1 k := by
    simpa only [proposition31Amplitude, pow_one] using
      (pow_le_pow_right₀ (a := q.1 + 1) (by omega) hk)
  have hA : 1 < proposition31Amplitude q.1 k := hbase.trans_le hpow
  exact Nat.mul_pos (Nat.zero_lt_of_lt hA) (Nat.sub_pos_of_lt hA)

private theorem proposition31_order_mul_amplitude
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    proposition31PrimePowerOrder k q * proposition31Amplitude q.1 k =
      qFactorial q.1 (2 * k + 1) := by
  simpa only [proposition31Amplitude] using
    (proposition_3_1_for_prime_power q k hk).2.1

private theorem proposition31_degree_le_cap
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    proposition31PrimePowerDegree k q ≤ proposition31DegreeCap q.1 k := by
  simpa only [proposition31DegreeCap, proposition31Amplitude] using
    (proposition_3_1_for_prime_power q k hk).2.2.2.1

private theorem proposition31_order_div_cap_pow_eq_qFactorial_ratio
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    (proposition31PrimePowerOrder k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) ^ k =
      (qFactorial q.1 (2 * k + 1) : ℝ) /
        (proposition31Amplitude q.1 k *
          proposition31DegreeCap q.1 k ^ k : ℕ) := by
  have hmul :
      (proposition31PrimePowerOrder k q : ℝ) *
          proposition31Amplitude q.1 k =
        qFactorial q.1 (2 * k + 1) := by
    exact_mod_cast proposition31_order_mul_amplitude q k hk
  have hA : (proposition31Amplitude q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast (proposition31_amplitude_pos q.1 k).ne'
  have hC : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast (proposition31_cap_pos q hk).ne'
  push_cast
  rw [← hmul]
  field_simp [hA, hC]

/-- The exact graph order divided by the `k`-th power of the displayed cap
tends to one.  This is the algebraic input to the Moore squeeze. -/
theorem proposition31_order_div_cap_pow_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ) ^ k)
      atTop (nhds 1) := by
  refine (proposition31_qFactorial_div_capDenominator_tendsto_one k hk).congr' ?_
  exact Eventually.of_forall fun q ↦
    (proposition31_order_div_cap_pow_eq_qFactorial_ratio q k hk).symm

/-! ## The Moore squeeze for the actual common degree -/
private theorem proposition31_val_le_cap
    (q : PrimePowerIndex) {k : ℕ} (hk : 0 < k) :
    q.1 ≤ proposition31DegreeCap q.1 k := by
  have hAone : 1 ≤ proposition31Amplitude q.1 k := by
    exact Nat.one_le_pow' k q.1
  have hqA : q.1 + 1 ≤ proposition31Amplitude q.1 k := by
    simpa only [proposition31Amplitude, pow_one] using
      (pow_le_pow_right₀ (a := q.1 + 1) (by omega) hk)
  have hqsub : q.1 ≤ proposition31Amplitude q.1 k - 1 := by
    omega
  calc
    q.1 ≤ proposition31Amplitude q.1 k - 1 := hqsub
    _ = 1 * (proposition31Amplitude q.1 k - 1) := by simp
    _ ≤ proposition31Amplitude q.1 k *
          (proposition31Amplitude q.1 k - 1) :=
      Nat.mul_le_mul_right _ hAone
    _ = proposition31DegreeCap q.1 k := rfl

private theorem proposition31_cap_tendsto_atTop
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun q : PrimePowerIndex ↦ proposition31DegreeCap q.1 k)
      atTop atTop :=
  tendsto_atTop_mono (fun q ↦ proposition31_val_le_cap q hk)
    tendsto_primePowerIndex_val

private theorem proposition31_inv_cap_tendsto_zero
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31DegreeCap q.1 k : ℝ)⁻¹)
      atTop (nhds 0) := by
  have hcast : Tendsto
      (fun q : PrimePowerIndex ↦ (proposition31DegreeCap q.1 k : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (proposition31_cap_tendsto_atTop hk)
  exact tendsto_inv_atTop_zero.comp hcast

private theorem proposition31_order_le_degree_add_one_pow
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    proposition31PrimePowerOrder k q ≤
      (proposition31PrimePowerDegree k q + 1) ^ k := by
  let G := Proposition31Graph (PrimePowerField q) k
  have hp := proposition_3_1_for_prime_power q k hk
  have hregular : ∀ P,
      ((G.neighborSet P).ncard : ℕ) = proposition31PrimePowerDegree k q := by
    intro P
    simpa only [G, Nat.card_coe_set_eq] using hp.1 P
  have hdegree : MaxDegreeLE G (proposition31PrimePowerDegree k q) := by
    intro P
    exact (hregular P).le
  have hdiam : G.ediam ≤ (k : ℕ∞) := hp.2.2.2.2.le
  have hmoore := natCard_le_mooreBound_of_ediam_le' hdegree hdiam
  have hcoarse := mooreBound_le_add_one_pow k
    (proposition31PrimePowerDegree k q)
  simpa only [G] using hmoore.trans hcoarse

/-- **First asymptotic in Proposition 3.1, equation (9).**  For fixed
positive `k`, the actual common degree of the concrete graph is asymptotic
to the paper's sharp cap as `q` tends to infinity through prime powers. -/
theorem proposition31_degree_div_cap_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31Degree (PrimePowerField q) k : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ))
      atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · intro y hy
    by_cases hy0 : y < 0
    · exact Eventually.of_forall fun q ↦ hy0.trans_le (by positivity)
    · have hy_nonneg : 0 ≤ y := le_of_not_gt hy0
      let s : ℝ := (y + 1) / 2
      have hys : y < s := by
        dsimp only [s]
        linarith
      have hs1 : s < 1 := by
        dsimp only [s]
        linarith
      have hs0 : 0 ≤ s := by
        dsimp only [s]
        linarith
      have hspow : s ^ k < 1 := pow_lt_one₀ hs0 hs1 hk.ne'
      have horder := (proposition31_order_div_cap_pow_tendsto_one k hk).eventually
        (Ioi_mem_nhds hspow)
      have hinv := (proposition31_inv_cap_tendsto_zero hk).eventually
        (Iio_mem_nhds (sub_pos.mpr hys))
      filter_upwards [horder, hinv] with q horderq hinvq
      by_contra hnot
      have hratio_le :
          (proposition31PrimePowerDegree k q : ℝ) /
              (proposition31DegreeCap q.1 k : ℝ) ≤ y :=
        le_of_not_gt hnot
      have hcapPos : (0 : ℝ) < proposition31DegreeCap q.1 k := by
        exact_mod_cast proposition31_cap_pos q hk
      have hbase_lt :
          (proposition31PrimePowerDegree k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) +
              1 / (proposition31DegreeCap q.1 k : ℝ) < s := by
        rw [one_div]
        linarith
      have hbase_nonneg :
          0 ≤
            (proposition31PrimePowerDegree k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) +
              1 / (proposition31DegreeCap q.1 k : ℝ) := by
        positivity
      have hpow_lt :
          ((proposition31PrimePowerDegree k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) +
              1 / (proposition31DegreeCap q.1 k : ℝ)) ^ k < s ^ k :=
        pow_lt_pow_left₀ hbase_lt hbase_nonneg hk.ne'
      have hMoore :
          (proposition31PrimePowerOrder k q : ℝ) ≤
            ((proposition31PrimePowerDegree k q + 1) ^ k : ℕ) := by
        exact_mod_cast proposition31_order_le_degree_add_one_pow q k hk
      have hdenPos :
          0 < (proposition31DegreeCap q.1 k : ℝ) ^ k :=
        pow_pos hcapPos k
      have hMooreRatio :
          (proposition31PrimePowerOrder k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) ^ k ≤
            ((proposition31PrimePowerDegree k q : ℝ) /
                  (proposition31DegreeCap q.1 k : ℝ) +
                1 / (proposition31DegreeCap q.1 k : ℝ)) ^ k := by
        calc
          (proposition31PrimePowerOrder k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) ^ k ≤
              (((proposition31PrimePowerDegree k q + 1) ^ k : ℕ) : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) ^ k :=
            div_le_div_of_nonneg_right hMoore hdenPos.le
          _ = ((proposition31PrimePowerDegree k q : ℝ) /
                  (proposition31DegreeCap q.1 k : ℝ) +
                1 / (proposition31DegreeCap q.1 k : ℝ)) ^ k := by
            push_cast
            rw [← div_pow]
            congr 1
            field_simp [hcapPos.ne']
      have hcontr :
          (proposition31PrimePowerOrder k q : ℝ) /
              (proposition31DegreeCap q.1 k : ℝ) ^ k < s ^ k :=
        hMooreRatio.trans_lt hpow_lt
      exact lt_asymm horderq hcontr
  · intro z hz
    exact Eventually.of_forall fun q ↦ by
      have hcapPos : (0 : ℝ) < proposition31DegreeCap q.1 k := by
        exact_mod_cast proposition31_cap_pos q hk
      have hdegree :
          (proposition31PrimePowerDegree k q : ℝ) ≤
            proposition31DegreeCap q.1 k := by
        exact_mod_cast proposition31_degree_le_cap q k hk
      exact ((div_le_one hcapPos).2 hdegree).trans_lt hz

/-- **Second asymptotic in Proposition 3.1, equation (9).**  For fixed
positive `k`, the exact order of the concrete graph is asymptotic to the
`k`-th power of its actual common degree as `q` tends to infinity through
prime powers. -/
theorem proposition31_order_div_degree_pow_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (Nat.card (Proposition31Vertex (PrimePowerField q) k) : ℝ) /
          (proposition31Degree (PrimePowerField q) k : ℝ) ^ k)
      atTop (nhds 1) := by
  have horder := proposition31_order_div_cap_pow_tendsto_one k hk
  have hdegree := proposition31_degree_div_cap_tendsto_one k hk
  have hquot : Tendsto
      (fun q : PrimePowerIndex ↦
        ((proposition31PrimePowerOrder k q : ℝ) /
            (proposition31DegreeCap q.1 k : ℝ) ^ k) /
          (((proposition31PrimePowerDegree k q : ℝ) /
            (proposition31DegreeCap q.1 k : ℝ)) ^ k))
      atTop (nhds 1) := by
    simpa only [proposition31PrimePowerDegree, Pi.div_def, Pi.div_apply, Pi.pow_apply,
      one_pow, div_one] using
      horder.div (hdegree.pow k) (by simp)
  have hdegreePos : ∀ᶠ q : PrimePowerIndex in atTop,
      0 < (proposition31PrimePowerDegree k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) :=
    hdegree.eventually (Ioi_mem_nhds zero_lt_one)
  refine hquot.congr' ?_
  filter_upwards [hdegreePos] with q hdegreeq
  have hcap : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast (proposition31_cap_pos q hk).ne'
  have hdegree_ne : (proposition31PrimePowerDegree k q : ℝ) ≠ 0 := by
    intro hzero
    simp [hzero] at hdegreeq
  rw [div_pow]
  field_simp [hcap, hdegree_ne]

end

end DegreeDiameter

end MooreBound

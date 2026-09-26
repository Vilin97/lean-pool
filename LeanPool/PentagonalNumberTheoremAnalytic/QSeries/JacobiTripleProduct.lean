/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.JTPCore

/-!
# Jacobi triple product identity

The **Jacobi triple product identity** states that for $\|q\| < 1$ and $z \neq 0$:
$$(q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty
  = \sum_{k \in \mathbb{Z}} z^k \, q^{k(k-1)/2}.$$

## Proof strategy

The proof uses:
1. Both sides satisfy the functional equation $H(qz) = H(z)/z$.
2. The Euler identities (first and second) provide series expansions.
3. The Cauchy identity (`hasSum_qPochhammer_div_mul_pow`) relates the product to sums.
4. Extension from the annulus ‖q‖ < ‖z‖ < 1 to the full punctured disk.

## Main results

* `QSeries.jacobiTripleProduct` — the Jacobi triple product identity.
-/

public section

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section


/-- For `‖q‖ < 1` the q-Pochhammer factor `1 - q ^ (n + 1)` is nonzero. -/
private theorem one_sub_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    (1 : ℂ) - q ^ (n + 1) ≠ 0 := by
  intro h
  have h1 : ‖q‖ ^ (n + 1) = 1 := by
    rw [← norm_pow, show q ^ (n + 1) = 1 from by linear_combination -h, norm_one]
  have h2 : ‖q‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
  linarith

/-- Summability of the non-negative part $\sum_{k \geq 0} z^k q^{\binom{k}{2}}$. -/
theorem summable_pow_mul_pow_choose_two {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => z ^ k * q ^ k.choose 2) := by
  refine Summable.of_norm ?_
  simp only [norm_mul, norm_pow]
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hq.le))
    (summable_geometric_of_lt_one (by positivity) hz)

/-- Summability of the negative-index part $\sum_{m \geq 0} z^{-(m+1)} q^{\binom{m+2}{2}}$
for $\|q\| < 1$ and $z \neq 0$. -/
theorem summable_inv_pow_mul_pow_choose_two {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2) := by
  have hr : (0 : ℝ) < ‖q‖ + (1 - ‖q‖) / 2 := by linarith [norm_nonneg q]
  refine summable_of_ratio_norm_eventually_le (r := ‖q‖ + (1 - ‖q‖) / 2) (by linarith) ?_
  have h0 : Tendsto (fun n : ℕ => ‖z⁻¹‖ * ‖q‖ ^ (n + 2)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
        (tendsto_add_atTop_nat 2))
  filter_upwards [h0.eventually (gt_mem_nhds hr)] with n hn
  have hstep : (n + 1 + 2).choose 2 = (n + 2).choose 2 + (n + 2) := Nat.choose_two_succ (n + 2)
  calc ‖z⁻¹ ^ (n + 1 + 1) * q ^ (n + 1 + 2).choose 2‖
      = ‖z⁻¹ ^ (n + 1) * q ^ (n + 2).choose 2‖ * (‖z⁻¹‖ * ‖q‖ ^ (n + 2)) := by
        rw [hstep, pow_add]
        simp only [norm_mul, norm_pow, pow_succ]
        ring
    _ ≤ ‖z⁻¹ ^ (n + 1) * q ^ (n + 2).choose 2‖ * (‖q‖ + (1 - ‖q‖) / 2) :=
        mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)
    _ = _ := by ring

/-- The Jacobi triple product function
$f(z) = (q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty$. -/
@[expose] def jacobiProd (q z : ℂ) : ℂ :=
  qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q

/-- The bilateral Jacobi series (non-negative part). -/
@[expose] def jacobiBilateralPos (q z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ k * q ^ k.choose 2

/-- The bilateral Jacobi series (negative part).
For $k = -(m+1)$ with $m \geq 0$, the exponent is $\binom{m+2}{2} = (m+1)(m+2)/2$. -/
@[expose] def jacobiBilateralNeg (q z : ℂ) : ℂ :=
  ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2

/-- The full bilateral Jacobi series. -/
@[expose] def jacobiBilateral (q z : ℂ) : ℂ :=
  jacobiBilateralPos q z + jacobiBilateralNeg q z

/-- **Telescoping for $(-z;q)_\infty$**: $(-z;q)_\infty = (1+z)(-zq;q)_\infty$. -/
theorem qPochhammerInf_neg_eq_one_add_mul {z q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf (-z) q = (1 + z) * qPochhammerInf (-(z * q)) q := by
  have h := qPochhammerInf_eq_one_sub_mul (z := -z) hq
  rw [show (1 : ℂ) - -z = 1 + z from by ring,
      show -z * q = -(z * q) from by ring] at h
  exact h

/-- The product satisfies $f(qz) = f(z)/z$ when $q \neq 0$ and $z \neq 0$. -/
theorem jacobiProd_mul_eq_div {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0) (hz : z ≠ 0) :
    jacobiProd q (q * z) = jacobiProd q z / z := by
  unfold jacobiProd
  have hqz : q * z ≠ 0 := mul_ne_zero hq' hz
  have h1 := qPochhammerInf_neg_eq_one_add_mul (z := z) hq
  have h2 := qPochhammerInf_neg_eq_one_add_mul (z := z⁻¹) hq
  rw [show -(q * z) = -(z * q) from by ring]
  rw [show -q / (q * z) = -(z⁻¹) from by field_simp]
  rw [show -(z⁻¹ * q) = -q / z from by field_simp] at h2
  rw [h1, h2]
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  field_simp
  ring

/-- The bilateral Jacobi series satisfies the same functional equation $f(qz) = f(z)/z$
as the triple product. -/
theorem jacobiBilateral_mul_eq_div {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0) (hz : ‖z‖ < 1)
    (hz' : z ≠ 0) :
    jacobiBilateral q (q * z) = jacobiBilateral q z / z := by
  rw [eq_div_iff hz', mul_comm]
  have h_pos : z * jacobiBilateralPos q (q * z) =
      ∑' k : ℕ, if k = 0 then 0 else z ^ k * q ^ k.choose 2 := by
    rw [eq_comm, Summable.tsum_eq_zero_add]
    · simp +decide only [↓reduceIte, Nat.add_eq_zero_iff, and_false, pow_succ',
        Nat.choose_succ_succ, Nat.choose_one_right, Nat.succ_eq_add_one, Nat.reduceAdd,
        mul_assoc, tsum_mul_left, zero_add, mul_eq_mul_left_iff]
      exact Or.inl (tsum_congr fun n => by ring)
    · have h_summable : Summable (fun k : ℕ => z ^ k * q ^ k.choose 2) :=
        summable_pow_mul_pow_choose_two hq hz
      rw [← summable_nat_add_iff 1] at *; aesop
  have h_neg : z * jacobiBilateralNeg q (q * z) =
      ∑' m : ℕ, z ^ (-m : ℤ) * q ^ (m + 1).choose 2 := by
    unfold jacobiBilateralNeg
    simp +decide [pow_add, mul_assoc, mul_comm, tsum_mul_left]
    simp +decide [Nat.choose_succ_succ]
    simp +decide [add_comm, add_left_comm, add_assoc, pow_add, mul_left_comm, tsum_mul_left,
      hq', hz']
    simp +decide [mul_pow, mul_assoc, hq']
  convert congr_arg₂ (· + ·) h_pos h_neg using 1
  · rw [← mul_add, jacobiBilateral]
  · unfold jacobiBilateral jacobiBilateralPos jacobiBilateralNeg
    rw [Summable.tsum_eq_zero_add]
    · rw [eq_comm, Summable.tsum_eq_zero_add]
      · norm_num [Nat.choose_succ_succ, pow_succ']
        rw [eq_comm, Summable.tsum_eq_zero_add]
        · norm_num [add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm,
            tsum_mul_left, tsum_mul_right]
          rw [eq_comm, Summable.tsum_eq_zero_add]
          · norm_num [Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm,
              tsum_mul_left, tsum_mul_right]
            ring_nf
          · have := summable_inv_pow_mul_pow_choose_two (z := z) hq
            rw [← summable_nat_add_iff 1]
            (convert this using 2; try rfl)
            norm_num [Nat.choose_succ_succ, pow_succ']
            ring
        · refine Summable.of_norm ?_
          norm_num [pow_add, pow_mul]
          refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
            (summable_geometric_of_lt_one (by positivity) hz)
          exact le_trans (mul_le_of_le_one_right (by positivity)
            ((mul_le_of_le_one_left (pow_nonneg (by positivity) _)
              (pow_le_one₀ (by positivity) hq.le)).trans (pow_le_one₀ (by positivity) hq.le)))
            (mul_le_of_le_one_left (by positivity) hz.le)
      · rw [← summable_nat_add_iff 1]
        exact (summable_pow_mul_pow_choose_two hq hz).comp_injective Nat.succ_injective
    · exact summable_pow_mul_pow_choose_two hq hz

/-- Summability of the Euler second series $\sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$
for all $z$ when $\|q\| < 1$. -/
theorem summable_euler_second' {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n) := by
  have hr : (0 : ℝ) < ‖q‖ + (1 - ‖q‖) / 2 := by linarith [norm_nonneg q]
  refine summable_of_ratio_norm_eventually_le (r := ‖q‖ + (1 - ‖q‖) / 2) (by linarith) ?_
  have h0 : Tendsto (fun n : ℕ => ‖q‖ ^ n * ‖z‖ / ‖1 - q ^ (n + 1)‖) atTop (𝓝 0) := by
    simpa [Pi.div_def] using Tendsto.div
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).mul_const ‖z‖)
      (((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp
        (tendsto_add_atTop_nat 1)).const_sub 1).norm (by norm_num)
  filter_upwards [h0.eventually (gt_mem_nhds hr)] with n hn
  have hstep : (n + 1).choose 2 = n.choose 2 + n := Nat.choose_two_succ n
  have hpoch : qPochhammer q q (n + 1) = qPochhammer q q n * (1 - q ^ (n + 1)) := by
    rw [qPochhammer_succ]; ring
  calc ‖q ^ (n + 1).choose 2 * z ^ (n + 1) / qPochhammer q q (n + 1)‖
      = ‖q ^ n.choose 2 * z ^ n / qPochhammer q q n‖ * (‖q‖ ^ n * ‖z‖ / ‖1 - q ^ (n + 1)‖) := by
        rw [hstep, hpoch, pow_add]
        simp only [norm_mul, norm_div, norm_pow, pow_succ]
        ring
    _ ≤ ‖q ^ n.choose 2 * z ^ n / qPochhammer q q n‖ * (‖q‖ + (1 - ‖q‖) / 2) :=
        mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)
    _ = _ := by ring

/-- The Euler second series satisfies the recursion $E(z) = (1+z) \cdot E(qz)$. -/
theorem tsum_euler_second_eq_one_add_mul {q z : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) =
    (1 + z) * (∑' n : ℕ, q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) := by
  have h_series : ∀ n : ℕ, (q ^ n.choose 2 * z ^ n / qPochhammer q q n) -
      (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) =
      z * (q ^ (n - 1).choose 2 * (z * q) ^ (n - 1) / qPochhammer q q (n - 1)) *
        (if n = 0 then 0 else 1) := by
    rintro (_ | m)
    · simp
    · have hne := one_sub_pow_ne_zero hq m
      have hpne : qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq m
      have hpoch : qPochhammer q q (m + 1) = qPochhammer q q m * (1 - q ^ (m + 1)) := by
        rw [qPochhammer_succ]; ring
      rw [ite_eq_right (Nat.succ_ne_zero m), mul_one, Nat.add_sub_cancel, Nat.choose_two_succ,
        hpoch]
      field_simp
      ring
  have h_series_sum : ∑' n : ℕ, (q ^ n.choose 2 * z ^ n / qPochhammer q q n) -
      ∑' n : ℕ, (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) =
      z * ∑' n : ℕ, (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) := by
    rw [← Summable.tsum_sub, tsum_congr h_series]
    · rw [← tsum_mul_left]
      rw [Summable.tsum_eq_zero_add]
      · aesop
      · rw [← summable_nat_add_iff 1]
        convert Summable.mul_left z
          ((summable_euler_second' hq).comp_injective Nat.cast_injective) using 2 <;> try rfl
        aesop
    · exact summable_euler_second' hq
    · exact summable_euler_second' hq
  linear_combination h_series_sum

/-- The finite telescoping $(-z;q)_\infty = \prod_{k<N}(1+zq^k)\cdot(-zq^N;q)_\infty$. -/
private theorem qPochhammerInf_neg_eq_prod_mul {q z : ℂ} (hq : ‖q‖ < 1) (N : ℕ) :
    qPochhammerInf (-z) q =
      (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.prod_range_succ, qPochhammerInf_eq_one_sub_mul (z := -(z * q ^ N)) hq,
      show -(z * q ^ N) * q = -(z * q ^ (N + 1)) from by ring]
    ring

/-- Euler second identity for all $z$: the series $\sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$
has sum $(-z;q)_\infty$. -/
theorem euler_second_identity' {q z : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n)
      (qPochhammerInf (-z) q) := by
  have h_ind : ∀ N : ℕ, (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) =
      (∏ k ∈ Finset.range N, (1 + z * q ^ k)) *
        ∑' n : ℕ, q ^ n.choose 2 * (z * q ^ N) ^ n / qPochhammer q q n := by
    intro N
    induction N with
    | zero => aesop
    | succ N ih =>
        have h_rec : (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ N) ^ n / qPochhammer q q n) =
            (1 + z * q ^ N) *
              ∑' n : ℕ, q ^ n.choose 2 * (z * q ^ (N + 1)) ^ n / qPochhammer q q n := by
          convert tsum_euler_second_eq_one_add_mul hq using 1; ring_nf
        rw [Finset.prod_range_succ, ih, h_rec, mul_assoc]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖z * q ^ N‖ < 1 := by
    have h_lim : Tendsto (fun N : ℕ => ‖z * q ^ N‖) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq)
    exact (h_lim.eventually (gt_mem_nhds zero_lt_one)).exists
  have h_tsum : (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) =
      (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
    rw [h_ind N, (euler_second_identity hq hN).tsum_eq]
  rw [(qPochhammerInf_neg_eq_prod_mul hq N).trans h_tsum.symm]
  exact (summable_euler_second' hq).hasSum

/-- Euler second identity evaluated at $q/z$: the series
$\sum_{m \geq 0} q^{\binom{m}{2}+m} z^{-m} / (q;q)_m$ has sum $(-q/z;q)_\infty$. -/
theorem euler_second_identity_div' {q z : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q) := by
  convert euler_second_identity' hq |> HasSum.congr_fun <| fun n => ?_ using 1
  rotate_left
  exacts [q * z⁻¹, by ring, by ring_nf]

/-- **Jacobi triple product identity**: $(q;q)_\infty (-z;q)_\infty (-q/z;q)_\infty$ equals the
bilateral theta series $\sum_{k \in \mathbb{Z}} z^k q^{k(k-1)/2}$ for $\|q\| < 1$, $\|z\| < 1$,
and $z \neq 0$. -/
theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  unfold jacobiProd jacobiBilateral jacobiBilateralPos jacobiBilateralNeg
  exact jacobiTripleProduct_of_hasSum hq hz'
    (hasSum_pow_choose_two_mul_pow_mul_qPochhammerInf hq hz)
    (euler_second_identity_div' (z := z) hq)

end

end QSeries

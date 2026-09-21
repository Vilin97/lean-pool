/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.CauchyIdentity
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FiniteBinomial

/-!
# Euler's q-exponential identities

Two classical specializations of the Cauchy identity:

1. **First Euler identity** ($a = 0$):
   $$\frac{1}{(z;q)_\infty} = \sum_{n \geq 0} \frac{z^n}{(q;q)_n}.$$

2. **Second Euler identity** (limit of the finite q-binomial theorem):
   $$(-z;q)_\infty = \sum_{n \geq 0} \frac{q^{\binom{n}{2}}}{(q;q)_n} z^n.$$

## Main results

* `QSeries.euler_first_identity` — the first Euler identity.
* `QSeries.euler_second_identity` — the second Euler identity.
-/

open Finset Filter
open scoped Topology

namespace QSeries

variable {R : Type*}

/-- $(0;q)_n = 1$ for all $n$. -/
@[simp]
theorem qPochhammer_zero_left [CommRing R] (q : R) (n : ℕ) :
    qPochhammer 0 q n = 1 := by
  simp [qPochhammer]

/-- $(0;q)_\infty = 1$. -/
@[simp]
theorem qPochhammerInf_zero_left (q : ℂ) : qPochhammerInf 0 q = 1 := by
  simp [qPochhammerInf]

/-- **First Euler identity.**
$$\sum_{n=0}^{\infty} \frac{z^n}{(q;q)_n} = \frac{1}{(z;q)_\infty}$$
for $\|q\| < 1$ and $\|z\| < 1$. -/
theorem euler_first_identity {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / qPochhammer q q n)
      (1 / qPochhammerInf z q) := by
  have h := hasSum_qPochhammer_div_mul_pow 0 z q hq hz
  simp only [qPochhammer_zero_left, one_div] at h
  convert h using 1
  · ext n; ring
  · simp [zero_mul]

section SecondEuler

/-- The finite q-binomial theorem specialised to $z = -1$ gives a vanishing alternating sum
for every positive $n$. -/
theorem sum_pow_choose_two_mul_qBinom_mul_neg_one_pow [CommRing R] (q : R) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * (-1) ^ k = 0 := by
  rw [← prod_one_add_mul_pow_eq_sum_qBinom]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by ring)

/-- The series $\sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$ is summable for $\|q\| < 1$
and $\|z\| < 1$. -/
theorem summable_euler_second {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n) := by
  have h_const_mul : Summable fun n : ℕ => z ^ n / qPochhammer q q n :=
    (euler_first_identity hq hz).summable
  rw [← summable_norm_iff] at h_const_mul ⊢
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) h_const_mul
  rw [mul_div_assoc, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg q) hq.le)

/-- For $\|q\| < 1$ the ratio $(q;q)_N / (q;q)_{N-k}$ tends to $1$ as $N \to \infty$. -/
private theorem tendsto_qPochhammer_self_div {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun N => qPochhammer q q N / qPochhammer q q (N - k)) atTop (𝓝 1) := by
  have hne : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero hq hq
  have h : Tendsto (fun N => qPochhammer q q (N + k) / qPochhammer q q N) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N => qPochhammer q q (N + k)) atTop (𝓝 (qPochhammerInf q q)) :=
      (tendsto_qPochhammer hq).comp (tendsto_add_atTop_nat k)
    simpa [div_self hne, Pi.div_def] using h1.div (tendsto_qPochhammer hq) hne
  rw [← tendsto_add_atTop_iff_nat k]
  simpa using h

/-- The ratios $(q;q)_N / (q;q)_{N-k}$ are bounded uniformly in both $k$ and $N$. -/
private theorem exists_norm_qPochhammer_self_div_le {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ C, ∀ k N : ℕ, ‖qPochhammer q q N / qPochhammer q q (N - k)‖ ≤ C := by
  have hne : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero hq hq
  obtain ⟨A, hA⟩ := ((tendsto_qPochhammer hq).norm).bddAbove_range
  obtain ⟨B, hB⟩ := (((tendsto_qPochhammer hq).inv₀ hne).norm).bddAbove_range
  refine ⟨A * B, fun k N => ?_⟩
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul (hA ⟨N, rfl⟩) (hB ⟨N - k, rfl⟩) (norm_nonneg _)
    ((norm_nonneg _).trans (hA ⟨0, rfl⟩))

/-- **Second Euler identity**: for $\|q\|, \|z\| < 1$, the infinite product $(-z;q)_\infty$
equals the series $\sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$. -/
theorem euler_second_identity {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n)
      (qPochhammerInf (-z) q) := by
  have h_limit : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      q ^ k.choose 2 * qBinom N k q * z ^ k) atTop (𝓝 (qPochhammerInf (-z) q)) := by
    have hprod : Tendsto (fun N => ∏ k ∈ Finset.range N, (1 + z * q ^ k)) atTop
        (𝓝 (qPochhammerInf (-z) q)) := by
      convert tendsto_qPochhammer (a := -z) hq using 1
      exact funext fun n => Finset.prod_congr rfl fun _ _ => by ring
    exact hprod.congr fun N => prod_one_add_mul_pow_eq_sum_qBinom q z N
  have h_rewrite : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * qBinom N k q * z ^ k =
      ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * z ^ k / qPochhammer q q k *
        (qPochhammer q q N / qPochhammer q q (N - k)) := by
    refine fun N => Finset.sum_congr rfl fun k hk => ?_
    have h_eq : qBinom N k q =
        qPochhammer q q N / (qPochhammer q q k * qPochhammer q q (N - k)) := by
      rw [eq_div_iff (mul_ne_zero (qPochhammer_self_ne_zero hq k)
        (qPochhammer_self_ne_zero hq (N - k))), ← mul_assoc,
        qBinom_mul_qPochhammer_mul_qPochhammer q (Finset.mem_range_succ_iff.mp hk)]
    rw [h_eq]
    field_simp
  have h_tsum : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      q ^ k.choose 2 * z ^ k / qPochhammer q q k *
        (qPochhammer q q N / qPochhammer q q (N - k))) atTop
      (𝓝 (∑' k : ℕ, q ^ k.choose 2 * z ^ k / qPochhammer q q k)) := by
    obtain ⟨C, hC⟩ := exists_norm_qPochhammer_self_div_le (q := q) hq
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
    have hdom : Tendsto (fun N => ∑' k : ℕ, if k < N + 1 then
        q ^ k.choose 2 * z ^ k / qPochhammer q q k *
          (qPochhammer q q N / qPochhammer q q (N - k)) else 0) atTop
        (𝓝 (∑' k : ℕ, q ^ k.choose 2 * z ^ k / qPochhammer q q k)) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun k => ‖q ^ k.choose 2 * z ^ k / qPochhammer q q k‖ * C)
        ((summable_euler_second hq hz).norm.mul_right C) (fun k => ?_) (.of_forall fun N k => ?_)
      · have h1 : Tendsto (fun N => q ^ k.choose 2 * z ^ k / qPochhammer q q k *
            (qPochhammer q q N / qPochhammer q q (N - k))) atTop
            (𝓝 (q ^ k.choose 2 * z ^ k / qPochhammer q q k)) := by
          simpa using tendsto_const_nhds.mul (tendsto_qPochhammer_self_div hq k)
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop k] with N hN
        exact (ite_eq_left (by omega)).symm
      · split_ifs
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hC k N) (norm_nonneg _)
        · simp only [norm_zero]
          exact mul_nonneg (norm_nonneg _) hC0
    refine hdom.congr fun N => ?_
    rw [tsum_eq_sum (s := Finset.range (N + 1)) fun i hi => ite_eq_right (by simpa using hi)]
    exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.mp hi)
  have key : ∑' k : ℕ, q ^ k.choose 2 * z ^ k / qPochhammer q q k = qPochhammerInf (-z) q :=
    tendsto_nhds_unique h_tsum (h_limit.congr h_rewrite)
  rw [← key]
  exact (summable_euler_second hq hz).hasSum

end SecondEuler

end QSeries

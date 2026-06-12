/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import LeanPool.RlTheoryInLean.Defs

/-!
# LeanPool.RlTheoryInLean.StochasticApproximation.DiscreteGronwall
-/

open Real Finset

namespace StochasticApproximation

variable {u b c : ℕ → ℝ}

theorem discrete_gronwall_aux
  {n₀ : ℕ}
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0) :
  ∀ n, n₀ ≤ n → u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
  ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) := by
  intro n hn
  refine Nat.le_induction ?base ?succ n hn
  case base => simp
  case succ =>
    intro k hk ih
    have hck : (0 : ℝ) ≤ 1 + c k := by have := hc k (by linarith); linarith
    grw [hu k (by linarith), ih]
    rw [mul_add, mul_comm, mul_assoc, prod_Ico_mul_eq_prod_Ico_add_one hk,
      add_assoc]
    simp only [add_le_add_iff_left]
    rw [mul_sum, ← sum_Ico_add_eq_sum_Ico_add_one hk]
    simp only [Ico_self, prod_empty, mul_one, add_le_add_iff_right]
    apply sum_le_sum
    intro i hi
    simp only [mem_Ico] at hi
    rw [mul_comm, mul_assoc,
      prod_Ico_mul_eq_prod_Ico_add_one (by omega : i + 1 ≤ k)]

private theorem prod_one_add_le_prod_one_add_of_le
    {n₀ k n : ℕ} (hc : ∀ m ≥ n₀, c m ≥ 0) (hn₀k : n₀ ≤ k) (hkn : k < n) :
    ∏ i ∈ Ico (k + 1) n, (1 + c i) ≤ ∏ i ∈ Ico n₀ n, (1 + c i) := by
  rw [← prod_Ico_consecutive (fun i => 1 + c i) (m := n₀) (n := k + 1) (k := n)
    (by omega) (by omega)]
  apply le_mul_of_one_le_left
  · apply prod_nonneg
    intro i hi
    simp only [mem_Ico] at hi
    linarith [hc i (by linarith)]
  · apply Finset.one_le_prod
    intro i hi
    simp only [mem_Ico] at hi
    linarith [hc i (by linarith)]

private theorem prod_one_add_le_exp_sum
    {n₀ n : ℕ} (hc : ∀ m ≥ n₀, c m ≥ 0) :
    ∏ i ∈ Ico n₀ n, (1 + c i) ≤ exp (∑ i ∈ Ico n₀ n, c i) := by
  rw [exp_sum]
  apply prod_le_prod
  · intro i hi
    simp only [mem_Ico] at hi
    linarith [hc i (by linarith)]
  · intro i _
    rw [add_comm]
    exact add_one_le_exp (c i)

theorem discrete_gronwall
  {n₀ : ℕ}
  (hun₀ : 0 ≤ u n₀)
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0)
  (hb : ∀ n ≥ n₀, b n ≥ 0) :
  ∀ n, n₀ ≤ n →
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
  intro n hn
  grw [discrete_gronwall_aux hu hc n hn]
  have hsum : ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) ≤
      ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico n₀ n, (1 + c i) :=
    sum_le_sum fun j hj => by
      simp only [mem_Ico] at hj
      exact mul_le_mul_of_nonneg_left
        (prod_one_add_le_prod_one_add_of_le hc (by linarith) (by linarith))
        (hb j (by linarith))
  have hnn : 0 ≤ u n₀ + ∑ k ∈ Ico n₀ n, b k :=
    add_nonneg hun₀ (sum_nonneg fun i hi => by simp only [mem_Ico] at hi; exact hb i (by linarith))
  calc u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
        ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i)
      ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
        ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico n₀ n, (1 + c i) := by linarith [hsum]
    _ = (u n₀ + ∑ k ∈ Ico n₀ n, b k) * ∏ i ∈ Ico n₀ n, (1 + c i) := by
        rw [← sum_mul, ← add_mul]
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) :=
        mul_le_mul_of_nonneg_left (prod_one_add_le_exp_sum hc) hnn

theorem discrete_gronwall_Ico
  {n₀ n₁ : ℕ}
  (hun₀ : 0 ≤ u n₀)
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0)
  (hb : ∀ n ≥ n₀, b n ≥ 0) :
  ∀ n ∈ Ico n₀ n₁,
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) := by
  intro n hn
  simp only [mem_Ico] at hn
  grw [discrete_gronwall hun₀ hu hc hb n hn.1]
  have hsubset : Ico n₀ n ⊆ Ico n₀ n₁ := Ico_subset_Ico_right (by omega)
  have hbsum : ∑ k ∈ Ico n₀ n, b k ≤ ∑ k ∈ Ico n₀ n₁, b k :=
    sum_le_sum_of_subset_of_nonneg hsubset
      fun i hi _ => by simp only [mem_Ico] at hi
                       exact hb i (by linarith)
  have hcsum : ∑ i ∈ Ico n₀ n, c i ≤ ∑ i ∈ Ico n₀ n₁, c i :=
    sum_le_sum_of_subset_of_nonneg hsubset
      fun i hi _ => by simp only [mem_Ico] at hi
                       exact hc i (by linarith)
  have hbnn : 0 ≤ u n₀ + ∑ k ∈ Ico n₀ n₁, b k :=
    add_nonneg hun₀ (sum_nonneg fun i hi => by simp only [mem_Ico] at hi; exact hb i (by linarith))
  exact mul_le_mul (by linarith) (exp_le_exp.mpr hcsum) (by positivity) hbnn

end StochasticApproximation

/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoResumeS3E.GuardScaling

/-!
The explicit below-two coefficient matrices satisfy recurrence, support, and row-sum
conditions.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage3BelowTwoS3F

/-- The quadratic below-two weights, constant at the terminal index and zero beyond it. -/
noncomputable def weight (n k : ℕ) : ℝ :=
  if k < n then (((k : ℝ) + 1) ^ (2 : ℕ)) / 4
  else if k = n then ((n : ℝ) ^ (2 : ℕ)) / 4
  else 0

/-- The below-two weight increments, set to zero from the terminal index onward. -/
noncomputable def increment (n k : ℕ) : ℝ :=
  if k < n then weight n k - (if k = 0 then 0 else weight n (k - 1)) else 0

/-- The subdiagonal coefficient matrix selecting each weighted gradient increment. -/
noncomputable def alpha (n : ℕ) : ScalarMatrix := fun row i =>
  if 0 < row ∧ row ≤ n then
    if i = row - 1 then increment n (row - 1) else 0
  else 0

/-- The recursive coefficients expressing primal iterates as combinations of mirror iterates. -/
noncomputable def coeffC (n : ℕ) : ScalarMatrix
  | 0, i => if i = 0 then 1 else 0
  | k + 1, i =>
      (weight n k / weight n (k + 1)) * coeffC n k i +
      ((increment n (k + 1) + increment n k) / weight n (k + 1)) *
        (if i = k + 1 then 1 else 0) -
      (increment n k / weight n (k + 1)) * (if i = k then 1 else 0)

/-- The differences of successive primal coefficient rows, with the prescribed initial row. -/
noncomputable def coeffB (n : ℕ) : ScalarMatrix
  | 0, i => if i = 0 then -1 else 0
  | k + 1, i => coeffC n k i - coeffC n (k + 1) i

@[simp] theorem weight_of_lt {n k : ℕ} (hk : k < n) :
    weight n k = (((k : ℝ) + 1) ^ (2 : ℕ)) / 4 := by
  simp [weight, hk]

@[simp] theorem weight_at {n : ℕ} :
    weight n n = ((n : ℝ) ^ (2 : ℕ)) / 4 := by
  simp [weight]

theorem weight_pos {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    0 < weight n k := by
  by_cases hlt : k < n
  · rw [weight_of_lt hlt]
    positivity
  · have hkn : k = n := by omega
    subst k
    rw [weight_at]
    positivity

@[simp] theorem increment_of_lt {n k : ℕ} (hk : k < n) :
    increment n k = weight n k - (if k = 0 then 0 else weight n (k - 1)) := by
  simp [increment, hk]

@[simp] theorem increment_at {n : ℕ} : increment n n = 0 := by
  simp [increment]

theorem increment_formula {n k : ℕ} (hk : k < n) :
    increment n k = ((2 : ℝ) * k + 1) / 4 := by
  rw [increment_of_lt hk, weight_of_lt hk]
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · simp only [hk0, ↓reduceIte]
    have hpred : k - 1 < n := by omega
    rw [weight_of_lt hpred]
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hcast]
    ring

theorem weight_sub_increment_sq {n k : ℕ} (hk : k < n) :
    weight n k - (increment n k) ^ (2 : ℕ) = ((4 : ℝ) * k + 3) / 16 := by
  rw [weight_of_lt hk, increment_formula hk]
  ring

theorem weight_succ_relation {n k : ℕ} (hk : k < n) :
    weight n (k + 1) = weight n k + increment n (k + 1) := by
  by_cases hs : k + 1 < n
  · rw [increment_of_lt hs]
    simp only [show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
    ring
  · have heq : k + 1 = n := by omega
    rw [heq, increment_at]
    have hweights : weight n n = weight n k := by
      rw [weight_at, weight_of_lt hk]
      have hcast : ((k : ℝ) + 1) = (n : ℝ) := by exact_mod_cast heq
      rw [hcast]
    rw [hweights]
    ring

@[simp] theorem alpha_row {n k i : ℕ} (hk : k < n) :
    alpha n (k + 1) i = if i = k then increment n k else 0 := by
  simp [alpha, hk]

@[simp] theorem coeffC_zero : coeffC n 0 0 = 1 := by
  simp [coeffC]

@[simp] theorem coeffB_zero : coeffB n 0 0 = -1 := by
  simp [coeffB]

theorem coeffC_support (n : ℕ) : ∀ k i, k < i → coeffC n k i = 0 := by
  intro k
  induction k with
  | zero =>
      intro i hi
      simp [coeffC, Nat.ne_of_gt hi]
  | succ k ih =>
      intro i hi
      have hik : i ≠ k := by omega
      have hiks : i ≠ k + 1 := by omega
      rw [coeffC]
      simp [ih i (by omega), hik, hiks]

theorem coeffC_row_sum (n : ℕ) (hn : 1 ≤ n) :
    ∀ k ≤ n, (∑ i ∈ Finset.range (k + 1), coeffC n k i) = 1 := by
  intro k hk
  induction k with
  | zero => simp [coeffC]
  | succ k ih =>
      have hkn : k < n := by omega
      have hupos : 0 < weight n (k + 1) := weight_pos hn (by omega)
      have hune : weight n (k + 1) ≠ 0 := hupos.ne'
      rw [Finset.sum_range_succ]
      simp_rw [coeffC]
      have hsupport : coeffC n k (k + 1) = 0 := coeffC_support n k (k + 1) (by omega)
      have hsumc : (∑ x ∈ Finset.range (k + 1), coeffC n k x) = 1 := ih (by omega)
      have hfirst :
          (∑ x ∈ Finset.range (k + 1),
            ((weight n k / weight n (k + 1)) * coeffC n k x +
              ((increment n (k + 1) + increment n k) / weight n (k + 1)) *
                (if x = k + 1 then 1 else 0) -
              (increment n k / weight n (k + 1)) * (if x = k then 1 else 0))) =
          weight n k / weight n (k + 1) -
            increment n k / weight n (k + 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have hmul :
            (∑ x ∈ Finset.range (k + 1),
              weight n k / weight n (k + 1) * coeffC n k x) =
              weight n k / weight n (k + 1) := by
          rw [← Finset.mul_sum, hsumc, mul_one]
        rw [hmul]
        simp
      rw [hfirst]
      simp [hsupport]
      field_simp [hune]
      have hrel := weight_succ_relation hkn
      linarith

theorem coeffB_row_sum (n : ℕ) (hn : 1 ≤ n) :
    ∀ k < n, (∑ i ∈ Finset.range (k + 2), coeffB n (k + 1) i) = 0 := by
  intro k hk
  simp_rw [coeffB]
  rw [Finset.sum_sub_distrib]
  have hsupp : coeffC n k (k + 1) = 0 := coeffC_support n k (k + 1) (by omega)
  rw [Finset.sum_range_succ, hsupp, add_zero,
    coeffC_row_sum n hn k (by omega), coeffC_row_sum n hn (k + 1) (by omega)]
  ring

theorem coefficient_assumptions (n : ℕ) (hn : 1 ≤ n) :
    BelowCoefficientAssumptions n (weight n) (increment n)
      (alpha n) (coeffC n) (coeffB n) := by
  refine ⟨?_, ?_, increment_at, coeffC_zero, coeffB_zero, ?_, ?_, ?_, ?_, ?_⟩
  · rw [weight_of_lt hn]
    norm_num
  · rw [weight_at, weight_of_lt (show n - 1 < n by omega)]
    have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      ring
    rw [hcast]
  · intro k hk
    exact ⟨weight_of_lt hk, increment_of_lt hk, fun i => alpha_row hk⟩
  · intro k hk i
    exact ⟨rfl, rfl⟩
  · exact coeffC_row_sum n hn
  · intro k hk i hi
    exact coeffC_support n k i hi
  · exact coeffB_row_sum n hn

end V7.Stage3BelowTwoS3F

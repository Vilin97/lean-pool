/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoDualPhase.AnalyticPrefix
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Machine

/-!
The above-two trial coefficients satisfy recurrence, support, and row-sum assumptions.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage4AboveTwoFinalTrial

/-- The terminal-plateau weight sequence used by the above-two trial. -/
noncomputable def weight (p eta : ℝ) (n : ℕ) : ScalarSeq :=
  Stage4AboveTwoDualPhase.plateauU p eta n

/-- The increments of the above-two trial's weight sequence. -/
noncomputable def increment (p eta : ℝ) (n : ℕ) : ScalarSeq :=
  Stage4AboveTwoDualPhase.plateauDw p eta n

/-- The subdiagonal matrix selecting weighted gradient increments in an above-two phase. -/
noncomputable def alpha (p eta : ℝ) (n : ℕ) : ScalarMatrix := fun row i =>
  if 0 < row ∧ row ≤ n then
    if i = row - 1 then increment p eta n (row - 1) else 0
  else 0

/-- The recursive coefficients expressing above-two primal iterates in mirror iterates. -/
noncomputable def coeffC (p eta : ℝ) (n : ℕ) : ScalarMatrix
  | 0, i => if i = 0 then 1 else 0
  | k + 1, i =>
      (weight p eta n k / weight p eta n (k + 1)) * coeffC p eta n k i +
      ((increment p eta n (k + 1) + increment p eta n k) /
        weight p eta n (k + 1)) * (if i = k + 1 then 1 else 0) -
      (increment p eta n k / weight p eta n (k + 1)) *
        (if i = k then 1 else 0)

/-- The differences of successive above-two primal coefficient rows. -/
noncomputable def coeffB (p eta : ℝ) (n : ℕ) : ScalarMatrix
  | 0, i => if i = 0 then -1 else 0
  | k + 1, i => coeffC p eta n k i - coeffC p eta n (k + 1) i

@[simp] theorem weight_of_lt {p eta : ℝ} {n k : ℕ} (hk : k < n) :
    weight p eta n k = aboveGamma p eta n * ((k : ℝ) + 1) ^ (2 : ℕ) := by
  simp [weight, Stage4AboveTwoDualPhase.plateauU, hk]

@[simp] theorem weight_at {p eta : ℝ} {n : ℕ} :
    weight p eta n n = aboveGamma p eta n * (n : ℝ) ^ (2 : ℕ) := by
  simp [weight, Stage4AboveTwoDualPhase.plateauU]

theorem increment_of_lt {p eta : ℝ} {n k : ℕ} :
    increment p eta n k = weight p eta n k -
      (if k = 0 then 0 else weight p eta n (k - 1)) := by
  simp [increment, Stage4AboveTwoDualPhase.plateauDw, weight]

@[simp] theorem increment_at {p eta : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    increment p eta n n = 0 := by
  simp only [increment, Stage4AboveTwoDualPhase.plateauDw,
    Stage4AboveTwoDualPhase.plateauU, lt_irrefl, ite_false,
    show n ≠ 0 by omega]
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  rw [hcast]
  rw [ite_eq_left (show n - 1 < n by omega)]
  ring

theorem gamma_pos {p eta : ℝ} {n : ℕ} (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) : 0 < aboveGamma p eta n :=
  Stage4AboveTwo.gamma_pos hp heta hn

theorem weight_pos {p eta : ℝ} {n k : ℕ} (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) (hk : k ≤ n) :
    0 < weight p eta n k := by
  by_cases hlt : k < n
  · rw [weight_of_lt hlt]
    exact mul_pos (gamma_pos hp heta hn) (sq_pos_of_pos (by positivity))
  · have hkn : k = n := by omega
    subst k
    rw [weight_at]
    exact mul_pos (gamma_pos hp heta hn) (sq_pos_of_pos (by
      exact_mod_cast (Nat.zero_lt_of_lt hn)))

theorem weight_succ_relation {p eta : ℝ} {n k : ℕ}
     (hn : 1 ≤ n) (hk : k < n) :
    weight p eta n (k + 1) =
      weight p eta n k + increment p eta n (k + 1) := by
  by_cases hs : k + 1 < n
  · rw [increment_of_lt]
    simp only [show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
    ring
  · have heq : k + 1 = n := by omega
    rw [heq, increment_at hn]
    have hweights : weight p eta n n = weight p eta n k := by
      rw [weight_at, weight_of_lt hk]
      have hcast : ((k : ℝ) + 1) = (n : ℝ) := by exact_mod_cast heq
      rw [hcast]
    rw [hweights]
    ring

@[simp] theorem alpha_row {p eta : ℝ} {n k i : ℕ} (hk : k < n) :
    alpha p eta n (k + 1) i =
      if i = k then increment p eta n k else 0 := by
  simp [alpha, hk]

@[simp] theorem coeffC_zero {p eta : ℝ} {n : ℕ} :
    coeffC p eta n 0 0 = 1 := by simp [coeffC]

@[simp] theorem coeffB_zero {p eta : ℝ} {n : ℕ} :
    coeffB p eta n 0 0 = -1 := by simp [coeffB]

theorem coeffC_support (p eta : ℝ) (n : ℕ) :
    ∀ k i, k < i → coeffC p eta n k i = 0 := by
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

theorem coeffC_row_sum (p eta : ℝ) (n : ℕ) (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) :
    ∀ k ≤ n, (∑ i ∈ Finset.range (k + 1), coeffC p eta n k i) = 1 := by
  intro k hk
  induction k with
  | zero => simp [coeffC]
  | succ k ih =>
      have hkn : k < n := by omega
      have hupos : 0 < weight p eta n (k + 1) :=
        weight_pos hp heta hn (by omega)
      have hune : weight p eta n (k + 1) ≠ 0 := hupos.ne'
      rw [Finset.sum_range_succ]
      simp_rw [coeffC]
      have hsupport : coeffC p eta n k (k + 1) = 0 :=
        coeffC_support p eta n k (k + 1) (by omega)
      have hsumc : (∑ x ∈ Finset.range (k + 1), coeffC p eta n k x) = 1 :=
        ih (by omega)
      have hfirst :
          (∑ x ∈ Finset.range (k + 1),
            ((weight p eta n k / weight p eta n (k + 1)) *
                coeffC p eta n k x +
              ((increment p eta n (k + 1) + increment p eta n k) /
                weight p eta n (k + 1)) *
                  (if x = k + 1 then 1 else 0) -
              (increment p eta n k / weight p eta n (k + 1)) *
                (if x = k then 1 else 0))) =
          weight p eta n k / weight p eta n (k + 1) -
            increment p eta n k / weight p eta n (k + 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have hmul :
            (∑ x ∈ Finset.range (k + 1),
              weight p eta n k / weight p eta n (k + 1) *
                coeffC p eta n k x) =
              weight p eta n k / weight p eta n (k + 1) := by
          rw [← Finset.mul_sum, hsumc, mul_one]
        rw [hmul]
        simp
      rw [hfirst]
      simp [hsupport]
      field_simp [hune]
      have hrel := weight_succ_relation (p := p) (eta := eta) hn hkn
      linarith

theorem coeffB_row_sum (p eta : ℝ) (n : ℕ) (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) :
    ∀ k < n, (∑ i ∈ Finset.range (k + 2), coeffB p eta n (k + 1) i) = 0 := by
  intro k hk
  simp_rw [coeffB]
  rw [Finset.sum_sub_distrib]
  have hsupp : coeffC p eta n k (k + 1) = 0 :=
    coeffC_support p eta n k (k + 1) (by omega)
  rw [Finset.sum_range_succ, hsupp, add_zero,
    coeffC_row_sum p eta n hp heta hn k (by omega),
    coeffC_row_sum p eta n hp heta hn (k + 1) (by omega)]
  ring

theorem coefficient_assumptions (p eta : ℝ) (n : ℕ) (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) :
    AboveCoefficientAssumptions n (weight p eta n) (increment p eta n)
      (alpha p eta n) (coeffC p eta n) (coeffB p eta n) := by
  refine ⟨?_, ?_, increment_at hn, coeffC_zero, coeffB_zero, ?_, ?_, ?_, ?_, ?_⟩
  · exact weight_pos hp heta hn (by omega)
  · rw [weight_at, weight_of_lt (show n - 1 < n by omega)]
    have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      rw [Nat.cast_sub hn, Nat.cast_one]
      ring
    rw [hcast]
  · intro k hk
    refine ⟨weight_pos hp heta hn (by omega), ?_, increment_of_lt,
      fun i => alpha_row hk⟩
    rw [weight_succ_relation hn hk]
    have hinc : 0 ≤ increment p eta n (k + 1) := by
      by_cases hsucc : k + 1 < n
      · rw [increment_of_lt]
        simp only [show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
        rw [weight_of_lt hsucc, weight_of_lt hk]
        have hg : 0 < aboveGamma p eta n := gamma_pos hp heta hn
        push_cast
        rw [show aboveGamma p eta n * ((k : ℝ) + 1 + 1) ^ 2 -
            aboveGamma p eta n * ((k : ℝ) + 1) ^ 2 =
            aboveGamma p eta n * (2 * (k : ℝ) + 3) by ring]
        positivity
      · have heq : k + 1 = n := by omega
        rw [heq, increment_at hn]
    linarith
  · intro k hk i
    exact ⟨rfl, rfl⟩
  · exact coeffC_row_sum p eta n hp heta hn
  · intro k hk i hi
    exact coeffC_support p eta n k i hi
  · exact coeffB_row_sum p eta n hp heta hn

end V7.Stage4AboveTwoFinalTrial

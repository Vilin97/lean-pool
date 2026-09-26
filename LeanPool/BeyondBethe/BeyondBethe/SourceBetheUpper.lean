/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Optimizer
public import LeanPool.BeyondBethe.BeyondBethe.SourceAnariRezaeiList

/-! # Source Bethe Upper -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# The upper half of the Bethe sandwich

For a positive matrix, the Gibbs distribution on perfect matchings has a
doubly stochastic marginal matrix `P`.  The exact sequential identity writes
`log(per A)` as the Bethe objective at `P`, plus one correction per row, minus
a nonnegative averaged relative entropy.  The sharp Anari--Rezaei row theorem
bounds every correction by `log 2 / 2`.  This is the whole upper-bound proof.
-/

theorem sum_rowCorrection_le_log_two_half
    {n : ℕ} (hn : 2 ≤ n) {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) :
    (∑ i, rowCorrection (P i)) ≤ n * (Real.log 2 / 2) := by
  have hrow : ∀ i : Fin n, rowCorrection (P i) ≤ Real.log 2 / 2 := by
    intro i
    have hPi : IsProbabilityVector (P i) :=
      ⟨fun j ↦ hP.1 i j, hP.2.1 i⟩
    have hdeficit := anariRezaeiRowInequality hn (P i) hPi
    rw [rowDeficit] at hdeficit
    linarith
  calc
    (∑ i, rowCorrection (P i)) ≤ ∑ _i : Fin n, Real.log 2 / 2 :=
      Finset.sum_le_sum fun i _ ↦ hrow i
    _ = n * (Real.log 2 / 2) := by simp

/-- Logarithmic upper Bethe bound for positive matrices of order at least two. -/
theorem log_permanent_le_betheLogValue_add_log_two_half
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.Positive A) :
    Real.log (Matrix.permanent A) ≤
      betheLogValue A + n * (Real.log 2 / 2) := by
  let P := assignmentMarginal A
  have hper : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hP : IsDoublyStochastic P :=
    assignmentMarginal_doublyStochastic A (fun i j ↦ (hA i j).le) hper.ne'
  have hobjective : betheObjective A P ≤ betheLogValue A :=
    betheObjective_le_betheLogValue_of_positive hA hP
  have hrows : (∑ i, rowCorrection (P i)) ≤
      n * (Real.log 2 / 2) := sum_rowCorrection_le_log_two_half hn hP
  have hdiv : 0 ≤ gibbsSequentialDivergence A :=
    gibbsSequentialDivergence_nonneg A hA
  have hexact := gibbs_exact_sequential_identity A hA
  dsimp only [P] at hP hobjective hrows hexact
  linarith

/-- The upper half of the Bethe sandwich for positive matrices. -/
theorem permanent_le_sqrtTwo_pow_mul_bethePermanent_of_positive
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.Positive A) :
    Matrix.permanent A ≤
      (Real.sqrt 2) ^ n * bethePermanent A := by
  have hmatch : Matrix.HasPerfectMatching A := positiveMatrix_hasPerfectMatching hA
  have hper : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hlog := log_permanent_le_betheLogValue_add_log_two_half hn A hA
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hper, Real.exp_add] at hexp
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hfactor : Real.exp (n * (Real.log 2 / 2)) =
      (Real.sqrt 2) ^ n := by
    rw [Real.exp_nat_mul]
    congr 1
    rw [← Real.exp_log hsqrt, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hbethe : bethePermanent A = Real.exp (betheLogValue A) := by
    rw [bethePermanent, ite_eq_left hmatch]
  rw [hfactor, ← hbethe] at hexp
  simpa [mul_comm] using hexp

end BeyondBethe

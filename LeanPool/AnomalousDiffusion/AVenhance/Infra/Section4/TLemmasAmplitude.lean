/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Tactic.IntervalCases

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRecursion

/-! Factorial-weighted closure of the source amplitudes in
`l.Tm.minus.thetam`.  The analytic input is the exact per-increment `l.V`
bound; this file closes only its finite scalar sum. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- For the positive increments, the source amplitude after the first two
levels is dominated by a geometric tail when `η ≤ 1/4`. -/
theorem iterateAmplitude_two_shift_le_geometric {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4) (k : ℕ) :
    iterateAmplitude η (k + 2) ≤ η * (1 / 2 : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp [iterateAmplitude]
  · have hidx : 3 ≤ k + 2 := by omega
    have hsq : iterateAmplitude η (k + 2) ^ 2 = η ^ (k + 2) := by
      rw [iterateAmplitude_square hη (k + 2)]
      simp [iterateAmplitudeSq, show ¬ k + 2 ≤ 2 by omega]
    have hpow : η ^ k ≤ (1 / 4 : ℝ) ^ k :=
      pow_le_pow_left₀ hη hηsmall k
    have hpow' : η ^ (k + 2) ≤ η ^ 2 * (1 / 4 : ℝ) ^ k := by
      calc
        η ^ (k + 2) = η ^ 2 * η ^ k := by
          rw [show k + 2 = 2 + k by omega, pow_add]
        _ ≤ η ^ 2 * (1 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow (sq_nonneg η)
    have hhalf : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
      calc
        ((1 / 2 : ℝ) ^ k) ^ 2 = ((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k) := by ring
        _ = ((1 / 2 : ℝ) * (1 / 2 : ℝ)) ^ k := by rw [← mul_pow]
        _ = (1 / 4 : ℝ) ^ k := by norm_num
    have htarget : (η * (1 / 2 : ℝ) ^ k) ^ 2 =
        η ^ 2 * (1 / 4 : ℝ) ^ k := by rw [mul_pow, hhalf]
    have hA : 0 ≤ iterateAmplitude η (k + 2) := by
      simp only [iterateAmplitude, ite_eq_right (by omega : k + 2 ≠ 0),
        ite_eq_right (by omega : ¬ k + 2 ≤ 2)]
      exact Real.rpow_nonneg hη _
    have hB : 0 ≤ η * (1 / 2 : ℝ) ^ k := mul_nonneg hη (by positivity)
    apply (sq_le_sq₀ hA hB).mp
    rw [hsq, htarget]
    exact hpow'

/-- The finite sum of all positive-increment source amplitudes costs at most
`3η`: the first increment contributes `η`, the second-through-last increments
have a geometric majorant of mass at most `2η`. -/
theorem iterateAmplitude_positive_sum_le_three {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4) (N : ℕ) :
    (∑ i ∈ Finset.range N, iterateAmplitude η (i + 1)) ≤ 3 * η := by
  have hsplit (n : ℕ) :
      (∑ i ∈ Finset.range (n + 2), iterateAmplitude η (i + 1)) =
        iterateAmplitude η 1 + iterateAmplitude η 2 +
          ∑ i ∈ Finset.range n, iterateAmplitude η (i + 3) := by
    induction n with
    | zero => simp [Finset.sum_range_succ, iterateAmplitude]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
  have htail (n : ℕ) :
      (∑ i ∈ Finset.range n, iterateAmplitude η (i + 3)) ≤ η := by
    calc
      (∑ i ∈ Finset.range n, iterateAmplitude η (i + 3)) ≤
          ∑ i ∈ Finset.range n, (η / 2) * (1 / 2 : ℝ) ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        have h := iterateAmplitude_two_shift_le_geometric hη hηsmall (i + 1)
        have heq : i + 1 + 2 = i + 3 := by omega
        rw [heq] at h
        have hscale : η * (1 / 2 : ℝ) ^ (i + 1) =
            (η / 2) * (1 / 2 : ℝ) ^ i := by
          rw [pow_succ]
          ring
        simpa only [hscale] using h
      _ = (η / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]
      _ ≤ (η / 2) * 2 := by
        exact mul_le_mul_of_nonneg_left
          (iterate_geometric_kernel_le_two (by norm_num) (by norm_num) n) (by positivity)
      _ = η := by ring
  by_cases hN : N < 2
  · interval_cases N <;> simp [iterateAmplitude] <;> nlinarith [hη]
  · let n := N - 2
    have hN' : N = n + 2 := by dsimp [n]; omega
    rw [hN']
    rw [hsplit n]
    have h₁ : iterateAmplitude η 1 = η := by simp [iterateAmplitude]
    have h₂ : iterateAmplitude η 2 = η := by simp [iterateAmplitude]
    rw [h₁, h₂]
    have htail' := htail n
    nlinarith [hη]

/-- The source `l.V` amplitude estimates sum to the error scale in
`l.Tm.minus.thetam`.  This is the numerical closure with the source's
`4 C₀^3` slack; application to the actual L² norms uses Minkowski separately. -/
theorem iterate_Tm_minus_theta_factorial_sum_bound {η ρ C₀ : ℝ} {N : ℕ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4) (hscale : η ≤ C₀ * ρ)
    (hC₀ρ : 0 ≤ C₀ * ρ) :
    (∑ i ∈ Finset.range N,
      (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1)) ≤
      (Nat.factorial (2 * N) : ℝ) * (4 * C₀ * ρ) := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range N) :
      (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1) ≤
        (Nat.factorial (2 * N) : ℝ) * iterateAmplitude η (i + 1) := by
    have hA : 0 ≤ iterateAmplitude η (i + 1) := by
      unfold iterateAmplitude
      split_ifs <;> positivity
    have hi' : i < N := Finset.mem_range.mp hi
    apply mul_le_mul_of_nonneg_right _ hA
    exact_mod_cast Nat.factorial_le (by omega : 2 * (i + 1) ≤ 2 * N)
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (Nat.factorial (2 * N) : ℝ) * iterateAmplitude η (i + 1) :=
      Finset.sum_le_sum (fun i hi => hterm i hi)
    _ = (Nat.factorial (2 * N) : ℝ) *
        ∑ i ∈ Finset.range N, iterateAmplitude η (i + 1) := by
      rw [Finset.mul_sum]
    _ ≤ (Nat.factorial (2 * N) : ℝ) * (3 * η) :=
      mul_le_mul_of_nonneg_left
        (iterateAmplitude_positive_sum_le_three hη hηsmall N) (by positivity)
    _ ≤ (Nat.factorial (2 * N) : ℝ) * (4 * C₀ * ρ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hscale, hC₀ρ]

end AVenhance.Infra.Section4

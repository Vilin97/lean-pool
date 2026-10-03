/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAmplitude
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Iterates Finite Analytic Sum

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The printed amplitudes have a geometric majorant at the T threshold. -/
theorem iterate_amplitude_le_half_pow {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (i : ℕ) : iterateAmplitude η i ≤ (1 / 2 : ℝ) ^ i := by
  have hn : 0 ≤ iterateAmplitude η i := by unfold iterateAmplitude; split_ifs <;> positivity
  apply (sq_le_sq₀ hn (by positivity)).mp
  rw [iterateAmplitude_square hη]
  by_cases hi0 : i = 0
  · subst i; norm_num [iterateAmplitudeSq]
  · by_cases hi2 : i ≤ 2
    · have hi : i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl
      · norm_num [iterateAmplitudeSq]
        nlinarith only [hη, hsmall]
      · norm_num [iterateAmplitudeSq]
        have hh := pow_le_pow_left₀ hη hsmall 2
        norm_num at hh
        exact hh
    · simp only [iterateAmplitudeSq, hi0, hi2, ite_false]
      calc
        η ^ i ≤ (1 / 4 : ℝ) ^ i := pow_le_pow_left₀ hη hsmall i
        _ = ((1 / 2 : ℝ) ^ i) ^ 2 := by rw [← pow_mul, mul_comm i 2, pow_mul]; norm_num

/-- The finite weighted sum supplies precisely the printed 2^(2N) constant. -/
theorem iterate_amplitude_four_sum {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (N : ℕ) : ∑ i ∈ Finset.range (N + 1), iterateAmplitude η i * (4 : ℝ) ^ i ≤ 4 ^ N := by
  have hg : ∑ i ∈ Finset.range (N + 1), (2 : ℝ) ^ i = 2 ^ (N + 1) - 1 := by
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have hb : 2 ^ (N + 1) - (1 : ℝ) ≤ 4 ^ N := by
    by_cases hN : N = 0
    · subst N; norm_num
    · have hp : (2 : ℝ) ^ (N + 1) ≤ 2 ^ (2 * N) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have he : (2 : ℝ) ^ (2 * N) = 4 ^ N := by rw [pow_mul]; norm_num
      rw [he] at hp
      linarith only [hp]
  calc
    _ ≤ ∑ i ∈ Finset.range (N + 1), (2 : ℝ) ^ i := by
      apply Finset.sum_le_sum
      intro i _hi
      have h := mul_le_mul_of_nonneg_right (iterate_amplitude_le_half_pow hη hsmall i)
        (by positivity : 0 ≤ (4 : ℝ) ^ i)
      have he : (1 / 2 : ℝ) ^ i * 4 ^ i = 2 ^ i := by rw [← mul_pow]; norm_num
      exact h.trans_eq he
    _ = _ := hg
    _ ≤ _ := hb

/-- A factorial shift costs a binomial power and the finite terminal factorial. -/
theorem iterate_factorial_shift_bound (n N : ℕ) {i : ℕ} (hi : i ≤ N) :
    ((n + 2 * i).factorial : ℝ) ≤
      (n.factorial : ℝ) * ((2 * N).factorial : ℝ) * (2 : ℝ) ^ n * (4 : ℝ) ^ i := by
  have hchoose : ((n + 2 * i).choose (2 * i) : ℝ) ≤ (2 : ℝ) ^ (n + 2 * i) :=
    by exact_mod_cast Nat.choose_le_two_pow (n + 2 * i) (2 * i)
  have hfact : ((2 * i).factorial : ℝ) ≤ ((2 * N).factorial : ℝ) :=
    by exact_mod_cast Nat.factorial_le (by omega : 2 * i ≤ 2 * N)
  have he : ((n + 2 * i).factorial : ℝ) =
      ((n + 2 * i).choose (2 * i) : ℝ) * (n.factorial : ℝ) * ((2 * i).factorial : ℝ) :=
    by exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n (2 * i)).symm
  rw [he]
  have h1 := mul_le_mul_of_nonneg_right hchoose
    (by positivity : 0 ≤ (n.factorial : ℝ) * ((2 * i).factorial : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hfact
    (by positivity : 0 ≤ (2 : ℝ) ^ (n + 2 * i) * (n.factorial : ℝ))
  have hp : (2 : ℝ) ^ (n + 2 * i) = 2 ^ n * 4 ^ i := by
    rw [pow_add, pow_mul]; norm_num
  calc
    _ ≤ 2 ^ (n + 2 * i) * (n.factorial : ℝ) * ((2 * i).factorial : ℝ) := by
      convert h1 using 1 <;> ring
    _ ≤ 2 ^ (n + 2 * i) * (n.factorial : ℝ) * ((2 * N).factorial : ℝ) := h2
    _ = _ := by rw [hp]; ring

/-- Analytic finite-sum bound for the printed increment weights. -/
theorem iterate_finite_analytic_sum {η L : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hL : 0 ≤ L) (n N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), iterateAmplitude η i *
      ((n + 2 * i).factorial : ℝ) * L ^ n ≤
      (4 : ℝ) ^ N * ((2 * N).factorial : ℝ) * (n.factorial : ℝ) * (2 * L) ^ n := by
  have hsum := iterate_amplitude_four_sum hη hsmall N
  calc
    _ ≤ ∑ i ∈ Finset.range (N + 1),
        ((2 * N).factorial : ℝ) * (n.factorial : ℝ) * (2 * L) ^ n *
          (iterateAmplitude η i * (4 : ℝ) ^ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hA : 0 ≤ iterateAmplitude η i := by unfold iterateAmplitude; split_ifs <;> positivity
      have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have ht := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (iterate_factorial_shift_bound n N hiN)
          (pow_nonneg hL n)) hA
      simp only [mul_pow]
      convert ht using 1 <;> ring
    _ = ((2 * N).factorial : ℝ) * (n.factorial : ℝ) * (2 * L) ^ n *
        ∑ i ∈ Finset.range (N + 1), iterateAmplitude η i * (4 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ ((2 * N).factorial : ℝ) * (n.factorial : ℝ) * (2 * L) ^ n * (4 : ℝ) ^ N :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Every positive correction amplitude is at most the small parameter. -/
theorem iterate_amplitude_le_parameter {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {i : ℕ} (hi : 1 ≤ i) : iterateAmplitude η i ≤ η := by
  have hn : 0 ≤ iterateAmplitude η i := by unfold iterateAmplitude; split_ifs <;> positivity
  apply (sq_le_sq₀ hn hη).mp
  rw [iterateAmplitude_square hη]
  by_cases hi2 : i ≤ 2
  · simp [iterateAmplitudeSq, show i ≠ 0 by omega, hi2]
  · simp only [iterateAmplitudeSq, show i ≠ 0 by omega, hi2, ite_false]
    exact pow_le_pow_of_le_one hη hη1 (by omega : 2 ≤ i)

/-- A gradient-only finite T sum is one base amplitude plus small corrections. -/
theorem iterate_finite_gradient_amplitude_sum {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), iterateAmplitude η i * ((2 * i).factorial : ℝ) ≤
      1 + η * (N : ℝ) * ((2 * N).factorial : ℝ) := by
  rw [Finset.sum_range_succ']
  have hsum : (∑ i ∈ Finset.range N, iterateAmplitude η (i + 1) * ((2 * (i + 1)).factorial : ℝ)) ≤
      η * (N : ℝ) * ((2 * N).factorial : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N, η * ((2 * N).factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hA := iterate_amplitude_le_parameter hη hη1 (by omega : 1 ≤ i + 1)
        have hf : ((2 * (i + 1)).factorial : ℝ) ≤ ((2 * N).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (by have ht := Finset.mem_range.mp hi; omega)
        exact mul_le_mul hA hf (by positivity) hη
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  simpa [iterateAmplitude, add_comm] using add_le_add_right hsum (1 : ℝ)

end AVenhance.Infra.Section4

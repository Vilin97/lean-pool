/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds

/-! Geometric summability of the construction scales (the use of
`e.minsep` in the §2 limit argument). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Construction

theorem LimitSeries.epsilon_pos_for_ingredients {β : ℝ} (I : Ingredients β) (m : ℕ) :
    0 < epsilon β I.Λ m :=
  Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le

/-- `e.minsep`: one step of the scale sequence contracts by `Λ`. -/
theorem epsilon_step_le {β : ℝ} (I : Ingredients β) (m : ℕ) :
    epsilon β I.Λ (m + 1) ≤ epsilon β I.Λ m / (I.Λ : ℝ) := by
  have hΛ : 0 < (I.Λ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2 ^ 7) I.two_pow_seven_le)
  apply (le_div_iff₀ hΛ).2
  simpa [mul_comm] using
    (Infra.Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m))

/-- The scale powers contract geometrically for every positive real exponent. -/
theorem epsilon_rpow_step_le {β s : ℝ} (I : Ingredients β) (hs : 0 < s) (m : ℕ) :
    epsilon β I.Λ (m + 1) ^ s ≤
      epsilon β I.Λ m ^ s * (I.Λ : ℝ) ^ (-s) := by
  have he₀ := LimitSeries.epsilon_pos_for_ingredients I m
  have he₁ := LimitSeries.epsilon_pos_for_ingredients I (m + 1)
  have hΛ : 0 < (I.Λ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2 ^ 7) I.two_pow_seven_le)
  calc
    epsilon β I.Λ (m + 1) ^ s ≤
        (epsilon β I.Λ m / (I.Λ : ℝ)) ^ s :=
      Real.rpow_le_rpow he₁.le (epsilon_step_le I m) hs.le
    _ = epsilon β I.Λ m ^ s * (I.Λ : ℝ) ^ (-s) := by
      rw [Real.div_rpow he₀.le hΛ.le, Real.rpow_neg hΛ.le]
      ring

/-- Repeated `e.minsep`, in a form ready for comparison with a geometric
series. -/
theorem epsilon_rpow_le_geom {β s : ℝ} (I : Ingredients β) (hs : 0 < s)
    (m k : ℕ) :
    epsilon β I.Λ (m + k) ^ s ≤
      epsilon β I.Λ m ^ s * ((I.Λ : ℝ) ^ (-s)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := epsilon_rpow_step_le I hs (m + k)
      have hq : 0 ≤ (I.Λ : ℝ) ^ (-s) := by positivity
      calc
        epsilon β I.Λ (m + (k + 1)) ^ s =
            epsilon β I.Λ ((m + k) + 1) ^ s := by congr 1
        _ ≤ epsilon β I.Λ (m + k) ^ s * (I.Λ : ℝ) ^ (-s) := hstep
        _ ≤ (epsilon β I.Λ m ^ s * ((I.Λ : ℝ) ^ (-s)) ^ k) *
              (I.Λ : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_right ih hq
        _ = epsilon β I.Λ m ^ s * ((I.Λ : ℝ) ^ (-s)) ^ (k + 1) := by
            rw [pow_succ]
            ring

theorem LimitSeries.sum_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, q ^ k) ≤ 1 / (1 - q) := by
  have hden : 0 < 1 - q := by linarith
  have hsum : (1 - q) * (∑ k ∈ Finset.range n, q ^ k) = 1 - q ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        calc
          (1 - q) * (∑ k ∈ Finset.range n, q ^ k + q ^ n) =
              (1 - q) * (∑ k ∈ Finset.range n, q ^ k) + (1 - q) * q ^ n := by ring
          _ = (1 - q ^ n) + (1 - q) * q ^ n := by rw [ih]
          _ = 1 - q ^ (n + 1) := by rw [pow_succ]; ring
  have hmul : (∑ k ∈ Finset.range n, q ^ k) * (1 - q) ≤ 1 := by
    rw [mul_comm, hsum]
    nlinarith [pow_nonneg hq0 n]
  exact (le_div_iff₀ hden).2 hmul

/-- The source's `e.minsep` series estimate, with the tail based at an
arbitrary scale.  In particular, taking `m = 1` gives
`Σ_{j=1}^N ε_j^s ≤ ε_1^s/(1-Λ^{-s})`. -/
theorem epsilon_rpow_sum_bound {β s : ℝ} (I : Ingredients β) (hs : 0 < s)
    (m n : ℕ) :
    (∑ k ∈ Finset.range n, epsilon β I.Λ (m + k) ^ s) ≤
      epsilon β I.Λ m ^ s / (1 - (I.Λ : ℝ) ^ (-s)) := by
  have hΛ : 1 < (I.Λ : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2 ^ 7) I.two_pow_seven_le
  have hpow : 1 < (I.Λ : ℝ) ^ s := Real.one_lt_rpow hΛ hs
  have hq0 : 0 ≤ (I.Λ : ℝ) ^ (-s) := by positivity
  have hq1 : (I.Λ : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by positivity : 0 ≤ (I.Λ : ℝ))]
    rw [inv_lt_one_iff₀]
    exact Or.inr hpow
  have hepsm := LimitSeries.epsilon_pos_for_ingredients I m
  calc
    (∑ k ∈ Finset.range n, epsilon β I.Λ (m + k) ^ s) ≤
        ∑ k ∈ Finset.range n,
          epsilon β I.Λ m ^ s * ((I.Λ : ℝ) ^ (-s)) ^ k :=
      Finset.sum_le_sum fun k hk => epsilon_rpow_le_geom I hs m k
    _ = epsilon β I.Λ m ^ s *
        (∑ k ∈ Finset.range n, ((I.Λ : ℝ) ^ (-s)) ^ k) := by
      rw [Finset.mul_sum]
    _ ≤ epsilon β I.Λ m ^ s / (1 - (I.Λ : ℝ) ^ (-s)) := by
      simpa [div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left (LimitSeries.sum_geom_le hq0 hq1 n)
          (Real.rpow_nonneg hepsm.le _))

theorem inverse_lambda_rpow_lt_one {β s : ℝ} (I : Ingredients β)
    (hs : 0 < s) : (I.Λ : ℝ) ^ (-s) < 1 := by
  have hΛ : 1 < (I.Λ : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2 ^ 7) I.two_pow_seven_le
  have hpow : 1 < (I.Λ : ℝ) ^ s := Real.one_lt_rpow hΛ hs
  rw [Real.rpow_neg (by positivity : 0 ≤ (I.Λ : ℝ))]
  rw [inv_lt_one_iff₀]
  exact Or.inr hpow

/-- Positive powers of the scales decrease with the index. -/
theorem epsilon_rpow_antitone {β s : ℝ} (I : Ingredients β) (hs : 0 < s)
    {m n : ℕ} (hmn : m ≤ n) :
    epsilon β I.Λ n ^ s ≤ epsilon β I.Λ m ^ s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hq0 : 0 ≤ (I.Λ : ℝ) ^ (-s) := by positivity
  have hq1 : (I.Λ : ℝ) ^ (-s) ≤ 1 := (inverse_lambda_rpow_lt_one I hs).le
  have hpow : ((I.Λ : ℝ) ^ (-s)) ^ k ≤ 1 := pow_le_one₀ hq0 hq1
  calc
    epsilon β I.Λ (m + k) ^ s ≤
        epsilon β I.Λ m ^ s * ((I.Λ : ℝ) ^ (-s)) ^ k :=
      epsilon_rpow_le_geom I hs m k
    _ ≤ epsilon β I.Λ m ^ s * 1 :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg
        (LimitSeries.epsilon_pos_for_ingredients I m).le _)
    _ = epsilon β I.Λ m ^ s := mul_one _

/-- The scales and all their positive real powers tend to zero. -/
theorem epsilon_rpow_tendsto_zero {β s : ℝ} (I : Ingredients β) (hs : 0 < s) :
    Tendsto (fun m => epsilon β I.Λ m ^ s) atTop (𝓝 0) := by
  have hq0 : 0 ≤ (I.Λ : ℝ) ^ (-s) := by positivity
  have hq1 := inverse_lambda_rpow_lt_one I hs
  have hgeom : Tendsto (fun n : ℕ => ((I.Λ : ℝ) ^ (-s)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hbound : ∀ n, epsilon β I.Λ n ^ s ≤
      ((I.Λ : ℝ) ^ (-s)) ^ n := by
    intro n
    have h := epsilon_rpow_le_geom I hs 0 n
    simpa [epsilon] using h
  refine squeeze_zero (fun n => Real.rpow_nonneg
      (LimitSeries.epsilon_pos_for_ingredients I n).le _) hbound hgeom

end AVenhance.Infra.Construction

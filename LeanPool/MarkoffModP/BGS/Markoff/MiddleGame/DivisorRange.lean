/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierStep

namespace BGS.Markoff

open Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt_rpow
    {C a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have hExponent : 0 < b - a := sub_pos.mpr hab
  have hEventuallyConstant :
      ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ (b - a) :=
    ((tendsto_rpow_atTop hExponent).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop C)
  filter_upwards [hEventuallyConstant, eventually_gt_atTop 0] with n hC hn
  have hnRealPos : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    C * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hnRealPos _)
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnRealPos]
      congr 1
      ring

theorem exists_threshold_middleGameDivisorCount_le_two_mul_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) ≤
        2 * ((p + 1 : ℕ) : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := BGS.NumberTheory.exists_threshold_card_divisors_le_rpow hε
  refine ⟨N + 1, ?_⟩
  intro p hp
  have hpMinus : N ≤ p - 1 := by omega
  have hpPlus : N ≤ p + 1 := by omega
  have hMinus := hN (p - 1) hpMinus
  have hPlus := hN (p + 1) hpPlus
  have hBase : (((p - 1 : ℕ) : ℝ)) ≤ (((p + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show p - 1 ≤ p + 1 by omega)
  have hPower : (((p - 1 : ℕ) : ℝ)) ^ ε ≤ (((p + 1 : ℕ) : ℝ)) ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hBase hε.le
  have hPlus' : ((p + 1).divisors.card : ℝ) ≤ ((p : ℝ) + 1) ^ ε := by
    simpa only [Nat.cast_add, Nat.cast_one] using hPlus
  have hPower' : (((p - 1 : ℕ) : ℝ)) ^ ε ≤ ((p : ℝ) + 1) ^ ε := by
    simpa only [Nat.cast_add, Nat.cast_one] using hPower
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    ((p - 1).divisors.card : ℝ) + ((p + 1).divisors.card : ℝ) ≤
        (((p - 1 : ℕ) : ℝ)) ^ ε + ((p : ℝ) + 1) ^ ε :=
      add_le_add hMinus hPlus'
    _ ≤ ((p : ℝ) + 1) ^ ε + ((p : ℝ) + 1) ^ ε :=
      add_le_add hPower' (le_refl _)
    _ = 2 * ((p : ℝ) + 1) ^ ε := by ring

theorem eventually_corvajaZannierDivisorCount_le_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) : ℝ) ≤
        ((2 * corvajaZannierCorollaryTwoSafeCoefficient : ℕ) * (2 : ℝ) ^ ε) *
          (p : ℝ) ^ ε := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_middleGameDivisorCount_le_two_mul_rpow hε
  filter_upwards [eventually_ge_atTop threshold, eventually_ge_atTop 1] with p hp hpOne
  have hdivisor := hthreshold p hp
  have hpCast : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hbase : (((p + 1 : ℕ) : ℝ)) ≤ 2 * (p : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact_mod_cast (show p + 1 ≤ 2 * p by omega)
  have hpower : (((p + 1 : ℕ) : ℝ)) ^ ε ≤ (2 * (p : ℝ)) ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hbase hε.le
  calc
    (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) : ℝ) =
        corvajaZannierCorollaryTwoSafeCoefficient *
          (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) := by
      norm_num
    _ ≤ corvajaZannierCorollaryTwoSafeCoefficient *
        (2 * (((p + 1 : ℕ) : ℝ)) ^ ε) :=
      mul_le_mul_of_nonneg_left hdivisor (by
        simp [corvajaZannierCorollaryTwoSafeCoefficient])
    _ ≤ corvajaZannierCorollaryTwoSafeCoefficient *
        (2 * (2 * (p : ℝ)) ^ ε) := by gcongr
    _ = ((2 * corvajaZannierCorollaryTwoSafeCoefficient : ℕ) * (2 : ℝ) ^ ε) *
        (p : ℝ) ^ ε := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hpCast]
      norm_num [corvajaZannierCorollaryTwoSafeCoefficient]
      ring

/-- Throughout the genuine middle range, the two finite inequalities needed by the
Corvaja--Zannier escape theorem eventually hold uniformly in the current order. -/
theorem eventually_middleGame_corvajaZannier_sizeBounds
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop, ∀ currentOrder : ℕ,
      (p : ℝ) ^ δ < currentOrder →
      (currentOrder : ℝ) < (p : ℝ) ^ (1 - δ) →
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < currentOrder ∧
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p := by
  let ε : ℝ := δ / 6
  let C : ℝ :=
    (2 * corvajaZannierCorollaryTwoSafeCoefficient : ℕ) * (2 : ℝ) ^ ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hThreeε : 3 * ε < δ := by dsimp [ε]; linarith
  have hLinearExponent : 1 - δ + ε < 1 := by dsimp [ε]; linarith
  have hDivisor := eventually_corvajaZannierDivisorCount_le_rpow hε
  have hCubeDominance :
      ∀ᶠ p : ℕ in atTop, C ^ 3 * (p : ℝ) ^ (3 * ε) < (p : ℝ) ^ δ :=
    eventually_const_mul_rpow_lt_rpow hThreeε
  have hLinearDominance :
      ∀ᶠ p : ℕ in atTop, C * (p : ℝ) ^ (1 - δ + ε) < (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow hLinearExponent
  filter_upwards [hDivisor, hCubeDominance, hLinearDominance,
    eventually_ge_atTop 1] with p hDivisor hCubeDominance hLinearDominance hpOne
  intro currentOrder hLower hUpper
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpRealNonneg : (0 : ℝ) ≤ p := hpRealPos.le
  have hCPos : 0 < C := by
    dsimp [C]
    simp only [corvajaZannierCorollaryTwoSafeCoefficient]
    positivity
  have hCurrentNonneg : (0 : ℝ) ≤ currentOrder := Nat.cast_nonneg currentOrder
  have hCoeffNonneg :
      (0 : ℝ) ≤ corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) := by
    simp only [corvajaZannierCorollaryTwoSafeCoefficient]
    positivity
  have hPowerIdentity :
      (C * (p : ℝ) ^ ε) ^ 3 = C ^ 3 * (p : ℝ) ^ (3 * ε) := by
    rw [mul_pow]
    rw [← Real.rpow_mul_natCast hpRealNonneg ε 3]
    congr 2
    ring
  have hCubeReal :
      (((corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 : ℕ) : ℝ) <
        (currentOrder : ℝ) := by
    calc
      (((corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 : ℕ) : ℝ) =
          (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card + (p + 1).divisors.card) : ℝ) ^ 3 := by
        norm_num
      _ ≤ (C * (p : ℝ) ^ ε) ^ 3 :=
        pow_le_pow_left₀ hCoeffNonneg hDivisor 3
      _ = C ^ 3 * (p : ℝ) ^ (3 * ε) := hPowerIdentity
      _ < (p : ℝ) ^ δ := hCubeDominance
      _ < (currentOrder : ℝ) := hLower
  have hLinearIdentity :
      (C * (p : ℝ) ^ ε) * (p : ℝ) ^ (1 - δ) =
        C * (p : ℝ) ^ (1 - δ + ε) := by
    rw [mul_assoc, ← Real.rpow_add hpRealPos]
    congr 2
    ring
  have hLinearReal :
      (((corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder : ℕ) : ℝ)) <
        (p : ℝ) := by
    calc
      (((corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder : ℕ) : ℝ)) =
          (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card + (p + 1).divisors.card) : ℝ) *
            (currentOrder : ℝ) := by norm_num
      _ ≤ (C * (p : ℝ) ^ ε) * (currentOrder : ℝ) :=
        mul_le_mul_of_nonneg_right hDivisor hCurrentNonneg
      _ < (C * (p : ℝ) ^ ε) * (p : ℝ) ^ (1 - δ) :=
        mul_lt_mul_of_pos_left hUpper (mul_pos hCPos (Real.rpow_pos_of_pos hpRealPos _))
      _ = C * (p : ℝ) ^ (1 - δ + ε) := hLinearIdentity
      _ < (p : ℝ) ^ (1 : ℝ) := hLinearDominance
      _ = (p : ℝ) := by simp
  constructor
  · exact_mod_cast hCubeReal
  · exact_mod_cast hLinearReal

end BGS.Markoff

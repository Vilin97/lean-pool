/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.ExplicitNumericCertificates
import LeanPool.MarkoffModP.BGS.NumberTheory.PreliminaryDivisorBound

/-!
# Elementary numerical certificates for the paper's preliminary route

The published preliminary argument uses Nicolas' explicit divisor bound to
obtain the threshold `10^532`.  Here we formalize the same all-divisors
Corvaja--Zannier route using a completely elementary tenth-moment estimate.
The resulting cutoff is somewhat larger, but every numerical input is checked
inside Lean.
-/

namespace BGS.Markoff

/-- The simultaneous tenth-moment constant for the divisor counts of `p - 1`
and `p + 1`. -/
def preliminaryDivisorMomentConstant : ℕ := 2 ^ 457

theorem preliminaryDivisorMomentConstant_eq :
    preliminaryDivisorMomentConstant = 2 ^ 457 := rfl

theorem preliminaryDivisorMomentConstant_pos :
    0 < preliminaryDivisorMomentConstant := by
  rw [preliminaryDivisorMomentConstant_eq]
  positivity

/-- Sealed data for the elementary preliminary-route cutoff. -/
@[irreducible] def preliminaryStrongApproximationCutoffData :
    {n : ℕ // n = 2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1} :=
  ⟨2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1, rfl⟩

/-- A fully elementary replacement for the paper's `10^532` threshold. -/
def preliminaryStrongApproximationCutoff : ℕ :=
  preliminaryStrongApproximationCutoffData.1

theorem preliminaryStrongApproximationCutoff_eq :
    preliminaryStrongApproximationCutoff =
      2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1 :=
  preliminaryStrongApproximationCutoffData.2

theorem preliminaryCutoff_gt_one :
    1 < preliminaryStrongApproximationCutoff := by
  rw [preliminaryStrongApproximationCutoff_eq]
  have h : 0 < 2 ^ 1833 * (48 ^ 3 + 1) ^ 10 :=
    Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  omega

theorem preliminaryCutoff_constant_lt
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p) :
    2 ^ 1833 * (48 ^ 3 + 1) ^ 10 < p := by
  rw [preliminaryStrongApproximationCutoff_eq] at hp
  omega

/-- The two divisor counts needed by the preliminary route satisfy one
simultaneous tenth-moment estimate. -/
theorem preliminary_divisor_sum_pow_ten_le
    {p : ℕ} (hp : 2 ≤ p) :
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 10 ≤
      preliminaryDivisorMomentConstant * p := by
  have hminusNe : p - 1 ≠ 0 := by omega
  have hplusNe : p + 1 ≠ 0 := by omega
  have hminus :=
    BGS.NumberTheory.card_divisors_pow_ten_le_preliminary_constant_mul
      (p - 1) hminusNe
  have hplus :=
    BGS.NumberTheory.card_divisors_pow_ten_le_preliminary_constant_mul
      (p + 1) hplusNe
  calc
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 10 ≤
        2 ^ (10 - 1) *
          ((p - 1).divisors.card ^ 10 + (p + 1).divisors.card ^ 10) :=
      add_pow_le (Nat.zero_le _) (Nat.zero_le _) 10
    _ ≤ 2 ^ 9 *
        (2 ^ 447 * (p - 1) + 2 ^ 447 * (p + 1)) := by
      norm_num
      gcongr
    _ = preliminaryDivisorMomentConstant * p := by
      rw [preliminaryDivisorMomentConstant_eq]
      have hsum : p - 1 + (p + 1) = 2 * p := by omega
      have hpow : 2 ^ 9 * 2 ^ 447 * 2 = 2 ^ 457 := by
        have h447 : 2 ^ 447 * 2 = 2 ^ 448 := by
          simpa using (pow_succ 2 447).symm
        calc
          2 ^ 9 * 2 ^ 447 * 2 = 2 ^ 9 * (2 ^ 447 * 2) := by ring
          _ = 2 ^ 9 * 2 ^ 448 := by rw [h447]
          _ = 2 ^ (9 + 448) := (pow_add 2 9 448).symm
          _ = 2 ^ 457 := by norm_num
      calc
        2 ^ 9 * (2 ^ 447 * (p - 1) + 2 ^ 447 * (p + 1)) =
            2 ^ 9 * 2 ^ 447 * (p - 1 + (p + 1)) := by ring
        _ = 2 ^ 9 * 2 ^ 447 * (2 * p) := by rw [hsum]
        _ = (2 ^ 9 * 2 ^ 447 * 2) * p := by ring
        _ = 2 ^ 457 * p := by rw [hpow]

private theorem preliminary_moment_pow_eight_le_cutoff_sq :
    preliminaryDivisorMomentConstant ^ 8 ≤
      (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 2 := by
  rw [preliminaryDivisorMomentConstant_eq]
  calc
    (2 ^ 457) ^ 8 = 2 ^ 3656 := by
      rw [show (3656 : ℕ) = 457 * 8 by norm_num, pow_mul]
    _ ≤ 2 ^ 3666 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    _ = (2 ^ 1833) ^ 2 := by
      rw [show (3666 : ℕ) = 1833 * 2 by norm_num, pow_mul]
    _ ≤ (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 2 := by
      gcongr
      exact Nat.le_mul_of_pos_right _ (by positivity)

private theorem preliminary_middle_coefficient_le_cutoff_pow_four :
    48 ^ 60 * preliminaryDivisorMomentConstant ^ 6 ≤
      (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 4 := by
  rw [preliminaryDivisorMomentConstant_eq]
  have htwo : (2 ^ 457) ^ 6 ≤ 2 ^ 7332 := by
    calc
      (2 ^ 457) ^ 6 = 2 ^ 2742 := by
        rw [show (2742 : ℕ) = 457 * 6 by norm_num, pow_mul]
      _ ≤ 2 ^ 7332 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hbase : 48 ^ 60 ≤ (48 ^ 3 + 1) ^ 40 := by
    calc
      48 ^ 60 = (48 ^ 3) ^ 20 := by
        rw [show (60 : ℕ) = 3 * 20 by norm_num, pow_mul]
      _ ≤ (48 ^ 3 + 1) ^ 20 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (48 ^ 3 + 1) ^ 40 :=
        Nat.pow_le_pow_right (by positivity) (by norm_num)
  calc
    48 ^ 60 * (2 ^ 457) ^ 6 = (2 ^ 457) ^ 6 * 48 ^ 60 := by ring
    _ ≤ 2 ^ 7332 * (48 ^ 3 + 1) ^ 40 := Nat.mul_le_mul htwo hbase
    _ = (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 4 := by
      norm_num [mul_pow, ← pow_mul]

private theorem preliminary_endgame_coefficient_le_cutoff_pow_four :
    68 ^ 30 * preliminaryDivisorMomentConstant ^ 6 ≤
      (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 4 := by
  rw [preliminaryDivisorMomentConstant_eq]
  have htwo : (2 ^ 457) ^ 6 ≤ 2 ^ 7332 := by
    calc
      (2 ^ 457) ^ 6 = 2 ^ 2742 := by
        rw [show (2742 : ℕ) = 457 * 6 by norm_num, pow_mul]
      _ ≤ 2 ^ 7332 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hbase : 68 ^ 30 ≤ (48 ^ 3 + 1) ^ 40 := by
    calc
      68 ^ 30 ≤ (48 ^ 3 + 1) ^ 30 :=
        Nat.pow_le_pow_left (by norm_num) _
      _ ≤ (48 ^ 3 + 1) ^ 40 :=
        Nat.pow_le_pow_right (by positivity) (by norm_num)
  calc
    68 ^ 30 * (2 ^ 457) ^ 6 = (2 ^ 457) ^ 6 * 68 ^ 30 := by ring
    _ ≤ 2 ^ 7332 * (48 ^ 3 + 1) ^ 40 := Nat.mul_le_mul htwo hbase
    _ = (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 4 := by
      norm_num [mul_pow, ← pow_mul]

private theorem preliminary_fixed_pow_eight_le_cutoff :
    100522 ^ 8 ≤ 2 ^ 1833 * (48 ^ 3 + 1) ^ 10 := by
  decide +kernel

private theorem preliminary_lowOrder_coefficient_eq_cutoff_sq :
    2 ^ 10 * (48 ^ 3 + 1) ^ 20 * preliminaryDivisorMomentConstant ^ 8 =
      (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 2 := by
  rw [preliminaryDivisorMomentConstant_eq]
  have htwo457 : (2 ^ 457) ^ 8 = 2 ^ 3656 := by
    rw [show (3656 : ℕ) = 457 * 8 by norm_num, pow_mul]
  have htwo : 2 ^ 10 * (2 ^ 457) ^ 8 = 2 ^ 3666 := by
    rw [htwo457]
    exact (pow_add 2 10 3656).symm.trans (by norm_num)
  have htwo' : (2 ^ 1833) ^ 2 = 2 ^ 3666 := by
    rw [show (3666 : ℕ) = 1833 * 2 by norm_num, pow_mul]
  have hbase :
      (48 ^ 3 + 1) ^ 20 = ((48 ^ 3 + 1) ^ 10) ^ 2 := by
    rw [show (20 : ℕ) = 10 * 2 by norm_num, pow_mul]
  calc
    2 ^ 10 * (48 ^ 3 + 1) ^ 20 * (2 ^ 457) ^ 8 =
        (2 ^ 10 * (2 ^ 457) ^ 8) * (48 ^ 3 + 1) ^ 20 := by ring
    _ = 2 ^ 3666 * (48 ^ 3 + 1) ^ 20 := by rw [htwo]
    _ = (2 ^ 1833) ^ 2 * ((48 ^ 3 + 1) ^ 10) ^ 2 := by
      rw [htwo', hbase]
    _ = (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 2 := by rw [mul_pow]
/-- The simultaneous divisor count is smaller than the eighth root of `p`. -/
theorem preliminary_divisor_sum_lt_rpow_one_div_eight
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p) :
    (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 8 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let Q := 2 ^ 1833 * (48 ^ 3 + 1) ^ 10
  have hpTwo : 2 ≤ p := by
    have := preliminaryCutoff_gt_one.trans_le hp
    omega
  have hmoment : T ^ 10 ≤ preliminaryDivisorMomentConstant * p := by
    simpa [T] using preliminary_divisor_sum_pow_ten_le hpTwo
  have hQ : Q < p := by
    simpa [Q] using preliminaryCutoff_constant_lt hp
  have hpowNat : T ^ 80 < p ^ 10 := by
    calc
      T ^ 80 = (T ^ 10) ^ 8 := by
        rw [show (80 : ℕ) = 10 * 8 by norm_num, pow_mul]
      _ ≤ (preliminaryDivisorMomentConstant * p) ^ 8 := by gcongr
      _ = preliminaryDivisorMomentConstant ^ 8 * p ^ 8 := by rw [mul_pow]
      _ ≤ Q ^ 2 * p ^ 8 := by
        exact Nat.mul_le_mul_right _ <| by
          simpa [Q] using preliminary_moment_pow_eight_le_cutoff_sq
      _ < p ^ 2 * p ^ 8 := by gcongr
      _ = p ^ 10 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : (T : ℝ) ^ 80 < (p : ℝ) ^ 10 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 80 = (p : ℝ) ^ 10 := by
    calc
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 80 =
          (p : ℝ) ^ ((1 / 8 : ℝ) * 80) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 8 : ℝ) 80).symm
      _ = (p : ℝ) ^ 10 := by norm_num
  change (T : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 80 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- The coefficient-48 all-divisors term is smaller than the sixth root of
`p`, as required by the preliminary middle game. -/
theorem preliminary_corvajaZannier_divisor_term_lt_rpow_one_div_six
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p) :
    (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) : ℕ) <
      (p : ℝ) ^ (1 / 6 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let Q := 2 ^ 1833 * (48 ^ 3 + 1) ^ 10
  have hpTwo : 2 ≤ p := by
    have := preliminaryCutoff_gt_one.trans_le hp
    omega
  have hmoment : T ^ 10 ≤ preliminaryDivisorMomentConstant * p := by
    simpa [T] using preliminary_divisor_sum_pow_ten_le hpTwo
  have hQ : Q < p := by
    simpa [Q] using preliminaryCutoff_constant_lt hp
  have hpowNat : (48 * T) ^ 60 < p ^ 10 := by
    calc
      (48 * T) ^ 60 = 48 ^ 60 * (T ^ 10) ^ 6 := by ring
      _ ≤ 48 ^ 60 * (preliminaryDivisorMomentConstant * p) ^ 6 := by gcongr
      _ = (48 ^ 60 * preliminaryDivisorMomentConstant ^ 6) * p ^ 6 := by
        rw [mul_pow]
        ring
      _ ≤ Q ^ 4 * p ^ 6 := by
        exact Nat.mul_le_mul_right _ <| by
          simpa [Q] using preliminary_middle_coefficient_le_cutoff_pow_four
      _ < p ^ 4 * p ^ 6 := by gcongr
      _ = p ^ 10 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((48 * T : ℕ) : ℝ) ^ 60 < (p : ℝ) ^ 10 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 60 = (p : ℝ) ^ 10 := by
    calc
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 60 =
          (p : ℝ) ^ ((1 / 6 : ℝ) * 60) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 6 : ℝ) 60).symm
      _ = (p : ℝ) ^ 10 := by norm_num
  norm_num only [corvajaZannierCorollaryTwoSafeCoefficient]
  change ((48 * T : ℕ) : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 60 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- The weighted divisor square is smaller than the one-third power needed
by the primitive-trace endgame. -/
theorem preliminary_weighted_divisor_sum_sq_lt_rpow_one_div_three
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p) :
    ((68 * ((p - 1).divisors.card + (p + 1).divisors.card) ^ 2 : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 3 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let Q := 2 ^ 1833 * (48 ^ 3 + 1) ^ 10
  have hpTwo : 2 ≤ p := by
    have := preliminaryCutoff_gt_one.trans_le hp
    omega
  have hmoment : T ^ 10 ≤ preliminaryDivisorMomentConstant * p := by
    simpa [T] using preliminary_divisor_sum_pow_ten_le hpTwo
  have hQ : Q < p := by
    simpa [Q] using preliminaryCutoff_constant_lt hp
  have hpowNat : (68 * T ^ 2) ^ 30 < p ^ 10 := by
    calc
      (68 * T ^ 2) ^ 30 = 68 ^ 30 * (T ^ 10) ^ 6 := by ring
      _ ≤ 68 ^ 30 * (preliminaryDivisorMomentConstant * p) ^ 6 := by gcongr
      _ = (68 ^ 30 * preliminaryDivisorMomentConstant ^ 6) * p ^ 6 := by
        rw [mul_pow]
        ring
      _ ≤ Q ^ 4 * p ^ 6 := by
        exact Nat.mul_le_mul_right _ <| by
          simpa [Q] using preliminary_endgame_coefficient_le_cutoff_pow_four
      _ < p ^ 4 * p ^ 6 := by gcongr
      _ = p ^ 10 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((68 * T ^ 2 : ℕ) : ℝ) ^ 30 < (p : ℝ) ^ 10 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 30 = (p : ℝ) ^ 10 := by
    calc
      ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 30 =
          (p : ℝ) ^ ((1 / 3 : ℝ) * 30) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 3 : ℝ) 30).symm
      _ = (p : ℝ) ^ 10 := by norm_num
  change ((68 * T ^ 2 : ℕ) : ℝ) < (p : ℝ) ^ (1 / 3 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 30 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- Every fixed coefficient used in the cage is smaller than the eighth root
of `p`. -/
theorem preliminary_small_fixed_lt_rpow_one_div_eight
    {p fixed : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p)
    (hfixed : fixed ≤ 100522) :
    (fixed : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) := by
  have hpowNat : fixed ^ 8 < p := by
    calc
      fixed ^ 8 ≤ 100522 ^ 8 := Nat.pow_le_pow_left hfixed _
      _ ≤ 2 ^ 1833 * (48 ^ 3 + 1) ^ 10 :=
        preliminary_fixed_pow_eight_le_cutoff
      _ < p := preliminaryCutoff_constant_lt hp
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : (fixed : ℝ) ^ 8 < (p : ℝ) := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 8 = (p : ℝ) := by
    calc
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 8 =
          (p : ℝ) ^ ((1 / 8 : ℝ) * 8) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 8 : ℝ) 8).symm
      _ = (p : ℝ) := by norm_num
  apply lt_of_pow_lt_pow_left₀ 8 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

private theorem preliminary_prime_one_lt
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p) :
    (1 : ℝ) < p := by
  exact_mod_cast preliminaryCutoff_gt_one.trans_le hp

private theorem preliminary_rpow_lt_self_of_exponent_lt_one
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p)
    {a : ℝ} (ha : a < 1) :
    (p : ℝ) ^ a < p := by
  simpa only [Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt (preliminary_prime_one_lt hp) ha

/-- Assembly-facing preliminary middle-game certificate. -/
theorem preliminary_middleGame_corvajaZannier_linearBound
    {p currentOrder : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p)
    (hUpper : (currentOrder : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ)) :
    corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p := by
  let A : ℕ := corvajaZannierCorollaryTwoSafeCoefficient *
    ((p - 1).divisors.card + (p + 1).divisors.card)
  have hpRealPos : (0 : ℝ) < p :=
    (preliminary_prime_one_lt hp).trans' zero_lt_one
  have hA : (A : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ) := by
    simpa [A] using
      preliminary_corvajaZannier_divisor_term_lt_rpow_one_div_six hp
  have hLinearPower :
      (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (5 / 6 : ℝ) = (p : ℝ) := by
    rw [← Real.rpow_add hpRealPos]
    norm_num
  have hLinear : (A : ℝ) * currentOrder < p := by
    calc
      (A : ℝ) * currentOrder ≤
          (p : ℝ) ^ (1 / 6 : ℝ) * currentOrder :=
        mul_le_mul_of_nonneg_right hA.le (Nat.cast_nonneg currentOrder)
      _ < (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (5 / 6 : ℝ) :=
        mul_lt_mul_of_pos_left hUpper (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) := hLinearPower
  exact_mod_cast hLinear

/-- Preliminary primitive-trace inclusion--exclusion certificate. -/
theorem preliminary_endgamePrimitiveTrace_explicitInequality
    {p orbitExponent coefficient : ℕ}
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (horbit : (orbitExponent : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 6 : ℝ))
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpRealPos : (0 : ℝ) < p :=
    (preliminary_prime_one_lt hp).trans' zero_lt_one
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (show (p - 1).divisors.card ≤ T by
      dsimp [T]
      omega)
  have hweighted : (68 : ℝ) * (T : ℝ) ^ 2 <
      (p : ℝ) ^ (1 / 3 : ℝ) := by
    simpa [T] using
      preliminary_weighted_divisor_sum_sq_lt_rpow_one_div_three hp
  calc
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      (2 * (p : ℝ) ^ (1 / 6 : ℝ)) * (T : ℝ) ^ 2 *
        (34 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = (68 * (T : ℝ) ^ 2) *
        ((p : ℝ) ^ (1 / 6 : ℝ) * Real.sqrt (p : ℝ)) := by ring
    _ < (p : ℝ) ^ (1 / 3 : ℝ) *
        ((p : ℝ) ^ (1 / 6 : ℝ) * Real.sqrt (p : ℝ)) := by
      exact mul_lt_mul_of_pos_right hweighted <|
        mul_pos (Real.rpow_pos_of_pos hpRealPos _) (Real.sqrt_pos.2 hpRealPos)
    _ = (p : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpRealPos,
        ← Real.rpow_add hpRealPos]
      norm_num

theorem preliminary_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p - 1)
    (horder : (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply preliminary_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p :=
    Nat.zero_lt_one.trans (preliminaryCutoff_gt_one.trans_le hp)
  have horbit := orbitExponent_le_rpow_of_mul_order_eq_card_sub_one
    p orbitExponent orbitOrder (δ := (1 / 3 : ℝ)) hpNat hmul (by
      convert horder using 1 <;> norm_num)
  calc
    (orbitExponent : ℝ) ≤ (p : ℝ) ^ (1 / 6 : ℝ) := by
      convert horbit using 1 <;> norm_num
    _ ≤ 2 * (p : ℝ) ^ (1 / 6 : ℝ) := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) (1 / 6 : ℝ)]

theorem preliminary_endgamePrimitiveTrace_explicitInequality_of_card_add_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p + 1)
    (horder : (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply preliminary_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p :=
    Nat.zero_lt_one.trans (preliminaryCutoff_gt_one.trans_le hp)
  have horbit := orbitExponent_le_two_mul_rpow_of_mul_order_eq_card_add_one
    p orbitExponent orbitOrder (δ := (1 / 3 : ℝ)) hpNat hmul (by
      convert horder using 1 <;> norm_num)
  convert horbit using 1 <;> norm_num

theorem preliminary_four_lt_rpow_five_div_six
    {p : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p) :
    (4 : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
  have hfour : (4 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    preliminary_small_fixed_lt_rpow_one_div_eight hp (by norm_num)
  exact hfour.trans <|
    Real.rpow_lt_rpow_of_exponent_lt (preliminary_prime_one_lt hp) (by norm_num)

/-- Preliminary cage inequality with the existing point-count coefficient. -/
theorem preliminary_cageWitness_explicitInequality
    {p coefficient : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p)
    (hcoefficient : coefficient ≤ 100522) :
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealPos : (0 : ℝ) < p :=
    (preliminary_prime_one_lt hp).trans' zero_lt_one
  have hpRealNonneg : (0 : ℝ) ≤ p := hpRealPos.le
  have hsum := preliminary_divisor_sum_lt_rpow_one_div_eight hp
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤
      (p : ℝ) ^ (1 / 8 : ℝ) := by
    norm_num only [Nat.cast_add] at hsum
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum.le
  have hfixed : (100522 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    preliminary_small_fixed_lt_rpow_one_div_eight hp (by norm_num)
  have hsqrt : Real.sqrt (p : ℝ) = (p : ℝ) ^ (4 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hpower : ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 2 * Real.sqrt (p : ℝ) =
      (p : ℝ) ^ (6 / 8 : ℝ) := by
    rw [hsqrt, ← Real.rpow_mul_natCast hpRealNonneg,
      ← Real.rpow_add hpRealPos]
    congr 1
    norm_num
  calc
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 2 *
        (100522 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = 100522 * (p : ℝ) ^ (6 / 8 : ℝ) := by
      rw [← hpower]
      ring
    _ < (p : ℝ) ^ (1 / 8 : ℝ) * (p : ℝ) ^ (6 / 8 : ℝ) := by
      exact mul_lt_mul_of_pos_right hfixed (Real.rpow_pos_of_pos hpRealPos _)
    _ = (p : ℝ) ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hpRealPos]
      congr 1
      norm_num
    _ < p :=
      preliminary_rpow_lt_self_of_exponent_lt_one hp (by norm_num)

/-- The low-order Corvaja--Zannier cube contradiction, now driven by the
elementary tenth moment. -/
theorem preliminary_lowOrder_divisorSensitive_cube
    {p d : ℕ} (hp : preliminaryStrongApproximationCutoff ≤ p)
    (hdPos : 0 < d)
    (hpLe : p ≤ 2 * (2 + d *
      ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2) :
    (corvajaZannierCorollaryTwoSafeCoefficient *
      ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < d := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let B := 48 ^ 3 + 1
  let Q := 2 ^ 1833 * B ^ 10
  have hpTwo : 2 ≤ p := by
    have := preliminaryCutoff_gt_one.trans_le hp
    omega
  have hminusNonempty : (p - 1).divisors.Nonempty :=
    (Nat.nonempty_divisors).2 (by omega)
  have hplusNonempty : (p + 1).divisors.Nonempty :=
    (Nat.nonempty_divisors).2 (by omega)
  have hTtwo : 2 ≤ T := by
    have hm : 0 < (p - 1).divisors.card :=
      Finset.card_pos.mpr hminusNonempty
    have hp' : 0 < (p + 1).divisors.card :=
      Finset.card_pos.mpr hplusNonempty
    dsimp [T]
    omega
  have hTfour : 2 ≤ T ^ 4 := by
    calc
      2 ≤ T := hTtwo
      _ = T * 1 := by ring
      _ ≤ T * T ^ 3 := by
        gcongr
        exact Nat.one_le_pow 3 T (by omega)
      _ = T ^ 4 := by ring
  change (48 * T) ^ 3 < d
  by_contra hcube
  have hdUpper : d ≤ (48 * T) ^ 3 := by omega
  have hinner : 2 + d * T ≤ B * T ^ 4 := by
    calc
      2 + d * T ≤ T ^ 4 + d * T := Nat.add_le_add_right hTfour _
      _ ≤ T ^ 4 + (48 * T) ^ 3 * T := by gcongr
      _ = B * T ^ 4 := by
        dsimp [B]
        ring
  have hpLeCoarse : p ≤ 2 * B ^ 2 * T ^ 8 := by
    calc
      p ≤ 2 * (2 + d * T) ^ 2 := by simpa [T] using hpLe
      _ ≤ 2 * (B * T ^ 4) ^ 2 := by gcongr
      _ = 2 * B ^ 2 * T ^ 8 := by ring
  have hmoment : T ^ 10 ≤ preliminaryDivisorMomentConstant * p := by
    simpa [T] using preliminary_divisor_sum_pow_ten_le hpTwo
  have hpPowLe :
      p ^ 10 ≤ Q ^ 2 * p ^ 8 := by
    calc
      p ^ 10 ≤ (2 * B ^ 2 * T ^ 8) ^ 10 :=
        Nat.pow_le_pow_left hpLeCoarse _
      _ = 2 ^ 10 * B ^ 20 * (T ^ 10) ^ 8 := by ring
      _ ≤ 2 ^ 10 * B ^ 20 *
          (preliminaryDivisorMomentConstant * p) ^ 8 := by gcongr
      _ = (2 ^ 10 * B ^ 20 *
          preliminaryDivisorMomentConstant ^ 8) * p ^ 8 := by ring
      _ = Q ^ 2 * p ^ 8 := by
        change (2 ^ 10 * (48 ^ 3 + 1) ^ 20 *
          preliminaryDivisorMomentConstant ^ 8) * p ^ 8 =
          (2 ^ 1833 * (48 ^ 3 + 1) ^ 10) ^ 2 * p ^ 8
        exact congrArg (fun n : ℕ => n * p ^ 8)
          preliminary_lowOrder_coefficient_eq_cutoff_sq
  have hQ : Q < p := by
    simpa [Q, B] using preliminaryCutoff_constant_lt hp
  have hstrict : Q ^ 2 * p ^ 8 < p ^ 10 := by
    calc
      Q ^ 2 * p ^ 8 < p ^ 2 * p ^ 8 := by gcongr
      _ = p ^ 10 := by ring
  exact (not_lt_of_ge hpPowLe) hstrict

end BGS.Markoff

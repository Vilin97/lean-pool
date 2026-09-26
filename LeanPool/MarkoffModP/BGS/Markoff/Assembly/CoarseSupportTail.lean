/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.CoarseLinearTail
public import LeanPool.MarkoffModP.BGS.Markoff.ExplicitEndgame

/-!
# Coarse support tails below the paper scale

The single clean threshold `2^756 < p`, together with the simultaneous
tenth-moment divisor estimate, discharges the non-cubic middle-game,
primitive-endgame, cage, and split-sign support inequalities.
-/

@[expose] public section


namespace BGS.Markoff

open BGS.NumberTheory

theorem twentyFour_support_margin :
    24 ^ 15 * 2 ^ 687 < 2 ^ 756 := by
  have hbase : 24 ^ 5 < 2 ^ 23 := by norm_num
  calc
    24 ^ 15 * 2 ^ 687 = (24 ^ 5) ^ 3 * 2 ^ 687 := by ring
    _ < (2 ^ 23) ^ 3 * 2 ^ 687 :=
      Nat.mul_lt_mul_of_pos_right
        (pow_lt_pow_left₀ hbase (Nat.zero_le _) (by norm_num))
        (pow_pos (by norm_num) 687)
    _ = 2 ^ 756 := by
      rw [← pow_mul, ← pow_add]

theorem sixtyEight_support_margin :
    68 ^ 15 * 2 ^ 1374 < 2 ^ 1512 := by
  have hbase : (68 : ℕ) < 2 ^ 7 := by norm_num
  have hproduct : (68 : ℕ) ^ 15 * 2 ^ 1374 < (2 ^ 7) ^ 15 * 2 ^ 1374 := by
    exact Nat.mul_lt_mul_of_pos_right
      (pow_lt_pow_left₀ hbase (Nat.zero_le _) (by norm_num))
      (pow_pos (by norm_num) 1374)
  have hpower : ((2 : ℕ) ^ 7) ^ 15 * 2 ^ 1374 = 2 ^ 1479 := by
    rw [← pow_mul, ← pow_add]
  have hmargin : (2 : ℕ) ^ 1479 < 2 ^ 1512 :=
    pow_lt_pow_right₀ (by norm_num) (by norm_num)
  exact lt_trans (lt_of_lt_of_eq hproduct hpower) hmargin

theorem cageCoefficient_support_margin :
    100522 ^ 10 * 2 ^ 916 < 2 ^ 2268 := by
  have hbase : (100522 : ℕ) < 2 ^ 17 := by norm_num
  have hproduct : (100522 : ℕ) ^ 10 * 2 ^ 916 < (2 ^ 17) ^ 10 * 2 ^ 916 := by
    exact Nat.mul_lt_mul_of_pos_right
      (pow_lt_pow_left₀ hbase (Nat.zero_le _) (by norm_num))
      (pow_pos (by norm_num) 916)
  have hpower : ((2 : ℕ) ^ 17) ^ 10 * 2 ^ 916 = 2 ^ 1086 := by
    rw [← pow_mul, ← pow_add]
  have hmargin : (2 : ℕ) ^ 1086 < 2 ^ 2268 :=
    pow_lt_pow_right₀ (by norm_num) (by norm_num)
  exact lt_trans (lt_of_lt_of_eq hproduct hpower) hmargin

theorem seven_le_of_twoPow756_lt
    {p : ℕ} (hp : 2 ^ 756 < p) :
    7 ≤ p := by
  have hseven : 7 < 2 ^ 756 := by
    calc
      7 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 756 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- The linear-tail theorem at the unified clean support cutoff. -/
theorem twentyFour_mul_lt_rpow_one_div_six_of_twoPow756
    {p T : ℕ}
    (hp : 2 ^ 756 < p)
    (hmoment : T ^ 10 ≤ 2 ^ 458 * p) :
    ((24 * T : ℕ) : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ) :=
  twentyFour_mul_lt_rpow_one_div_six_of_tenthMoment
    (twentyFour_support_margin.trans hp) hmoment

/-- The weighted primitive-endgame divisor term is below `p^(1/3)`. -/
theorem sixtyEight_mul_square_lt_rpow_one_div_three_of_tenthMoment
    {p T : ℕ}
    (hpCoefficient : 68 ^ 15 * 2 ^ 1374 < p ^ 2)
    (hmoment : T ^ 10 ≤ 2 ^ 458 * p) :
    ((68 * T ^ 2 : ℕ) : ℝ) < (p : ℝ) ^ (1 / 3 : ℝ) := by
  let Q : ℕ := 68 ^ 15 * 2 ^ 1374
  have hQ : Q < p ^ 2 := by
    simpa [Q] using hpCoefficient
  have hpPos : 0 < p := by
    by_contra hpNot
    have hpZero : p = 0 := Nat.eq_zero_of_not_pos hpNot
    subst p
    simp [Q] at hQ
  have h68 : (68 ^ 15) ^ 2 = 68 ^ 30 := by
    rw [← pow_mul]
  have hTwoLeft : (2 ^ 458) ^ 6 = 2 ^ 2748 := by
    rw [← pow_mul]
  have hTwoRight : (2 ^ 1374) ^ 2 = 2 ^ 2748 := by
    rw [← pow_mul]
  have hpowNat : (68 * T ^ 2) ^ 30 < p ^ 10 := by
    calc
      (68 * T ^ 2) ^ 30 = 68 ^ 30 * (T ^ 10) ^ 6 := by ring
      _ ≤ 68 ^ 30 * (2 ^ 458 * p) ^ 6 := by gcongr
      _ = (68 ^ 30 * (2 ^ 458) ^ 6) * p ^ 6 := by
        rw [mul_pow]
        ring
      _ = ((68 ^ 15) ^ 2 * (2 ^ 1374) ^ 2) * p ^ 6 := by
        rw [h68, hTwoLeft, hTwoRight]
      _ = Q ^ 2 * p ^ 6 := by
        simp only [Q, mul_pow]
      _ < (p ^ 2) ^ 2 * p ^ 6 :=
        Nat.mul_lt_mul_of_pos_right
          (pow_lt_pow_left₀ hQ (Nat.zero_le Q) (by norm_num))
          (pow_pos hpPos 6)
      _ = p ^ 10 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((68 * T ^ 2 : ℕ) : ℝ) ^ 30 <
      (p : ℝ) ^ 10 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 30 = (p : ℝ) ^ 10 := by
    calc
      ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 30 =
          (p : ℝ) ^ ((1 / 3 : ℝ) * 30) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 3 : ℝ) 30).symm
      _ = (p : ℝ) ^ 10 := by norm_num
  apply lt_of_pow_lt_pow_left₀ 30 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

theorem preliminary_sixtyEight_mul_divisorSum_sq_lt_rpow_one_div_three_of_twoPow756
    {p : ℕ} (hp : 2 ^ 756 < p) :
    ((68 * ((p - 1).divisors.card + (p + 1).divisors.card) ^ 2 : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 3 : ℝ) := by
  apply sixtyEight_mul_square_lt_rpow_one_div_three_of_tenthMoment
  · calc
      68 ^ 15 * 2 ^ 1374 < 2 ^ 1512 :=
        sixtyEight_support_margin
      _ = (2 ^ 756) ^ 2 := by rw [← pow_mul]
      _ < p ^ 2 :=
        pow_lt_pow_left₀ hp (Nat.zero_le _) (by norm_num)
  · have hpTwo : 2 ≤ p := by
      have := seven_le_of_twoPow756_lt hp
      omega
    calc
      ((p - 1).divisors.card + (p + 1).divisors.card) ^ 10 ≤
          2 ^ 457 * p := by
        simpa [preliminaryDivisorMomentConstant] using
          preliminary_divisor_sum_pow_ten_le hpTwo
      _ ≤ 2 ^ 458 * p := by
        apply Nat.mul_le_mul_right
        calc
          2 ^ 457 = 2 ^ 457 * 1 := by simp
          _ ≤ 2 ^ 457 * 2 := Nat.mul_le_mul_left _ (by norm_num)
          _ = 2 ^ (457 + 1) := (pow_succ 2 457).symm
          _ = 2 ^ 458 := by norm_num

/-- The cage coefficient times the squared divisor sum is below `sqrt p`. -/
theorem cageCoefficient_mul_square_lt_sqrt_of_tenthMoment
    {p T : ℕ}
    (hpCoefficient : 100522 ^ 10 * 2 ^ 916 < p ^ 3)
    (hmoment : T ^ 10 ≤ 2 ^ 458 * p) :
    ((100522 * T ^ 2 : ℕ) : ℝ) < Real.sqrt (p : ℝ) := by
  let Q : ℕ := 100522 ^ 10 * 2 ^ 916
  have hQ : Q < p ^ 3 := by
    simpa [Q] using hpCoefficient
  have hpPos : 0 < p := by
    by_contra hpNot
    have hpZero : p = 0 := Nat.eq_zero_of_not_pos hpNot
    subst p
    simp [Q] at hQ
  have hTwo : (2 ^ 458) ^ 2 = 2 ^ 916 := by
    rw [← pow_mul]
  have hpowNat : (100522 * T ^ 2) ^ 10 < p ^ 5 := by
    calc
      (100522 * T ^ 2) ^ 10 =
          100522 ^ 10 * (T ^ 10) ^ 2 := by ring
      _ ≤ 100522 ^ 10 * (2 ^ 458 * p) ^ 2 := by gcongr
      _ = (100522 ^ 10 * (2 ^ 458) ^ 2) * p ^ 2 := by
        rw [mul_pow]
        ring
      _ = Q * p ^ 2 := by rw [hTwo]
      _ < p ^ 3 * p ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hQ (pow_pos hpPos 2)
      _ = p ^ 5 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((100522 * T ^ 2 : ℕ) : ℝ) ^ 10 <
      (p : ℝ) ^ 5 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 2 : ℝ)) ^ 10 = (p : ℝ) ^ 5 := by
    calc
      ((p : ℝ) ^ (1 / 2 : ℝ)) ^ 10 =
          (p : ℝ) ^ ((1 / 2 : ℝ) * 10) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 2 : ℝ) 10).symm
      _ = (p : ℝ) ^ 5 := by norm_num
  rw [Real.sqrt_eq_rpow]
  apply lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

theorem preliminary_cageCoefficient_mul_divisorSum_sq_lt_sqrt_of_twoPow756
    {p : ℕ} (hp : 2 ^ 756 < p) :
    ((100522 *
        ((p - 1).divisors.card + (p + 1).divisors.card) ^ 2 : ℕ) : ℝ) <
      Real.sqrt (p : ℝ) := by
  apply cageCoefficient_mul_square_lt_sqrt_of_tenthMoment
  · calc
      100522 ^ 10 * 2 ^ 916 < 2 ^ 2268 :=
        cageCoefficient_support_margin
      _ = (2 ^ 756) ^ 3 := by rw [← pow_mul]
      _ < p ^ 3 :=
        pow_lt_pow_left₀ hp (Nat.zero_le _) (by norm_num)
  · have hpTwo : 2 ≤ p := by
      have := seven_le_of_twoPow756_lt hp
      omega
    calc
      ((p - 1).divisors.card + (p + 1).divisors.card) ^ 10 ≤
          2 ^ 457 * p := by
        simpa [preliminaryDivisorMomentConstant] using
          preliminary_divisor_sum_pow_ten_le hpTwo
      _ ≤ 2 ^ 458 * p := by
        apply Nat.mul_le_mul_right
        calc
          2 ^ 457 = 2 ^ 457 * 1 := by simp
          _ ≤ 2 ^ 457 * 2 := Nat.mul_le_mul_left _ (by norm_num)
          _ = 2 ^ (457 + 1) := (pow_succ 2 457).symm
          _ = 2 ^ 458 := by norm_num

/-- Primitive trace inclusion--exclusion above the unified support cutoff. -/
theorem coarse_endgamePrimitiveTrace_explicitInequality
    {p orbitExponent coefficient : ℕ}
    (hp : 2 ^ 756 < p)
    (horbit : (orbitExponent : ℝ) ≤
      2 * (p : ℝ) ^ (1 / 6 : ℝ))
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpRealPos : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (show (p - 1).divisors.card ≤ T by
      dsimp [T]
      omega)
  have hweighted : (68 : ℝ) * (T : ℝ) ^ 2 <
      (p : ℝ) ^ (1 / 3 : ℝ) := by
    simpa [T] using
      preliminary_sixtyEight_mul_divisorSum_sq_lt_rpow_one_div_three_of_twoPow756 hp
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

theorem coarse_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : 2 ^ 756 < p)
    (hmul : orbitExponent * orbitOrder = p - 1)
    (horder : (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply coarse_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p := Nat.zero_lt_of_lt hp
  have horbit := orbitExponent_le_rpow_of_mul_order_eq_card_sub_one
    p orbitExponent orbitOrder (δ := (1 / 3 : ℝ)) hpNat hmul (by
      convert horder using 1 <;> norm_num)
  calc
    (orbitExponent : ℝ) ≤ (p : ℝ) ^ (1 / 6 : ℝ) := by
      convert horbit using 1 <;> norm_num
    _ ≤ 2 * (p : ℝ) ^ (1 / 6 : ℝ) := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) (1 / 6 : ℝ)]

theorem coarse_endgamePrimitiveTrace_explicitInequality_of_card_add_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : 2 ^ 756 < p)
    (hmul : orbitExponent * orbitOrder = p + 1)
    (horder : (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply coarse_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p := Nat.zero_lt_of_lt hp
  have horbit := orbitExponent_le_two_mul_rpow_of_mul_order_eq_card_add_one
    p orbitExponent orbitOrder (δ := (1 / 3 : ℝ)) hpNat hmul (by
      convert horder using 1 <;> norm_num)
  convert horbit using 1 <;> norm_num

theorem coarse_four_lt_rpow_five_div_six
    {p : ℕ} (hp : 2 ^ 756 < p) :
    (4 : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
  have hpPos : 0 < p := Nat.zero_lt_of_lt hp
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hpSeven : 7 ≤ p := seven_le_of_twoPow756_lt hp
  have hpOneNat : 1 < p := by omega
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hpOneNat
  have hpowNat : 4 ^ 6 < p := by
    calc
      4 ^ 6 < 2 ^ 756 := by
        calc
          4 ^ 6 = 2 ^ 12 := by norm_num
          _ < 2 ^ 756 :=
            Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ < p := hp
  have hpowReal : (4 : ℝ) ^ 6 < (p : ℝ) := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (p : ℝ) := by
    calc
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 6 =
          (p : ℝ) ^ ((1 / 6 : ℝ) * 6) :=
        (Real.rpow_mul_natCast hpRealPos.le (1 / 6 : ℝ) 6).symm
      _ = (p : ℝ) := by norm_num
  have hfour : (4 : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 6 (Real.rpow_nonneg hpRealPos.le _)
    rw [hrootPow]
    exact hpowReal
  exact hfour.trans
    (Real.rpow_lt_rpow_of_exponent_lt hpOne (by norm_num))

/-- Cage connectivity inequality above the unified support cutoff. -/
theorem coarse_cageWitness_explicitInequality
    {p coefficient : ℕ} (hp : 2 ^ 756 < p)
    (hcoefficient : coefficient ≤ 100522) :
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpRealPos : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (show (p - 1).divisors.card ≤ T by
      dsimp [T]
      omega)
  have hcage : (100522 : ℝ) * (T : ℝ) ^ 2 <
      Real.sqrt (p : ℝ) := by
    simpa [T] using
      preliminary_cageCoefficient_mul_divisorSum_sq_lt_sqrt_of_twoPow756 hp
  calc
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      (T : ℝ) ^ 2 * (100522 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = (100522 * (T : ℝ) ^ 2) * Real.sqrt (p : ℝ) := by ring
    _ < Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) :=
      mul_lt_mul_of_pos_right hcage (Real.sqrt_pos.2 hpRealPos)
    _ = (p : ℝ) := Real.mul_self_sqrt hpRealPos.le

/-- The half-order sign threshold is automatic above `2^756`. -/
theorem coarse_halfOrderThreshold
    {p : ℕ} (hp : 2 ^ 756 < p) :
    (p : ℝ) ^ (5 / 6 : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ) := by
  have hpPos : 0 < p := Nat.zero_lt_of_lt hp
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hthreePowNat : 3 ^ 6 < p := by
    calc
      3 ^ 6 < 2 ^ 756 := by
        calc
          3 ^ 6 < 2 ^ 12 := by norm_num
          _ < 2 ^ 756 :=
            Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ < p := hp
  have hthreePowReal : (3 : ℝ) ^ 6 < (p : ℝ) := by
    exact_mod_cast hthreePowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (p : ℝ) := by
    calc
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 6 =
          (p : ℝ) ^ ((1 / 6 : ℝ) * 6) :=
        (Real.rpow_mul_natCast hpRealPos.le (1 / 6 : ℝ) 6).symm
      _ = (p : ℝ) := by norm_num
  have hthree : (3 : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 6 (Real.rpow_nonneg hpRealPos.le _)
    rw [hrootPow]
    exact hthreePowReal
  have hproduct :
      3 * (p : ℝ) ^ (5 / 6 : ℝ) < p := by
    calc
      3 * (p : ℝ) ^ (5 / 6 : ℝ) <
          (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (5 / 6 : ℝ) :=
        mul_lt_mul_of_pos_right hthree
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        norm_num
  have hthird :
      (p : ℝ) ^ (5 / 6 : ℝ) < (p : ℝ) / 3 := by
    linarith
  have hpSeven : 7 ≤ p := seven_le_of_twoPow756_lt hp
  have hNat : p ≤ 3 * ((p - 1) / 2) := by omega
  have hthirdLe :
      (p : ℝ) / 3 ≤ (((p - 1) / 2 : ℕ) : ℝ) := by
    have hcast : (p : ℝ) ≤ 3 * (((p - 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    linarith
  exact hthird.le.trans hthirdLe

end BGS.Markoff

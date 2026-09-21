/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MaximalDivisorLowOrderCount
import LeanPool.MarkoffModP.BGS.Markoff.PreliminaryNumerics

/-!
# Coarse automatic linear tail

The simultaneous tenth-moment bound makes the linear middle-game condition
automatic at a cutoff far below the paper scale.  No divisor-table tuning is
used here.
-/

namespace BGS.Markoff

open BGS.NumberTheory

/-- A tenth-moment estimate and the clean coefficient threshold
`24^15 * 2^687 < p` imply `24*T < p^(1/6)`.

The exponent choice is exact:
`(24^15 * 2^687)^4 = 24^60 * (2^458)^6`. -/
theorem twentyFour_mul_lt_rpow_one_div_six_of_tenthMoment
    {p T : ℕ}
    (hp : 24 ^ 15 * 2 ^ 687 < p)
    (hmoment : T ^ 10 ≤ 2 ^ 458 * p) :
    ((24 * T : ℕ) : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ) := by
  let Q : ℕ := 24 ^ 15 * 2 ^ 687
  have hQ : Q < p := by
    simpa [Q] using hp
  have hpPos : 0 < p := by
    have hQPos : 0 < Q := by positivity
    exact hQPos.trans hQ
  have h24 : (24 ^ 15) ^ 4 = 24 ^ 60 := by
    rw [← pow_mul]
  have hTwoLeft : (2 ^ 458) ^ 6 = 2 ^ 2748 := by
    rw [← pow_mul]
  have hTwoRight : (2 ^ 687) ^ 4 = 2 ^ 2748 := by
    rw [← pow_mul]
  have hpowNat : (24 * T) ^ 60 < p ^ 10 := by
    calc
      (24 * T) ^ 60 = 24 ^ 60 * (T ^ 10) ^ 6 := by ring
      _ ≤ 24 ^ 60 * (2 ^ 458 * p) ^ 6 := by gcongr
      _ = (24 ^ 60 * (2 ^ 458) ^ 6) * p ^ 6 := by
        rw [mul_pow]
        ring
      _ = ((24 ^ 15) ^ 4 * (2 ^ 687) ^ 4) * p ^ 6 := by
        rw [h24, hTwoLeft, hTwoRight]
      _ = Q ^ 4 * p ^ 6 := by
        simp only [Q, mul_pow]
      _ < p ^ 4 * p ^ 6 :=
        Nat.mul_lt_mul_of_pos_right
          (pow_lt_pow_left₀ hQ (Nat.zero_le Q) (by norm_num))
          (pow_pos hpPos 6)
      _ = p ^ 10 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((24 * T : ℕ) : ℝ) ^ 60 < (p : ℝ) ^ 10 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 60 = (p : ℝ) ^ 10 := by
    calc
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 60 =
          (p : ℝ) ^ ((1 / 6 : ℝ) * 60) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 6 : ℝ) 60).symm
      _ = (p : ℝ) ^ 10 := by norm_num
  apply lt_of_pow_lt_pow_left₀ 60 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- Apply the generic tail estimate to the simultaneous divisor count
`T = τ(p-1) + τ(p+1)`. -/
theorem preliminary_twentyFour_mul_divisorSum_lt_rpow_one_div_six_of_coarseBound
    {p : ℕ}
    (hp : 24 ^ 15 * 2 ^ 687 < p) :
    ((24 * ((p - 1).divisors.card + (p + 1).divisors.card) : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 6 : ℝ) := by
  apply twentyFour_mul_lt_rpow_one_div_six_of_tenthMoment hp
  have hpTwo : 2 ≤ p := by
    have hcoefficientPos : 0 < 24 ^ 15 * 2 ^ 687 := by positivity
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

/-- Once `24*T < p^(1/6)`, every `M ≤ T` and every
`d < p^(5/6)` satisfy the linear middle-game inequality. -/
theorem twentyFour_mul_mul_lt_of_le_of_lt_fiveSixths
    {p T M d : ℕ}
    (hpPos : 0 < p)
    (hT : ((24 * T : ℕ) : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ))
    (hM : M ≤ T)
    (hd : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ)) :
    24 * M * d < p := by
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hLinearPower :
      (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (5 / 6 : ℝ) =
        (p : ℝ) := by
    rw [← Real.rpow_add hpRealPos]
    norm_num
  have hMT : 24 * M ≤ 24 * T :=
    Nat.mul_le_mul_left 24 hM
  have hLinearReal : ((24 * M * d : ℕ) : ℝ) < p := by
    calc
      ((24 * M * d : ℕ) : ℝ) =
          ((24 * M : ℕ) : ℝ) * (d : ℝ) := by norm_num
      _ ≤ ((24 * T : ℕ) : ℝ) * (d : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hMT
        · exact Nat.cast_nonneg d
      _ ≤ (p : ℝ) ^ (1 / 6 : ℝ) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hT.le (Nat.cast_nonneg d)
      _ < (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (5 / 6 : ℝ) :=
        mul_lt_mul_of_pos_left hd (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) := hLinearPower
  exact_mod_cast hLinearReal

/-- Coarse all-divisor specialization: the linear branch is automatic for
any `M` bounded by the simultaneous divisor count. -/
theorem preliminary_twentyFour_mul_mul_lt_of_coarseBound
    {p M d : ℕ}
    (hp : 24 ^ 15 * 2 ^ 687 < p)
    (hM :
      M ≤ (p - 1).divisors.card + (p + 1).divisors.card)
    (hd : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ)) :
    24 * M * d < p := by
  have hpPos : 0 < p := by
    have hcoefficientPos : 0 < 24 ^ 15 * 2 ^ 687 := by positivity
    omega
  exact
    twentyFour_mul_mul_lt_of_le_of_lt_fiveSixths hpPos
      (preliminary_twentyFour_mul_divisorSum_lt_rpow_one_div_six_of_coarseBound hp)
      hM hd

/-- In particular, the maximal-divisor coefficient in the Euler-seven
frontier satisfies the linear branch automatically above the coarse tail. -/
theorem maximalDivisorCountSum_linear_lt_of_coarseBound
    {p d : ℕ}
    (hp : 24 ^ 15 * 2 ^ 687 < p)
    (hd : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ)) :
    24 * maximalDivisorCountSum p (d + 1) * d < p := by
  apply preliminary_twentyFour_mul_mul_lt_of_coarseBound hp
  · unfold maximalDivisorCountSum
    exact Nat.add_le_add
      (maximalDivisorsBelow_card_le_card_divisors (p - 1) (d + 1))
      (maximalDivisorsBelow_card_le_card_divisors (p + 1) (d + 1))
  · exact hd

end BGS.Markoff

/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.JointNeighborDivisorBound
import LeanPool.MarkoffModP.BGS.NumberTheory.WeightedDivisorMoment

/-!
# A weighted joint divisor bound for neighboring integers

The weighted divisor estimate `τ(n)^20 ≤ 2^796 n^2` retains substantially
more information than the square of the tenth-moment bound.  For the
neighboring even integers `p - 1` and `p + 1`, their exact gcd-two identity
also controls the product of their divisor counts.  Splitting into balanced
and dominant cases then gives a twentieth moment for their sum whose leading
constant is still `2^796`.
-/

namespace BGS.NumberTheory

/-- The product of the two neighboring divisor counts has only one weighted
prime-penalty factor in its twentieth moment. -/
theorem card_divisors_pred_mul_card_divisors_succ_pow_twenty_le
    {p : ℕ} (hp : Odd p) (hpTwo : 2 < p) :
    ((p - 1).divisors.card * (p + 1).divisors.card) ^ 20 ≤
      2 ^ 814 * (p ^ 2 - 1) ^ 2 := by
  let core := (p ^ 2 - 1) / 2
  have hpSq : 9 ≤ p ^ 2 := by nlinarith
  have hcorePos : 0 < core := by
    apply Nat.div_pos
    · omega
    · norm_num
  have hmoment :=
    card_divisors_pow_twenty_le_weighted_constant_mul_sq
      core hcorePos.ne'
  have htwiceCore : 2 * core = p ^ 2 - 1 := by
    rcases hp with ⟨k, rfl⟩
    dsimp [core]
    have hsquare :
        (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    rw [hsquare]
    omega
  calc
    ((p - 1).divisors.card * (p + 1).divisors.card) ^ 20 =
        (2 * core.divisors.card) ^ 20 := by
      rw [card_divisors_pred_mul_card_divisors_succ_of_odd hp]
    _ = 2 ^ 20 * core.divisors.card ^ 20 := by rw [mul_pow]
    _ ≤ 2 ^ 20 * (2 ^ 796 * core ^ 2) :=
      Nat.mul_le_mul_left _ hmoment
    _ = 2 ^ 816 * core ^ 2 := by
      rw [show (816 : ℕ) = 20 + 796 by norm_num, pow_add]
      ring
    _ = 2 ^ 814 * (2 * core) ^ 2 := by
      rw [show (816 : ℕ) = 814 + 2 by norm_num, pow_add]
      norm_num
      ring
    _ = 2 ^ 814 * (p ^ 2 - 1) ^ 2 := by rw [htwiceCore]

/-- Square-root form of the weighted joint product moment. -/
theorem card_divisors_pred_mul_card_divisors_succ_pow_ten_weighted_le
    {p : ℕ} (hp : Odd p) (hpTwo : 2 < p) :
    ((p - 1).divisors.card * (p + 1).divisors.card) ^ 10 ≤
      2 ^ 407 * p ^ 2 := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp
  have htwo : (2 ^ 407) ^ 2 = 2 ^ 814 := by
    rw [← pow_mul]
  calc
    (((p - 1).divisors.card * (p + 1).divisors.card) ^ 10) ^ 2 =
        ((p - 1).divisors.card * (p + 1).divisors.card) ^ 20 := by
      rw [← pow_mul]
    _ ≤ 2 ^ 814 * (p ^ 2 - 1) ^ 2 :=
      card_divisors_pred_mul_card_divisors_succ_pow_twenty_le hp hpTwo
    _ ≤ 2 ^ 814 * (p ^ 2) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = (2 ^ 407 * p ^ 2) ^ 2 := by rw [mul_pow, htwo]

/-- Joint weighted twentieth-moment constant for the sum of the neighboring
divisor counts. -/
def neighboringDivisorSumWeightedMomentConstant : ℕ :=
  2 ^ 796 + 2 ^ 781

theorem neighboringDivisorSumWeightedMomentConstant_eq :
    neighboringDivisorSumWeightedMomentConstant = 2 ^ 781 * 32769 := by
  rw [neighboringDivisorSumWeightedMomentConstant,
    show (796 : ℕ) = 781 + 15 by norm_num, pow_add]
  norm_num
  ring

private def neighboringDivisorSumWeightedSplit : ℕ :=
  716198

private theorem neighboringDivisorSumWeighted_balanced_constant :
    (neighboringDivisorSumWeightedSplit + 1) ^ 20 * 2 ^ 407 ≤
      neighboringDivisorSumWeightedMomentConstant := by
  norm_num [neighboringDivisorSumWeightedSplit,
    neighboringDivisorSumWeightedMomentConstant]

private theorem neighboringDivisorSumWeighted_dominant_constant
    {p : ℕ} (hp : 794039 ≤ p) :
    (neighboringDivisorSumWeightedSplit + 1) ^ 20 * 2 ^ 796 *
        (p + 1) ^ 2 ≤
      neighboringDivisorSumWeightedSplit ^ 20 *
        neighboringDivisorSumWeightedMomentConstant * p ^ 2 := by
  let R := neighboringDivisorSumWeightedSplit
  let K := 2 ^ 796
  let D := neighboringDivisorSumWeightedMomentConstant
  let P := 794039
  have hground :
      (R + 1) ^ 20 * K * (P + 1) ^ 2 ≤
        R ^ 20 * D * P ^ 2 := by
    norm_num [R, K, D, P, neighboringDivisorSumWeightedSplit,
      neighboringDivisorSumWeightedMomentConstant]
  have hlinear : P * (p + 1) ≤ (P + 1) * p := by
    dsimp [P]
    omega
  have hratioPow :=
    Nat.pow_le_pow_left hlinear 2
  have hratio :
      P ^ 2 * (p + 1) ^ 2 ≤ (P + 1) ^ 2 * p ^ 2 := by
    simpa only [mul_pow] using hratioPow
  have hcombined :
      P ^ 2 * ((R + 1) ^ 20 * K * (p + 1) ^ 2) ≤
        P ^ 2 * (R ^ 20 * D * p ^ 2) := by
    calc
      P ^ 2 * ((R + 1) ^ 20 * K * (p + 1) ^ 2) =
          ((R + 1) ^ 20 * K) * (P ^ 2 * (p + 1) ^ 2) := by ring
      _ ≤ ((R + 1) ^ 20 * K) * ((P + 1) ^ 2 * p ^ 2) :=
        Nat.mul_le_mul_left _ hratio
      _ = ((R + 1) ^ 20 * K * (P + 1) ^ 2) * p ^ 2 := by ring
      _ ≤ (R ^ 20 * D * P ^ 2) * p ^ 2 :=
        Nat.mul_le_mul_right _ hground
      _ = P ^ 2 * (R ^ 20 * D * p ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hcombined (pow_pos (by norm_num : 0 < P) 2)

private theorem nat_le_of_pos_mul_le_mul_left_weighted
    {c x y : ℕ} (hc : 0 < c) (h : c * x ≤ c * y) :
    x ≤ y :=
  Nat.le_of_mul_le_mul_left h hc

/-- Weighted joint twentieth moment for the sum of the neighboring divisor
counts.  Comparable counts are controlled by their product; a dominant count
is controlled by its individual weighted moment. -/
theorem card_divisors_pred_add_card_divisors_succ_pow_twenty_le
    {p : ℕ} (hp : Odd p) (hpLarge : 794039 ≤ p) :
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 20 ≤
      neighboringDivisorSumWeightedMomentConstant * p ^ 2 := by
  let a := (p - 1).divisors.card
  let b := (p + 1).divisors.card
  let R := neighboringDivisorSumWeightedSplit
  let K := 2 ^ 796
  let D := neighboringDivisorSumWeightedMomentConstant
  have hpTwo : 2 < p := by omega
  have hminus : a ^ 20 ≤ K * (p - 1) ^ 2 := by
    simpa [a, K] using
      card_divisors_pow_twenty_le_weighted_constant_mul_sq
        (p - 1) (by omega)
  have hplus : b ^ 20 ≤ K * (p + 1) ^ 2 := by
    simpa [b, K] using
      card_divisors_pow_twenty_le_weighted_constant_mul_sq
        (p + 1) (by omega)
  have hminusCommon : a ^ 20 ≤ K * (p + 1) ^ 2 :=
    hminus.trans (Nat.mul_le_mul_left K
      (Nat.pow_le_pow_left (by omega) 2))
  have hproductTen : (a * b) ^ 10 ≤ 2 ^ 407 * p ^ 2 := by
    simpa [a, b] using
      card_divisors_pred_mul_card_divisors_succ_pow_ten_weighted_le hp hpTwo
  have hbalanced : (R + 1) ^ 20 * 2 ^ 407 ≤ D := by
    simpa [R, D] using neighboringDivisorSumWeighted_balanced_constant
  have hRPos : 0 < R := by
    norm_num [R, neighboringDivisorSumWeightedSplit]
  have hRpowPos : 0 < R ^ 20 := pow_pos hRPos 20
  have hdominant :
      (R + 1) ^ 20 * K * (p + 1) ^ 2 ≤ R ^ 20 * D * p ^ 2 := by
    simpa [R, K, D] using
      neighboringDivisorSumWeighted_dominant_constant hpLarge
  rcases le_total a b with hab | hba
  · by_cases hfar : R * a ≤ b
    · have hlinear : R * (a + b) ≤ (R + 1) * b := by
        calc
          R * (a + b) = R * a + R * b := by ring
          _ ≤ b + R * b := Nat.add_le_add_right hfar _
          _ = (R + 1) * b := by ring
      have hpow := Nat.pow_le_pow_left hlinear 20
      have hscaled :
          R ^ 20 * (a + b) ^ 20 ≤ R ^ 20 * (D * p ^ 2) := by
        calc
          R ^ 20 * (a + b) ^ 20 = (R * (a + b)) ^ 20 := by ring
          _ ≤ ((R + 1) * b) ^ 20 := hpow
          _ = (R + 1) ^ 20 * b ^ 20 := by ring
          _ ≤ (R + 1) ^ 20 * (K * (p + 1) ^ 2) :=
            Nat.mul_le_mul_left _ hplus
          _ = (R + 1) ^ 20 * K * (p + 1) ^ 2 := by ring
          _ ≤ R ^ 20 * (D * p ^ 2) := by
            simpa only [Nat.mul_assoc] using hdominant
      exact nat_le_of_pos_mul_le_mul_left_weighted
        (c := R ^ 20) (x := (a + b) ^ 20) (y := D * p ^ 2)
        hRpowPos hscaled
    · have hnear : b ≤ R * a := by omega
      have hlinear : a + b ≤ (R + 1) * a := by
        calc
          a + b ≤ a + R * a := Nat.add_le_add_left hnear _
          _ = (R + 1) * a := by ring
      have haa : a * a ≤ a * b := Nat.mul_le_mul_left a hab
      calc
        (a + b) ^ 20 ≤ ((R + 1) * a) ^ 20 :=
          Nat.pow_le_pow_left hlinear 20
        _ = (R + 1) ^ 20 * (a * a) ^ 10 := by ring
        _ ≤ (R + 1) ^ 20 * (a * b) ^ 10 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left haa 10)
        _ ≤ (R + 1) ^ 20 * (2 ^ 407 * p ^ 2) :=
          Nat.mul_le_mul_left _ hproductTen
        _ = ((R + 1) ^ 20 * 2 ^ 407) * p ^ 2 := by ring
        _ ≤ D * p ^ 2 := Nat.mul_le_mul_right (p ^ 2) hbalanced
  · by_cases hfar : R * b ≤ a
    · have hlinear : R * (a + b) ≤ (R + 1) * a := by
        calc
          R * (a + b) = R * a + R * b := by ring
          _ = R * b + R * a := by ring
          _ ≤ a + R * a := Nat.add_le_add_right hfar _
          _ = (R + 1) * a := by ring
      have hpow := Nat.pow_le_pow_left hlinear 20
      have hscaled :
          R ^ 20 * (a + b) ^ 20 ≤ R ^ 20 * (D * p ^ 2) := by
        calc
          R ^ 20 * (a + b) ^ 20 = (R * (a + b)) ^ 20 := by ring
          _ ≤ ((R + 1) * a) ^ 20 := hpow
          _ = (R + 1) ^ 20 * a ^ 20 := by ring
          _ ≤ (R + 1) ^ 20 * (K * (p + 1) ^ 2) :=
            Nat.mul_le_mul_left _ hminusCommon
          _ = (R + 1) ^ 20 * K * (p + 1) ^ 2 := by ring
          _ ≤ R ^ 20 * (D * p ^ 2) := by
            simpa only [Nat.mul_assoc] using hdominant
      exact nat_le_of_pos_mul_le_mul_left_weighted
        (c := R ^ 20) (x := (a + b) ^ 20) (y := D * p ^ 2)
        hRpowPos hscaled
    · have hnear : a ≤ R * b := by omega
      have hlinear : a + b ≤ (R + 1) * b := by
        calc
          a + b ≤ R * b + b := Nat.add_le_add_right hnear _
          _ = (R + 1) * b := by ring
      have hbb : b * b ≤ a * b := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left b hba
      calc
        (a + b) ^ 20 ≤ ((R + 1) * b) ^ 20 :=
          Nat.pow_le_pow_left hlinear 20
        _ = (R + 1) ^ 20 * (b * b) ^ 10 := by ring
        _ ≤ (R + 1) ^ 20 * (a * b) ^ 10 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbb 10)
        _ ≤ (R + 1) ^ 20 * (2 ^ 407 * p ^ 2) :=
          Nat.mul_le_mul_left _ hproductTen
        _ = ((R + 1) ^ 20 * 2 ^ 407) * p ^ 2 := by ring
        _ ≤ D * p ^ 2 := Nat.mul_le_mul_right (p ^ 2) hbalanced

end BGS.NumberTheory

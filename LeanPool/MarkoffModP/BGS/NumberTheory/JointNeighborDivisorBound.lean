/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.PreliminaryDivisorBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Joint divisor bounds for neighboring even integers

For an odd natural number `p`, the two torus orders `p - 1` and `p + 1`
have gcd exactly two. Consequently their divisor counts are not independent:

`τ(p - 1) τ(p + 1) = 2 τ((p^2 - 1) / 2)`.

Combining this identity with the elementary tenth-moment divisor bound gives
a joint estimate with one copy, rather than two copies, of the prime-factor
penalty. This is the arithmetic input for improving the maximal-divisor
cutoff.
-/

namespace BGS.NumberTheory

private theorem card_divisors_two_mul_of_odd {n : ℕ} (hn : Odd n) :
    (2 * n).divisors.card = 2 * n.divisors.card := by
  have htwo : (2 : ℕ).divisors.card = 2 := by decide
  rw [hn.coprime_two_left.card_divisors_mul]
  rw [htwo]

/-- Exact joint divisor-count identity for the neighboring torus orders. -/
theorem card_divisors_pred_mul_card_divisors_succ_of_odd
    {p : ℕ} (hp : Odd p) :
    (p - 1).divisors.card * (p + 1).divisors.card =
      2 * (((p ^ 2 - 1) / 2).divisors.card) := by
  rcases hp with ⟨k, rfl⟩
  have hcore :
      (((2 * k + 1) ^ 2 - 1) / 2) = 2 * k * (k + 1) := by
    have hsquare :
        (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    rw [hsquare]
    omega
  have hconsecutive : k.Coprime (k + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right k
  have hpred : 2 * k + 1 - 1 = 2 * k := by omega
  have hsucc : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rcases k.even_or_odd with hkEven | hkOdd
  · have hkSuccOdd : Odd (k + 1) := hkEven.add_one
    have hcoprime : (2 * k).Coprime (k + 1) :=
      hkSuccOdd.coprime_two_left.mul_left hconsecutive
    have hmul := hcoprime.card_divisors_mul
    have htwo := card_divisors_two_mul_of_odd hkSuccOdd
    rw [hcore, hpred, hsucc]
    rw [htwo, hmul]
    ring
  · have hcoprime : k.Coprime (2 * (k + 1)) :=
      hkOdd.coprime_two_right.mul_right hconsecutive
    have hmul := hcoprime.card_divisors_mul
    have htwo := card_divisors_two_mul_of_odd hkOdd
    have hfactor : 2 * k * (k + 1) = k * (2 * (k + 1)) := by ring
    rw [hcore, hpred, hsucc, hfactor]
    rw [htwo, hmul]
    ring

/-- The product of the two neighboring divisor counts has a single
prime-penalty factor in its tenth moment. -/
theorem card_divisors_pred_mul_card_divisors_succ_pow_ten_le
    {p : ℕ} (hp : Odd p) (hpTwo : 2 < p) :
    ((p - 1).divisors.card * (p + 1).divisors.card) ^ 10 ≤
      2 ^ 456 * (p ^ 2 - 1) := by
  let core := (p ^ 2 - 1) / 2
  have hpSq : 9 ≤ p ^ 2 := by nlinarith
  have hcorePos : 0 < core := by
    apply Nat.div_pos
    · omega
    · norm_num
  have hmoment :=
    card_divisors_pow_ten_le_preliminary_constant_mul core hcorePos.ne'
  have htwiceCore : 2 * core = p ^ 2 - 1 := by
    rcases hp with ⟨k, rfl⟩
    dsimp [core]
    have hsquare : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    rw [hsquare]
    omega
  have hexponent : 10 + 447 = 456 + 1 := by norm_num
  calc
    ((p - 1).divisors.card * (p + 1).divisors.card) ^ 10 =
        (2 * core.divisors.card) ^ 10 := by
      rw [card_divisors_pred_mul_card_divisors_succ_of_odd hp]
    _ = 2 ^ 10 * core.divisors.card ^ 10 := by rw [mul_pow]
    _ ≤ 2 ^ 10 * (2 ^ 447 * core) := Nat.mul_le_mul_left _ hmoment
    _ = (2 ^ 10 * 2 ^ 447) * core := (Nat.mul_assoc _ _ _).symm
    _ = 2 ^ (10 + 447) * core := by rw [pow_add]
    _ = 2 ^ (456 + 1) * core := by rw [hexponent]
    _ = (2 ^ 456 * 2) * core := by rw [pow_succ]
    _ = 2 ^ 456 * (2 * core) := Nat.mul_assoc _ _ _
    _ = 2 ^ 456 * (p ^ 2 - 1) := by rw [htwiceCore]

/-- Joint tenth-moment constant for the sum of the neighboring divisor counts.
The leading term is the one-number prime penalty; the smaller correction pays
for the transition between the balanced and dominant cases. -/
def neighboringDivisorSumMomentConstant : Nat :=
  2 ^ 447 + 2 ^ 429

/-- Split point used to combine the product moment with the two individual
moments. It is chosen so that both resulting integer inequalities hold. -/
theorem neighboringDivisorSumMomentConstant_eq :
    neighboringDivisorSumMomentConstant = 2 ^ 429 * 262145 := by
  rw [neighboringDivisorSumMomentConstant,
    show (447 : Nat) = 429 + 18 by norm_num, pow_add]
  norm_num
  ring

private def neighboringDivisorSumSplit : Nat :=
  3913424

private theorem neighboringDivisorSum_balanced_constant :
    (neighboringDivisorSumSplit + 1) ^ 10 * 2 ^ 228 ≤
      neighboringDivisorSumMomentConstant := by
  norm_num [neighboringDivisorSumSplit, neighboringDivisorSumMomentConstant]

private theorem neighboringDivisorSum_dominant_constant
    {p : Nat} (hp : 794039 ≤ p) :
    (neighboringDivisorSumSplit + 1) ^ 10 * 2 ^ 447 * (p + 1) ≤
      neighboringDivisorSumSplit ^ 10 *
        neighboringDivisorSumMomentConstant * p := by
  norm_num [neighboringDivisorSumSplit, neighboringDivisorSumMomentConstant] at *
  omega

/-- Square-root form of the joint product moment. -/
theorem card_divisors_pred_mul_card_divisors_succ_pow_five_le
    {p : Nat} (hp : Odd p) (hpTwo : 2 < p) :
    ((p - 1).divisors.card * (p + 1).divisors.card) ^ 5 ≤
      2 ^ 228 * p := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp
  calc
    (((p - 1).divisors.card * (p + 1).divisors.card) ^ 5) ^ 2 =
        ((p - 1).divisors.card * (p + 1).divisors.card) ^ 10 := by ring
    _ ≤ 2 ^ 456 * (p ^ 2 - 1) :=
      card_divisors_pred_mul_card_divisors_succ_pow_ten_le hp hpTwo
    _ ≤ 2 ^ 456 * p ^ 2 := by
      gcongr
      omega
    _ = (2 ^ 228 * p) ^ 2 := by
      rw [show (456 : Nat) = 228 * 2 by norm_num, pow_mul]
      ring

private theorem nat_le_of_pos_mul_le_mul_left
    {c x y : Nat} (hc : 0 < c) (h : c * x ≤ c * y) :
    x ≤ y :=
  Nat.le_of_mul_le_mul_left h hc

/-- A joint tenth moment for the sum of the neighboring divisor counts.

The usual power-of-a-sum inequality loses a factor of (2^9). Here comparable
counts are controlled by the product moment, while in the dominant case the
larger individual count controls the sum. -/
theorem card_divisors_pred_add_card_divisors_succ_pow_ten_le
    {p : Nat} (hp : Odd p) (hpLarge : 794039 ≤ p) :
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 10 ≤
      neighboringDivisorSumMomentConstant * p := by
  let a := (p - 1).divisors.card
  let b := (p + 1).divisors.card
  let R := neighboringDivisorSumSplit
  let K := 2 ^ 447
  let D := neighboringDivisorSumMomentConstant
  have hpTwo : 2 < p := by omega
  have hminus : a ^ 10 ≤ K * (p - 1) := by
    simpa [a, K] using
      card_divisors_pow_ten_le_preliminary_constant_mul (p - 1) (by omega)
  have hplus : b ^ 10 ≤ K * (p + 1) := by
    simpa [b, K] using
      card_divisors_pow_ten_le_preliminary_constant_mul (p + 1) (by omega)
  have hminusCommon : a ^ 10 ≤ K * (p + 1) :=
    hminus.trans (Nat.mul_le_mul_left K (by omega))
  have hproductFive : (a * b) ^ 5 ≤ 2 ^ 228 * p := by
    simpa [a, b] using
      card_divisors_pred_mul_card_divisors_succ_pow_five_le hp hpTwo
  have hbalanced : (R + 1) ^ 10 * 2 ^ 228 ≤ D := by
    simpa [R, D] using neighboringDivisorSum_balanced_constant
  have hRPos : 0 < R := by norm_num [R, neighboringDivisorSumSplit]
  have hRpowPos : 0 < R ^ 10 := pow_pos hRPos 10
  have hdominant :
      (R + 1) ^ 10 * K * (p + 1) ≤ R ^ 10 * D * p := by
    simpa [R, K, D] using neighboringDivisorSum_dominant_constant hpLarge
  rcases le_total a b with hab | hba
  · by_cases hfar : R * a ≤ b
    · have hlinear : R * (a + b) ≤ (R + 1) * b := by
        calc
          R * (a + b) = R * a + R * b := by ring
          _ ≤ b + R * b := Nat.add_le_add_right hfar _
          _ = (R + 1) * b := by ring
      have hpow := Nat.pow_le_pow_left hlinear 10
      have hscaled : R ^ 10 * (a + b) ^ 10 ≤ R ^ 10 * (D * p) := by
        calc
          R ^ 10 * (a + b) ^ 10 = (R * (a + b)) ^ 10 := by ring
          _ ≤ ((R + 1) * b) ^ 10 := hpow
          _ = (R + 1) ^ 10 * b ^ 10 := by ring
          _ ≤ (R + 1) ^ 10 * (K * (p + 1)) :=
            Nat.mul_le_mul_left _ hplus
          _ = (R + 1) ^ 10 * K * (p + 1) := by ring
          _ ≤ R ^ 10 * (D * p) := by
            simpa only [Nat.mul_assoc] using hdominant
      exact nat_le_of_pos_mul_le_mul_left
        (c := R ^ 10) (x := (a + b) ^ 10) (y := D * p)
        hRpowPos hscaled
    · have hnear : b ≤ R * a := by omega
      have hlinear : a + b ≤ (R + 1) * a := by
        calc
          a + b ≤ a + R * a := Nat.add_le_add_left hnear _
          _ = (R + 1) * a := by ring
      have haa : a * a ≤ a * b := Nat.mul_le_mul_left a hab
      calc
        (a + b) ^ 10 ≤ ((R + 1) * a) ^ 10 :=
          Nat.pow_le_pow_left hlinear 10
        _ = (R + 1) ^ 10 * (a * a) ^ 5 := by ring
        _ ≤ (R + 1) ^ 10 * (a * b) ^ 5 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left haa 5)
        _ ≤ (R + 1) ^ 10 * (2 ^ 228 * p) :=
          Nat.mul_le_mul_left _ hproductFive
        _ = ((R + 1) ^ 10 * 2 ^ 228) * p := by ring
        _ ≤ D * p := Nat.mul_le_mul_right p hbalanced
  · by_cases hfar : R * b ≤ a
    · have hlinear : R * (a + b) ≤ (R + 1) * a := by
        calc
          R * (a + b) = R * a + R * b := by ring
          _ = R * b + R * a := by ring
          _ ≤ a + R * a := Nat.add_le_add_right hfar _
          _ = (R + 1) * a := by ring
      have hpow := Nat.pow_le_pow_left hlinear 10
      have hscaled : R ^ 10 * (a + b) ^ 10 ≤ R ^ 10 * (D * p) := by
        calc
          R ^ 10 * (a + b) ^ 10 = (R * (a + b)) ^ 10 := by ring
          _ ≤ ((R + 1) * a) ^ 10 := hpow
          _ = (R + 1) ^ 10 * a ^ 10 := by ring
          _ ≤ (R + 1) ^ 10 * (K * (p + 1)) :=
            Nat.mul_le_mul_left _ hminusCommon
          _ = (R + 1) ^ 10 * K * (p + 1) := by ring
          _ ≤ R ^ 10 * (D * p) := by
            simpa only [Nat.mul_assoc] using hdominant
      exact nat_le_of_pos_mul_le_mul_left
        (c := R ^ 10) (x := (a + b) ^ 10) (y := D * p)
        hRpowPos hscaled
    · have hnear : a ≤ R * b := by omega
      have hlinear : a + b ≤ (R + 1) * b := by
        calc
          a + b ≤ R * b + b := Nat.add_le_add_right hnear _
          _ = (R + 1) * b := by ring
      have hbb : b * b ≤ a * b := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left b hba
      calc
        (a + b) ^ 10 ≤ ((R + 1) * b) ^ 10 :=
          Nat.pow_le_pow_left hlinear 10
        _ = (R + 1) ^ 10 * (b * b) ^ 5 := by ring
        _ ≤ (R + 1) ^ 10 * (a * b) ^ 5 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbb 5)
        _ ≤ (R + 1) ^ 10 * (2 ^ 228 * p) :=
          Nat.mul_le_mul_left _ hproductFive
        _ = ((R + 1) ^ 10 * 2 ^ 228) * p := by ring
        _ ≤ D * p := Nat.mul_le_mul_right p hbalanced

/-- If two nonnegative counts are individually at most `C` and their product
is at most `J`, their squared sum is bounded by `C^2 + 3J`. This is the
elementary inequality that replaces the paper's independent `4C^2` bound. -/
theorem add_sq_le_sq_add_three_mul_of_le_of_mul_le
    {a b C J : ℕ} (ha : a ≤ C) (hb : b ≤ C) (hab : a * b ≤ J) :
    (a + b) ^ 2 ≤ C ^ 2 + 3 * J := by
  rcases le_total a b with habOrder | hbaOrder
  · have haSq : a * a ≤ a * b := Nat.mul_le_mul_left a habOrder
    have hbSq : b * b ≤ C * C := Nat.mul_le_mul hb hb
    nlinarith [hab]
  · have hbSq : b * b ≤ a * b := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left b hbaOrder
    have haSq : a * a ≤ C * C := Nat.mul_le_mul ha ha
    nlinarith [hab]

/-- Convert a certified tenth-moment envelope into the joint squared-sum
bound used by the improved maximal-divisor algorithm. -/
theorem add_sq_le_sq_add_three_mul_of_pow_ten_envelope
    {a b C J K : ℕ}
    (ha : a ≤ C) (hb : b ≤ C)
    (hmoment : (a * b) ^ 10 ≤ K) (henvelope : K ≤ J ^ 10) :
    (a + b) ^ 2 ≤ C ^ 2 + 3 * J := by
  apply add_sq_le_sq_add_three_mul_of_le_of_mul_le ha hb
  apply (Nat.pow_le_pow_iff_left (by norm_num : 10 ≠ 0)).mp
  exact hmoment.trans henvelope

end BGS.NumberTheory

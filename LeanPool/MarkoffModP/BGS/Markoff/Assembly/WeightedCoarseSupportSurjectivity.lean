/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.CoarseSupportSurjectivity
public import LeanPool.MarkoffModP.BGS.NumberTheory.WeightedNeighborDivisorBound

/-!
# Weighted certificate-free coarse-support surjectivity

This module feeds the weighted twentieth moment for the neighboring divisor
counts into the Euler-seven coarse-support obstruction.  It improves the
tenth-moment checkpoint without changing the geometric frontier and without
introducing a divisor table or a finite maximal-divisor certificate.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

/-- Open cutoff supplied by the weighted twentieth moment and the Euler-seven
obstruction. -/
def weightedCoarseSupportStrongApproximationOpenCutoff : ℕ :=
  35721 ^ 5 * 2 ^ 1547 * 32769 ^ 2

/-- Closed version of `weightedCoarseSupportStrongApproximationOpenCutoff`. -/
def weightedCoarseSupportStrongApproximationCutoff : ℕ :=
  weightedCoarseSupportStrongApproximationOpenCutoff + 1

private theorem twoPow756_lt_weightedCoarseSupportStrongApproximationOpenCutoff :
    2 ^ 756 < weightedCoarseSupportStrongApproximationOpenCutoff := by
  calc
    2 ^ 756 < 2 ^ 1547 :=
      Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ = 1 * 2 ^ 1547 * 1 := by ring
    _ ≤ 35721 ^ 5 * 2 ^ 1547 * 32769 ^ 2 := by
      gcongr <;> norm_num

/-- The weighted joint twentieth moment rules out the final Euler-seven
obstruction above the exact weighted cutoff. -/
theorem weighted_35721_mul_divisorSum_pow_eight_lt
    {p : ℕ} (hpOdd : Odd p)
    (hp : weightedCoarseSupportStrongApproximationOpenCutoff < p) :
    35721 * ((p - 1).divisors.card + (p + 1).divisors.card) ^ 8 < 8 * p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let D := neighboringDivisorSumWeightedMomentConstant
  have hpPos : 0 < p := (Nat.zero_le _).trans_lt hp
  have hpSupport : 2 ^ 756 < p :=
    twoPow756_lt_weightedCoarseSupportStrongApproximationOpenCutoff.trans hp
  have hpLarge : 794039 ≤ p := by
    have hsmall : 794039 < 2 ^ 20 := by norm_num
    have hpowers : 2 ^ 20 ≤ 2 ^ 756 :=
      Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hmoment : T ^ 20 ≤ D * p ^ 2 := by
    simpa [T, D] using
      card_divisors_pred_add_card_divisors_succ_pow_twenty_le hpOdd hpLarge
  by_contra hnot
  have hbad : 8 * p ≤ 35721 * T ^ 8 := by
    exact Nat.le_of_not_gt (by simpa [T] using hnot)
  have hbadPow : (8 * p) ^ 5 ≤ (35721 * T ^ 8) ^ 5 :=
    Nat.pow_le_pow_left hbad 5
  have hmomentPow : (T ^ 20) ^ 2 ≤ (D * p ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hmoment 2
  have hcombined :
      2 ^ 15 * p ^ 5 ≤ 35721 ^ 5 * D ^ 2 * p ^ 4 := by
    calc
      2 ^ 15 * p ^ 5 = (8 * p) ^ 5 := by ring
      _ ≤ (35721 * T ^ 8) ^ 5 := hbadPow
      _ = 35721 ^ 5 * (T ^ 20) ^ 2 := by ring
      _ ≤ 35721 ^ 5 * (D * p ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ hmomentPow
      _ = 35721 ^ 5 * D ^ 2 * p ^ 4 := by ring
  have hcombined' :
      (2 ^ 15 * p) * p ^ 4 ≤
        (35721 ^ 5 * D ^ 2) * p ^ 4 := by
    simpa only [show p ^ 5 = p * p ^ 4 by ring, Nat.mul_assoc] using hcombined
  have hcancel : 2 ^ 15 * p ≤ 35721 ^ 5 * D ^ 2 :=
    Nat.le_of_mul_le_mul_right hcombined' (pow_pos hpPos 4)
  have hfactor :
      35721 ^ 5 * D ^ 2 =
        2 ^ 15 * weightedCoarseSupportStrongApproximationOpenCutoff := by
    have hD : D = 2 ^ 781 * 32769 :=
      neighboringDivisorSumWeightedMomentConstant_eq
    rw [hD, mul_pow]
    rw [show (2 ^ 781) ^ 2 = 2 ^ 1562 by
      rw [show (1562 : ℕ) = 781 * 2 by norm_num, pow_mul]]
    rw [show (1562 : ℕ) = 15 + 1547 by norm_num, pow_add]
    unfold weightedCoarseSupportStrongApproximationOpenCutoff
    ring
  have hcutoffUpper :
      p ≤ weightedCoarseSupportStrongApproximationOpenCutoff := by
    rw [hfactor] at hcancel
    have hcancel' :
        p * 2 ^ 15 ≤
          weightedCoarseSupportStrongApproximationOpenCutoff * 2 ^ 15 := by
      simpa only [Nat.mul_comm] using hcancel
    exact Nat.le_of_mul_le_mul_right hcancel' (pow_pos (by norm_num) 15)
  exact (Nat.not_le_of_lt hp) hcutoffUpper

/-- The weighted cutoff dominates the support-only threshold used by the
coarse endgame and cage arguments. -/
theorem twoPow756_lt_of_weightedCoarseSupportOpenCutoff_lt
    {p : ℕ}
    (hp : weightedCoarseSupportStrongApproximationOpenCutoff < p) :
    2 ^ 756 < p :=
  twoPow756_lt_weightedCoarseSupportStrongApproximationOpenCutoff.trans hp

/-- Natural Markoff reduction is surjective above the weighted
certificate-free cutoff. -/
theorem markoffReduction_surjective_of_weightedCoarseSupportOpenCutoff
    (p : ℕ) (hpPrime : p.Prime)
    (hp : weightedCoarseSupportStrongApproximationOpenCutoff < p) :
    Function.Surjective (markoffReduction p) := by
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpThree : 3 < p := by
    have hsupport := twoPow756_lt_of_weightedCoarseSupportOpenCutoff_lt hp
    omega
  have hpOdd : Odd p :=
    hpPrime.odd_of_ne_two (by omega)
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero
      (natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) hpThree)
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  apply markoffReduction_surjective_of_eulerSevenSquareEnvelope_coarseSupport
      p (twoPow756_lt_of_weightedCoarseSupportOpenCutoff_lt hp) (fun _ ↦ T ^ 2)
  · intro d
    simpa [T] using maximalDivisorCountSum_sq_le_divisorSum_sq p d
  · intro d
    calc
      35721 * (T ^ 2) ^ 4 = 35721 * T ^ 8 := by ring
      _ < 8 * p := by
        simpa [T] using
          weighted_35721_mul_divisorSum_pow_eight_lt hpOdd hp

/-- Closed-cutoff form used by the public Comparator theorem. -/
theorem markoffReduction_surjective_of_weightedCoarseSupportBound
    (p : ℕ) (hpPrime : p.Prime)
    (hp : weightedCoarseSupportStrongApproximationCutoff ≤ p) :
    Function.Surjective (markoffReduction p) := by
  apply markoffReduction_surjective_of_weightedCoarseSupportOpenCutoff p hpPrime
  simpa [weightedCoarseSupportStrongApproximationCutoff] using hp

end BGS.Markoff

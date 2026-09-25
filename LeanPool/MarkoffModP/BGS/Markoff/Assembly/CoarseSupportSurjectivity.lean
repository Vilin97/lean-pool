/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenCoarseSupportFrontier
public import LeanPool.MarkoffModP.BGS.Markoff.PreliminaryNumerics
public import LeanPool.MarkoffModP.BGS.NumberTheory.JointNeighborDivisorBound

/-!
# Certificate-free coarse-support surjectivity

The Euler-seven complement argument reduces the last global obstruction to
`35721 * S^4 < 8 * p`.  Taking `S` to be the square of the simultaneous
divisor count and combining this obstruction with the elementary tenth moment
gives an unconditional cutoff without a divisor table.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

/-- The exact open cutoff supplied by the Euler-seven obstruction and the
joint tenth moment for the two neighboring divisor counts. -/
def coarseSupportStrongApproximationOpenCutoff : ℕ :=
  35721 ^ 5 * 2 ^ 1701 * 262145 ^ 4

/-- Closed version of `coarseSupportStrongApproximationOpenCutoff`. -/
def coarseSupportStrongApproximationCutoff : ℕ :=
  coarseSupportStrongApproximationOpenCutoff + 1

private theorem twoPow756_lt_coarseSupportStrongApproximationOpenCutoff :
    2 ^ 756 < coarseSupportStrongApproximationOpenCutoff := by
  calc
    2 ^ 756 < 2 ^ 1701 :=
      Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ = 1 * 2 ^ 1701 * 1 := by ring
    _ ≤ 35721 ^ 5 * 2 ^ 1701 * 262145 ^ 4 := by
      gcongr <;> norm_num

/-- The joint tenth moment rules out the final Euler-seven obstruction above
the exact coarse-support cutoff. -/
theorem preliminary_35721_mul_divisorSum_pow_eight_lt
    {p : ℕ} (hpOdd : Odd p)
    (hp : coarseSupportStrongApproximationOpenCutoff < p) :
    35721 * ((p - 1).divisors.card + (p + 1).divisors.card) ^ 8 < 8 * p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let D := neighboringDivisorSumMomentConstant
  have hpPos : 0 < p := (Nat.zero_le _).trans_lt hp
  have hpSupport : 2 ^ 756 < p :=
    twoPow756_lt_coarseSupportStrongApproximationOpenCutoff.trans hp
  have hpLarge : 794039 ≤ p := by
    have hsmall : 794039 < 2 ^ 20 := by norm_num
    have hpowers : 2 ^ 20 ≤ 2 ^ 756 :=
      Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hmoment : T ^ 10 ≤ D * p := by
    simpa [T, D] using
      card_divisors_pred_add_card_divisors_succ_pow_ten_le hpOdd hpLarge
  by_contra hnot
  have hbad : 8 * p ≤ 35721 * T ^ 8 := by
    exact Nat.le_of_not_gt (by simpa [T] using hnot)
  have hbadPow : (8 * p) ^ 5 ≤ (35721 * T ^ 8) ^ 5 :=
    Nat.pow_le_pow_left hbad 5
  have hmomentPow : (T ^ 10) ^ 4 ≤ (D * p) ^ 4 :=
    Nat.pow_le_pow_left hmoment 4
  have hcombined :
      2 ^ 15 * p ^ 5 ≤ 35721 ^ 5 * D ^ 4 * p ^ 4 := by
    calc
      2 ^ 15 * p ^ 5 = (8 * p) ^ 5 := by ring
      _ ≤ (35721 * T ^ 8) ^ 5 := hbadPow
      _ = 35721 ^ 5 * (T ^ 10) ^ 4 := by ring
      _ ≤ 35721 ^ 5 * (D * p) ^ 4 :=
        Nat.mul_le_mul_left _ hmomentPow
      _ = 35721 ^ 5 * D ^ 4 * p ^ 4 := by ring
  have hcombined' :
      (2 ^ 15 * p) * p ^ 4 ≤
        (35721 ^ 5 * D ^ 4) * p ^ 4 := by
    simpa only [show p ^ 5 = p * p ^ 4 by ring, Nat.mul_assoc] using hcombined
  have hcancel : 2 ^ 15 * p ≤ 35721 ^ 5 * D ^ 4 :=
    Nat.le_of_mul_le_mul_right hcombined' (pow_pos hpPos 4)
  have hfactor :
      35721 ^ 5 * D ^ 4 =
        2 ^ 15 * coarseSupportStrongApproximationOpenCutoff := by
    have hD : D = 2 ^ 429 * 262145 := by
      exact neighboringDivisorSumMomentConstant_eq
    rw [hD]
    rw [mul_pow]
    rw [show (2 ^ 429) ^ 4 = 2 ^ 1716 by
      rw [show (1716 : ℕ) = 429 * 4 by norm_num, pow_mul]]
    rw [show (1716 : ℕ) = 15 + 1701 by norm_num, pow_add]
    unfold coarseSupportStrongApproximationOpenCutoff
    ring
  have hcutoffUpper : p ≤ coarseSupportStrongApproximationOpenCutoff := by
    rw [hfactor] at hcancel
    have hcancel' :
        p * 2 ^ 15 ≤ coarseSupportStrongApproximationOpenCutoff * 2 ^ 15 := by
      simpa only [Nat.mul_comm] using hcancel
    exact Nat.le_of_mul_le_mul_right hcancel' (pow_pos (by norm_num) 15)
  exact (Nat.not_le_of_lt hp) hcutoffUpper

/-- Every joint maximal-divisor square count is bounded by the square of the
simultaneous all-divisor count. -/
theorem maximalDivisorCountSum_sq_le_divisorSum_sq
    (p d : ℕ) :
    maximalDivisorCountSum p (d + 1) ^ 2 ≤
      ((p - 1).divisors.card + (p + 1).divisors.card) ^ 2 := by
  apply Nat.pow_le_pow_left
  unfold maximalDivisorCountSum
  exact Nat.add_le_add
    (maximalDivisorsBelow_card_le_card_divisors (p - 1) (d + 1))
    (maximalDivisorsBelow_card_le_card_divisors (p + 1) (d + 1))

/-- The exact cutoff dominates the support-only threshold required by the
coarse endgame and cage arguments. -/
theorem twoPow756_lt_of_coarseSupportOpenCutoff_lt
    {p : ℕ} (hp : coarseSupportStrongApproximationOpenCutoff < p) :
    2 ^ 756 < p := by
  exact twoPow756_lt_coarseSupportStrongApproximationOpenCutoff.trans hp

/-- Natural Markoff reduction is surjective above the exact certificate-free
coarse-support cutoff. -/
theorem markoffReduction_surjective_of_coarseSupportOpenCutoff
    (p : ℕ) (hpPrime : p.Prime)
    (hp : coarseSupportStrongApproximationOpenCutoff < p) :
    Function.Surjective (markoffReduction p) := by
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpThree : 3 < p := by
    have hsupport := twoPow756_lt_of_coarseSupportOpenCutoff_lt hp
    omega
  have hpOdd : Odd p :=
    hpPrime.odd_of_ne_two (by omega)
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero
      (natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) hpThree)
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  apply markoffReduction_surjective_of_eulerSevenSquareEnvelope_coarseSupport
      p (twoPow756_lt_of_coarseSupportOpenCutoff_lt hp) (fun _ ↦ T ^ 2)
  · intro d
    simpa [T] using maximalDivisorCountSum_sq_le_divisorSum_sq p d
  · intro d
    calc
      35721 * (T ^ 2) ^ 4 = 35721 * T ^ 8 := by ring
      _ < 8 * p := by
        simpa [T] using
          preliminary_35721_mul_divisorSum_pow_eight_lt hpOdd hp

/-- Closed-cutoff form used by the public Comparator theorem. -/
theorem markoffReduction_surjective_of_coarseSupportBound
    (p : ℕ) (hpPrime : p.Prime)
    (hp : coarseSupportStrongApproximationCutoff ≤ p) :
    Function.Surjective (markoffReduction p) := by
  apply markoffReduction_surjective_of_coarseSupportOpenCutoff p hpPrime
  simpa [coarseSupportStrongApproximationCutoff] using hp

end BGS.Markoff

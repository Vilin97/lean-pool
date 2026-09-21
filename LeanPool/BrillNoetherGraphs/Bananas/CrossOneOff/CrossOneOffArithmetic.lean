/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions

/-!
# Arithmetic ranges for the cross one-off transmission block

This file isolates the meaning of "sufficiently long" in the both-off case
of Section 4.4.3 of the twice-marked banana paper.  If `n₁` is the length of the
second marked strand, the integral endpoint of the paper's rational interval

`b ≤ (n₁ / (n₁ - 1)) g`

is `g + g / (n₁ - 1)`.  The length assumption below is the exact uniform
threshold for the corrected block.  The three numerical bounds in Lemma 4.30
belong to three different congruence classes; in particular, its second bound
is not asserted for every integer below the cutoff.
-/

namespace Bananas

open Utilities

/-- The largest natural number in the interval
`b ≤ (n / (n - 1)) g`, for `1 < n`. -/
def crossOneOffCutoff (g n : ℕ) : ℕ := g + g / (n - 1)

/-- A precise, uniform version of the paper's phrase "the first marked strand
is sufficiently long relative to the genus".  The minimal integral threshold
needed for the corrected block is `g + 1 + g / (n₁ - 1) ≤ n₀`. -/
def CrossOneOffLongEnough (g n₀ n₁ : ℕ) : Prop :=
  g + 1 + g / (n₁ - 1) ≤ n₀

/-- The rational cutoff from the paper has the indicated natural-number
form. -/
theorem crossOneOffCutoff_eq_mul_div {g n : ℕ} (hn : 1 < n) :
    crossOneOffCutoff g n = n * g / (n - 1) := by
  unfold crossOneOffCutoff
  have hnPos : 0 < n - 1 := by omega
  have hRewrite : n * g = (n - 1) * g + g := by
    calc
      n * g = ((n - 1) + 1) * g := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = (n - 1) * g + g := by rw [Nat.add_mul, one_mul]
  symm
  rw [hRewrite, Nat.mul_add_div hnPos]

/-- The exact length hypothesis simultaneously implies all three
numerical side conditions used in the corrected three residue cases of Lemma
4.30.  The first conclusion is only needed at positive multiples of `n₁`;
its strict form is the interior bound `b < n₁ (n₀ - 1)`.  The endpoint
allowed by the paper's weak inequality requires a separate rank argument.
The third inequality is stated over `ℤ`, as in the paper; natural subtraction
would silently truncate its negative left-hand side. -/
theorem crossOneOffLongEnough_ranges
    {g n₀ n₁ b : ℕ} (hg : 1 ≤ g) (hn₁ : 1 < n₁)
    (hlong : CrossOneOffLongEnough g n₀ n₁)
    (hb : b ≤ crossOneOffCutoff g n₁) :
    b < n₁ * (n₀ - 1) ∧
      (b % n₁ = n₁ - 1 → b ≤ n₁ * (n₀ - 1 - g) - 1) ∧
      (2 ≤ b → b % n₁ ≠ 0 → b % n₁ ≠ n₁ - 1 →
        (2 : ℤ) * (b / n₁ : ℕ) - (b : ℤ) ≤
          (n₀ : ℤ) - 3 - (g : ℤ)) := by
  change g + 1 + g / (n₁ - 1) ≤ n₀ at hlong
  change b ≤ g + g / (n₁ - 1) at hb
  have hn₁Pos : 0 < n₁ := by omega
  let q := g / (n₁ - 1)
  have hlongQ : g + 1 + q ≤ n₀ := by simpa [q] using hlong
  have hbQ : b ≤ g + q := by simpa [q] using hb
  have hqMul : q * (n₁ - 1) ≤ g := by
    exact Nat.div_mul_le_self g (n₁ - 1)
  have hgLt : g < (q + 1) * (n₁ - 1) := by
    simpa only [q, Nat.mul_comm] using
      (Nat.lt_mul_div_succ g (show 0 < n₁ - 1 by omega))
  have hqTimes : q * n₁ = q * (n₁ - 1) + q := by
    calc
      q * n₁ = q * ((n₁ - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n₁)]
      _ = q * (n₁ - 1) + q := by rw [Nat.mul_add, Nat.mul_one]
  have hSuccTimes : n₁ * (q + 1) =
      (q + 1) * (n₁ - 1) + (q + 1) := by
    calc
      n₁ * (q + 1) = ((n₁ - 1) + 1) * (q + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n₁)]
      _ = (q + 1) * (n₁ - 1) + (q + 1) := by ring
  have hCutDiv : (g + q) / n₁ = q := by
    have hLower : q ≤ (g + q) / n₁ := by
      apply (Nat.le_div_iff_mul_le hn₁Pos).2
      rw [hqTimes]
      omega
    have hUpper : (g + q) / n₁ < q + 1 := by
      apply (Nat.div_lt_iff_lt_mul hn₁Pos).2
      rw [Nat.mul_comm (q + 1) n₁, hSuccTimes]
      omega
    omega
  have hDivLe : b / n₁ ≤ q := by
    rw [← hCutDiv]
    exact Nat.div_le_div_right hb
  constructor
  · have hn₀ : g + g / (n₁ - 1) ≤ n₀ - 1 := by omega
    have hbFirst : b ≤ n₀ - 1 := hb.trans hn₀
    have hn₀Pos : 0 < n₀ - 1 := by
      have hTwo : 2 ≤ g + 1 + q :=
        (Nat.succ_le_succ hg).trans (Nat.le_add_right (g + 1) q)
      have hTwo' : 2 ≤ n₀ := hTwo.trans hlongQ
      omega
    calc
      b ≤ n₀ - 1 := hbFirst
      _ < n₁ * (n₀ - 1) := by
        simpa only [one_mul] using
          (mul_lt_mul_of_pos_right hn₁ hn₀Pos)
  constructor
  · intro hResidue
    have hDecompose : b = (b / n₁) * n₁ + b % n₁ := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod b n₁).symm
    have hDivLt : b / n₁ < q := by
      have hDivLe' : b / n₁ ≤ q := hDivLe
      by_contra hNotLt
      have hDivEq : b / n₁ = q := by omega
      have hbEq : b = q * n₁ + (n₁ - 1) := by
        simpa [hDivEq, hResidue] using hDecompose
      have hExpand : (q + 1) * (n₁ - 1) =
          q * (n₁ - 1) + (n₁ - 1) := by ring
      have hBad : (q + 1) * (n₁ - 1) + q ≤ g + q := by
        calc
          (q + 1) * (n₁ - 1) + q = q * n₁ + (n₁ - 1) := by
            rw [hExpand, hqTimes]
            omega
          _ = b := hbEq.symm
          _ ≤ g + q := hbQ
      have : (q + 1) * (n₁ - 1) ≤ g := Nat.le_of_add_le_add_right hBad
      exact (Nat.not_le_of_gt hgLt) this
    have hGap : q ≤ n₀ - 1 - g := by omega
    have hbSuccEq : b + 1 = (b / n₁ + 1) * n₁ := by
      calc
        b + 1 = ((b / n₁) * n₁ + b % n₁) + 1 :=
          congrArg (fun x ↦ x + 1) hDecompose
        _ = ((b / n₁) * n₁ + (n₁ - 1)) + 1 := by rw [hResidue]
        _ = (b / n₁) * n₁ + n₁ := by
          rw [Nat.add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ n₁)]
        _ = (b / n₁ + 1) * n₁ := by rw [Nat.add_mul, one_mul]
    have hbSucc : b + 1 ≤ q * n₁ := by
      rw [hbSuccEq]
      exact Nat.mul_le_mul_right n₁ hDivLt
    have hProduct : q * n₁ ≤ n₁ * (n₀ - 1 - g) := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right n₁ hGap
    apply Nat.le_sub_one_of_lt
    omega
  · intro hbTwo hNotA hNotB
    have hRemainderPos : 0 < b % n₁ := Nat.pos_of_ne_zero hNotA
    have hDecompose : b = (b / n₁) * n₁ + b % n₁ := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod b n₁).symm
    have hLengthInt : (g : ℤ) + 1 + (q : ℤ) ≤ n₀ := by
      exact_mod_cast hlongQ
    have hRemainderInt : (1 : ℤ) ≤ b % n₁ := by
      exact_mod_cast hRemainderPos
    have hDecomposeInt : (b : ℤ) =
        (b / n₁ : ℕ) * (n₁ : ℤ) + (b % n₁ : ℕ) := by
      exact_mod_cast hDecompose
    by_cases hqZero : q = 0
    · have hDivZero : b / n₁ = 0 := by
        exact Nat.eq_zero_of_le_zero (by simpa [hqZero] using hDivLe)
      have hbTwoInt : (2 : ℤ) ≤ b := by exact_mod_cast hbTwo
      have hLengthZero : (g : ℤ) + 1 ≤ n₀ := by
        simpa [hqZero] using hLengthInt
      rw [hDivZero]
      norm_num
      omega
    · have hqPos : 0 < q := Nat.pos_of_ne_zero hqZero
      have hn₁DiffNonneg : (0 : ℤ) ≤ (n₁ : ℤ) - 2 := by omega
      have hQuotientNonneg : (0 : ℤ) ≤ (b / n₁ : ℕ) := by positivity
      have hProductNonneg : (0 : ℤ) ≤
          (b / n₁ : ℕ) * ((n₁ : ℤ) - 2) :=
        mul_nonneg hQuotientNonneg hn₁DiffNonneg
      have hLeftIdentity :
          (2 : ℤ) * (b / n₁ : ℕ) - (b : ℤ) =
            -((b / n₁ : ℕ) * ((n₁ : ℤ) - 2) +
              (b % n₁ : ℕ)) := by
        rw [hDecomposeInt]
        ring
      have hLeftLe :
          (2 : ℤ) * (b / n₁ : ℕ) - (b : ℤ) ≤ -1 := by
        rw [hLeftIdentity]
        omega
      have hqPosInt : (1 : ℤ) ≤ q := by exact_mod_cast hqPos
      have hRightGe : (-1 : ℤ) ≤ (n₀ : ℤ) - 3 - (g : ℤ) := by
        omega
      exact hLeftLe.trans hRightGe

end Bananas

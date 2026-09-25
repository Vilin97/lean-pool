/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffPositiveRows
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffBlock

/-!
# The affine-period bound for the same-strand one-off marking

The three residue formulas of Lemma 4.23 force every positive affine period
to lie strictly beyond `g + floor(g/(n-1))`, the exact natural-number form of
the paper's rational cutoff `(n/(n-1))g`.
-/

namespace Bananas

open Utilities

private theorem oneOff_cutoff_div
    {g n : ℕ} (hn : 1 < n) :
    crossOneOffCutoff g n / n = g / (n - 1) := by
  let q := g / (n - 1)
  let s := g % (n - 1)
  have hs : s < n := by
    have := Nat.mod_lt g (by omega : 0 < n - 1)
    dsimp [s]
    omega
  have hg : g = q * (n - 1) + s := by
    dsimp [q, s]
    simpa [Nat.mul_comm] using (Nat.div_add_mod g (n - 1)).symm
  have hCut : crossOneOffCutoff g n = q * n + s := by
    unfold crossOneOffCutoff
    change g + q = q * n + s
    rw [hg]
    calc
      q * (n - 1) + s + q = q * (n - 1) + q + s := by omega
      _ = q * ((n - 1) + 1) + s := by rw [Nat.mul_add, Nat.mul_one]
      _ = q * n + s := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hCut]
  calc
    (q * n + s) / n = (s + n * q) / n := by rw [Nat.mul_comm, Nat.add_comm]
    _ = s / n + q := Nat.add_mul_div_left s q (by omega)
    _ = q := by rw [Nat.div_eq_of_lt hs]; simp

private theorem oneOff_cutoff_sub_div
    {g n : ℕ} (hn : 1 < n) :
    crossOneOffCutoff g n - crossOneOffCutoff g n / n = g := by
  rw [oneOff_cutoff_div hn]
  unfold crossOneOffCutoff
  omega

/-- Below the cutoff, a row whose residue is not `n-1` has strictly less
than genus distance from its quotient. -/
private theorem oneOff_sub_div_lt_genus_of_lt_cutoff
    {g n b : ℕ} (hn : 1 < n)
    (hb : b < crossOneOffCutoff g n) (hr : b % n < n - 1) :
    b - b / n < g := by
  have hle := crossOneOff_sub_div_le_genus hn hb.le
  by_contra hNot
  have hEq : b - b / n = g := by omega
  let m := b / n
  let r := b % n
  have hDecompose : b = m * n + r := by
    dsimp [m, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod b n).symm
  have hg : g = m * (n - 1) + r := by
    have hmLeB : m ≤ b := Nat.div_le_self b n
    change b - m = g at hEq
    have hnEq : n = (n - 1) + 1 := by omega
    rw [hnEq, Nat.mul_add, Nat.mul_one] at hDecompose
    omega
  have hmDiv : g / (n - 1) = m := by
    rw [hg]
    calc
      (m * (n - 1) + r) / (n - 1) =
          (r + (n - 1) * m) / (n - 1) := by rw [Nat.mul_comm, Nat.add_comm]
      _ = r / (n - 1) + m := Nat.add_mul_div_left r m (by omega)
      _ = m := by
        rw [Nat.div_eq_of_lt (by simpa [r] using hr)]
        simp
  have hCutEq : crossOneOffCutoff g n = b := by
    unfold crossOneOffCutoff
    rw [hmDiv, hg]
    calc
      m * (n - 1) + r + m = m * (n - 1) + m + r := by omega
      _ = m * ((n - 1) + 1) + r := by rw [Nat.mul_add, Nat.mul_one]
      _ = m * n + r := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = b := hDecompose.symm
  omega

/-- Lemma 4.23's period consequence, in exact integral form.

Bijectivity is not needed here: the forced transmission rows together with
`k`-affinity already exclude every positive `k` at or below the cutoff. -/
theorem oneOff_affine_period_gt_cutoff
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (tau : ℤ → ℤ) (hg : 2 ≤ g) (hk : 0 < k)
    (hLength : 1 < B.length alpha)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hAffine : IsKAffine k tau) :
    crossOneOffCutoff g (B.length alpha) < k := by
  let n := B.length alpha
  let m := k / n
  let r := k % n
  have hn : 1 < n := by simpa [n] using hLength
  have hnPos : 0 < n := by omega
  have hrLt : r < n := by
    dsimp [r]
    exact Nat.mod_lt k hnPos
  have hDecompose : k = m * n + r := by
    dsimp [m, n, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod k (B.length alpha)).symm
  have hZero := transmission_oneOff_zero B alpha tau (by omega) hLength hTau
  have hAtPeriod : tau (k : ℤ) = (k : ℤ) := by
    have h := hAffine 0
    rw [hZero] at h
    simpa using h
  by_contra hNot
  push Not at hNot
  have hNotN : k ≤ crossOneOffCutoff g n := by simpa [n] using hNot
  have hGap : k - m ≤ g := by
    simpa [m] using crossOneOff_sub_div_le_genus hn hNotN
  by_cases hrZero : r = 0
  · have hb : k = m * B.length alpha := by
      simpa [n, hrZero] using hDecompose
    have hRow := transmission_oneOff_multiple B alpha k m tau hLength hb
      (by omega) hTau
    rw [hAtPeriod] at hRow
    have hkm : k = m := by exact_mod_cast hRow
    rw [hkm] at hDecompose hk
    nlinarith
  · by_cases hrLast : r = n - 1
    · have hb : k + 1 = (m + 1) * B.length alpha := by
        rw [show B.length alpha = n by rfl]
        rw [hDecompose, hrLast]
        rw [Nat.add_mul, one_mul]
        omega
      have hCompBound : k + 1 ≤ g + (m + 1) := by omega
      have hgPos : 0 < g := by omega
      have hmSucc : 0 < m + 1 := Nat.zero_lt_succ m
      have hRow := transmission_oneOff_complement B alpha k (m + 1) tau
        hgPos hLength hmSucc hb hCompBound hTau
      rw [hAtPeriod] at hRow
      have hEq : k = g + (m + 1) := by exact_mod_cast hRow
      omega
    · have hrLo : 1 ≤ r := Nat.pos_of_ne_zero hrZero
      have hrHi : r + 1 < n := by omega
      have hRow := transmission_oneOff_positive_residue B alpha k m r tau
        hg hLength (by simpa [n] using hDecompose) hrLo hrHi (by omega) hTau
      rw [hAtPeriod] at hRow
      have hFixed : k = g + 2 * m + 1 - k := by exact_mod_cast hRow
      by_cases hkCut : k = crossOneOffCutoff g n
      · have hCutGap := oneOff_cutoff_sub_div (g := g) (n := n) hn
        rw [← hkCut] at hCutGap
        change k - m = g at hCutGap
        omega
      · have hkLt : k < crossOneOffCutoff g n := by omega
        have hStrictGap : k - m < g := by
          apply oneOff_sub_div_lt_genus_of_lt_cutoff hn hkLt
          simpa [r] using (show r < n - 1 by omega)
        have hnThree : 2 < n := by omega
        have hOne := transmission_oneOff_positive_residue B alpha 1 0 1 tau
          hg hLength (by simp) (by omega) (by simpa [n] using hnThree)
          (by omega) hTau
        have hOneValue : tau 1 = (g : ℤ) := by simpa using hOne
        have hAffineOne := hAffine 1
        rw [hOneValue] at hAffineOne
        by_cases hrNextLast : r + 1 = n - 1
        · have hbNext : k + 1 + 1 = (m + 1) * B.length alpha := by
            rw [show B.length alpha = n by rfl]
            rw [hDecompose]
            rw [Nat.add_mul, one_mul]
            omega
          have hNextBound : k + 1 + 1 ≤ g + (m + 1) := by omega
          have hNext := transmission_oneOff_complement B alpha (k + 1)
            (m + 1) tau (by omega) hLength (by omega) hbNext
              hNextBound hTau
          have hCompare : (g : ℤ) + k = (g + (m + 1) : ℕ) := by
            rw [← hNext]
            simpa [add_assoc, add_comm, add_left_comm] using hAffineOne.symm
          have hkm : k = m + 1 := by exact_mod_cast (by omega :
            (k : ℤ) = (m + 1 : ℕ))
          have hmLeMul : m ≤ m * n := Nat.le_mul_of_pos_right m hnPos
          omega
        · have hrNextHi : r + 1 + 1 < n := by omega
          have hNextDecomp : k + 1 = m * B.length alpha + (r + 1) := by
            rw [show B.length alpha = n by rfl, hDecompose]
            omega
          have hNext := transmission_oneOff_positive_residue B alpha
            (k + 1) m (r + 1) tau hg hLength hNextDecomp (by omega)
              hrNextHi (by omega) hTau
          have hCompare : (g : ℤ) + k =
              (g + 2 * m + 1 - (k + 1) : ℕ) := by
            rw [← hNext]
            simpa [add_assoc, add_comm, add_left_comm] using hAffineOne.symm
          have hkEqM : k = m := by
            exact_mod_cast (show (k : ℤ) = (m : ℤ) by omega)
          have hmLeMul : m ≤ m * n := Nat.le_mul_of_pos_right m hnPos
          omega

end Bananas

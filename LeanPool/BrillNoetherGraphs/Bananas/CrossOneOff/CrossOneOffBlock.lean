/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffTransmission

/-!
# The corrected cross-one-off transmission block

This file assembles the three residue-specific calculations of corrected
Lemma 4.30 over the full interval guaranteed by `CrossOneOffLongEnough`.
-/

namespace Bananas

open Utilities

/-- The corrected value forced in row `b` of the both-off transmission
permutation. -/
def crossOneOffRow (g n b : ℕ) : ℕ :=
  if b % n = 0 then b / n + 1
  else if b % n = n - 1 then g + b / n + 1
  else g + 2 * (b / n) + 2 - b

/-- Every integer in the corrected cutoff interval is at distance at most
`g` from its quotient by the second marked-strand length. -/
theorem crossOneOff_sub_div_le_genus
    {g n b : ℕ} (hn : 1 < n) (hb : b ≤ crossOneOffCutoff g n) :
    b - b / n ≤ g := by
  let q := g / (n - 1)
  let m := b / n
  have hnPos : 0 < n := by omega
  have hnPredPos : 0 < n - 1 := by omega
  have hqMul : q * (n - 1) ≤ g := by
    exact Nat.div_mul_le_self g (n - 1)
  have hbQ : b ≤ g + q := by simpa [crossOneOffCutoff, q] using hb
  have hmLeB : m ≤ b := by
    dsimp [m]
    exact Nat.div_le_self b n
  by_contra hBad
  have hgmLt : g + m < b := by omega
  have hmLtQ : m < q := by omega
  have hDivUpper : b < (m + 1) * n := by
    simpa [m, Nat.mul_comm] using Nat.lt_mul_div_succ b hnPos
  have hExpand : (m + 1) * n = (m + 1) * (n - 1) + (m + 1) := by
    calc
      (m + 1) * n = (m + 1) * ((n - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = (m + 1) * (n - 1) + (m + 1) := by ring
  have hgLt : g < (m + 1) * (n - 1) := by omega
  have hMulLe : (m + 1) * (n - 1) ≤ q * (n - 1) :=
    Nat.mul_le_mul_right (n - 1) hmLtQ
  omega

/-- Corrected Lemma 4.30, uniformly over its valid block.

The printed lemma has incompatible residue conventions and includes the false
boundary `N = 2, b = 1`.  Here the block starts at `b = 2`, uses positive
remainders, and the positive-residue row has the corrected final `+2`. -/
theorem transmission_crossOneOff_block
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (b : ℕ) (tau : ℤ → ℤ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hbLo : 2 ≤ b) (hbHi : b ≤ crossOneOffCutoff g (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (crossOneOffRow g (B.length beta) b : ℕ) := by
  let n := B.length beta
  let n0 := B.length alpha
  let m := b / n
  let r := b % n
  have hn : 1 < n := by simpa [n] using hBeta
  have hnPos : 0 < n := by omega
  have hrLt : r < n := by
    dsimp [r]
    exact Nat.mod_lt b hnPos
  have hDecompose : b = m * n + r := by
    dsimp [m, n, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod b (B.length beta)).symm
  have hGap : b - m ≤ g := by
    simpa [m, n] using crossOneOff_sub_div_le_genus hn hbHi
  have hmLeB : m ≤ b := by
    dsimp [m]
    exact Nat.div_le_self b n
  have hbm : b ≤ g + m := by omega
  have hRanges := crossOneOffLongEnough_ranges
    (g := g) (n₀ := n0) (n₁ := n) (b := b)
    (by omega) hn (by simpa [n0, n] using hLong) (by simpa [n] using hbHi)
  by_cases hrZero : r = 0
  · have hbMultiple : b = m * B.length beta := by simpa [n, hrZero] using hDecompose
    have hmPos : 1 ≤ m := by
      rw [hbMultiple] at hbLo
      nlinarith
    have hmInterior : m + 1 < B.length alpha := by
      have hStrict := hRanges.1
      rw [hbMultiple] at hStrict
      have hmLt : m < n0 - 1 := by
        apply (Nat.mul_lt_mul_left hnPos).mp
        simpa [n, Nat.mul_comm] using hStrict
      simpa [n0] using (show m + 1 < n0 by omega)
    let c := g + m - b
    have hc : c ≤ g - 1 := by
      dsimp [c]
      have : 1 ≤ b - m := by
        rw [hbMultiple]
        have hTwom : m * 2 ≤ m * B.length beta :=
          Nat.mul_le_mul_left m (by omega)
        omega
      omega
    have hRow := transmission_crossOneOff_multiple B alpha beta b m c tau
      hg hab hbMultiple hmPos hmInterior (by omega)
      hc hbm rfl hTau
    simpa [crossOneOffRow, r, n, hrZero, m] using hRow
  · by_cases hrLast : r = n - 1
    · let mp := m + 1
      have hbComplement : b + 1 = mp * B.length beta := by
        rw [show B.length beta = n by rfl]
        calc
          b + 1 = (m * n + (n - 1)) + 1 := by rw [hDecompose, hrLast]
          _ = m * n + n := by omega
          _ = (m + 1) * n := by rw [Nat.add_mul, one_mul]
          _ = mp * n := by rfl
      have hProductEq : mp * (n - 1) = b - m := by
        have hnExpand : m * n = m * (n - 1) + m := by
          calc
            m * n = m * ((n - 1) + 1) := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
            _ = m * (n - 1) + m := by rw [Nat.mul_add, Nat.mul_one]
        calc
          mp * (n - 1) = m * (n - 1) + (n - 1) := by
            dsimp [mp]
            ring
          _ = (m * n + (n - 1)) - m := by rw [hnExpand]; omega
          _ = b - m := by rw [hDecompose, hrLast]
      have hProduct : mp * (B.length beta - 1) ≤ g := by
        simpa [n, hProductEq] using hGap
      have hProductTwo : 2 ≤ mp * (B.length beta - 1) := by
        have hPos : 1 ≤ mp * (B.length beta - 1) := by
          apply Nat.one_le_iff_ne_zero.mpr
          exact Nat.mul_ne_zero (by simp [mp]) (by omega)
        have hNeOne : mp * (B.length beta - 1) ≠ 1 := by
          intro hOne
          have hBoundary :=
            (crossOneOff_complement_boundary_iff_length_two
              (g := g) (N := B.length beta) (m := mp) (b := b)
              (by omega) (by simp [mp]) hProduct hbComplement).mp hOne
          omega
        omega
      have hMpInterior : g + mp < B.length alpha := by
        have hBound := hRanges.2.1 (by simpa [r, n] using hrLast)
        have hSucc : mp * n = b + 1 := by
          simpa [n] using hbComplement.symm
        have hMulBound : mp * n ≤ n * (n0 - 1 - g) := by omega
        have hMpLe : mp ≤ n0 - 1 - g := by
          exact Nat.le_of_mul_le_mul_left
            (by simpa [Nat.mul_comm] using hMulBound) hnPos
        have hMpPos : 1 ≤ mp := by simp [mp]
        simpa [n0] using (show g + mp < n0 by omega)
      let c := g - mp * (B.length beta - 1)
      have hc : c < g - 1 := by
        dsimp [c]
        omega
      have hRow := transmission_crossOneOff_complement_residue
        B alpha beta b mp c tau hg hab (by simp [mp]) hbComplement hMpInterior
        (by omega) hc hProduct rfl hTau
      have hnPred : n - 1 ≠ 0 := by omega
      simpa [crossOneOffRow, r, n, hrZero, hrLast, m, mp, hnPred,
        add_assoc] using hRow
    · have hrPos : 1 ≤ r := Nat.pos_of_ne_zero hrZero
      have hrHi : r + 1 < B.length beta := by
        change r + 1 < n
        omega
      have hDiffTwo : 2 ≤ b - m := by
        rw [hDecompose]
        by_cases hmZero : m = 0
        · rw [hmZero] at hDecompose
          simp only [zero_mul, zero_add] at hDecompose
          omega
        · have hmPos : 1 ≤ m := Nat.pos_of_ne_zero hmZero
          have hTwom : m * 2 ≤ m * n := Nat.mul_le_mul_left m (by omega)
          omega
      let a := g + 2 * m + 2 - b
      let c := g + m - b
      have haCandidate : b ≤ g + 2 * m + 2 := by omega
      have haLo : 2 ≤ a := by
        dsimp [a]
        omega
      have haHi : a < B.length alpha := by
        have hInt : (2 : ℤ) * (m : ℕ) - (b : ℤ) ≤
            (n0 : ℕ) - 3 - (g : ℤ) := by
          simpa [m, n0, n, r] using hRanges.2.2 hbLo
            (by simpa [r] using hrZero) (by simpa [r, n] using hrLast)
        have haCast : (a : ℤ) =
            (g : ℤ) + 2 * (m : ℕ) + 2 - (b : ℤ) := by
          dsimp [a]
          omega
        have haHi' : a < n0 := by omega
        simpa [n0] using haHi'
      have hc : c ≤ g - 2 := by
        dsimp [c]
        omega
      have hRow := transmission_crossOneOff_positive_residue
        B alpha beta b m r c tau hg hab (by simpa [n] using hDecompose)
        hrPos hrHi haCandidate (by simpa [a] using Nat.le_of_lt haHi)
        (by simpa [a] using haLo) (by simpa [a] using haHi) hc hbm rfl hTau
      simpa [crossOneOffRow, r, n, hrZero, hrLast, m, a] using hRow

end Bananas

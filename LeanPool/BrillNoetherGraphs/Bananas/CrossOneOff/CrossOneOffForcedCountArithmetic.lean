/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiniteRows
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality

/-!
# Arithmetic count for the corrected cross-one-off block

This file proves the pure finite-row count left open by
`crossOneOff_corrected_inversion_lower_bound_of_finiteRows`.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Positions congruent to `-1` modulo `n`, indexed from zero. -/
def crossOneOffHighIndex (n i : ℕ) : ℕ := i * n + (n - 1)

/-- Positive multiples of `n`, indexed from zero. -/
def crossOneOffLowIndex (n i : ℕ) : ℕ := (i + 1) * n

/-- Interior-residue positions in the block, starting at position `2`.
The shift by `t+1` omits the unavailable position `1`. -/
def crossOneOffMiddleIndex (n t : ℕ) : ℕ :=
  t + 2 + 2 * ((t + 1) / (n - 2))

theorem crossOneOffMiddleIndex_strictMono {n : ℕ} (_hn : 2 < n) :
    StrictMono (crossOneOffMiddleIndex n) := by
  apply strictMono_nat_of_lt_succ
  intro t
  unfold crossOneOffMiddleIndex
  have hDiv : (t + 1) / (n - 2) ≤ (t + 1 + 1) / (n - 2) :=
    Nat.div_le_div_right (by omega)
  omega

theorem crossOneOffHighIndex_data
    {g n F i : ℕ} (hn : 2 < n) (hF : F = g / (n - 1)) (hi : i < F) :
    2 ≤ crossOneOffHighIndex n i ∧
      crossOneOffHighIndex n i ≤ crossOneOffCutoff g n ∧
      crossOneOffRow g n (crossOneOffHighIndex n i) = g + i + 1 := by
  have hnPos : 0 < n := by omega
  have hnPred : n - 1 < n := by omega
  have hiFn : (i + 1) * n ≤ F * n := Nat.mul_le_mul_right n (by omega)
  have hFn : F * n ≤ g + F := by
    have hMul : F * (n - 1) ≤ g := by
      rw [hF]
      exact Nat.div_mul_le_self g (n - 1)
    have hnEq : n = (n - 1) + 1 := by omega
    rw [hnEq, Nat.mul_add, Nat.mul_one]
    omega
  have hIndexEq : crossOneOffHighIndex n i = i * n + (n - 1) := rfl
  have hMod : crossOneOffHighIndex n i % n = n - 1 := by
    rw [hIndexEq]
    calc
      (i * n + (n - 1)) % n = (n * i + (n - 1)) % n := by rw [Nat.mul_comm]
      _ = (n - 1) % n := Nat.mul_add_mod_self_left n i (n - 1)
      _ = n - 1 := Nat.mod_eq_of_lt hnPred
  have hDiv : crossOneOffHighIndex n i / n = i := by
    rw [hIndexEq]
    calc
      (i * n + (n - 1)) / n = ((n - 1) + n * i) / n := by
        congr 1
        rw [Nat.mul_comm i n, Nat.add_comm]
      _ = (n - 1) / n + i := Nat.add_mul_div_left (n - 1) i hnPos
      _ = i := by rw [Nat.div_eq_of_lt hnPred]; omega
  have hHighLe : crossOneOffHighIndex n i ≤ (i + 1) * n := by
    unfold crossOneOffHighIndex
    rw [Nat.add_mul, one_mul]
    omega
  have hnPredNe : n - 1 ≠ 0 := by omega
  refine ⟨by unfold crossOneOffHighIndex; omega, ?_, ?_⟩
  · simpa [crossOneOffCutoff, hF] using hHighLe.trans (hiFn.trans hFn)
  · simp [crossOneOffRow, hMod, hDiv, hnPredNe]

theorem crossOneOffLowIndex_data
    {g n F i : ℕ} (hn : 2 < n) (hF : F = g / (n - 1)) (hi : i < F) :
    2 ≤ crossOneOffLowIndex n i ∧
      crossOneOffLowIndex n i ≤ crossOneOffCutoff g n ∧
      crossOneOffRow g n (crossOneOffLowIndex n i) = i + 2 := by
  have hMul : F * (n - 1) ≤ g := by
    rw [hF]
    exact Nat.div_mul_le_self g (n - 1)
  have hiFn : (i + 1) * n ≤ F * n := Nat.mul_le_mul_right n (by omega)
  have hnEq : n = (n - 1) + 1 := by omega
  have hFn : F * n ≤ g + F := by
    rw [hnEq, Nat.mul_add, Nat.mul_one]
    omega
  have hMod : crossOneOffLowIndex n i % n = 0 := by
    simp [crossOneOffLowIndex]
  have hDiv : crossOneOffLowIndex n i / n = i + 1 := by
    unfold crossOneOffLowIndex
    exact Nat.mul_div_left (i + 1) (by omega)
  refine ⟨by unfold crossOneOffLowIndex; nlinarith, ?_, ?_⟩
  · simpa [crossOneOffCutoff, hF, crossOneOffLowIndex] using hiFn.trans hFn
  · simp [crossOneOffRow, hMod, hDiv]

theorem crossOneOffMiddleIndex_data
    {g n F H t : ℕ} (_hg : 2 ≤ g) (hn : 2 < n)
    (hF : F = g / (n - 1)) (hH : H = g - F - 1) (ht : t < H) :
    2 ≤ crossOneOffMiddleIndex n t ∧
      crossOneOffMiddleIndex n t ≤ crossOneOffCutoff g n ∧
      crossOneOffRow g n (crossOneOffMiddleIndex n t) = g - t ∧
      F + 2 ≤ g - t := by
  let q := (t + 1) / (n - 2)
  let s := (t + 1) % (n - 2)
  let r := s + 1
  have hdPos : 0 < n - 2 := by omega
  have hsLt : s < n - 2 := by
    dsimp [s]
    exact Nat.mod_lt _ hdPos
  have htDecompose : t + 1 = q * (n - 2) + s := by
    dsimp [q, s]
    simpa [Nat.mul_comm] using (Nat.div_add_mod (t + 1) (n - 2)).symm
  have hIndex : crossOneOffMiddleIndex n t = q * n + r := by
    unfold crossOneOffMiddleIndex
    change t + 2 + 2 * q = q * n + r
    have hnEq : n = (n - 2) + 2 := by omega
    have hqn : q * n = q * (n - 2) + 2 * q := by
      calc
        q * n = q * ((n - 2) + 2) := congrArg (q * ·) hnEq
        _ = q * (n - 2) + 2 * q := by
          rw [Nat.mul_add]
          exact congrArg (q * (n - 2) + ·) (Nat.mul_comm q 2)
    rw [hqn]
    dsimp [r]
    omega
  have hMod : crossOneOffMiddleIndex n t % n = r := by
    rw [hIndex]
    have hrLt : r < n := by dsimp [r]; omega
    calc
      (q * n + r) % n = (n * q + r) % n := by rw [Nat.mul_comm]
      _ = r % n := Nat.mul_add_mod_self_left n q r
      _ = r := Nat.mod_eq_of_lt hrLt
  have hDiv : crossOneOffMiddleIndex n t / n = q := by
    rw [hIndex]
    have hrLt : r < n := by dsimp [r]; omega
    calc
      (q * n + r) / n = (r + n * q) / n := by
        congr 1
        rw [Nat.mul_comm q n, Nat.add_comm]
      _ = r / n + q := Nat.add_mul_div_left r q (by omega)
      _ = q := by rw [Nat.div_eq_of_lt hrLt]; omega
  have hrZero : r ≠ 0 := by dsimp [r]; omega
  have hrLast : r ≠ n - 1 := by dsimp [r]; omega
  have htLe : t + 1 ≤ g - F - 1 := by omega
  have hMul : F * (n - 1) ≤ g := by
    rw [hF]
    exact Nat.div_mul_le_self g (n - 1)
  have hRem : g < (F + 1) * (n - 1) := by
    simpa [hF, Nat.mul_comm] using
      (Nat.lt_mul_div_succ g (by omega : 0 < n - 1))
  have hqLe : q ≤ F := by
    have hnPredEq : n - 1 = (n - 2) + 1 := by omega
    rw [hnPredEq, Nat.mul_add, Nat.mul_one] at hRem
    rw [Nat.add_mul, one_mul] at hRem
    have huLt : t + 1 < (F + 1) * (n - 2) := by
      rw [Nat.add_mul, one_mul]
      omega
    have hqLt : q < F + 1 := by
      apply (Nat.div_lt_iff_lt_mul hdPos).2
      simpa [q] using huLt
    omega
  have hBound : crossOneOffMiddleIndex n t ≤ g + F := by
    unfold crossOneOffMiddleIndex
    omega
  have hMiddle : crossOneOffRow g n (crossOneOffMiddleIndex n t) = g - t := by
    simp [crossOneOffRow, hMod, hDiv, hrZero, hrLast]
    unfold crossOneOffMiddleIndex
    omega
  refine ⟨by unfold crossOneOffMiddleIndex; omega, ?_, hMiddle, ?_⟩
  · simpa [crossOneOffCutoff, hF] using hBound
  · omega

end Bananas

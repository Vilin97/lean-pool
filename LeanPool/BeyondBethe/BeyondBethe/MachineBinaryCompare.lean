/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinarySub

/-!
# Polynomial-time comparison of canonical binary naturals

Truncated subtraction is zero exactly when the left operand is at most the
right.  This gives compact comparison machines while reusing the fully
verified borrow scan.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineBinaryNatLeBit (word : List Bool) : List Bool :=
  machineIfEmpty (machineBinarySubBits word) [true] [false]

def machineBinaryNatLtBit (word : List Bool) : List Bool :=
  let swapped := pair (machinePairSecond word) (machinePairFirst word)
  machineIfEmpty (machineBinarySubBits swapped) [false] [true]

def machineBinaryNatEqBit (word : List Bool) : List Bool :=
  machineAndBit (machineBinaryNatLeBit word)
    (machineBinaryNatLeBit
      (pair (machinePairSecond word) (machinePairFirst word)))

theorem machineBinaryNatLeBit_mem_FP :
    machineBinaryNatLeBit ∈ Complexity.FP := by
  simpa only [machineBinaryNatLeBit] using!
    machineIfEmpty_mem_FP machineBinarySubBits_mem_FP
      (machineConst_mem_FP [true]) (machineConst_mem_FP [false])

theorem machineBinaryNatLtBit_mem_FP :
    machineBinaryNatLtBit ∈ Complexity.FP := by
  have hswap : (fun word => pair (machinePairSecond word)
      (machinePairFirst word)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP
  have hsub := machineCompose_mem_FP hswap machineBinarySubBits_mem_FP
  simpa only [machineBinaryNatLtBit] using!
    machineIfEmpty_mem_FP hsub (machineConst_mem_FP [false])
      (machineConst_mem_FP [true])

theorem machineBinaryNatEqBit_mem_FP :
    machineBinaryNatEqBit ∈ Complexity.FP := by
  have hswap : (fun word => pair (machinePairSecond word)
      (machinePairFirst word)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP
  have hswappedLe := machineCompose_mem_FP hswap machineBinaryNatLeBit_mem_FP
  simpa only [machineBinaryNatEqBit] using!
    machineAndBit_mem_FP machineBinaryNatLeBit_mem_FP hswappedLe

theorem machineBinaryNatLeBit_pair_natBits (lhs rhs : ℕ) :
    machineBinaryNatLeBit (pair lhs.bits rhs.bits) = [decide (lhs ≤ rhs)] := by
  rw [machineBinaryNatLeBit, machineBinarySubBits_pair_natBits]
  by_cases h : lhs ≤ rhs
  · have hzero : lhs - rhs = 0 := Nat.sub_eq_zero_of_le h
    rw [hzero]
    simp [h]
  · have hpos : 0 < lhs - rhs := Nat.sub_pos_of_lt (Nat.lt_of_not_ge h)
    cases hbits : (lhs - rhs).bits with
    | nil =>
        have hlen : (lhs - rhs).bits.length = 0 := by rw [hbits]; rfl
        have hsize : (lhs - rhs).size = 0 := by
          simpa only [Nat.size_eq_bits_len] using! hlen
        have := Nat.size_eq_zero.mp hsize
        omega
    | cons bit rest => simp [hbits, h]

theorem machineBinaryNatLtBit_pair_natBits (lhs rhs : ℕ) :
    machineBinaryNatLtBit (pair lhs.bits rhs.bits) = [decide (lhs < rhs)] := by
  simp only [machineBinaryNatLtBit, machinePairFirst_pair,
    machinePairSecond_pair, machineBinarySubBits_pair_natBits]
  by_cases h : lhs < rhs
  · have hpos : 0 < rhs - lhs := Nat.sub_pos_of_lt h
    cases hbits : (rhs - lhs).bits with
    | nil =>
        have hlen : (rhs - lhs).bits.length = 0 := by rw [hbits]; rfl
        have hsize : (rhs - lhs).size = 0 := by
          simpa only [Nat.size_eq_bits_len] using! hlen
        have := Nat.size_eq_zero.mp hsize
        omega
    | cons bit rest => simp [hbits, h]
  · have hzero : rhs - lhs = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
    rw [hzero]
    simp [h]

theorem machineBinaryNatEqBit_pair_natBits (lhs rhs : ℕ) :
    machineBinaryNatEqBit (pair lhs.bits rhs.bits) = [decide (lhs = rhs)] := by
  simp only [machineBinaryNatEqBit, machinePairFirst_pair,
    machinePairSecond_pair, machineBinaryNatLeBit_pair_natBits]
  by_cases h : lhs = rhs
  · subst rhs
    simp
  · have hnotboth : ¬ (lhs ≤ rhs ∧ rhs ≤ lhs) := by
      exact fun hboth => h (Nat.le_antisymm hboth.1 hboth.2)
    rcases not_and_or.mp hnotboth with hleft | hright
    · simp [h, hleft]
    · simp [h, hright]

end BeyondBethe

/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryDivision
import LeanPool.BeyondBethe.BeyondBethe.MachineTrimHighZeros

/-!
# Polynomial-time binary gcd

This is a fixed-budget Euclidean algorithm on canonical little-endian words.
The input components are canonicalized first.  Each step obtains its remainder
from the verified long-division machine, and two iterations per bit of the
initial second component suffice by the previously proved Euclid bound.
-/

namespace BeyondBethe

open Complexity

def machineBinaryRemainderBits (word : List Bool) : List Bool :=
  machinePairSecond (machineBinaryDivModBits word)

def machineBinaryGcdStep (state : List Bool) : List Bool :=
  machineIfEmpty (machinePairSecond state) state
    (pair (machinePairSecond state) (machineBinaryRemainderBits state))

def machineBinaryGcdInit (word : List Bool) : List Bool :=
  pair (machineTrimHighZeros (machinePairFirst word))
    (machineTrimHighZeros (machinePairSecond word))

def machineBinaryGcdRuler (word : List Bool) : List Bool :=
  let second := machineTrimHighZeros (machinePairSecond word)
  second ++ second

def machineBinaryGcdWidth (word : List Bool) : List Bool :=
  let padded := List.replicate 16 false ++ word
  List.replicate (padded.length * padded.length) false

def machineBinaryGcdFinalState (word : List Bool) : List Bool :=
  machineBinaryGcdStep^[(machineBinaryGcdRuler word).length]
    (machineBinaryGcdInit word)

def machineBinaryGcdBits (word : List Bool) : List Bool :=
  machinePairFirst (machineBinaryGcdFinalState word)

theorem machineBinaryRemainderBits_mem_FP :
    machineBinaryRemainderBits ∈ Complexity.FP := by
  simpa only [machineBinaryRemainderBits] using
    machineCompose_mem_FP machineBinaryDivModBits_mem_FP
      machinePairSecond_mem_FP

theorem machineBinaryGcdStep_mem_FP :
    machineBinaryGcdStep ∈ Complexity.FP := by
  have hpair : (fun state => pair (machinePairSecond state)
      (machineBinaryRemainderBits state)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairSecond_mem_FP
      machineBinaryRemainderBits_mem_FP
  simpa only [machineBinaryGcdStep] using
    machineIfEmpty_mem_FP machinePairSecond_mem_FP id_mem_FP hpair

theorem machineBinaryGcdInit_mem_FP :
    machineBinaryGcdInit ∈ Complexity.FP := by
  have hfirst := machineCompose_mem_FP machinePairFirst_mem_FP
    machineTrimHighZeros_mem_FP
  have hsecond := machineCompose_mem_FP machinePairSecond_mem_FP
    machineTrimHighZeros_mem_FP
  simpa only [machineBinaryGcdInit] using machinePair_mem_FP hfirst hsecond

theorem machineBinaryGcdRuler_mem_FP :
    machineBinaryGcdRuler ∈ Complexity.FP := by
  have hsecond := machineCompose_mem_FP machinePairSecond_mem_FP
    machineTrimHighZeros_mem_FP
  simpa only [machineBinaryGcdRuler] using machineAppend_mem_FP hsecond hsecond

theorem machineBinaryGcdWidth_mem_FP :
    machineBinaryGcdWidth ∈ Complexity.FP := by
  let padded : List Bool → List Bool :=
    fun word => List.replicate 16 false ++ word
  have hpadded : padded ∈ Complexity.FP :=
    machineAppend_mem_FP (machineConst_mem_FP (List.replicate 16 false))
      id_mem_FP
  simpa only [machineBinaryGcdWidth, padded] using
    Cobham.mulLenFn_mem_FP hpadded hpadded

theorem machineBinaryGcdStep_pair_natBits (a b : ℕ) :
    machineBinaryGcdStep (pair a.bits b.bits) =
      pair (binaryEuclidStep (a, b)).1.bits
        (binaryEuclidStep (a, b)).2.bits := by
  rw [binaryEuclidStep_eq]
  by_cases hb : b = 0
  · subst b
    simp [machineBinaryGcdStep]
  · simp only [machineBinaryGcdStep, machinePairSecond_pair]
    rw [machineIfEmpty_of_ne_nil b.bits (pair a.bits b.bits)
      (pair b.bits (machineBinaryRemainderBits (pair a.bits b.bits)))
      (natBits_ne_nil_of_ne_zero hb)]
    simp only [machineBinaryRemainderBits,
      machineBinaryDivModBits_pair_natBits, machinePairSecond_pair,
      hb, ite_false, Prod.fst, Prod.snd]

def MachineBinaryGcdReachable (word state : List Bool) : Prop :=
  ∃ a b : ℕ,
    state = pair a.bits b.bits ∧
    a.bits.length ≤ word.length ∧ b.bits.length ≤ word.length

theorem machineBinaryGcdInit_reachable (word : List Bool) :
    MachineBinaryGcdReachable word (machineBinaryGcdInit word) := by
  let a := Nat.fromBitsLE (machinePairFirst word)
  let b := Nat.fromBitsLE (machinePairSecond word)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simp only [machineBinaryGcdInit, machineTrimHighZeros_eq,
      BinaryRippleSub.trimHighZeros_eq_natBits_internal, a, b]
  · have htrim := binaryTrimHighZeros_length_le (machinePairFirst word)
    rw [BinaryRippleSub.trimHighZeros_eq_natBits_internal] at htrim
    exact htrim.trans (machinePairFirst_length_le word)
  · have htrim := binaryTrimHighZeros_length_le (machinePairSecond word)
    rw [BinaryRippleSub.trimHighZeros_eq_natBits_internal] at htrim
    exact htrim.trans (machinePairSecond_length_le word)

theorem machineBinaryGcdStep_reachable {word state : List Bool}
    (hstate : MachineBinaryGcdReachable word state) :
    MachineBinaryGcdReachable word (machineBinaryGcdStep state) := by
  obtain ⟨a, b, rfl, ha, hb⟩ := hstate
  rw [machineBinaryGcdStep_pair_natBits]
  by_cases hbzero : b = 0
  · subst b
    refine ⟨a, 0, ?_, ha, by simp⟩
    simp [binaryEuclidStep]
  · refine ⟨b, a % b, ?_, hb, ?_⟩
    · simp [binaryEuclidStep, hbzero, binaryLongDiv_eq_div_mod]
    · have hsize := Nat.size_le_size (Nat.mod_le a b)
      have hbits : (a % b).bits.length ≤ a.bits.length := by
        simpa only [Nat.size_eq_bits_len] using hsize
      exact hbits.trans ha

theorem machineBinaryGcdIterate_reachable (word : List Bool) :
    ∀ steps : ℕ,
      MachineBinaryGcdReachable word
        (machineBinaryGcdStep^[steps] (machineBinaryGcdInit word)) := by
  intro steps
  induction steps with
  | zero => exact machineBinaryGcdInit_reachable word
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact machineBinaryGcdStep_reachable ih

theorem machineBinaryGcdIterate_length_le_width
    (word : List Bool) (steps : ℕ)
    (_hsteps : steps ≤ (machineBinaryGcdRuler word).length) :
    (machineBinaryGcdStep^[steps] (machineBinaryGcdInit word)).length ≤
      (machineBinaryGcdWidth word).length := by
  obtain ⟨a, b, hstate, ha, hb⟩ :=
    machineBinaryGcdIterate_reachable word steps
  rw [hstate]
  simp only [pair_length, machineBinaryGcdWidth, List.length_replicate,
    List.length_append]
  nlinarith

theorem machineBinaryGcdFinalState_mem_FP :
    machineBinaryGcdFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBinaryGcdStep_mem_FP
    machineBinaryGcdInit_mem_FP machineBinaryGcdRuler_mem_FP
    machineBinaryGcdWidth_mem_FP machineBinaryGcdIterate_length_le_width

theorem machineBinaryGcdBits_mem_FP :
    machineBinaryGcdBits ∈ Complexity.FP := by
  simpa only [machineBinaryGcdBits] using
    machineCompose_mem_FP machineBinaryGcdFinalState_mem_FP
      machinePairFirst_mem_FP

theorem machineBinaryGcdIterate_pair_natBits (steps a b : ℕ) :
    machineBinaryGcdStep^[steps] (pair a.bits b.bits) =
      let final := binaryEuclidIterate steps (a, b)
      pair final.1.bits final.2.bits := by
  induction steps generalizing a b with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply, machineBinaryGcdStep_pair_natBits]
      simpa only [binaryEuclidIterate] using
        ih (binaryEuclidStep (a, b)).1 (binaryEuclidStep (a, b)).2

theorem machineBinaryGcdBits_eq (word : List Bool) :
    machineBinaryGcdBits word =
      (Nat.gcd (Nat.fromBitsLE (machinePairFirst word))
        (Nat.fromBitsLE (machinePairSecond word))).bits := by
  let a := Nat.fromBitsLE (machinePairFirst word)
  let b := Nat.fromBitsLE (machinePairSecond word)
  simp only [machineBinaryGcdBits, machineBinaryGcdFinalState,
    machineBinaryGcdRuler, machineBinaryGcdInit,
    machineTrimHighZeros_eq,
    BinaryRippleSub.trimHighZeros_eq_natBits_internal,
    List.length_append, a, b]
  rw [show b.bits.length + b.bits.length = 2 * b.size by
    simp [Nat.size_eq_bits_len, two_mul]]
  rw [machineBinaryGcdIterate_pair_natBits]
  simp only [machinePairFirst_pair]
  change (binaryEuclidBounded
      (Nat.fromBitsLE (machinePairFirst word))
      (Nat.fromBitsLE (machinePairSecond word))).bits = _
  rw [binaryEuclidBounded_eq_gcd]

theorem machineBinaryGcdBits_pair_natBits (a b : ℕ) :
    machineBinaryGcdBits (pair a.bits b.bits) = (Nat.gcd a b).bits := by
  rw [machineBinaryGcdBits_eq]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    Nat.fromBitsLE_bits]

end BeyondBethe

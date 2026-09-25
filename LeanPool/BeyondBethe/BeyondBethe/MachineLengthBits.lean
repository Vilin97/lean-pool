/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryAddSemantics

/-!
# Binary encoding of an input length

This bounded counter converts the length of a bitstring to ordinary
little-endian binary.  It is useful whenever a later machine needs the value
of a unary ruler without expanding an unrestricted binary integer.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineLengthBitsStep (acc : List Bool) : List Bool :=
  machineBinaryAddBits (pair acc [true])

def machineLengthBitsWidth (word : List Bool) : List Bool := word

def machineLengthBits (word : List Bool) : List Bool :=
  (machineLengthBitsStep)^[word.length] []

theorem machineLengthBitsStep_mem_FP :
    machineLengthBitsStep ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP id_mem_FP (machineConst_mem_FP [true])
  simpa only [machineLengthBitsStep] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineLengthBitsWidth_mem_FP :
    machineLengthBitsWidth ∈ Complexity.FP := id_mem_FP

theorem machineLengthBitsIterate_encode : ∀ k,
    (machineLengthBitsStep)^[k] [] = k.bits := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, machineLengthBitsStep]
      have hone : ([true] : List Bool) = (1 : ℕ).bits := by rfl
      rw [hone, machineBinaryAddBits_pair_natBits]

private theorem lengthBits_natBits_length_le_self (k : ℕ) :
    k.bits.length ≤ k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr k.lt_two_pow_self

theorem machineLengthBitsIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (hiterations : iterations ≤ word.length) :
    ((machineLengthBitsStep)^[iterations] []).length ≤
      (machineLengthBitsWidth word).length := by
  rw [machineLengthBitsIterate_encode]
  exact (lengthBits_natBits_length_le_self iterations).trans hiterations

theorem machineLengthBits_mem_FP : machineLengthBits ∈ Complexity.FP := by
  simpa only [machineLengthBits] using!
    Cobham.iterate_mem_FP machineLengthBitsStep_mem_FP
      (machineConst_mem_FP []) id_mem_FP machineLengthBitsWidth_mem_FP
      machineLengthBitsIterate_length_le_width

@[simp] theorem machineLengthBits_encode (word : List Bool) :
    machineLengthBits word = word.length.bits := by
  rw [machineLengthBits, machineLengthBitsIterate_encode]

end BeyondBethe

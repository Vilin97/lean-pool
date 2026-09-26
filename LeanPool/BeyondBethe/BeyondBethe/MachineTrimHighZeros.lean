/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBitAssembly
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs

/-!
# Polynomial-time canonicalization of little-endian natural words

A bit-graph machine may emit a polynomially bounded fixed-width word.  The
public rational encoding uses canonical `Nat.bits`, so redundant high zeroes
must be removed.  The implementation below is a length-bounded Cobham fold,
not a semantic list primitive assumed to be efficient.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extract the accumulator from the recursive fold state used to trim high zero bits. -/
def machineTrimAcc (state : List Bool) : List Bool :=
  machinePairSecond (machinePairFirst state)

/-- Discard a false bit when the trimming accumulator is empty; otherwise prepend it. -/
def machineTrimFalseStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineTrimAcc state) []
    (false :: machineTrimAcc state)

/-- Prepend a true bit to the trimming accumulator. -/
def machineTrimTrueStep (state : List Bool) : List Bool :=
  true :: machineTrimAcc state

/-- Run the high-zero trimming fold with output clamped to the packed input length. -/
def machineTrimPacked (packed : List Bool) : List Bool :=
  Cobham.recFoldClamp machineTrimFalseStep machineTrimTrueStep
    packed.length []
    (machinePairFirst packed) (machinePairSecond packed)

/-- Trim high zero bits by running the packed trimming fold with an empty auxiliary word. -/
def machineTrimHighZeros (word : List Bool) : List Bool :=
  machineTrimPacked (pair [] word)

theorem machineTrimAcc_mem_FP : machineTrimAcc ∈ Complexity.FP := by
  simpa only [machineTrimAcc] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machinePairSecond_mem_FP

theorem machineTrimFalseStep_mem_FP :
    machineTrimFalseStep ∈ Complexity.FP := by
  have hcons : (fun state => false :: machineTrimAcc state) ∈
      Complexity.FP :=
    machineCompose_mem_FP machineTrimAcc_mem_FP
      (machinePrepend_mem_FP false)
  exact machineIfEmpty_mem_FP machineTrimAcc_mem_FP
    (machineConst_mem_FP []) hcons

theorem machineTrimTrueStep_mem_FP :
    machineTrimTrueStep ∈ Complexity.FP := by
  simpa only [machineTrimTrueStep] using!
    machineCompose_mem_FP machineTrimAcc_mem_FP
      (machinePrepend_mem_FP true)

theorem machineTrimPacked_mem_FP : machineTrimPacked ∈ Complexity.FP := by
  simpa only [machineTrimPacked, Polynomial.eval_X] using!
    Cobham.recFoldClamp_mem_FP machineTrimFalseStep_mem_FP
      machineTrimTrueStep_mem_FP (machineConst_mem_FP []) Polynomial.X

theorem machineTrimHighZeros_mem_FP :
    machineTrimHighZeros ∈ Complexity.FP := by
  have hpack : (fun word : List Bool => pair [] word) ∈ Complexity.FP :=
    machinePair_mem_FP (machineConst_mem_FP []) id_mem_FP
  simpa only [machineTrimHighZeros] using!
    machineCompose_mem_FP hpack machineTrimPacked_mem_FP

theorem binaryTrimHighZeros_length_le : ∀ bits : List Bool,
    (BinaryRippleSub.trimHighZeros bits).length ≤ bits.length := by
  intro bits
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp only [BinaryRippleSub.trimHighZeros]
      cases htrim : BinaryRippleSub.trimHighZeros rest with
      | nil => cases bit <;> simp
      | cons high tail =>
          simp only [htrim, List.length_cons] at ih ⊢
          omega

theorem machineTrim_recFold_eq : ∀ bits : List Bool,
    Cobham.recFold machineTrimFalseStep machineTrimTrueStep [] [] bits =
      BinaryRippleSub.trimHighZeros bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp only [Cobham.recFold]
      cases bit with
      | false =>
          simp only [Bool.false_eq, Bool.cond_false, machineTrimFalseStep,
            machineTrimAcc, machinePairFirst_pair, machinePairSecond_pair, ih]
          cases htrim : BinaryRippleSub.trimHighZeros rest with
          | nil => simp [BinaryRippleSub.trimHighZeros, htrim]
          | cons high tail =>
              simp [BinaryRippleSub.trimHighZeros, htrim]
      | true =>
          simp only [Bool.cond_true, ih]
          cases htrim : BinaryRippleSub.trimHighZeros rest <;>
            simp [machineTrimTrueStep, machineTrimAcc,
              BinaryRippleSub.trimHighZeros, htrim]

/-- The concrete bounded fold removes precisely the redundant high zeroes. -/
theorem machineTrimHighZeros_eq (word : List Bool) :
    machineTrimHighZeros word = BinaryRippleSub.trimHighZeros word := by
  rw [machineTrimHighZeros, machineTrimPacked]
  have hbound : ∀ t : List Bool, t.length ≤ word.length →
      (Cobham.recFold machineTrimFalseStep machineTrimTrueStep [] [] t).length ≤
        (pair [] word).length := by
    intro t ht
    rw [machineTrim_recFold_eq]
    have htrim := binaryTrimHighZeros_length_le t
    simp only [pair_length, List.length_nil]
    omega
  simp only [machinePairFirst_pair, machinePairSecond_pair]
  rw [Cobham.recFoldClamp_eq_recFold word hbound,
    machineTrim_recFold_eq]

/-- Assemble queried bits along the given ruler and trim high zeros to obtain a canonical binary
word. -/
def machineAssembleCanonicalBits
    (query ruler : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineTrimHighZeros (machineAssembleBits query ruler word)

theorem machineAssembleCanonicalBits_mem_FP
    {query ruler : List Bool → List Bool}
    (hquery : query ∈ Complexity.FP) (hruler : ruler ∈ Complexity.FP) :
    machineAssembleCanonicalBits query ruler ∈ Complexity.FP := by
  simpa only [machineAssembleCanonicalBits] using!
    machineCompose_mem_FP (machineAssembleBits_mem_FP hquery hruler)
      machineTrimHighZeros_mem_FP

theorem replicate_false_succ_append (k : ℕ) :
    List.replicate (k + 1) false = List.replicate k false ++ [false] := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        List.replicate (k + 1 + 1) false =
            false :: List.replicate (k + 1) false := by
          rw [List.replicate_succ]
        _ = false :: (List.replicate k false ++ [false]) := by rw [ih]
        _ = List.replicate (k + 1) false ++ [false] := by
          rw [List.replicate_succ, List.cons_append]

theorem binaryTrimHighZeros_append_false (bits : List Bool) :
    BinaryRippleSub.trimHighZeros (bits ++ [false]) =
      BinaryRippleSub.trimHighZeros bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      rw [List.cons_append, BinaryRippleSub.trimHighZeros, ih]
      cases htrim : BinaryRippleSub.trimHighZeros rest <;>
        simp [BinaryRippleSub.trimHighZeros, htrim]

theorem binaryTrimHighZeros_append_replicate_false
    (bits : List Bool) : ∀ k : ℕ,
    BinaryRippleSub.trimHighZeros (bits ++ List.replicate k false) =
      BinaryRippleSub.trimHighZeros bits := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [replicate_false_succ_append, ← List.append_assoc,
        binaryTrimHighZeros_append_false, ih]

theorem assembledOutputBitLanguage_padded
    (target : List Bool → List Bool) (word : List Bool) : ∀ extra : ℕ,
    assembledQueryBits
        (MachineRAMBridge.languageFlag (outputBitLanguage target)) word
        ((target word).length + extra) =
      target word ++ List.replicate extra false := by
  intro extra
  induction extra with
  | zero =>
      simpa using! assembledQueryBits_eq_take
        (MachineRAMBridge.languageFlag (outputBitLanguage target)) target
        (outputBitLanguage_flag_pair target) word
        (target word).length le_rfl
  | succ extra ih =>
      rw [Nat.add_succ, assembledQueryBits, ih,
        outputBitLanguage_flag_pair_all]
      have hnone :
          (target word)[(target word).length + extra]? = none :=
        List.getElem?_eq_none (by omega)
      rw [hnone]
      simp only [Option.getD_none, machineHeadBit_cons]
      rw [replicate_false_succ_append, List.append_assoc]

/-- With a polynomial upper bound on output width, bit-graph assembly followed
by verified high-zero trimming recovers any already-canonical target word. -/
theorem machineAssembleCanonicalBits_realizes
    (target ruler : List Bool → List Bool)
    (hruler : ∀ word, (target word).length ≤ (ruler word).length)
    (hcanonical : ∀ word,
      BinaryRippleSub.trimHighZeros (target word) = target word) :
    machineAssembleCanonicalBits
        (MachineRAMBridge.languageFlag (outputBitLanguage target)) ruler =
      target := by
  funext word
  rw [machineAssembleCanonicalBits, machineAssembleBits_eq]
  have hsum : (target word).length +
      ((ruler word).length - (target word).length) =
        (ruler word).length := Nat.add_sub_of_le (hruler word)
  rw [← hsum, assembledOutputBitLanguage_padded,
    machineTrimHighZeros_eq,
    binaryTrimHighZeros_append_replicate_false,
    hcanonical]

/-- Upper-bound version of the RAM bit-graph reduction.  This is the form
used for canonical natural and rational outputs. -/
theorem canonicalTarget_mem_FP_of_ramBitProgram
    (target ruler : List Bool → List Bool)
    (program : RAM.Program) (p : Polynomial ℕ)
    (hdecides : program.DecidesInTime (outputBitLanguage target) p.eval)
    (hrulerFP : ruler ∈ Complexity.FP)
    (hrulerLength : ∀ word,
      (target word).length ≤ (ruler word).length)
    (hcanonical : ∀ word,
      BinaryRippleSub.trimHighZeros (target word) = target word) :
    target ∈ Complexity.FP := by
  let query := MachineRAMBridge.languageFlag (outputBitLanguage target)
  have hqueryFP : query ∈ Complexity.FP :=
    MachineRAMBridge.languageFlag_mem_FP_of_ramProgram program p hdecides
  have hassembly : machineAssembleCanonicalBits query ruler ∈ Complexity.FP :=
    machineAssembleCanonicalBits_mem_FP hqueryFP hrulerFP
  have heq : machineAssembleCanonicalBits query ruler = target :=
    machineAssembleCanonicalBits_realizes target ruler hrulerLength hcanonical
  rwa [heq] at hassembly

/-- Scratch-register-prefix version of the upper-bound RAM bit-graph
reduction. -/
theorem canonicalTarget_mem_FP_of_paddedRamBitProgram
    (scratchRegisters : ℕ) (target ruler : List Bool → List Bool)
    (program : RAM.Program) (p : Polynomial ℕ)
    (hdecides : program.DecidesInTime
      (MachineRAMBridge.paddedLanguage scratchRegisters
        (outputBitLanguage target)) p.eval)
    (hrulerFP : ruler ∈ Complexity.FP)
    (hrulerLength : ∀ word,
      (target word).length ≤ (ruler word).length)
    (hcanonical : ∀ word,
      BinaryRippleSub.trimHighZeros (target word) = target word) :
    target ∈ Complexity.FP := by
  let query := MachineRAMBridge.languageFlag (outputBitLanguage target)
  have hqueryFP : query ∈ Complexity.FP :=
    MachineRAMBridge.languageFlag_mem_FP_of_paddedRamProgram
      scratchRegisters program p hdecides
  have hassembly : machineAssembleCanonicalBits query ruler ∈ Complexity.FP :=
    machineAssembleCanonicalBits_mem_FP hqueryFP hrulerFP
  have heq : machineAssembleCanonicalBits query ruler = target :=
    machineAssembleCanonicalBits_realizes target ruler hrulerLength hcanonical
  rwa [heq] at hassembly

end BeyondBethe

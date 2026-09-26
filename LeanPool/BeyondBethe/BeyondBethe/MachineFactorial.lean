/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalLogSeries

/-!
# Unary-input factorial in the finite-word machine model

The input length is the natural number whose factorial is required.  The
state stores the current factorial, the next multiplier, and a quadratic
clamp.  Both evolving fields are clamped on malformed inputs; the ordinary
binary-size proof shows that neither clamp fires on a unary ruler.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Encodes factorial state as accumulated product, next factor, and width bound. -/
def machineFactorialPack (acc next bound : List Bool) : List Bool :=
  pair acc (pair next bound)

/-- Extracts the accumulated product from a factorial state. -/
def machineFactorialAcc (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the next factor from a factorial state. -/
def machineFactorialNext (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the width-bound ruler stored in a factorial state. -/
def machineFactorialBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

/-- Increments the next factorial factor in binary. -/
def machineFactorialSuccessor (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineFactorialNext state) (1 : ℕ).bits)

/-- Multiplies the accumulated product by the next factorial factor. -/
def machineFactorialCandidate (state : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineFactorialAcc state) (machineFactorialNext state))

/-- Truncates the candidate factorial product to the stored width bound. -/
def machineFactorialNextAcc (state : List Bool) : List Bool :=
  (machineFactorialCandidate state).take (machineFactorialBound state).length

/-- Truncates the incremented factorial counter to the stored width bound. -/
def machineFactorialNextCounter (state : List Bool) : List Bool :=
  (machineFactorialSuccessor state).take (machineFactorialBound state).length

/-- Updates the bounded factorial product and counter while retaining the width ruler. -/
def machineFactorialStep (state : List Bool) : List Bool :=
  machineFactorialPack (machineFactorialNextAcc state)
    (machineFactorialNextCounter state) (machineFactorialBound state)

/-- Uses the binary-multiplication width constructor to bound factorial state components. -/
def machineFactorialInputBound (ruler : List Bool) : List Bool :=
  machineBinaryMulWidth ruler

/-- Initializes the factorial accumulator and next factor to one with the input-derived width
bound. -/
def machineFactorialInit (ruler : List Bool) : List Bool :=
  machineFactorialPack (1 : ℕ).bits (1 : ℕ).bits
    (machineFactorialInputBound ruler)

/-- Packs three copies of the input bound to bound the encoded factorial state. -/
def machineFactorialWidth (ruler : List Bool) : List Bool :=
  let bound := machineFactorialInputBound ruler
  machineFactorialPack bound bound bound

/-- Runs one factorial step per bit of the unary input ruler. -/
def machineFactorialFinalState (ruler : List Bool) : List Bool :=
  (machineFactorialStep)^[ruler.length] (machineFactorialInit ruler)

/-- Extracts the factorial accumulator after all ruler-specified iterations. -/
def machineFactorialBits (ruler : List Bool) : List Bool :=
  machineFactorialAcc (machineFactorialFinalState ruler)

/-- Encodes the final factorial accumulator as a nonnegative raw rational with denominator one. -/
def machineFactorialRawRatCode (ruler : List Bool) : List Bool :=
  pair (false :: machineFactorialBits ruler) (1 : ℕ).bits

theorem machineFactorialAcc_mem_FP :
    machineFactorialAcc ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineFactorialNext_mem_FP :
    machineFactorialNext ∈ Complexity.FP := by
  simpa only [machineFactorialNext] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineFactorialBound_mem_FP :
    machineFactorialBound ∈ Complexity.FP := by
  simpa only [machineFactorialBound] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineFactorialSuccessor_mem_FP :
    machineFactorialSuccessor ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineFactorialNext_mem_FP
    (machineConst_mem_FP (1 : ℕ).bits)
  simpa only [machineFactorialSuccessor] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineFactorialCandidate_mem_FP :
    machineFactorialCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineFactorialAcc_mem_FP
    machineFactorialNext_mem_FP
  simpa only [machineFactorialCandidate] using!
    machineCompose_mem_FP hpair machineBinaryMulBits_mem_FP

theorem machineFactorialNextAcc_mem_FP :
    machineFactorialNextAcc ∈ Complexity.FP := by
  simpa only [machineFactorialNextAcc] using!
    machineTake_mem_FP machineFactorialBound_mem_FP
      machineFactorialCandidate_mem_FP

theorem machineFactorialNextCounter_mem_FP :
    machineFactorialNextCounter ∈ Complexity.FP := by
  simpa only [machineFactorialNextCounter] using!
    machineTake_mem_FP machineFactorialBound_mem_FP
      machineFactorialSuccessor_mem_FP

theorem machineFactorialStep_mem_FP :
    machineFactorialStep ∈ Complexity.FP := by
  exact machinePair_mem_FP machineFactorialNextAcc_mem_FP
    (machinePair_mem_FP machineFactorialNextCounter_mem_FP
      machineFactorialBound_mem_FP)

theorem machineFactorialInputBound_mem_FP :
    machineFactorialInputBound ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

theorem machineFactorialInit_mem_FP :
    machineFactorialInit ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP (1 : ℕ).bits)
    (machinePair_mem_FP (machineConst_mem_FP (1 : ℕ).bits)
      machineFactorialInputBound_mem_FP)

theorem machineFactorialWidth_mem_FP :
    machineFactorialWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineFactorialInputBound_mem_FP
    (machinePair_mem_FP machineFactorialInputBound_mem_FP
      machineFactorialInputBound_mem_FP)

@[simp] theorem machineFactorialAcc_pack (acc next bound) :
    machineFactorialAcc (machineFactorialPack acc next bound) = acc := by
  simp [machineFactorialAcc, machineFactorialPack]

@[simp] theorem machineFactorialNext_pack (acc next bound) :
    machineFactorialNext (machineFactorialPack acc next bound) = next := by
  simp [machineFactorialNext, machineFactorialPack]

@[simp] theorem machineFactorialBound_pack (acc next bound) :
    machineFactorialBound (machineFactorialPack acc next bound) = bound := by
  simp [machineFactorialBound, machineFactorialPack]

/-- Bounds all three components of a canonically packed factorial state by the input-derived
width. -/
def MachineFactorialStateBound (ruler state : List Bool) : Prop :=
  let B := (machineFactorialInputBound ruler).length
  state = machineFactorialPack (machineFactorialAcc state)
      (machineFactorialNext state) (machineFactorialBound state) ∧
    (machineFactorialAcc state).length ≤ B ∧
    (machineFactorialNext state).length ≤ B ∧
    (machineFactorialBound state).length ≤ B

theorem machineFactorial_one_le_bound (ruler : List Bool) :
    (1 : ℕ).bits.length ≤ (machineFactorialInputBound ruler).length := by
  simp [machineFactorialInputBound, machineBinaryMulWidth]

theorem machineFactorialInit_bound (ruler : List Bool) :
    MachineFactorialStateBound ruler (machineFactorialInit ruler) := by
  simp only [MachineFactorialStateBound, machineFactorialInit,
    machineFactorialAcc_pack, machineFactorialNext_pack,
    machineFactorialBound_pack]
  exact ⟨trivial, machineFactorial_one_le_bound ruler,
    machineFactorial_one_le_bound ruler, le_rfl⟩

theorem machineFactorialStep_bound {ruler state : List Bool}
    (hstate : MachineFactorialStateBound ruler state) :
    MachineFactorialStateBound ruler (machineFactorialStep state) := by
  dsimp only [MachineFactorialStateBound] at hstate ⊢
  rcases hstate with ⟨hpack, hacc, hnext, hbound⟩
  simp only [machineFactorialStep, machineFactorialAcc_pack,
    machineFactorialNext_pack, machineFactorialBound_pack]
  refine ⟨trivial, ?_, ?_, hbound⟩
  · exact (List.length_take_le _ _).trans hbound
  · exact (List.length_take_le _ _).trans hbound

theorem machineFactorialIterate_bound (ruler : List Bool) : ∀ k,
    MachineFactorialStateBound ruler
      ((machineFactorialStep)^[k] (machineFactorialInit ruler)) := by
  intro k
  induction k with
  | zero => exact machineFactorialInit_bound ruler
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineFactorialStep_bound ih

theorem machineFactorialIterate_length_le_width
    (ruler : List Bool) (iterations : ℕ) (_ : iterations ≤ ruler.length) :
    ((machineFactorialStep)^[iterations]
      (machineFactorialInit ruler)).length ≤
        (machineFactorialWidth ruler).length := by
  have hstate := machineFactorialIterate_bound ruler iterations
  dsimp only [MachineFactorialStateBound] at hstate
  rcases hstate with ⟨hpack, hacc, hnext, hbound⟩
  rw [hpack]
  simp only [machineFactorialPack, machineFactorialWidth, pair_length]
  omega

theorem machineFactorialFinalState_mem_FP :
    machineFactorialFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineFactorialStep_mem_FP
    machineFactorialInit_mem_FP id_mem_FP machineFactorialWidth_mem_FP
    machineFactorialIterate_length_le_width

theorem machineFactorialBits_mem_FP :
    machineFactorialBits ∈ Complexity.FP := by
  simpa only [machineFactorialBits] using!
    machineCompose_mem_FP machineFactorialFinalState_mem_FP
      machineFactorialAcc_mem_FP

theorem machineFactorialRawRatCode_mem_FP :
    machineFactorialRawRatCode ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineFactorialBits_mem_FP
    (machinePrepend_mem_FP false)
  exact machinePair_mem_FP hnum (machineConst_mem_FP (1 : ℕ).bits)

/-! ## Exact semantics on unary rulers -/

theorem factorial_bits_length_le_bound {n k : ℕ} (hk : k ≤ n) :
    k.factorial.bits.length ≤
      (machineFactorialInputBound (List.replicate n true)).length := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  have hfac : k.factorial ≤ 2 ^ (k ^ 2) := by
    calc
      k.factorial ≤ k ^ k := Nat.factorial_le_pow k
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left k.lt_two_pow_self.le k
      _ = 2 ^ (k ^ 2) := by simp [pow_mul, pow_two]
  have hsq : k ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hk 2
  have hpow : 2 ^ (k ^ 2) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by decide) hsq
  have hexponent : n ^ 2 < (16 + n) * (16 + n) := by
    nlinarith
  have hstrict : 2 ^ (n ^ 2) < 2 ^ ((16 + n) * (16 + n)) :=
    (Nat.pow_lt_pow_iff_right (by omega)).2 hexponent
  have hlength :
      (machineFactorialInputBound (List.replicate n true)).length =
        (16 + n) * (16 + n) := by
    simp only [machineFactorialInputBound, machineBinaryMulWidth,
      List.length_replicate, List.length_append]
  rw [hlength]
  exact hfac.trans_lt (hpow.trans_lt hstrict)

theorem factorial_counter_bits_length_le_bound {n k : ℕ}
    (hk : k ≤ n + 1) :
    k.bits.length ≤
      (machineFactorialInputBound (List.replicate n true)).length := by
  have hbits : k.bits.length ≤ k := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact k.lt_two_pow_self
  have hlength :
      (machineFactorialInputBound (List.replicate n true)).length =
        (16 + n) * (16 + n) := by
    simp only [machineFactorialInputBound, machineBinaryMulWidth,
      List.length_replicate, List.length_append]
  rw [hlength]
  exact hbits.trans <| by nlinarith

/-- Encodes the semantic state after `k` factorial steps, with product `k!` and next factor `k +
1`. -/
def machineFactorialSemanticState (n k : ℕ) : List Bool :=
  machineFactorialPack k.factorial.bits (k + 1).bits
    (machineFactorialInputBound (List.replicate n true))

@[simp] theorem machineFactorialSemanticState_zero (n : ℕ) :
    machineFactorialSemanticState n 0 =
      machineFactorialInit (List.replicate n true) := by
  simp [machineFactorialSemanticState, machineFactorialInit]

theorem machineFactorialSemanticState_step (n k : ℕ) (hk : k < n) :
    machineFactorialStep (machineFactorialSemanticState n k) =
      machineFactorialSemanticState n (k + 1) := by
  have hfac := factorial_bits_length_le_bound (show k + 1 ≤ n by omega)
  have hcounter := factorial_counter_bits_length_le_bound
    (show k + 2 ≤ n + 1 by omega)
  simp only [machineFactorialStep, machineFactorialSemanticState,
    machineFactorialNextAcc, machineFactorialCandidate,
    machineFactorialAcc_pack, machineFactorialNext_pack,
    machineFactorialBound_pack, machineBinaryMulBits_pair_natBits,
    machineFactorialNextCounter, machineFactorialSuccessor,
    machineBinaryAddBits_pair_natBits]
  rw [(List.take_eq_self_iff _).2 (by
      simpa [Nat.factorial_succ, Nat.mul_comm] using! hfac),
    (List.take_eq_self_iff _).2 hcounter]
  simp [Nat.factorial_succ, Nat.mul_comm, Nat.add_assoc]

theorem machineFactorialIterate_semantics (n : ℕ) : ∀ k ≤ n,
    (machineFactorialStep)^[k]
        (machineFactorialInit (List.replicate n true)) =
      machineFactorialSemanticState n k := by
  intro k hk
  induction k with
  | zero => exact (machineFactorialSemanticState_zero n).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineFactorialSemanticState_step n k (by omega)

@[simp] theorem machineFactorialBits_encode (n : ℕ) :
    machineFactorialBits (List.replicate n true) = n.factorial.bits := by
  rw [machineFactorialBits, machineFactorialFinalState]
  simp only [List.length_replicate]
  rw [machineFactorialIterate_semantics n n le_rfl]
  simp [machineFactorialSemanticState]

@[simp] theorem machineFactorialRawRatCode_encode (n : ℕ) :
    machineFactorialRawRatCode (List.replicate n true) =
      rawRatBinaryCode (RawRat.ofNat n.factorial) := by
  simp [machineFactorialRawRatCode, rawRatBinaryCode, RawRat.ofNat,
    integerBinaryCode]

end BeyondBethe

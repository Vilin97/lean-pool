/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryMul
import LeanPool.BeyondBethe.BeyondBethe.MachineFPBasics

/-! # Machine Repeat Pair -/

namespace BeyondBethe

open Complexity

/-!
# Polynomial-time repeated pairing

`repeatPairCode n item tail` is the right-nested word obtained by prepending
`item` exactly `n` times to `tail`.  This is the machine-level constructor for
fixedValue rational vectors and, later, for the zero blocks of diagonal
matrices.  Its iteration count is supplied in unary and its accumulator is
clamped by an explicit quadratic envelope.
-/

def repeatPairCode : ℕ → List Bool → List Bool → List Bool
  | 0, _, tail => tail
  | n + 1, item, tail => pair item (repeatPairCode n item tail)

@[simp] theorem repeatPairCode_zero (item tail : List Bool) :
    repeatPairCode 0 item tail = tail := rfl

@[simp] theorem repeatPairCode_succ (n : ℕ) (item tail : List Bool) :
    repeatPairCode (n + 1) item tail =
      pair item (repeatPairCode n item tail) := rfl

theorem repeatPairCode_length (n : ℕ) (item tail : List Bool) :
    (repeatPairCode n item tail).length =
      n * (2 * item.length + 2) + tail.length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [repeatPairCode_succ, pair_length, ih]
      ring

theorem repeatPairCode_binaryListCode {α : Type*}
    (encode : α → List Bool) (n : ℕ) (x : α) (xs : List α) :
    repeatPairCode n (encode x) (binaryListCode encode xs) =
      binaryListCode encode (List.replicate n x ++ xs) := by
  induction n with
  | zero => simp [repeatPairCode]
  | succ n ih =>
      rw [repeatPairCode_succ, ih]
      simp only [List.replicate_succ, List.cons_append, binaryListCode]

def machineRepeatPairRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRepeatPairItem (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond word)

def machineRepeatPairTail (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond word)

def machineRepeatPairBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineRepeatPairPack
    (item acc bound : List Bool) : List Bool :=
  pair item (pair acc bound)

def machineRepeatPairStateItem (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRepeatPairStateAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRepeatPairStateBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineRepeatPairCandidate (state : List Bool) : List Bool :=
  pair (machineRepeatPairStateItem state)
    (machineRepeatPairStateAcc state)

def machineRepeatPairNextAcc (state : List Bool) : List Bool :=
  (machineRepeatPairCandidate state).take
    (machineRepeatPairStateBound state).length

def machineRepeatPairStep (state : List Bool) : List Bool :=
  machineRepeatPairPack (machineRepeatPairStateItem state)
    (machineRepeatPairNextAcc state)
    (machineRepeatPairStateBound state)

def machineRepeatPairInit (word : List Bool) : List Bool :=
  machineRepeatPairPack (machineRepeatPairItem word)
    (machineRepeatPairTail word) (machineRepeatPairBound word)

def machineRepeatPairWidth (word : List Bool) : List Bool :=
  machineRepeatPairPack (machineRepeatPairBound word)
    (machineRepeatPairBound word) (machineRepeatPairBound word)

def machineRepeatPairFinalState (word : List Bool) : List Bool :=
  (machineRepeatPairStep)^[(machineRepeatPairRuler word).length]
    (machineRepeatPairInit word)

def machineRepeatPairCode (word : List Bool) : List Bool :=
  machineRepeatPairStateAcc (machineRepeatPairFinalState word)

/-! ## Polynomial-time closure -/

theorem machineRepeatPairRuler_mem_FP : machineRepeatPairRuler ∈ FP :=
  machinePairFirst_mem_FP

theorem machineRepeatPairItem_mem_FP : machineRepeatPairItem ∈ FP := by
  simpa only [machineRepeatPairItem] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRepeatPairTail_mem_FP : machineRepeatPairTail ∈ FP := by
  simpa only [machineRepeatPairTail] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineRepeatPairBound_mem_FP : machineRepeatPairBound ∈ FP :=
  machineBinaryMulWidth_mem_FP

theorem machineRepeatPairStateItem_mem_FP :
    machineRepeatPairStateItem ∈ FP := machinePairFirst_mem_FP

theorem machineRepeatPairStateAcc_mem_FP :
    machineRepeatPairStateAcc ∈ FP := by
  simpa only [machineRepeatPairStateAcc] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRepeatPairStateBound_mem_FP :
    machineRepeatPairStateBound ∈ FP := by
  simpa only [machineRepeatPairStateBound] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineRepeatPairCandidate_mem_FP :
    machineRepeatPairCandidate ∈ FP :=
  machinePair_mem_FP machineRepeatPairStateItem_mem_FP
    machineRepeatPairStateAcc_mem_FP

theorem machineRepeatPairNextAcc_mem_FP :
    machineRepeatPairNextAcc ∈ FP := by
  simpa only [machineRepeatPairNextAcc] using
    machineTake_mem_FP machineRepeatPairStateBound_mem_FP
      machineRepeatPairCandidate_mem_FP

theorem machineRepeatPairStep_mem_FP : machineRepeatPairStep ∈ FP :=
  machinePair_mem_FP machineRepeatPairStateItem_mem_FP
    (machinePair_mem_FP machineRepeatPairNextAcc_mem_FP
      machineRepeatPairStateBound_mem_FP)

theorem machineRepeatPairInit_mem_FP : machineRepeatPairInit ∈ FP :=
  machinePair_mem_FP machineRepeatPairItem_mem_FP
    (machinePair_mem_FP machineRepeatPairTail_mem_FP
      machineRepeatPairBound_mem_FP)

theorem machineRepeatPairWidth_mem_FP : machineRepeatPairWidth ∈ FP :=
  machinePair_mem_FP machineRepeatPairBound_mem_FP
    (machinePair_mem_FP machineRepeatPairBound_mem_FP
      machineRepeatPairBound_mem_FP)

@[simp] theorem machineRepeatPairStateItem_pack (a b c) :
    machineRepeatPairStateItem (machineRepeatPairPack a b c) = a := by
  simp [machineRepeatPairStateItem, machineRepeatPairPack]

@[simp] theorem machineRepeatPairStateAcc_pack (a b c) :
    machineRepeatPairStateAcc (machineRepeatPairPack a b c) = b := by
  simp [machineRepeatPairStateAcc, machineRepeatPairPack]

@[simp] theorem machineRepeatPairStateBound_pack (a b c) :
    machineRepeatPairStateBound (machineRepeatPairPack a b c) = c := by
  simp [machineRepeatPairStateBound, machineRepeatPairPack]

def MachineRepeatPairStateBound (word state : List Bool) : Prop :=
  let B := (machineRepeatPairBound word).length
  state = machineRepeatPairPack
      (machineRepeatPairStateItem state)
      (machineRepeatPairStateAcc state)
      (machineRepeatPairStateBound state) ∧
    (machineRepeatPairStateItem state).length ≤ B ∧
    (machineRepeatPairStateAcc state).length ≤ B ∧
    (machineRepeatPairStateBound state).length ≤ B

theorem machineRepeatPair_word_length_le_bound (word : List Bool) :
    word.length ≤ (machineRepeatPairBound word).length := by
  simp only [machineRepeatPairBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineRepeatPairInit_bound (word : List Bool) :
    MachineRepeatPairStateBound word (machineRepeatPairInit word) := by
  simp only [MachineRepeatPairStateBound, machineRepeatPairInit,
    machineRepeatPairStateItem_pack, machineRepeatPairStateAcc_pack,
    machineRepeatPairStateBound_pack]
  refine ⟨trivial, ?_, ?_, le_rfl⟩
  · exact (machinePairFirst_length_le (machinePairSecond word)).trans
      ((machinePairSecond_length_le word).trans
        (machineRepeatPair_word_length_le_bound word))
  · exact (machinePairSecond_length_le (machinePairSecond word)).trans
      ((machinePairSecond_length_le word).trans
        (machineRepeatPair_word_length_le_bound word))

theorem machineRepeatPairStep_bound {word state : List Bool}
    (hstate : MachineRepeatPairStateBound word state) :
    MachineRepeatPairStateBound word (machineRepeatPairStep state) := by
  dsimp only [MachineRepeatPairStateBound] at hstate ⊢
  rcases hstate with ⟨_, hitem, _hacc, hbound⟩
  simp only [machineRepeatPairStep, machineRepeatPairStateItem_pack,
    machineRepeatPairStateAcc_pack, machineRepeatPairStateBound_pack]
  refine ⟨trivial, hitem, ?_, hbound⟩
  exact (List.length_take_le _ _).trans hbound

theorem machineRepeatPairIterate_bound (word : List Bool) : ∀ k,
    MachineRepeatPairStateBound word
      ((machineRepeatPairStep)^[k] (machineRepeatPairInit word)) := by
  intro k
  induction k with
  | zero => exact machineRepeatPairInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRepeatPairStep_bound ih

theorem machineRepeatPairIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineRepeatPairRuler word).length) :
    ((machineRepeatPairStep)^[iterations]
      (machineRepeatPairInit word)).length ≤
        (machineRepeatPairWidth word).length := by
  rcases machineRepeatPairIterate_bound word iterations with
    ⟨hdecomp, hitem, hacc, hbound⟩
  rw [hdecomp]
  simp only [machineRepeatPairPack, machineRepeatPairWidth, pair_length]
  omega

theorem machineRepeatPairFinalState_mem_FP :
    machineRepeatPairFinalState ∈ FP :=
  Cobham.iterate_mem_FP machineRepeatPairStep_mem_FP
    machineRepeatPairInit_mem_FP machineRepeatPairRuler_mem_FP
    machineRepeatPairWidth_mem_FP machineRepeatPairIterate_length_le_width

theorem machineRepeatPairCode_mem_FP : machineRepeatPairCode ∈ FP := by
  simpa only [machineRepeatPairCode] using
    machineCompose_mem_FP machineRepeatPairFinalState_mem_FP
      machineRepeatPairStateAcc_mem_FP

/-! ## Exact semantics on well-formed unary calls -/

def machineRepeatPairCanonicalInput
    (n : ℕ) (item tail : List Bool) : List Bool :=
  pair (List.replicate n true) (pair item tail)

def machineRepeatPairCanonicalState
    (n : ℕ) (item tail : List Bool) (k : ℕ) : List Bool :=
  let word := machineRepeatPairCanonicalInput n item tail
  machineRepeatPairPack item (repeatPairCode k item tail)
    (machineRepeatPairBound word)

theorem machineRepeatPair_candidate_length_le_bound
    (n k : ℕ) (item tail : List Bool) (hk : k + 1 ≤ n) :
    (pair item (repeatPairCode k item tail)).length ≤
      (machineRepeatPairBound
        (machineRepeatPairCanonicalInput n item tail)).length := by
  let W := (machineRepeatPairCanonicalInput n item tail).length
  have hnW : n ≤ W := by
    simp only [W, machineRepeatPairCanonicalInput, pair_length,
      List.length_replicate]
    omega
  have hiW : 2 * item.length + 2 ≤ W := by
    simp only [W, machineRepeatPairCanonicalInput, pair_length,
      List.length_replicate]
    omega
  have htW : tail.length ≤ W := by
    simp only [W, machineRepeatPairCanonicalInput, pair_length,
      List.length_replicate]
    omega
  have hkW : k + 1 ≤ W := hk.trans hnW
  have hproduct := Nat.mul_le_mul hkW hiW
  rw [pair_length, repeatPairCode_length]
  simp only [machineRepeatPairBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  change 2 * item.length + 2 +
      (k * (2 * item.length + 2) + tail.length) ≤
    (16 + W) * (16 + W)
  calc
    2 * item.length + 2 +
        (k * (2 * item.length + 2) + tail.length) =
      (k + 1) * (2 * item.length + 2) + tail.length := by ring
    _ ≤ W * W + W := Nat.add_le_add hproduct htW
    _ ≤ (16 + W) * (16 + W) := by nlinarith

theorem machineRepeatPairInit_semantics
    (n : ℕ) (item tail : List Bool) :
    machineRepeatPairInit (machineRepeatPairCanonicalInput n item tail) =
      machineRepeatPairCanonicalState n item tail 0 := by
  simp [machineRepeatPairInit, machineRepeatPairCanonicalInput,
    machineRepeatPairCanonicalState, machineRepeatPairItem,
    machineRepeatPairTail]

theorem machineRepeatPairStep_semantics
    (n k : ℕ) (item tail : List Bool) (hk : k < n) :
    machineRepeatPairStep
        (machineRepeatPairCanonicalState n item tail k) =
      machineRepeatPairCanonicalState n item tail (k + 1) := by
  have hbound := machineRepeatPair_candidate_length_le_bound
    n k item tail (by omega)
  have htake :
      (pair item (repeatPairCode k item tail)).take
          (machineRepeatPairBound
            (machineRepeatPairCanonicalInput n item tail)).length =
        pair item (repeatPairCode k item tail) :=
    List.take_of_length_le hbound
  simp only [machineRepeatPairStep, machineRepeatPairCanonicalState,
    machineRepeatPairStateItem_pack, machineRepeatPairStateAcc_pack,
    machineRepeatPairStateBound_pack, machineRepeatPairNextAcc,
    machineRepeatPairCandidate]
  rw [htake]
  rfl

theorem machineRepeatPairIterate_semantics
    (n : ℕ) (item tail : List Bool) : ∀ k ≤ n,
    (machineRepeatPairStep)^[k]
        (machineRepeatPairInit
          (machineRepeatPairCanonicalInput n item tail)) =
      machineRepeatPairCanonicalState n item tail k := by
  intro k hk
  induction k with
  | zero => exact machineRepeatPairInit_semantics n item tail
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRepeatPairStep_semantics n k item tail (by omega)

@[simp] theorem machineRepeatPairCode_encode
    (n : ℕ) (item tail : List Bool) :
    machineRepeatPairCode (machineRepeatPairCanonicalInput n item tail) =
      repeatPairCode n item tail := by
  have hstate := congrArg machineRepeatPairStateAcc
    (machineRepeatPairIterate_semantics n item tail n le_rfl)
  simpa [machineRepeatPairCode, machineRepeatPairFinalState,
    machineRepeatPairRuler, machineRepeatPairCanonicalInput,
    machineRepeatPairCanonicalState] using hstate

end BeyondBethe

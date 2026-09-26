/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinarySub

/-!
# Bounded conversion from binary to unary

An unrestricted binary integer can describe an exponentially long unary word,
so binary-to-unary conversion is not polynomial-time in general.  This machine
therefore receives an explicit unary guard.  It returns exactly `n` true bits
when the encoded natural `n` is at most the guard length, and otherwise returns
only the guarded prefix.  The guard is what later permits paper-specific
polynomial schedules without making a false global complexity claim.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Package the remaining binary integer and accumulated unary word. -/
def machineBoundedUnaryPack (remaining acc : List Bool) : List Bool :=
  pair remaining acc

/-- Extract the remaining binary integer from a bounded unary-conversion state. -/
def machineBoundedUnaryRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extract the unary true-bit accumulator. -/
def machineBoundedUnaryAcc (state : List Bool) : List Bool :=
  machinePairSecond state

/-- Subtract one from the remaining binary integer using truncated natural subtraction. -/
def machineBoundedUnaryDecrement (state : List Bool) : List Bool :=
  machineBinarySubBits
    (pair (machineBoundedUnaryRemaining state) [true])

/-- Decrement the remaining binary integer and prepend one true bit to the unary accumulator. -/
def machineBoundedUnaryContinue (state : List Bool) : List Bool :=
  machineBoundedUnaryPack (machineBoundedUnaryDecrement state)
    (true :: machineBoundedUnaryAcc state)

/-- Leave an empty remaining word fixed; otherwise perform one decrement-and-append conversion
step. -/
def machineBoundedUnaryStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineBoundedUnaryRemaining state) state
    (machineBoundedUnaryContinue state)

/-- Extract the iteration ruler that limits binary-to-unary conversion. -/
def machineBoundedUnaryRuler (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the binary integer to convert. -/
def machineBoundedUnaryBits (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Initialize bounded unary conversion with the input integer and an empty accumulator. -/
def machineBoundedUnaryInit (word : List Bool) : List Bool :=
  machineBoundedUnaryPack (machineBoundedUnaryBits word) []

/-- A conversion-state width envelope obtained by pairing the input word with itself. -/
def machineBoundedUnaryWidth (word : List Bool) : List Bool :=
  pair word word

/-- Run binary-to-unary conversion for the ruler's length, stopping early once the remaining
word is empty. -/
def machineBoundedUnaryFinalState (word : List Bool) : List Bool :=
  (machineBoundedUnaryStep)^[(machineBoundedUnaryRuler word).length]
    (machineBoundedUnaryInit word)

/-- Expand the encoded natural into true bits, stopping at the unary guard. -/
def machineBoundedUnary (word : List Bool) : List Bool :=
  machineBoundedUnaryAcc (machineBoundedUnaryFinalState word)

private theorem machineIfEmpty_of_ne_nil_local
    (test whenEmpty whenNonempty : List Bool) (h : test ≠ []) :
    machineIfEmpty test whenEmpty whenNonempty = whenNonempty := by
  cases test with
  | nil => exact False.elim (h rfl)
  | cons bit tail => simp

theorem machineBoundedUnaryRemaining_mem_FP :
    machineBoundedUnaryRemaining ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineBoundedUnaryAcc_mem_FP :
    machineBoundedUnaryAcc ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineBoundedUnaryDecrement_mem_FP :
    machineBoundedUnaryDecrement ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineBoundedUnaryRemaining_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineBoundedUnaryDecrement] using!
    machineCompose_mem_FP hpair machineBinarySubBits_mem_FP

theorem machineBoundedUnaryContinue_mem_FP :
    machineBoundedUnaryContinue ∈ Complexity.FP := by
  exact machinePair_mem_FP machineBoundedUnaryDecrement_mem_FP
    (machineCompose_mem_FP machineBoundedUnaryAcc_mem_FP
      (machinePrepend_mem_FP true))

theorem machineBoundedUnaryStep_mem_FP :
    machineBoundedUnaryStep ∈ Complexity.FP := by
  simpa only [machineBoundedUnaryStep] using!
    machineIfEmpty_mem_FP machineBoundedUnaryRemaining_mem_FP
      id_mem_FP machineBoundedUnaryContinue_mem_FP

theorem machineBoundedUnaryRuler_mem_FP :
    machineBoundedUnaryRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineBoundedUnaryBits_mem_FP :
    machineBoundedUnaryBits ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineBoundedUnaryInit_mem_FP :
    machineBoundedUnaryInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineBoundedUnaryBits_mem_FP
    (machineConst_mem_FP [])

theorem machineBoundedUnaryWidth_mem_FP :
    machineBoundedUnaryWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP id_mem_FP

@[simp] theorem machineBoundedUnaryRemaining_pack (remaining acc) :
    machineBoundedUnaryRemaining (machineBoundedUnaryPack remaining acc) =
      remaining := by
  simp [machineBoundedUnaryRemaining, machineBoundedUnaryPack]

@[simp] theorem machineBoundedUnaryAcc_pack (remaining acc) :
    machineBoundedUnaryAcc (machineBoundedUnaryPack remaining acc) = acc := by
  simp [machineBoundedUnaryAcc, machineBoundedUnaryPack]

/-- The packed conversion state has a remaining binary word bounded by the input length and an
accumulator bounded by the elapsed iteration count. -/
def MachineBoundedUnaryStateBound
    (word : List Bool) (iterations : ℕ) (state : List Bool) : Prop :=
  state = machineBoundedUnaryPack
      (machineBoundedUnaryRemaining state) (machineBoundedUnaryAcc state) ∧
  (machineBoundedUnaryRemaining state).length ≤ word.length ∧
  (machineBoundedUnaryAcc state).length ≤ iterations

theorem machineBoundedUnaryInit_bound (word : List Bool) :
    MachineBoundedUnaryStateBound word 0 (machineBoundedUnaryInit word) := by
  simp only [MachineBoundedUnaryStateBound, machineBoundedUnaryInit,
    machineBoundedUnaryRemaining_pack, machineBoundedUnaryAcc_pack]
  constructor
  · trivial
  constructor
  · exact machinePairSecond_length_le word
  · simp

theorem machineBoundedUnaryStep_bound
    {word state : List Bool} {iterations : ℕ}
    (hstate : MachineBoundedUnaryStateBound word iterations state) :
    MachineBoundedUnaryStateBound word (iterations + 1)
      (machineBoundedUnaryStep state) := by
  rcases hstate with ⟨hdecomp, hremaining, hacc⟩
  by_cases hempty : machineBoundedUnaryRemaining state = []
  · rw [machineBoundedUnaryStep, hempty, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc.trans (by omega)⟩
  · rw [machineBoundedUnaryStep,
      machineIfEmpty_of_ne_nil_local _ _ _ hempty,
      machineBoundedUnaryContinue]
    simp only [MachineBoundedUnaryStateBound,
      machineBoundedUnaryRemaining_pack, machineBoundedUnaryAcc_pack]
    constructor
    · trivial
    constructor
    · have hsub := machineBinarySubBits_pair_length_le
          (machineBoundedUnaryRemaining state) [true]
      simp only [machineBoundedUnaryDecrement]
      have hnonzero : 1 ≤ (machineBoundedUnaryRemaining state).length := by
        have hlength : (machineBoundedUnaryRemaining state).length ≠ 0 := by
          intro hzero
          exact hempty (List.length_eq_zero_iff.mp hzero)
        omega
      rw [show [true].length = 1 by rfl, max_eq_left hnonzero] at hsub
      exact hsub.trans hremaining
    · simp only [List.length_cons]
      omega

theorem machineBoundedUnaryIterate_bound (word : List Bool) : ∀ k,
    MachineBoundedUnaryStateBound word k
      ((machineBoundedUnaryStep)^[k] (machineBoundedUnaryInit word)) := by
  intro k
  induction k with
  | zero => exact machineBoundedUnaryInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineBoundedUnaryStep_bound ih

theorem machineBoundedUnaryIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (machineBoundedUnaryRuler word).length) :
    ((machineBoundedUnaryStep)^[iterations]
      (machineBoundedUnaryInit word)).length ≤
        (machineBoundedUnaryWidth word).length := by
  rcases machineBoundedUnaryIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc⟩
  rw [hdecomp]
  simp only [machineBoundedUnaryPack, machineBoundedUnaryWidth, pair_length]
  have hruler := machinePairFirst_length_le word
  simp only [machineBoundedUnaryRuler] at hiterations
  omega

theorem machineBoundedUnaryFinalState_mem_FP :
    machineBoundedUnaryFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBoundedUnaryStep_mem_FP
    machineBoundedUnaryInit_mem_FP machineBoundedUnaryRuler_mem_FP
    machineBoundedUnaryWidth_mem_FP
    machineBoundedUnaryIterate_length_le_width

theorem machineBoundedUnary_mem_FP :
    machineBoundedUnary ∈ Complexity.FP := by
  simpa only [machineBoundedUnary] using!
    machineCompose_mem_FP machineBoundedUnaryFinalState_mem_FP
      machineBoundedUnaryAcc_mem_FP

/-! ## Exact semantics -/

/-- The canonical state after `k` steps on `n`: binary remainder `n-k` and `min k n` true bits. -/
def boundedUnaryState (n k : ℕ) : List Bool :=
  machineBoundedUnaryPack (n - k).bits
    (List.replicate (min k n) true)

theorem machineBoundedUnaryStep_encode (n k : ℕ) :
    machineBoundedUnaryStep (boundedUnaryState n k) =
      boundedUnaryState n (k + 1) := by
  by_cases hkn : k < n
  · have hpos : 0 < n - k := Nat.sub_pos_of_lt hkn
    have hbits : (n - k).bits ≠ [] := by
      intro hnil
      have hzero : n - k = 0 := by
        have h := congrArg Nat.fromBitsLE hnil
        simpa only [Nat.fromBitsLE_bits] using! h
      omega
    rw [machineBoundedUnaryStep]
    simp only [boundedUnaryState, machineBoundedUnaryRemaining_pack]
    rw [machineIfEmpty_of_ne_nil_local _ _ _ hbits]
    rw [machineBoundedUnaryContinue]
    simp only [machineBoundedUnaryDecrement,
      machineBoundedUnaryRemaining_pack, machineBoundedUnaryAcc_pack]
    have hone : ([true] : List Bool) = (1 : ℕ).bits := by rfl
    rw [hone, machineBinarySubBits_pair_natBits]
    apply congrArg₂ machineBoundedUnaryPack
    · congr 1
    · rw [min_eq_left (Nat.le_of_lt hkn),
        min_eq_left (by omega : k + 1 ≤ n)]
      simp [List.replicate_succ]
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    rw [machineBoundedUnaryStep]
    simp [boundedUnaryState, Nat.sub_eq_zero_of_le hnk,
      Nat.sub_eq_zero_of_le (hnk.trans (Nat.le_succ k)),
      min_eq_right hnk, min_eq_right (hnk.trans (Nat.le_succ k))]

theorem machineBoundedUnaryIterate_encode (n : ℕ) : ∀ k,
    (machineBoundedUnaryStep)^[k]
        (machineBoundedUnaryPack n.bits []) = boundedUnaryState n k := by
  intro k
  induction k with
  | zero => simp [boundedUnaryState]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        machineBoundedUnaryStep_encode]

theorem machineBoundedUnary_encode (guard : List Bool) (n : ℕ) :
    machineBoundedUnary (pair guard n.bits) =
      List.replicate (min guard.length n) true := by
  rw [machineBoundedUnary, machineBoundedUnaryFinalState]
  simp only [machineBoundedUnaryRuler, machinePairFirst_pair,
    machineBoundedUnaryInit, machineBoundedUnaryBits,
    machinePairSecond_pair]
  rw [machineBoundedUnaryIterate_encode]
  simp [boundedUnaryState]

theorem machineBoundedUnary_encode_of_le
    (guard : List Bool) (n : ℕ) (hn : n ≤ guard.length) :
    machineBoundedUnary (pair guard n.bits) =
      List.replicate n true := by
  rw [machineBoundedUnary_encode, min_eq_right hn]

end BeyondBethe

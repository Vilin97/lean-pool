/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMateMemory
import LeanPool.BeyondBethe.BeyondBethe.KuhnSmallStep

/-!
# Constructing the unary column range

The matching evaluator scans `List.finRange n`.  This module constructs its
right-nested finite-word encoding from the unary dimension ruler.  The
constructor counts down and prepends, so after `n` steps the values occur in
the required increasing order `0,1,...,n-1`.
-/

namespace BeyondBethe

open Complexity

def finUnaryCode {n : ℕ} (i : Fin n) : List Bool :=
  List.replicate i.1 true

def finRangeUnaryCode (n : ℕ) : List Bool :=
  binaryListCode finUnaryCode (List.finRange n)

def machineUnaryRangePack
    (remaining acc bound : List Bool) : List Bool :=
  pair remaining (pair acc bound)

def machineUnaryRangeRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineUnaryRangeAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineUnaryRangeBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineUnaryRangeCandidate (state : List Bool) : List Bool :=
  pair (machineUnaryRangeRemaining state).tail
    (machineUnaryRangeAcc state)

def machineUnaryRangeNextAcc (state : List Bool) : List Bool :=
  (machineUnaryRangeCandidate state).take
    (machineUnaryRangeBound state).length

def machineUnaryRangeStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineUnaryRangeRemaining state) state
    (machineUnaryRangePack (machineUnaryRangeRemaining state).tail
      (machineUnaryRangeNextAcc state) (machineUnaryRangeBound state))

def machineUnaryRangeInputBound (ruler : List Bool) : List Bool :=
  machineListUpdateInputBound ruler

def machineUnaryRangeInit (ruler : List Bool) : List Bool :=
  machineUnaryRangePack ruler [] (machineUnaryRangeInputBound ruler)

def machineUnaryRangeWidth (ruler : List Bool) : List Bool :=
  let bound := machineUnaryRangeInputBound ruler
  machineUnaryRangePack bound bound bound

def machineUnaryRangeFinalState (ruler : List Bool) : List Bool :=
  (machineUnaryRangeStep)^[ruler.length] (machineUnaryRangeInit ruler)

def machineUnaryRangeCode (ruler : List Bool) : List Bool :=
  machineUnaryRangeAcc (machineUnaryRangeFinalState ruler)

theorem machineUnaryRangeRemaining_mem_FP :
    machineUnaryRangeRemaining ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineUnaryRangeAcc_mem_FP :
    machineUnaryRangeAcc ∈ Complexity.FP := by
  simpa only [machineUnaryRangeAcc] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineUnaryRangeBound_mem_FP :
    machineUnaryRangeBound ∈ Complexity.FP := by
  simpa only [machineUnaryRangeBound] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineUnaryRangeCandidate_mem_FP :
    machineUnaryRangeCandidate ∈ Complexity.FP := by
  have hremainingTail := machineCompose_mem_FP
    machineUnaryRangeRemaining_mem_FP machineTail_mem_FP
  exact machinePair_mem_FP hremainingTail machineUnaryRangeAcc_mem_FP

theorem machineUnaryRangeNextAcc_mem_FP :
    machineUnaryRangeNextAcc ∈ Complexity.FP := by
  simpa only [machineUnaryRangeNextAcc] using!
    machineTake_mem_FP machineUnaryRangeBound_mem_FP
      machineUnaryRangeCandidate_mem_FP

theorem machineUnaryRangeStep_mem_FP :
    machineUnaryRangeStep ∈ Complexity.FP := by
  have hremainingTail := machineCompose_mem_FP
    machineUnaryRangeRemaining_mem_FP machineTail_mem_FP
  have hadvance := machinePair_mem_FP hremainingTail
    (machinePair_mem_FP machineUnaryRangeNextAcc_mem_FP
      machineUnaryRangeBound_mem_FP)
  exact machineIfEmpty_mem_FP machineUnaryRangeRemaining_mem_FP id_mem_FP
    hadvance

theorem machineUnaryRangeInputBound_mem_FP :
    machineUnaryRangeInputBound ∈ Complexity.FP :=
  machineListUpdateInputBound_mem_FP

theorem machineUnaryRangeInit_mem_FP :
    machineUnaryRangeInit ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      machineUnaryRangeInputBound_mem_FP)

theorem machineUnaryRangeWidth_mem_FP :
    machineUnaryRangeWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineUnaryRangeInputBound_mem_FP
    (machinePair_mem_FP machineUnaryRangeInputBound_mem_FP
      machineUnaryRangeInputBound_mem_FP)

@[simp] theorem machineUnaryRangeRemaining_pack (a b c) :
    machineUnaryRangeRemaining (machineUnaryRangePack a b c) = a := by
  simp [machineUnaryRangeRemaining, machineUnaryRangePack]

@[simp] theorem machineUnaryRangeAcc_pack (a b c) :
    machineUnaryRangeAcc (machineUnaryRangePack a b c) = b := by
  simp [machineUnaryRangeAcc, machineUnaryRangePack]

@[simp] theorem machineUnaryRangeBound_pack (a b c) :
    machineUnaryRangeBound (machineUnaryRangePack a b c) = c := by
  simp [machineUnaryRangeBound, machineUnaryRangePack]

def MachineUnaryRangeStateBound (ruler state : List Bool) : Prop :=
  let B := (machineUnaryRangeInputBound ruler).length
  state = machineUnaryRangePack
      (machineUnaryRangeRemaining state)
      (machineUnaryRangeAcc state)
      (machineUnaryRangeBound state) ∧
    (machineUnaryRangeRemaining state).length ≤ B ∧
    (machineUnaryRangeAcc state).length ≤ B ∧
    (machineUnaryRangeBound state).length ≤ B

theorem machineUnaryRange_ruler_le_bound (ruler : List Bool) :
    ruler.length ≤ (machineUnaryRangeInputBound ruler).length := by
  simp only [machineUnaryRangeInputBound, machineListUpdateInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  nlinarith

theorem machineUnaryRangeInit_bound (ruler : List Bool) :
    MachineUnaryRangeStateBound ruler (machineUnaryRangeInit ruler) := by
  simp only [MachineUnaryRangeStateBound, machineUnaryRangeInit,
    machineUnaryRangeRemaining_pack, machineUnaryRangeAcc_pack,
    machineUnaryRangeBound_pack]
  exact ⟨trivial, machineUnaryRange_ruler_le_bound ruler, by simp, le_rfl⟩

theorem machineUnaryRangeStep_bound {ruler state : List Bool}
    (hstate : MachineUnaryRangeStateBound ruler state) :
    MachineUnaryRangeStateBound ruler (machineUnaryRangeStep state) := by
  dsimp only [MachineUnaryRangeStateBound] at hstate ⊢
  rcases hstate with ⟨hpack, hremaining, hacc, hbound⟩
  cases hremainingEq : machineUnaryRangeRemaining state with
  | nil =>
    rw [hremainingEq] at hpack hremaining
    rw [machineUnaryRangeStep]
    simp only [hremainingEq, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hacc, hbound⟩
  | cons bit tail =>
    have htail : tail.length ≤
        (machineUnaryRangeInputBound ruler).length := by
      rw [hremainingEq] at hremaining
      simp only [List.length_cons] at hremaining
      omega
    rw [machineUnaryRangeStep]
    simp only [hremainingEq, machineIfEmpty_cons,
      machineUnaryRangeRemaining_pack, machineUnaryRangeAcc_pack,
      machineUnaryRangeBound_pack]
    refine ⟨trivial, htail, ?_, hbound⟩
    · simp only [machineUnaryRangeNextAcc, List.length_take]
      exact (Nat.min_le_left _ _).trans hbound

theorem machineUnaryRangeIterate_bound (ruler : List Bool) : ∀ k,
    MachineUnaryRangeStateBound ruler
      ((machineUnaryRangeStep)^[k] (machineUnaryRangeInit ruler)) := by
  intro k
  induction k with
  | zero => simpa using! machineUnaryRangeInit_bound ruler
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineUnaryRangeStep_bound ih

theorem machineUnaryRangeIterate_length_le_width
    (ruler : List Bool) (iterations : ℕ)
    (_ : iterations ≤ ruler.length) :
    ((machineUnaryRangeStep)^[iterations]
      (machineUnaryRangeInit ruler)).length ≤
        (machineUnaryRangeWidth ruler).length := by
  have hbound := machineUnaryRangeIterate_bound ruler iterations
  dsimp only [MachineUnaryRangeStateBound] at hbound
  rcases hbound with ⟨hpack, hremaining, hacc, hbound⟩
  rw [hpack]
  simp only [machineUnaryRangePack, machineUnaryRangeWidth, pair_length]
  omega

theorem machineUnaryRangeFinalState_mem_FP :
    machineUnaryRangeFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineUnaryRangeStep_mem_FP
    machineUnaryRangeInit_mem_FP id_mem_FP machineUnaryRangeWidth_mem_FP
    machineUnaryRangeIterate_length_le_width

theorem machineUnaryRangeCode_mem_FP :
    machineUnaryRangeCode ∈ Complexity.FP := by
  simpa only [machineUnaryRangeCode] using!
    machineCompose_mem_FP machineUnaryRangeFinalState_mem_FP
      machineUnaryRangeAcc_mem_FP

/-! ## Exact semantics -/

def machineUnaryRangeSemanticState (n k : ℕ) : List Bool :=
  machineUnaryRangePack (List.replicate (n - k) true)
    (binaryListCode finUnaryCode ((List.finRange n).drop (n - k)))
    (machineUnaryRangeInputBound (List.replicate n true))

theorem finRangeUnaryCode_length_le_bound (n : ℕ) :
    (finRangeUnaryCode n).length ≤
      (machineUnaryRangeInputBound (List.replicate n true)).length := by
  rw [finRangeUnaryCode, binaryListCode_length_eq_sum]
  have heach : ∀ i ∈ List.finRange n,
      (finUnaryCode i).length ≤ n := by
    intro i _
    simpa [finUnaryCode] using! i.isLt.le
  have hsum :
      ((List.finRange n).map fun i ↦ 2 * (finUnaryCode i).length + 2).sum ≤
        n * (2 * n + 2) := by
    have h := List.sum_le_card_nsmul
      ((List.finRange n).map fun i ↦ 2 * (finUnaryCode i).length + 2)
      (2 * n + 2) (by
        intro value hvalue
        rw [List.mem_map] at hvalue
        obtain ⟨i, hi, rfl⟩ := hvalue
        have := heach i hi
        omega)
    simpa [List.length_finRange, Nat.nsmul_eq_mul] using! h
  simp only [machineUnaryRangeInputBound, machineListUpdateInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  exact hsum.trans (by nlinarith)

@[simp] theorem machineUnaryRangeSemanticState_zero (n : ℕ) :
    machineUnaryRangeSemanticState n 0 =
      machineUnaryRangeInit (List.replicate n true) := by
  rw [machineUnaryRangeSemanticState, machineUnaryRangeInit,
    List.drop_eq_nil_of_le (by simp)]
  rfl

theorem machineUnaryRangeSemanticState_step (n k : ℕ) (hk : k < n) :
    machineUnaryRangeStep (machineUnaryRangeSemanticState n k) =
      machineUnaryRangeSemanticState n (k + 1) := by
  have hindex : n - k - 1 < (List.finRange n).length := by
    simp only [List.length_finRange]
    omega
  have hdrop :
      (List.finRange n).drop (n - k - 1) =
        ⟨n - k - 1, by omega⟩ :: (List.finRange n).drop (n - k) := by
    convert List.drop_eq_getElem_cons hindex using 1 <;>
      simp [List.getElem_finRange] <;> omega
  have hcandidateLength :
      (pair (List.replicate (n - k - 1) true)
        (binaryListCode finUnaryCode
          ((List.finRange n).drop (n - k)))).length ≤
        (machineUnaryRangeInputBound (List.replicate n true)).length := by
    rw [show pair (List.replicate (n - k - 1) true)
          (binaryListCode finUnaryCode ((List.finRange n).drop (n - k))) =
        binaryListCode finUnaryCode ((List.finRange n).drop (n - k - 1)) by
          rw [hdrop]
          rfl]
    exact (binaryListCode_drop_length_le finUnaryCode (List.finRange n)
      (n - k - 1)).trans (finRangeUnaryCode_length_le_bound n)
  have hsub : n - k = (n - k - 1) + 1 := by omega
  have htake :
      (pair (List.replicate (n - k - 1) true)
        (binaryListCode finUnaryCode
          ((List.finRange n).drop (n - k)))).take
          (machineUnaryRangeInputBound (List.replicate n true)).length =
        pair (List.replicate (n - k - 1) true)
          (binaryListCode finUnaryCode
            ((List.finRange n).drop (n - k))) :=
    (List.take_eq_self_iff _).2 hcandidateLength
  have htake' :
      (pair (List.replicate (n - k - 1) true)
        (binaryListCode finUnaryCode
          ((List.finRange n).drop (n - k - 1 + 1)))).take
          (machineUnaryRangeInputBound (List.replicate n true)).length =
        pair (List.replicate (n - k - 1) true)
          (binaryListCode finUnaryCode
            ((List.finRange n).drop (n - k - 1 + 1))) := by
    simpa only [← hsub] using! htake
  have hnext : n - (k + 1) = n - k - 1 := by omega
  rw [machineUnaryRangeSemanticState, hsub, List.replicate_succ,
    machineUnaryRangeStep]
  simp only [machineUnaryRangeSemanticState,
    machineUnaryRangeRemaining_pack, machineIfEmpty_cons,
    machineUnaryRangeAcc_pack, machineUnaryRangeBound_pack,
    machineUnaryRangeNextAcc, machineUnaryRangeCandidate,
    List.tail_cons, htake']
  unfold machineUnaryRangePack
  apply congrArg₂ pair
  · congr 1
  · apply congrArg₂ pair
    · rw [hnext, hdrop]
      rw [← hsub]
      rfl
    · rfl

theorem machineUnaryRangeIterate_semantics (n k : ℕ) (hk : k ≤ n) :
    (machineUnaryRangeStep)^[k]
        (machineUnaryRangeInit (List.replicate n true)) =
      machineUnaryRangeSemanticState n k := by
  induction k with
  | zero => exact (machineUnaryRangeSemanticState_zero n).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega),
        machineUnaryRangeSemanticState_step n k (by omega)]

@[simp] theorem machineUnaryRangeCode_encode (n : ℕ) :
    machineUnaryRangeCode (List.replicate n true) = finRangeUnaryCode n := by
  rw [machineUnaryRangeCode, machineUnaryRangeFinalState,
    List.length_replicate, machineUnaryRangeIterate_semantics n n le_rfl,
    machineUnaryRangeSemanticState, machineUnaryRangeAcc_pack]
  simp [finRangeUnaryCode]

end BeyondBethe

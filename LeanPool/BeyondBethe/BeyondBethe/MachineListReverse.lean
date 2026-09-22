/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineListUpdate
import Mathlib.Tactic

/-!
# Reversal of a self-delimiting machine list

The machine scans a right-nested list code and pushes each decoded head onto
an accumulator.  The accumulator is clamped to the input-word length on
arbitrary malformed strings.  On canonical list codes its length never
exceeds the input length, so the semantic proof below shows that the clamp is
inactive.
-/

namespace BeyondBethe

open Complexity

def machineListReversePack
    (remaining accumulator bound : List Bool) : List Bool :=
  pair remaining (pair accumulator bound)

def machineListReverseRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineListReverseAccumulator (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineListReverseBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineListReverseCandidate (state : List Bool) : List Bool :=
  pair (machineListHead (machineListReverseRemaining state))
    (machineListReverseAccumulator state)

def machineListReverseNextAccumulator (state : List Bool) : List Bool :=
  (machineListReverseCandidate state).take
    (machineListReverseBound state).length

def machineListReverseAdvance (state : List Bool) : List Bool :=
  machineListReversePack
    (machineListTail (machineListReverseRemaining state))
    (machineListReverseNextAccumulator state)
    (machineListReverseBound state)

def machineListReverseStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineListReverseRemaining state) state
    (machineListReverseAdvance state)

def machineListReverseInit (word : List Bool) : List Bool :=
  machineListReversePack word [] word

def machineListReverseWidth (word : List Bool) : List Bool :=
  machineListReversePack word word word

def machineListReverseFinalState (word : List Bool) : List Bool :=
  (machineListReverseStep)^[word.length] (machineListReverseInit word)

def machineListReverse (word : List Bool) : List Bool :=
  machineListReverseAccumulator (machineListReverseFinalState word)

theorem machineListReverseRemaining_mem_FP :
    machineListReverseRemaining ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineListReverseAccumulator_mem_FP :
    machineListReverseAccumulator ∈ Complexity.FP := by
  simpa only [machineListReverseAccumulator] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineListReverseBound_mem_FP :
    machineListReverseBound ∈ Complexity.FP := by
  simpa only [machineListReverseBound] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineListReverseCandidate_mem_FP :
    machineListReverseCandidate ∈ Complexity.FP := by
  have hhead := machineCompose_mem_FP machineListReverseRemaining_mem_FP
    machineListHead_mem_FP
  exact machinePair_mem_FP hhead machineListReverseAccumulator_mem_FP

theorem machineListReverseNextAccumulator_mem_FP :
    machineListReverseNextAccumulator ∈ Complexity.FP := by
  simpa only [machineListReverseNextAccumulator] using!
    machineTake_mem_FP machineListReverseBound_mem_FP
      machineListReverseCandidate_mem_FP

theorem machineListReverseAdvance_mem_FP :
    machineListReverseAdvance ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineListReverseRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineListReverseNextAccumulator_mem_FP
      machineListReverseBound_mem_FP)

theorem machineListReverseStep_mem_FP :
    machineListReverseStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineListReverseRemaining_mem_FP id_mem_FP
    machineListReverseAdvance_mem_FP

theorem machineListReverseInit_mem_FP :
    machineListReverseInit ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP []) id_mem_FP)

theorem machineListReverseWidth_mem_FP :
    machineListReverseWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP id_mem_FP)

@[simp] theorem machineListReverseRemaining_pack (a b c) :
    machineListReverseRemaining (machineListReversePack a b c) = a := by
  simp [machineListReverseRemaining, machineListReversePack]

@[simp] theorem machineListReverseAccumulator_pack (a b c) :
    machineListReverseAccumulator (machineListReversePack a b c) = b := by
  simp [machineListReverseAccumulator, machineListReversePack]

@[simp] theorem machineListReverseBound_pack (a b c) :
    machineListReverseBound (machineListReversePack a b c) = c := by
  simp [machineListReverseBound, machineListReversePack]

def MachineListReverseStateBound (word state : List Bool) : Prop :=
  state = machineListReversePack
      (machineListReverseRemaining state)
      (machineListReverseAccumulator state)
      (machineListReverseBound state) ∧
    (machineListReverseRemaining state).length ≤ word.length ∧
    (machineListReverseAccumulator state).length ≤ word.length ∧
    machineListReverseBound state = word

theorem machineListReverseInit_bound (word : List Bool) :
    MachineListReverseStateBound word (machineListReverseInit word) := by
  simp [MachineListReverseStateBound, machineListReverseInit]

theorem machineListReverseStep_bound {word state : List Bool}
    (hstate : MachineListReverseStateBound word state) :
    MachineListReverseStateBound word (machineListReverseStep state) := by
  rcases hstate with ⟨hdecomp, hremaining, haccumulator, hbound⟩
  by_cases hnil : machineListReverseRemaining state = []
  · rw [machineListReverseStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, haccumulator, hbound⟩
  · rw [machineListReverseStep]
    cases hremainingCode : machineListReverseRemaining state with
    | nil => exact False.elim (hnil hremainingCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineListReverseAdvance]
        simp only [MachineListReverseStateBound,
          machineListReverseRemaining_pack,
          machineListReverseAccumulator_pack,
          machineListReverseBound_pack]
        refine ⟨trivial, ?_, ?_, hbound⟩
        · exact (machineListTail_length_le
            (machineListReverseRemaining state)).trans hremaining
        · rw [machineListReverseNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineListReverseIterate_bound (word : List Bool) : ∀ k,
    MachineListReverseStateBound word
      ((machineListReverseStep)^[k] (machineListReverseInit word)) := by
  intro k
  induction k with
  | zero => exact machineListReverseInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineListReverseStep_bound ih

theorem machineListReverseIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineListReverseStep)^[iterations]
      (machineListReverseInit word)).length ≤
        (machineListReverseWidth word).length := by
  rcases machineListReverseIterate_bound word iterations with
    ⟨hdecomp, hremaining, haccumulator, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineListReversePack, machineListReverseWidth, pair_length]
  omega

theorem machineListReverseFinalState_mem_FP :
    machineListReverseFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineListReverseStep_mem_FP
    machineListReverseInit_mem_FP id_mem_FP machineListReverseWidth_mem_FP
    machineListReverseIterate_length_le_width

theorem machineListReverse_mem_FP : machineListReverse ∈ Complexity.FP := by
  simpa only [machineListReverse] using!
    machineCompose_mem_FP machineListReverseFinalState_mem_FP
      machineListReverseAccumulator_mem_FP

/-! ## Exact semantics on canonical list codes -/

def machineListReverseSemanticState
    {alpha : Type*} (encode : alpha → List Bool)
    (xs : List alpha) (k : ℕ) : List Bool :=
  machineListReversePack
    (binaryListCode encode (xs.drop k))
    (binaryListCode encode (xs.take k).reverse)
    (binaryListCode encode xs)

theorem machineListReverseInit_semantics
    {alpha : Type*} (encode : alpha → List Bool) (xs : List alpha) :
    machineListReverseInit (binaryListCode encode xs) =
      machineListReverseSemanticState encode xs 0 := by
  simp [machineListReverseInit, machineListReverseSemanticState,
    binaryListCode]

theorem machineListReverseStep_semantics
    {alpha : Type*} (encode : alpha → List Bool)
    (xs : List alpha) (k : ℕ) (hk : k < xs.length) :
    machineListReverseStep
        (machineListReverseSemanticState encode xs k) =
      machineListReverseSemanticState encode xs (k + 1) := by
  have hdrop := List.drop_eq_getElem_cons hk
  have htake := List.take_concat_get hk
  have hprefix : (xs.take (k + 1)).reverse =
      xs[k] :: (xs.take k).reverse := by
    rw [← htake]
    simpa only [List.concat_eq_append] using!
      (List.reverse_concat (l := xs.take k) (a := xs[k]))
  have hprefixLength :
      (binaryListCode encode (xs.take (k + 1)).reverse).length ≤
        (binaryListCode encode xs).length :=
    binaryListCode_take_reverse_length_le encode xs (k + 1)
  have htakeBound :
      (binaryListCode encode (xs.take (k + 1)).reverse).take
          (binaryListCode encode xs).length =
        binaryListCode encode (xs.take (k + 1)).reverse :=
    List.take_of_length_le hprefixLength
  have hnonempty : binaryListCode encode (xs.drop k) ≠ [] := by
    rw [hdrop]
    intro hnil
    have hlen := congrArg List.length hnil
    simp [binaryListCode] at hlen
  rw [machineListReverseStep]
  simp only [machineListReverseSemanticState,
    machineListReverseRemaining_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hnonempty,
    machineListReverseAdvance]
  simp only [machineListReverseRemaining_pack,
    machineListReverseAccumulator_pack, machineListReverseBound_pack,
    machineListReverseNextAccumulator, machineListReverseCandidate]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineListReversePack (binaryListCode encode (xs.drop (k + 1)))
      ((binaryListCode encode
        (xs[k] :: (xs.take k).reverse)).take
          (binaryListCode encode xs).length)
      (binaryListCode encode xs) = _
  rw [← hprefix, htakeBound]

theorem machineListReverseIterate_semantics
    {alpha : Type*} (encode : alpha → List Bool)
    (xs : List alpha) : ∀ k ≤ xs.length,
    (machineListReverseStep)^[k]
        (machineListReverseInit (binaryListCode encode xs)) =
      machineListReverseSemanticState encode xs k := by
  intro k hk
  induction k with
  | zero => exact machineListReverseInit_semantics encode xs
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineListReverseStep_semantics encode xs k (by omega)

theorem binaryListCode_listLength_le
    {alpha : Type*} (encode : alpha → List Bool) : ∀ xs : List alpha,
    xs.length ≤ (binaryListCode encode xs).length := by
  intro xs
  induction xs with
  | nil => simp [binaryListCode]
  | cons x xs ih =>
      simp only [List.length_cons, binaryListCode, pair_length]
      omega

theorem machineListReverse_done_iterate
    (extra : ℕ) (accumulator bound : List Bool) :
    (machineListReverseStep)^[extra]
        (machineListReversePack [] accumulator bound) =
      machineListReversePack [] accumulator bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineListReverseStep]

theorem machineListReverseFinalState_encode
    {alpha : Type*} (encode : alpha → List Bool) (xs : List alpha) :
    machineListReverseFinalState (binaryListCode encode xs) =
      machineListReversePack [] (binaryListCode encode xs.reverse)
        (binaryListCode encode xs) := by
  let word := binaryListCode encode xs
  have hlength : xs.length ≤ word.length :=
    binaryListCode_listLength_le encode xs
  have hsplit : word.length =
      (word.length - xs.length) + xs.length := by omega
  change (machineListReverseStep)^[word.length]
      (machineListReverseInit word) = _
  rw [hsplit, Function.iterate_add_apply,
    machineListReverseIterate_semantics encode xs xs.length le_rfl]
  simp only [machineListReverseSemanticState, List.drop_length,
    List.take_length, binaryListCode, word]
  rw [machineListReverse_done_iterate]

@[simp] theorem machineListReverse_encode
    {alpha : Type*} (encode : alpha → List Bool) (xs : List alpha) :
    machineListReverse (binaryListCode encode xs) =
      binaryListCode encode xs.reverse := by
  rw [machineListReverse, machineListReverseFinalState_encode]
  simp

end BeyondBethe

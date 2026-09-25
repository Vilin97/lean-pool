/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineListIndex

/-!
# Indexed update of right-nested machine lists

This file supplies the mutable-array primitive used by the matching and
ellipsoid machines.  The input is
`pair indexUnary (pair replacement listCode)`.  A first bounded pass removes
the indexed prefix while storing it in reverse order.  A second bounded pass
rebuilds the prefix around the replacement.  Both passes clamp their growing
field to an explicit quadratic word.  The semantic invariant proves that the
clamps are inactive on every canonical in-range list update.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Forward scan -/

def machineListUpdateRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineListUpdatePayload (word : List Bool) : List Bool :=
  machinePairSecond word

def machineListUpdateReplacement (word : List Bool) : List Bool :=
  machinePairFirst (machineListUpdatePayload word)

def machineListUpdateData (word : List Bool) : List Bool :=
  machinePairSecond (machineListUpdatePayload word)

def machineListUpdateInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth word)

def machineListUpdateScanPack
    (remaining pref current replacement bound : List Bool) : List Bool :=
  pair remaining (pair pref (pair current (pair replacement bound)))

def machineListUpdateScanRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineListUpdateScanPrefix (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineListUpdateScanCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineListUpdateScanReplacement (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineListUpdateScanBound (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineListUpdateScanPrefixCandidate (state : List Bool) : List Bool :=
  pair (machineListHead (machineListUpdateScanCurrent state))
    (machineListUpdateScanPrefix state)

def machineListUpdateScanNextPrefix (state : List Bool) : List Bool :=
  (machineListUpdateScanPrefixCandidate state).take
    (machineListUpdateScanBound state).length

def machineListUpdateScanAdvance (state : List Bool) : List Bool :=
  machineListUpdateScanPack
    (machineListUpdateScanRemaining state).tail
    (machineListUpdateScanNextPrefix state)
    (machineListTail (machineListUpdateScanCurrent state))
    (machineListUpdateScanReplacement state)
    (machineListUpdateScanBound state)

def machineListUpdateScanStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineListUpdateScanRemaining state) state
    (machineIfEmpty (machineListUpdateScanCurrent state) state
      (machineListUpdateScanAdvance state))

def machineListUpdateScanInit (word : List Bool) : List Bool :=
  machineListUpdateScanPack (machineListUpdateRuler word) []
    (machineListUpdateData word) (machineListUpdateReplacement word)
    (machineListUpdateInputBound word)

def machineListUpdateScanWidth (word : List Bool) : List Bool :=
  let bound := machineListUpdateInputBound word
  machineListUpdateScanPack bound bound bound bound bound

def machineListUpdateScanFinalState (word : List Bool) : List Bool :=
  (machineListUpdateScanStep)^[(machineListUpdateRuler word).length]
    (machineListUpdateScanInit word)

theorem machineListUpdateRuler_mem_FP :
    machineListUpdateRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineListUpdatePayload_mem_FP :
    machineListUpdatePayload ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineListUpdateReplacement_mem_FP :
    machineListUpdateReplacement ∈ Complexity.FP := by
  simpa only [machineListUpdateReplacement] using!
    machineCompose_mem_FP machineListUpdatePayload_mem_FP
      machinePairFirst_mem_FP

theorem machineListUpdateData_mem_FP :
    machineListUpdateData ∈ Complexity.FP := by
  simpa only [machineListUpdateData] using!
    machineCompose_mem_FP machineListUpdatePayload_mem_FP
      machinePairSecond_mem_FP

theorem machineListUpdateInputBound_mem_FP :
    machineListUpdateInputBound ∈ Complexity.FP := by
  simpa only [machineListUpdateInputBound] using!
    machineCompose_mem_FP machineBinaryMulWidth_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineBinaryMulWidth_length_mono {left right : List Bool}
    (h : left.length ≤ right.length) :
    (machineBinaryMulWidth left).length ≤
      (machineBinaryMulWidth right).length := by
  simp only [machineBinaryMulWidth, List.length_replicate,
    List.length_append]
  simpa [pow_two] using!
    Nat.pow_le_pow_left (Nat.add_le_add_left h 16) 2

theorem machineListUpdateInputBound_length_mono {left right : List Bool}
    (h : left.length ≤ right.length) :
    (machineListUpdateInputBound left).length ≤
      (machineListUpdateInputBound right).length := by
  exact machineBinaryMulWidth_length_mono
    (machineBinaryMulWidth_length_mono h)

theorem machineListUpdateScanRemaining_mem_FP :
    machineListUpdateScanRemaining ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineListUpdateScanPrefix_mem_FP :
    machineListUpdateScanPrefix ∈ Complexity.FP := by
  simpa only [machineListUpdateScanPrefix] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineListUpdateScanCurrent_mem_FP :
    machineListUpdateScanCurrent ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineListUpdateScanCurrent] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineListUpdateScanReplacement_mem_FP :
    machineListUpdateScanReplacement ∈ Complexity.FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineListUpdateScanReplacement] using!
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineListUpdateScanBound_mem_FP :
    machineListUpdateScanBound ∈ Complexity.FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineListUpdateScanBound] using!
    machineCompose_mem_FP htailThree machinePairSecond_mem_FP

theorem machineListUpdateScanPrefixCandidate_mem_FP :
    machineListUpdateScanPrefixCandidate ∈ Complexity.FP := by
  have hhead := machineCompose_mem_FP
    machineListUpdateScanCurrent_mem_FP machineListHead_mem_FP
  exact machinePair_mem_FP hhead machineListUpdateScanPrefix_mem_FP

theorem machineListUpdateScanNextPrefix_mem_FP :
    machineListUpdateScanNextPrefix ∈ Complexity.FP := by
  simpa only [machineListUpdateScanNextPrefix] using!
    machineTake_mem_FP machineListUpdateScanBound_mem_FP
      machineListUpdateScanPrefixCandidate_mem_FP

theorem machineListUpdateScanAdvance_mem_FP :
    machineListUpdateScanAdvance ∈ Complexity.FP := by
  have hremaining := machineCompose_mem_FP
    machineListUpdateScanRemaining_mem_FP machineTail_mem_FP
  have hcurrent := machineCompose_mem_FP
    machineListUpdateScanCurrent_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP hremaining
    (machinePair_mem_FP machineListUpdateScanNextPrefix_mem_FP
      (machinePair_mem_FP hcurrent
        (machinePair_mem_FP machineListUpdateScanReplacement_mem_FP
          machineListUpdateScanBound_mem_FP)))

theorem machineListUpdateScanStep_mem_FP :
    machineListUpdateScanStep ∈ Complexity.FP := by
  have hinner := machineIfEmpty_mem_FP
    machineListUpdateScanCurrent_mem_FP id_mem_FP
    machineListUpdateScanAdvance_mem_FP
  simpa only [machineListUpdateScanStep] using!
    machineIfEmpty_mem_FP machineListUpdateScanRemaining_mem_FP
      id_mem_FP hinner

theorem machineListUpdateScanInit_mem_FP :
    machineListUpdateScanInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineListUpdateRuler_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineListUpdateData_mem_FP
        (machinePair_mem_FP machineListUpdateReplacement_mem_FP
          machineListUpdateInputBound_mem_FP)))

theorem machineListUpdateScanWidth_mem_FP :
    machineListUpdateScanWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineListUpdateInputBound_mem_FP
    (machinePair_mem_FP machineListUpdateInputBound_mem_FP
      (machinePair_mem_FP machineListUpdateInputBound_mem_FP
        (machinePair_mem_FP machineListUpdateInputBound_mem_FP
          machineListUpdateInputBound_mem_FP)))

@[simp] theorem machineListUpdateScanRemaining_pack (a b c d e) :
    machineListUpdateScanRemaining
      (machineListUpdateScanPack a b c d e) = a := by
  simp [machineListUpdateScanRemaining, machineListUpdateScanPack]

@[simp] theorem machineListUpdateScanPrefix_pack (a b c d e) :
    machineListUpdateScanPrefix
      (machineListUpdateScanPack a b c d e) = b := by
  simp [machineListUpdateScanPrefix, machineListUpdateScanPack]

@[simp] theorem machineListUpdateScanCurrent_pack (a b c d e) :
    machineListUpdateScanCurrent
      (machineListUpdateScanPack a b c d e) = c := by
  simp [machineListUpdateScanCurrent, machineListUpdateScanPack]

@[simp] theorem machineListUpdateScanReplacement_pack (a b c d e) :
    machineListUpdateScanReplacement
      (machineListUpdateScanPack a b c d e) = d := by
  simp [machineListUpdateScanReplacement, machineListUpdateScanPack]

@[simp] theorem machineListUpdateScanBound_pack (a b c d e) :
    machineListUpdateScanBound
      (machineListUpdateScanPack a b c d e) = e := by
  simp [machineListUpdateScanBound, machineListUpdateScanPack]

theorem machineListUpdate_word_length_le_bound (word : List Bool) :
    word.length ≤ (machineListUpdateInputBound word).length := by
  simp only [machineListUpdateInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

def MachineListUpdateScanStateBound
    (word state : List Bool) : Prop :=
  let B := (machineListUpdateInputBound word).length
  state = machineListUpdateScanPack
      (machineListUpdateScanRemaining state)
      (machineListUpdateScanPrefix state)
      (machineListUpdateScanCurrent state)
      (machineListUpdateScanReplacement state)
      (machineListUpdateScanBound state) ∧
    (machineListUpdateScanRemaining state).length ≤ B ∧
    (machineListUpdateScanPrefix state).length ≤ B ∧
    (machineListUpdateScanCurrent state).length ≤ B ∧
    (machineListUpdateScanReplacement state).length ≤ B ∧
    (machineListUpdateScanBound state).length ≤ B

theorem machineListUpdateScanInit_bound (word : List Bool) :
    MachineListUpdateScanStateBound word
      (machineListUpdateScanInit word) := by
  simp only [MachineListUpdateScanStateBound, machineListUpdateScanInit,
    machineListUpdateScanRemaining_pack, machineListUpdateScanPrefix_pack,
    machineListUpdateScanCurrent_pack,
    machineListUpdateScanReplacement_pack,
    machineListUpdateScanBound_pack]
  have hword := machineListUpdate_word_length_le_bound word
  refine ⟨trivial, ?_, by simp, ?_, ?_, le_rfl⟩
  · exact (machinePairFirst_length_le word).trans hword
  · exact (machinePairSecond_length_le
      (machineListUpdatePayload word)).trans
      ((machinePairSecond_length_le word).trans hword)
  · exact (machinePairFirst_length_le
      (machineListUpdatePayload word)).trans
      ((machinePairSecond_length_le word).trans hword)

theorem machineListUpdateScanStep_bound
    {word state : List Bool}
    (hstate : MachineListUpdateScanStateBound word state) :
    MachineListUpdateScanStateBound word
      (machineListUpdateScanStep state) := by
  dsimp only [MachineListUpdateScanStateBound] at hstate ⊢
  rcases hstate with ⟨hdecomp, hrem, hprefix, hcurrent, hrepl, hbound⟩
  by_cases hr : machineListUpdateScanRemaining state = []
  · rw [machineListUpdateScanStep, hr, machineIfEmpty_nil]
    exact ⟨hdecomp, hrem, hprefix, hcurrent, hrepl, hbound⟩
  · cases hremCode : machineListUpdateScanRemaining state with
    | nil => exact False.elim (hr hremCode)
    | cons rb rt =>
      rw [machineListUpdateScanStep, hremCode, machineIfEmpty_cons]
      by_cases hc : machineListUpdateScanCurrent state = []
      · rw [hc, machineIfEmpty_nil]
        exact ⟨hdecomp, hrem, hprefix, hcurrent, hrepl, hbound⟩
      · cases hcurrentCode : machineListUpdateScanCurrent state with
        | nil => exact False.elim (hc hcurrentCode)
        | cons cb ct =>
          rw [machineIfEmpty_cons, machineListUpdateScanAdvance]
          simp only [machineListUpdateScanRemaining_pack,
            machineListUpdateScanPrefix_pack,
            machineListUpdateScanCurrent_pack,
            machineListUpdateScanReplacement_pack,
            machineListUpdateScanBound_pack]
          refine ⟨trivial, ?_, ?_, ?_, hrepl, hbound⟩
          · rw [List.length_tail]
            omega
          · exact (List.length_take_le _ _).trans hbound
          · exact (machineListTail_length_le _).trans hcurrent

theorem machineListUpdateScanIterate_bound (word : List Bool) : ∀ k,
    MachineListUpdateScanStateBound word
      ((machineListUpdateScanStep)^[k]
        (machineListUpdateScanInit word)) := by
  intro k
  induction k with
  | zero => exact machineListUpdateScanInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineListUpdateScanStep_bound ih

theorem machineListUpdateScanIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineListUpdateRuler word).length) :
    ((machineListUpdateScanStep)^[iterations]
      (machineListUpdateScanInit word)).length ≤
        (machineListUpdateScanWidth word).length := by
  rcases machineListUpdateScanIterate_bound word iterations with
    ⟨hdecomp, hrem, hprefix, hcurrent, hrepl, hbound⟩
  rw [hdecomp]
  simp only [machineListUpdateScanPack, machineListUpdateScanWidth,
    pair_length]
  omega

theorem machineListUpdateScanFinalState_mem_FP :
    machineListUpdateScanFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineListUpdateScanStep_mem_FP
    machineListUpdateScanInit_mem_FP machineListUpdateRuler_mem_FP
    machineListUpdateScanWidth_mem_FP
    machineListUpdateScanIterate_length_le_width

/-! ## Reverse-prefix rebuild -/

def machineListUpdateSeed (word : List Bool) : List Bool :=
  let scan := machineListUpdateScanFinalState word
  machineIfEmpty (machineListUpdateScanCurrent scan) []
    ((pair (machineListUpdateScanReplacement scan)
      (machineListTail (machineListUpdateScanCurrent scan))).take
        (machineListUpdateScanBound scan).length)

def machineListUpdateRebuildPack
    (pref output bound : List Bool) : List Bool :=
  pair pref (pair output bound)

def machineListUpdateRebuildPrefix (state : List Bool) : List Bool :=
  machinePairFirst state

def machineListUpdateRebuildOutput (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineListUpdateRebuildBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineListUpdateRebuildCandidate (state : List Bool) : List Bool :=
  pair (machineListHead (machineListUpdateRebuildPrefix state))
    (machineListUpdateRebuildOutput state)

def machineListUpdateRebuildNextOutput (state : List Bool) : List Bool :=
  (machineListUpdateRebuildCandidate state).take
    (machineListUpdateRebuildBound state).length

def machineListUpdateRebuildAdvance (state : List Bool) : List Bool :=
  machineListUpdateRebuildPack
    (machineListTail (machineListUpdateRebuildPrefix state))
    (machineListUpdateRebuildNextOutput state)
    (machineListUpdateRebuildBound state)

def machineListUpdateRebuildStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineListUpdateRebuildPrefix state) state
    (machineListUpdateRebuildAdvance state)

def machineListUpdateRebuildInit (word : List Bool) : List Bool :=
  let scan := machineListUpdateScanFinalState word
  machineListUpdateRebuildPack (machineListUpdateScanPrefix scan)
    (machineListUpdateSeed word) (machineListUpdateScanBound scan)

def machineListUpdateRebuildWidth (word : List Bool) : List Bool :=
  let bound := machineListUpdateInputBound word
  machineListUpdateRebuildPack bound bound bound

def machineListUpdateRebuildFinalState (word : List Bool) : List Bool :=
  (machineListUpdateRebuildStep)^[(machineListUpdateRuler word).length]
    (machineListUpdateRebuildInit word)

/-- Replace the element at the unary index.  Out-of-range and malformed
inputs return a total, polynomially bounded default determined above. -/
def machineListUpdate (word : List Bool) : List Bool :=
  machineListUpdateRebuildOutput
    (machineListUpdateRebuildFinalState word)

theorem machineListUpdateSeed_mem_FP :
    machineListUpdateSeed ∈ Complexity.FP := by
  let scan : List Bool → List Bool := machineListUpdateScanFinalState
  have hscan : scan ∈ Complexity.FP :=
    machineListUpdateScanFinalState_mem_FP
  have hcurrent := machineCompose_mem_FP hscan
    machineListUpdateScanCurrent_mem_FP
  have hrepl := machineCompose_mem_FP hscan
    machineListUpdateScanReplacement_mem_FP
  have htailCurrent := machineCompose_mem_FP hcurrent machineListTail_mem_FP
  have hcandidate := machinePair_mem_FP hrepl htailCurrent
  have hbound := machineCompose_mem_FP hscan
    machineListUpdateScanBound_mem_FP
  have htaken := machineTake_mem_FP hbound hcandidate
  simpa only [machineListUpdateSeed, scan] using!
    machineIfEmpty_mem_FP hcurrent (machineConst_mem_FP []) htaken

theorem machineListUpdateRebuildPrefix_mem_FP :
    machineListUpdateRebuildPrefix ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineListUpdateRebuildOutput_mem_FP :
    machineListUpdateRebuildOutput ∈ Complexity.FP := by
  simpa only [machineListUpdateRebuildOutput] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineListUpdateRebuildBound_mem_FP :
    machineListUpdateRebuildBound ∈ Complexity.FP := by
  simpa only [machineListUpdateRebuildBound] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineListUpdateRebuildCandidate_mem_FP :
    machineListUpdateRebuildCandidate ∈ Complexity.FP := by
  have hhead := machineCompose_mem_FP
    machineListUpdateRebuildPrefix_mem_FP machineListHead_mem_FP
  exact machinePair_mem_FP hhead machineListUpdateRebuildOutput_mem_FP

theorem machineListUpdateRebuildNextOutput_mem_FP :
    machineListUpdateRebuildNextOutput ∈ Complexity.FP := by
  simpa only [machineListUpdateRebuildNextOutput] using!
    machineTake_mem_FP machineListUpdateRebuildBound_mem_FP
      machineListUpdateRebuildCandidate_mem_FP

theorem machineListUpdateRebuildAdvance_mem_FP :
    machineListUpdateRebuildAdvance ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP
    machineListUpdateRebuildPrefix_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineListUpdateRebuildNextOutput_mem_FP
      machineListUpdateRebuildBound_mem_FP)

theorem machineListUpdateRebuildStep_mem_FP :
    machineListUpdateRebuildStep ∈ Complexity.FP := by
  simpa only [machineListUpdateRebuildStep] using!
    machineIfEmpty_mem_FP machineListUpdateRebuildPrefix_mem_FP
      id_mem_FP machineListUpdateRebuildAdvance_mem_FP

theorem machineListUpdateRebuildInit_mem_FP :
    machineListUpdateRebuildInit ∈ Complexity.FP := by
  have hprefix := machineCompose_mem_FP
    machineListUpdateScanFinalState_mem_FP machineListUpdateScanPrefix_mem_FP
  have hbound := machineCompose_mem_FP
    machineListUpdateScanFinalState_mem_FP machineListUpdateScanBound_mem_FP
  exact machinePair_mem_FP hprefix
    (machinePair_mem_FP machineListUpdateSeed_mem_FP hbound)

theorem machineListUpdateRebuildWidth_mem_FP :
    machineListUpdateRebuildWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineListUpdateInputBound_mem_FP
    (machinePair_mem_FP machineListUpdateInputBound_mem_FP
      machineListUpdateInputBound_mem_FP)

@[simp] theorem machineListUpdateRebuildPrefix_pack (a b c) :
    machineListUpdateRebuildPrefix
      (machineListUpdateRebuildPack a b c) = a := by
  simp [machineListUpdateRebuildPrefix, machineListUpdateRebuildPack]

@[simp] theorem machineListUpdateRebuildOutput_pack (a b c) :
    machineListUpdateRebuildOutput
      (machineListUpdateRebuildPack a b c) = b := by
  simp [machineListUpdateRebuildOutput, machineListUpdateRebuildPack]

@[simp] theorem machineListUpdateRebuildBound_pack (a b c) :
    machineListUpdateRebuildBound
      (machineListUpdateRebuildPack a b c) = c := by
  simp [machineListUpdateRebuildBound, machineListUpdateRebuildPack]

def MachineListUpdateRebuildStateBound
    (word state : List Bool) : Prop :=
  let B := (machineListUpdateInputBound word).length
  state = machineListUpdateRebuildPack
      (machineListUpdateRebuildPrefix state)
      (machineListUpdateRebuildOutput state)
      (machineListUpdateRebuildBound state) ∧
    (machineListUpdateRebuildPrefix state).length ≤ B ∧
    (machineListUpdateRebuildOutput state).length ≤ B ∧
    (machineListUpdateRebuildBound state).length ≤ B

theorem machineListUpdateRebuildInit_bound (word : List Bool) :
    MachineListUpdateRebuildStateBound word
      (machineListUpdateRebuildInit word) := by
  have hscan := machineListUpdateScanIterate_bound word
    (machineListUpdateRuler word).length
  change MachineListUpdateScanStateBound word
    (machineListUpdateScanFinalState word) at hscan
  dsimp only [MachineListUpdateScanStateBound] at hscan
  rcases hscan with ⟨_, _, hprefix, _, _, hbound⟩
  simp only [MachineListUpdateRebuildStateBound,
    machineListUpdateRebuildInit,
    machineListUpdateRebuildPrefix_pack,
    machineListUpdateRebuildOutput_pack,
    machineListUpdateRebuildBound_pack]
  refine ⟨trivial, hprefix, ?_, hbound⟩
  simp only [machineListUpdateSeed]
  exact (machineIfEmpty_length_le_max _ _ _).trans (by
    apply max_le
    · simp
    · exact (List.length_take_le _ _).trans hbound)

theorem machineListUpdateRebuildStep_bound
    {word state : List Bool}
    (hstate : MachineListUpdateRebuildStateBound word state) :
    MachineListUpdateRebuildStateBound word
      (machineListUpdateRebuildStep state) := by
  dsimp only [MachineListUpdateRebuildStateBound] at hstate ⊢
  rcases hstate with ⟨hdecomp, hprefix, houtput, hbound⟩
  by_cases hp : machineListUpdateRebuildPrefix state = []
  · rw [machineListUpdateRebuildStep, hp, machineIfEmpty_nil]
    exact ⟨hdecomp, hprefix, houtput, hbound⟩
  · cases hprefixCode : machineListUpdateRebuildPrefix state with
    | nil => exact False.elim (hp hprefixCode)
    | cons pb pt =>
      rw [machineListUpdateRebuildStep, hprefixCode]
      rw [machineIfEmpty_cons,
        machineListUpdateRebuildAdvance]
      simp only [machineListUpdateRebuildPrefix_pack,
        machineListUpdateRebuildOutput_pack,
        machineListUpdateRebuildBound_pack]
      refine ⟨trivial, ?_, ?_, hbound⟩
      · exact (machineListTail_length_le _).trans hprefix
      · exact (List.length_take_le _ _).trans hbound

theorem machineListUpdateRebuildIterate_bound (word : List Bool) : ∀ k,
    MachineListUpdateRebuildStateBound word
      ((machineListUpdateRebuildStep)^[k]
        (machineListUpdateRebuildInit word)) := by
  intro k
  induction k with
  | zero => exact machineListUpdateRebuildInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineListUpdateRebuildStep_bound ih

theorem machineListUpdateRebuildIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineListUpdateRuler word).length) :
    ((machineListUpdateRebuildStep)^[iterations]
      (machineListUpdateRebuildInit word)).length ≤
        (machineListUpdateRebuildWidth word).length := by
  rcases machineListUpdateRebuildIterate_bound word iterations with
    ⟨hdecomp, hprefix, houtput, hbound⟩
  rw [hdecomp]
  simp only [machineListUpdateRebuildPack, machineListUpdateRebuildWidth,
    pair_length]
  omega

theorem machineListUpdateRebuildFinalState_mem_FP :
    machineListUpdateRebuildFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineListUpdateRebuildStep_mem_FP
    machineListUpdateRebuildInit_mem_FP machineListUpdateRuler_mem_FP
    machineListUpdateRebuildWidth_mem_FP
    machineListUpdateRebuildIterate_length_le_width

theorem machineListUpdate_mem_FP :
    machineListUpdate ∈ Complexity.FP := by
  simpa only [machineListUpdate] using!
    machineCompose_mem_FP machineListUpdateRebuildFinalState_mem_FP
      machineListUpdateRebuildOutput_mem_FP

/-! ## Exact semantics on canonical list codes -/

theorem binaryListCode_length_eq_sum
    {α : Type*} (encode : α → List Bool) : ∀ xs : List α,
    (binaryListCode encode xs).length =
      (xs.map fun x ↦ 2 * (encode x).length + 2).sum := by
  intro xs
  induction xs with
  | nil => simp [binaryListCode]
  | cons x xs ih =>
      simp only [binaryListCode, pair_length, List.map_cons, List.sum_cons, ih]

private theorem natList_sum_take_le_sum : ∀ (xs : List ℕ) (k : ℕ),
    (xs.take k).sum ≤ xs.sum := by
  intro xs k
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
      cases k with
      | zero => simp
      | succ k =>
          simp only [List.take_succ_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih k) x

theorem binaryListCode_take_reverse_length_le
    {α : Type*} (encode : α → List Bool) (xs : List α) (k : ℕ) :
    (binaryListCode encode (xs.take k).reverse).length ≤
      (binaryListCode encode xs).length := by
  rw [binaryListCode_length_eq_sum, binaryListCode_length_eq_sum,
    List.map_reverse, List.sum_reverse, List.map_take]
  exact natList_sum_take_le_sum _ _

theorem binaryListCode_drop_length_le
    {α : Type*} (encode : α → List Bool) (xs : List α) (k : ℕ) :
    (binaryListCode encode (xs.drop k)).length ≤
      (binaryListCode encode xs).length := by
  rw [binaryListCode_length_eq_sum, binaryListCode_length_eq_sum,
    List.map_drop]
  have h := congrArg List.sum
    (show (xs.map fun x ↦ 2 * (encode x).length + 2).take k ++
        (xs.map fun x ↦ 2 * (encode x).length + 2).drop k =
      xs.map fun x ↦ 2 * (encode x).length + 2 by
      exact List.take_append_drop _ _)
  simp only [List.sum_append] at h
  omega

theorem binaryListCode_element_length_le
    {α : Type*} (encode : α → List Bool)
    {x : α} {xs : List α} (hx : x ∈ xs) :
    (encode x).length ≤ (binaryListCode encode xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [binaryListCode, pair_length]
        omega
      · exact (ih hx).trans (by simp [binaryListCode])

def machineListUpdateCanonicalInput
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ) : List Bool :=
  pair (List.replicate index true)
    (pair (encode replacement) (binaryListCode encode xs))

def machineListUpdateScanSemanticState
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index k : ℕ) : List Bool :=
  let word := machineListUpdateCanonicalInput encode xs replacement index
  machineListUpdateScanPack (List.replicate (index - k) true)
    (binaryListCode encode (xs.take k).reverse)
    (binaryListCode encode (xs.drop k)) (encode replacement)
    (machineListUpdateInputBound word)

theorem machineListUpdateScanInit_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ) :
    machineListUpdateScanInit
        (machineListUpdateCanonicalInput encode xs replacement index) =
      machineListUpdateScanSemanticState encode xs replacement index 0 := by
  simp [machineListUpdateScanInit, machineListUpdateScanSemanticState,
    machineListUpdateCanonicalInput, machineListUpdateRuler,
    machineListUpdateData, machineListUpdatePayload,
    machineListUpdateReplacement, binaryListCode]

theorem machineListUpdateScanStep_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index k : ℕ)
    (hk : k < index) (hindex : index < xs.length) :
    machineListUpdateScanStep
        (machineListUpdateScanSemanticState
          encode xs replacement index k) =
      machineListUpdateScanSemanticState
        encode xs replacement index (k + 1) := by
  let word := machineListUpdateCanonicalInput encode xs replacement index
  have hkxs : k < xs.length := hk.trans hindex
  have hremain : index - k = (index - (k + 1)) + 1 := by omega
  have hdrop := List.drop_eq_getElem_cons hkxs
  have htake := List.take_concat_get hkxs
  have hprefix : (xs.take (k + 1)).reverse =
      xs[k] :: (xs.take k).reverse := by
    rw [← htake]
    simpa only [List.concat_eq_append] using!
      (List.reverse_concat (l := xs.take k) (a := xs[k]))
  have hprefixLength :
      (binaryListCode encode (xs.take (k + 1)).reverse).length ≤
        (machineListUpdateInputBound word).length := by
    exact (binaryListCode_take_reverse_length_le encode xs (k + 1)).trans
      ((show (binaryListCode encode xs).length ≤ word.length by
          simp only [word, machineListUpdateCanonicalInput, pair_length]
          omega).trans
        (machineListUpdate_word_length_le_bound word))
  have htakeBound :
      (binaryListCode encode (xs.take (k + 1)).reverse).take
          (machineListUpdateInputBound word).length =
        binaryListCode encode (xs.take (k + 1)).reverse :=
    List.take_of_length_le hprefixLength
  have hcurrentNonempty :
      binaryListCode encode (xs.drop k) ≠ [] := by
    rw [hdrop]
    intro hnil
    have hlen := congrArg List.length hnil
    simp [binaryListCode] at hlen
  have hhead :
      machineListHead (binaryListCode encode (xs.drop k)) = encode xs[k] := by
    rw [hdrop]
    exact machineListHead_cons encode xs[k] (xs.drop (k + 1))
  have htail :
      machineListTail (binaryListCode encode (xs.drop k)) =
        binaryListCode encode (xs.drop (k + 1)) := by
    rw [hdrop]
    exact machineListTail_cons encode xs[k] (xs.drop (k + 1))
  have hnextPrefix :
      (pair (machineListHead (binaryListCode encode (xs.drop k)))
          (binaryListCode encode (xs.take k).reverse)).take
            (machineListUpdateInputBound word).length =
        binaryListCode encode (xs.take (k + 1)).reverse := by
    rw [hhead]
    change (binaryListCode encode
        (xs[k] :: (xs.take k).reverse)).take
          (machineListUpdateInputBound word).length = _
    rw [← hprefix]
    exact htakeBound
  rw [machineListUpdateScanStep]
  simp only [machineListUpdateScanSemanticState,
    machineListUpdateScanRemaining_pack, hremain, List.replicate_succ,
    machineIfEmpty_cons, machineListUpdateScanCurrent_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hcurrentNonempty]
  simp only [machineListUpdateScanAdvance,
      machineListUpdateScanRemaining_pack, List.tail_cons,
      machineListUpdateScanCurrent_pack,
      machineListUpdateScanReplacement_pack,
      machineListUpdateScanBound_pack,
      machineListUpdateScanNextPrefix,
      machineListUpdateScanPrefixCandidate,
      machineListUpdateScanPrefix_pack]
  rw [hnextPrefix, htail]

theorem machineListUpdateScanIterate_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) : ∀ k ≤ index,
    (machineListUpdateScanStep)^[k]
        (machineListUpdateScanInit
          (machineListUpdateCanonicalInput encode xs replacement index)) =
      machineListUpdateScanSemanticState
        encode xs replacement index k := by
  intro k hk
  induction k with
  | zero => exact machineListUpdateScanInit_semantics _ _ _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineListUpdateScanStep_semantics
        encode xs replacement index k (by omega) hindex

theorem machineListUpdateScanFinalState_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) :
    machineListUpdateScanFinalState
        (machineListUpdateCanonicalInput encode xs replacement index) =
      machineListUpdateScanSemanticState
        encode xs replacement index index := by
  rw [machineListUpdateScanFinalState]
  simp only [machineListUpdateRuler, machineListUpdateCanonicalInput,
    machinePairFirst_pair, List.length_replicate]
  exact machineListUpdateScanIterate_semantics
    encode xs replacement index hindex index le_rfl

theorem binaryListCode_append_length
    {α : Type*} (encode : α → List Bool) : ∀ xs ys : List α,
    (binaryListCode encode (xs ++ ys)).length =
      (binaryListCode encode xs).length +
        (binaryListCode encode ys).length := by
  intro xs ys
  induction xs with
  | nil => simp [binaryListCode]
  | cons x xs ih =>
      simp only [List.cons_append, binaryListCode, pair_length, ih]
      omega

theorem machineListUpdate_double_word_length_le_bound (word : List Bool) :
    2 * word.length ≤ (machineListUpdateInputBound word).length := by
  simp only [machineListUpdateInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineListUpdateSeed_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) :
    machineListUpdateSeed
        (machineListUpdateCanonicalInput encode xs replacement index) =
      binaryListCode encode (replacement :: xs.drop (index + 1)) := by
  let word := machineListUpdateCanonicalInput encode xs replacement index
  have hdrop := List.drop_eq_getElem_cons hindex
  have hseedLength :
      (binaryListCode encode (replacement :: xs.drop (index + 1))).length ≤
        (machineListUpdateInputBound word).length := by
    have hdropLength := binaryListCode_drop_length_le
      encode xs (index + 1)
    have hword :
        (binaryListCode encode
          (replacement :: xs.drop (index + 1))).length ≤ word.length := by
      simp only [binaryListCode, pair_length, word,
        machineListUpdateCanonicalInput]
      omega
    exact hword.trans (machineListUpdate_word_length_le_bound word)
  rw [machineListUpdateSeed, machineListUpdateScanFinalState_semantics
    encode xs replacement index hindex]
  simp only [machineListUpdateScanSemanticState,
    machineListUpdateScanCurrent_pack,
    machineListUpdateScanReplacement_pack,
    machineListUpdateScanBound_pack, Nat.sub_self,
    List.replicate_zero]
  rw [hdrop]
  rw [machineIfEmpty_of_ne_nil]
  · rw [machineListTail_cons]
    change (binaryListCode encode
      (replacement :: xs.drop (index + 1))).take
        (machineListUpdateInputBound word).length = _
    exact List.take_of_length_le hseedLength
  · intro hnil
    have hlen := congrArg List.length hnil
    simp [binaryListCode] at hlen

def machineListUpdateRebuildSemanticState
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index k : ℕ) : List Bool :=
  let word := machineListUpdateCanonicalInput encode xs replacement index
  let pref := (xs.take index).reverse
  let suffix := replacement :: xs.drop (index + 1)
  machineListUpdateRebuildPack (binaryListCode encode (pref.drop k))
    (binaryListCode encode ((pref.take k).reverse ++ suffix))
    (machineListUpdateInputBound word)

theorem machineListUpdateRebuildInit_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) :
    machineListUpdateRebuildInit
        (machineListUpdateCanonicalInput encode xs replacement index) =
      machineListUpdateRebuildSemanticState
        encode xs replacement index 0 := by
  rw [machineListUpdateRebuildInit,
    machineListUpdateScanFinalState_semantics
      encode xs replacement index hindex,
    machineListUpdateSeed_semantics encode xs replacement index hindex]
  simp [machineListUpdateRebuildSemanticState,
    machineListUpdateScanSemanticState, binaryListCode]

theorem machineListUpdateRebuildStep_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index k : ℕ)
    (hk : k < index) (hindex : index < xs.length) :
    machineListUpdateRebuildStep
        (machineListUpdateRebuildSemanticState
          encode xs replacement index k) =
      machineListUpdateRebuildSemanticState
        encode xs replacement index (k + 1) := by
  let word := machineListUpdateCanonicalInput encode xs replacement index
  let pref := (xs.take index).reverse
  let suffix := replacement :: xs.drop (index + 1)
  have hindexLe : index ≤ xs.length := hindex.le
  have hprefLength : pref.length = index := by
    simp [pref, List.length_take_of_le hindexLe]
  have hkPref : k < pref.length := by omega
  have hdrop := List.drop_eq_getElem_cons hkPref
  have htake := List.take_concat_get hkPref
  have hpart : (pref.take (k + 1)).reverse =
      pref[k] :: (pref.take k).reverse := by
    rw [← htake]
    simpa only [List.concat_eq_append] using!
      (List.reverse_concat (l := pref.take k) (a := pref[k]))
  have hprefCodeLength :
      (binaryListCode encode pref).length ≤
        (binaryListCode encode xs).length := by
    simpa only [pref] using!
      binaryListCode_take_reverse_length_le encode xs index
  have hpartCodeLength :
      (binaryListCode encode (pref.take (k + 1)).reverse).length ≤
        word.length := by
    exact (binaryListCode_take_reverse_length_le encode pref (k + 1)).trans
      (hprefCodeLength.trans (by
        simp only [word, machineListUpdateCanonicalInput, pair_length]
        omega))
  have hsuffixCodeLength :
      (binaryListCode encode suffix).length ≤ word.length := by
    have hdropLength := binaryListCode_drop_length_le
      encode xs (index + 1)
    simp only [suffix, binaryListCode, pair_length, word,
      machineListUpdateCanonicalInput]
    omega
  have hnextLength :
      (binaryListCode encode
          ((pref.take (k + 1)).reverse ++ suffix)).length ≤
        (machineListUpdateInputBound word).length := by
    rw [binaryListCode_append_length]
    exact (Nat.add_le_add hpartCodeLength hsuffixCodeLength).trans
      (by simpa [two_mul] using!
        machineListUpdate_double_word_length_le_bound word)
  have htakeBound :
      (binaryListCode encode
          ((pref.take (k + 1)).reverse ++ suffix)).take
            (machineListUpdateInputBound word).length =
        binaryListCode encode
          ((pref.take (k + 1)).reverse ++ suffix) :=
    List.take_of_length_le hnextLength
  have hprefNonempty : binaryListCode encode (pref.drop k) ≠ [] := by
    rw [hdrop]
    intro hnil
    have hlen := congrArg List.length hnil
    simp [binaryListCode] at hlen
  have hhead :
      machineListHead (binaryListCode encode (pref.drop k)) =
        encode pref[k] := by
    rw [hdrop]
    exact machineListHead_cons encode pref[k] (pref.drop (k + 1))
  have htail :
      machineListTail (binaryListCode encode (pref.drop k)) =
        binaryListCode encode (pref.drop (k + 1)) := by
    rw [hdrop]
    exact machineListTail_cons encode pref[k] (pref.drop (k + 1))
  have hnextOutput :
      (pair (machineListHead (binaryListCode encode (pref.drop k)))
          (binaryListCode encode ((pref.take k).reverse ++ suffix))).take
            (machineListUpdateInputBound word).length =
        binaryListCode encode
          ((pref.take (k + 1)).reverse ++ suffix) := by
    rw [hhead]
    change (binaryListCode encode
      (pref[k] :: (pref.take k).reverse ++ suffix)).take
        (machineListUpdateInputBound word).length = _
    rw [← hpart]
    exact htakeBound
  rw [machineListUpdateRebuildStep]
  simp only [machineListUpdateRebuildSemanticState,
    machineListUpdateRebuildPrefix_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hprefNonempty]
  simp only [machineListUpdateRebuildAdvance,
    machineListUpdateRebuildPrefix_pack,
    machineListUpdateRebuildOutput_pack,
    machineListUpdateRebuildBound_pack,
    machineListUpdateRebuildNextOutput,
    machineListUpdateRebuildCandidate]
  rw [htail, hnextOutput]

theorem machineListUpdateRebuildIterate_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) : ∀ k ≤ index,
    (machineListUpdateRebuildStep)^[k]
        (machineListUpdateRebuildInit
          (machineListUpdateCanonicalInput encode xs replacement index)) =
      machineListUpdateRebuildSemanticState
        encode xs replacement index k := by
  intro k hk
  induction k with
  | zero =>
      simpa using! (machineListUpdateRebuildInit_semantics
        encode xs replacement index hindex)
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineListUpdateRebuildStep_semantics
        encode xs replacement index k (by omega) hindex

theorem machineListUpdateRebuildFinalState_semantics
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) :
    machineListUpdateRebuildFinalState
        (machineListUpdateCanonicalInput encode xs replacement index) =
      machineListUpdateRebuildSemanticState
        encode xs replacement index index := by
  rw [machineListUpdateRebuildFinalState]
  simp only [machineListUpdateRuler, machineListUpdateCanonicalInput,
    machinePairFirst_pair, List.length_replicate]
  exact machineListUpdateRebuildIterate_semantics
    encode xs replacement index hindex index le_rfl

@[simp] theorem machineListUpdate_binaryListCode
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (replacement : α) (index : ℕ)
    (hindex : index < xs.length) :
    machineListUpdate
        (machineListUpdateCanonicalInput encode xs replacement index) =
      binaryListCode encode (xs.set index replacement) := by
  rw [machineListUpdate, machineListUpdateRebuildFinalState_semantics
    encode xs replacement index hindex]
  simp only [machineListUpdateRebuildSemanticState,
    machineListUpdateRebuildOutput_pack]
  have htakeLength : (xs.take index).length = index :=
    List.length_take_of_le hindex.le
  have hprefLength : (xs.take index).reverse.length = index := by
    simp [htakeLength]
  have htakePref :
      List.take index (xs.take index).reverse = (xs.take index).reverse := by
    exact List.take_of_length_le hprefLength.le
  rw [htakePref, List.reverse_reverse]
  rw [List.set_eq_take_cons_drop replacement hindex]

end BeyondBethe

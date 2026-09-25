/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineListReverse

/-!
# Appending one entry to a finite-word list

The canonical list representation is right-nested, so appending an entry is
not a constant-time constructor operation.  This machine reverses the encoded
list, prepends the supplied encoded entry, and reverses once more.  The two
uses of the verified list-reversal machine make the construction total and
polynomial-time on arbitrary finite words.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Input layout: `pair encodedEntry encodedList`. -/
def machineBinaryListSnocEntry (word : List Bool) : List Bool :=
  machinePairFirst word

def machineBinaryListSnocList (word : List Bool) : List Bool :=
  machinePairSecond word

def machineBinaryListSnocReversedList (word : List Bool) : List Bool :=
  machineListReverse (machineBinaryListSnocList word)

def machineBinaryListSnocPrependInput (word : List Bool) : List Bool :=
  pair (machineBinaryListSnocEntry word)
    (machineBinaryListSnocReversedList word)

def machineBinaryListSnoc (word : List Bool) : List Bool :=
  machineListReverse (machineBinaryListSnocPrependInput word)

theorem machineBinaryListSnocEntry_mem_FP :
    machineBinaryListSnocEntry ∈ FP := machinePairFirst_mem_FP

theorem machineBinaryListSnocList_mem_FP :
    machineBinaryListSnocList ∈ FP := machinePairSecond_mem_FP

theorem machineBinaryListSnocReversedList_mem_FP :
    machineBinaryListSnocReversedList ∈ FP := by
  simpa only [machineBinaryListSnocReversedList] using!
    machineCompose_mem_FP machineBinaryListSnocList_mem_FP
      machineListReverse_mem_FP

theorem machineBinaryListSnocPrependInput_mem_FP :
    machineBinaryListSnocPrependInput ∈ FP :=
  machinePair_mem_FP machineBinaryListSnocEntry_mem_FP
    machineBinaryListSnocReversedList_mem_FP

theorem machineBinaryListSnoc_mem_FP : machineBinaryListSnoc ∈ FP := by
  simpa only [machineBinaryListSnoc] using!
    machineCompose_mem_FP machineBinaryListSnocPrependInput_mem_FP
      machineListReverse_mem_FP

@[simp] theorem machineBinaryListSnoc_encode
    {alpha : Type*} (encode : alpha → List Bool)
    (xs : List alpha) (x : alpha) :
    machineBinaryListSnoc
        (pair (encode x) (binaryListCode encode xs)) =
      binaryListCode encode (xs ++ [x]) := by
  rw [machineBinaryListSnoc, machineBinaryListSnocPrependInput,
    machineBinaryListSnocEntry, machineBinaryListSnocReversedList,
    machineBinaryListSnocList, machinePairFirst_pair,
    machinePairSecond_pair, machineListReverse_encode]
  change machineListReverse
      (binaryListCode encode (x :: xs.reverse)) = _
  rw [machineListReverse_encode]
  simp

end BeyondBethe

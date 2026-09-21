/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineListReverse

/-!
# Removing the last entry of a finite-word list

The center of an epigraph ellipsoid is stored as a right-nested list.  The
base point consists of every coordinate except the final height coordinate.
This machine reverses the list, removes its first encoded entry, and reverses
again.  It is total and polynomial-time on arbitrary finite words.
-/

namespace BeyondBethe

open Complexity

def machineBinaryListInitReversed (word : List Bool) : List Bool :=
  machineListReverse word

def machineBinaryListInitReversedTail (word : List Bool) : List Bool :=
  machineListTail (machineBinaryListInitReversed word)

def machineBinaryListInit (word : List Bool) : List Bool :=
  machineListReverse (machineBinaryListInitReversedTail word)

theorem machineBinaryListInitReversed_mem_FP :
    machineBinaryListInitReversed ∈ FP := by
  simpa only [machineBinaryListInitReversed] using
    machineListReverse_mem_FP

theorem machineBinaryListInitReversedTail_mem_FP :
    machineBinaryListInitReversedTail ∈ FP := by
  simpa only [machineBinaryListInitReversedTail] using
    machineCompose_mem_FP machineBinaryListInitReversed_mem_FP
      machineListTail_mem_FP

theorem machineBinaryListInit_mem_FP : machineBinaryListInit ∈ FP := by
  simpa only [machineBinaryListInit] using
    machineCompose_mem_FP machineBinaryListInitReversedTail_mem_FP
      machineListReverse_mem_FP

@[simp] theorem machineBinaryListInit_encode
    {alpha : Type*} (encode : alpha → List Bool)
    (xs : List alpha) (x : alpha) :
    machineBinaryListInit (binaryListCode encode (xs ++ [x])) =
      binaryListCode encode xs := by
  rw [machineBinaryListInit, machineBinaryListInitReversedTail,
    machineBinaryListInitReversed, machineListReverse_encode]
  rw [List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append]
  rw [machineListTail_cons, machineListReverse_encode]
  simp

end BeyondBethe

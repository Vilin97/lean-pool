/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineKuhnRunner
public import Mathlib.Tactic

/-!
# Testing whether the final mate table is total

The Kuhn machine returns a column-to-row mate table.  This module scans its
self-delimiting encoding and returns one bit indicating whether every column
contains a row.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineMateAllSomePack
    (remaining ruler ok : List Bool) : List Bool :=
  pair remaining (pair ruler ok)

def machineMateAllSomeRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineMateAllSomeRulerState (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineMateAllSomeOk (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineMateAllSomeCurrentBit (state : List Bool) : List Bool :=
  machineHeadBit (machineListHead (machineMateAllSomeRemaining state))

def machineMateAllSomeAdvance (state : List Bool) : List Bool :=
  machineMateAllSomePack (machineListTail (machineMateAllSomeRemaining state))
    (machineMateAllSomeRulerState state).tail
    (machineAndBit (machineMateAllSomeOk state)
      (machineMateAllSomeCurrentBit state))

def machineMateAllSomeStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMateAllSomeRulerState state) state
    (machineMateAllSomeAdvance state)

def machineMateAllSomeInputRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineMateAllSomeInputMate (word : List Bool) : List Bool :=
  machinePairSecond word

def machineMateAllSomeInit (word : List Bool) : List Bool :=
  machineMateAllSomePack (machineMateAllSomeInputMate word)
    (machineMateAllSomeInputRuler word) [true]

def machineMateAllSomeWidth (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineMateAllSomeFinalState (word : List Bool) : List Bool :=
  (machineMateAllSomeStep^[(machineMateAllSomeInputRuler word).length])
    (machineMateAllSomeInit word)

def machineMateAllSomeBit (word : List Bool) : List Bool :=
  machineMateAllSomeOk (machineMateAllSomeFinalState word)

theorem machineMateAllSomeRemaining_mem_FP :
    machineMateAllSomeRemaining ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineMateAllSomeRulerState_mem_FP :
    machineMateAllSomeRulerState ∈ Complexity.FP := by
  simpa only [machineMateAllSomeRulerState] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMateAllSomeOk_mem_FP :
    machineMateAllSomeOk ∈ Complexity.FP := by
  simpa only [machineMateAllSomeOk] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineMateAllSomeCurrentBit_mem_FP :
    machineMateAllSomeCurrentBit ∈ Complexity.FP := by
  have hhead := machineCompose_mem_FP machineMateAllSomeRemaining_mem_FP
    machineListHead_mem_FP
  simpa only [machineMateAllSomeCurrentBit] using!
    machineCompose_mem_FP hhead machineHeadBit_mem_FP

theorem machineMateAllSomeAdvance_mem_FP :
    machineMateAllSomeAdvance ∈ Complexity.FP := by
  have hremainingTail := machineCompose_mem_FP
    machineMateAllSomeRemaining_mem_FP machineListTail_mem_FP
  have hrulerTail := machineCompose_mem_FP
    machineMateAllSomeRulerState_mem_FP machineTail_mem_FP
  have hok := machineAndBit_mem_FP machineMateAllSomeOk_mem_FP
    machineMateAllSomeCurrentBit_mem_FP
  exact machinePair_mem_FP hremainingTail
    (machinePair_mem_FP hrulerTail hok)

theorem machineMateAllSomeStep_mem_FP :
    machineMateAllSomeStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMateAllSomeRulerState_mem_FP id_mem_FP
    machineMateAllSomeAdvance_mem_FP

theorem machineMateAllSomeInputRuler_mem_FP :
    machineMateAllSomeInputRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineMateAllSomeInputMate_mem_FP :
    machineMateAllSomeInputMate ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineMateAllSomeInit_mem_FP :
    machineMateAllSomeInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMateAllSomeInputMate_mem_FP
    (machinePair_mem_FP machineMateAllSomeInputRuler_mem_FP
      (machineConst_mem_FP [true]))

theorem machineMateAllSomeWidth_mem_FP :
    machineMateAllSomeWidth ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

@[simp] theorem machineMateAllSomeRemaining_pack (a b c) :
    machineMateAllSomeRemaining (machineMateAllSomePack a b c) = a := by
  simp [machineMateAllSomeRemaining, machineMateAllSomePack]

@[simp] theorem machineMateAllSomeRulerState_pack (a b c) :
    machineMateAllSomeRulerState (machineMateAllSomePack a b c) = b := by
  simp [machineMateAllSomeRulerState, machineMateAllSomePack]

@[simp] theorem machineMateAllSomeOk_pack (a b c) :
    machineMateAllSomeOk (machineMateAllSomePack a b c) = c := by
  simp [machineMateAllSomeOk, machineMateAllSomePack]

@[simp] theorem machineMateAllSomeCurrentBit_pack (a b c) :
    machineMateAllSomeCurrentBit (machineMateAllSomePack a b c) =
      machineHeadBit (machineListHead a) := by
  simp [machineMateAllSomeCurrentBit]

@[simp] theorem machineMateAllSomeCurrentBit_length (state) :
    (machineMateAllSomeCurrentBit state).length = 1 := by
  exact machineHeadBit_length _

def MachineMateAllSomeStateBound (word state : List Bool) : Prop :=
  state = machineMateAllSomePack (machineMateAllSomeRemaining state)
      (machineMateAllSomeRulerState state) (machineMateAllSomeOk state) ∧
    (machineMateAllSomeRemaining state).length ≤ word.length ∧
    (machineMateAllSomeRulerState state).length ≤ word.length ∧
    (machineMateAllSomeOk state).length ≤ word.length + 1

theorem machineMateAllSomeInit_bound (word : List Bool) :
    MachineMateAllSomeStateBound word (machineMateAllSomeInit word) := by
  dsimp only [MachineMateAllSomeStateBound]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [machineMateAllSomeInit]
  · simpa [machineMateAllSomeInit] using! machinePairSecond_length_le word
  · simpa [machineMateAllSomeInit] using! machinePairFirst_length_le word
  · simp [machineMateAllSomeInit]

theorem machineMateAllSomeStep_bound {word state : List Bool}
    (hstate : MachineMateAllSomeStateBound word state) :
    MachineMateAllSomeStateBound word (machineMateAllSomeStep state) := by
  rcases hstate with ⟨hpack, hremaining, hruler, hok⟩
  cases hrulerEq : machineMateAllSomeRulerState state with
  | nil =>
      rw [machineMateAllSomeStep, hrulerEq, machineIfEmpty_nil]
      exact ⟨hpack, hremaining, hruler, hok⟩
  | cons bit tail =>
      rw [machineMateAllSomeStep, hrulerEq, machineIfEmpty_cons,
        machineMateAllSomeAdvance]
      dsimp only [MachineMateAllSomeStateBound]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp
      · simpa only [machineMateAllSomeRemaining_pack] using!
          (machinePairSecond_length_le
            (machineMateAllSomeRemaining state)).trans hremaining
      · rw [hrulerEq] at hruler
        simp only [List.length_cons] at hruler
        simp only [machineMateAllSomeRulerState_pack]
        rw [hrulerEq]
        simp only [List.tail_cons]
        omega
      · have hbit :
            (machineAndBit (machineMateAllSomeOk state)
              (machineMateAllSomeCurrentBit state)).length ≤ 1 := by
            simpa only [machineAndBit, machineMateAllSomeCurrentBit_length,
              List.length_cons, List.length_nil, Nat.zero_add, max_self] using!
              machineIfHead_length_le_max (machineMateAllSomeOk state)
                (machineMateAllSomeCurrentBit state) [false]
        simpa only [machineMateAllSomeOk_pack] using!
          hbit.trans (by omega : 1 ≤ word.length + 1)

theorem machineMateAllSomeIterate_bound (word : List Bool) : ∀ iterations,
    MachineMateAllSomeStateBound word
      ((machineMateAllSomeStep^[iterations])
        (machineMateAllSomeInit word)) := by
  intro iterations
  induction iterations with
  | zero => simpa using! machineMateAllSomeInit_bound word
  | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      exact machineMateAllSomeStep_bound ih

theorem machineMateAllSomeIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_hiterations : iterations ≤ (machineMateAllSomeInputRuler word).length) :
    ((machineMateAllSomeStep^[iterations])
      (machineMateAllSomeInit word)).length ≤
        (machineMateAllSomeWidth word).length := by
  rcases machineMateAllSomeIterate_bound word iterations with
    ⟨hpack, hremaining, hruler, hok⟩
  rw [hpack]
  simp only [machineMateAllSomePack, pair_length]
  simp only [machineMateAllSomeWidth, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineMateAllSomeFinalState_mem_FP :
    machineMateAllSomeFinalState ∈ Complexity.FP := by
  simpa only [machineMateAllSomeFinalState] using!
    Cobham.iterate_mem_FP machineMateAllSomeStep_mem_FP
      machineMateAllSomeInit_mem_FP machineMateAllSomeInputRuler_mem_FP
      machineMateAllSomeWidth_mem_FP
      machineMateAllSomeIterate_length_le_width

theorem machineMateAllSomeBit_mem_FP :
    machineMateAllSomeBit ∈ Complexity.FP := by
  simpa only [machineMateAllSomeBit] using!
    machineCompose_mem_FP machineMateAllSomeFinalState_mem_FP
      machineMateAllSomeOk_mem_FP

/-! ## Exact scan semantics -/

@[simp] theorem machineHeadBit_mateValueCode (value : Option ℕ) :
    machineHeadBit (mateValueCode value) = [value.isSome] := by
  cases value <;> simp [machineHeadBit, mateValueCode]

def mateAllSomeSemanticState (mate : List (Option ℕ)) (k : ℕ) : List Bool :=
  machineMateAllSomePack (mateVectorCode (mate.drop k))
    (List.replicate (mate.length - k) true)
    [(mate.take k).all Option.isSome]

theorem machineMateAllSomeStep_semantics
    (mate : List (Option ℕ)) (k : ℕ) (hk : k < mate.length) :
    machineMateAllSomeStep (mateAllSomeSemanticState mate k) =
      mateAllSomeSemanticState mate (k + 1) := by
  have hdrop := List.drop_eq_getElem_cons hk
  have htake := List.take_concat_get hk
  rw [mateAllSomeSemanticState, machineMateAllSomeStep]
  simp only [machineMateAllSomeRulerState_pack]
  have hremain : mate.length - k = (mate.length - (k + 1)) + 1 := by omega
  rw [hremain, List.replicate_succ, machineIfEmpty_cons,
    machineMateAllSomeAdvance]
  simp only [machineMateAllSomeRemaining_pack,
    machineMateAllSomeRulerState_pack, machineMateAllSomeOk_pack,
    List.tail_cons, mateVectorCode]
  rw [hdrop]
  simp only [machineListTail_cons, machineMateAllSomeCurrentBit_pack,
    machineListHead_cons,
    machineHeadBit_mateValueCode]
  rw [mateAllSomeSemanticState]
  have hall :
      (mate.take (k + 1)).all Option.isSome =
        ((mate.take k).all Option.isSome && mate[k].isSome) := by
    rw [← htake]
    simp only [List.concat_eq_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true]
  rw [hall]
  cases (mate.take k).all Option.isSome <;>
    cases mate[k].isSome <;>
    simp [machineAndBit, mateVectorCode]

theorem machineMateAllSomeIterate_semantics
    (mate : List (Option ℕ)) : ∀ k, k ≤ mate.length →
    (machineMateAllSomeStep^[k])
        (mateAllSomeSemanticState mate 0) =
      mateAllSomeSemanticState mate k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega),
        machineMateAllSomeStep_semantics mate k (by omega)]

@[simp] theorem machineMateAllSomeBit_encode
    (mate : List (Option ℕ)) :
    machineMateAllSomeBit
        (pair (List.replicate mate.length true) (mateVectorCode mate)) =
      [mate.all Option.isSome] := by
  rw [machineMateAllSomeBit, machineMateAllSomeFinalState]
  simp only [machineMateAllSomeInputRuler, machinePairFirst_pair,
    List.length_replicate, machineMateAllSomeInit,
    machineMateAllSomeInputMate, machinePairSecond_pair]
  change machineMateAllSomeOk
      ((machineMateAllSomeStep^[mate.length])
        (mateAllSomeSemanticState mate 0)) = _
  rw [machineMateAllSomeIterate_semantics mate mate.length (le_rfl)]
  simp [mateAllSomeSemanticState]

end BeyondBethe

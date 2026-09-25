/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryAddSemantics
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits

/-!
# A composed polynomial-time binary multiplier

The multiplier scans the little-endian multiplier.  Its state contains the
unread multiplier, the current doubled multiplicand, and the accumulated
partial product.  Each iteration uses the already verified binary adder.  A
quadratic Cobham width bound is proved for every input string, while exact
arithmetic correctness is proved on canonical `Nat.bits` operands.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineBinaryMulPack
    (remaining shift acc : List Bool) : List Bool :=
  pair remaining (pair shift acc)

def machineBinaryMulRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineBinaryMulShift (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineBinaryMulAcc (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineBinaryMulNextShift (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineBinaryMulShift state) (machineBinaryMulShift state))

def machineBinaryMulNextAcc (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineBinaryMulRemaining state))
    (machineBinaryAddBits
      (pair (machineBinaryMulAcc state) (machineBinaryMulShift state)))
    (machineBinaryMulAcc state)

def machineBinaryMulStep (state : List Bool) : List Bool :=
  machineBinaryMulPack
    (machineBinaryMulRemaining state).tail
    (machineBinaryMulNextShift state)
    (machineBinaryMulNextAcc state)

def machineBinaryMulInit (word : List Bool) : List Bool :=
  machineBinaryMulPack (machinePairSecond word) (machinePairFirst word) []

def machineBinaryMulRuler (word : List Bool) : List Bool :=
  machinePairSecond word

/-- A deliberately generous quadratic state envelope. -/
def machineBinaryMulWidth (word : List Bool) : List Bool :=
  let padded := List.replicate 16 false ++ word
  List.replicate (padded.length * padded.length) false

def machineBinaryMulFinalState (word : List Bool) : List Bool :=
  machineBinaryMulStep^[(machineBinaryMulRuler word).length]
    (machineBinaryMulInit word)

def machineBinaryMulBits (word : List Bool) : List Bool :=
  machineBinaryMulAcc (machineBinaryMulFinalState word)

theorem machineBinaryMulRemaining_mem_FP :
    machineBinaryMulRemaining ∈ Complexity.FP := by
  simpa only [machineBinaryMulRemaining] using! machinePairFirst_mem_FP

theorem machineBinaryMulShift_mem_FP :
    machineBinaryMulShift ∈ Complexity.FP := by
  simpa only [machineBinaryMulShift] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBinaryMulAcc_mem_FP :
    machineBinaryMulAcc ∈ Complexity.FP := by
  simpa only [machineBinaryMulAcc] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineBinaryMulPack_mem_FP
    {remaining shift acc : List Bool → List Bool}
    (hremaining : remaining ∈ Complexity.FP)
    (hshift : shift ∈ Complexity.FP) (hacc : acc ∈ Complexity.FP) :
    (fun word => machineBinaryMulPack (remaining word) (shift word)
      (acc word)) ∈ Complexity.FP := by
  exact machinePair_mem_FP hremaining (machinePair_mem_FP hshift hacc)

theorem machineBinaryMulNextShift_mem_FP :
    machineBinaryMulNextShift ∈ Complexity.FP := by
  have hpair : (fun state => pair (machineBinaryMulShift state)
      (machineBinaryMulShift state)) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryMulShift_mem_FP
      machineBinaryMulShift_mem_FP
  simpa only [machineBinaryMulNextShift] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineBinaryMulNextAcc_mem_FP :
    machineBinaryMulNextAcc ∈ Complexity.FP := by
  have hflag : (fun state =>
      machineHeadBit (machineBinaryMulRemaining state)) ∈ Complexity.FP :=
    machineCompose_mem_FP machineBinaryMulRemaining_mem_FP
      machineHeadBit_mem_FP
  have hpair : (fun state => pair (machineBinaryMulAcc state)
      (machineBinaryMulShift state)) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryMulAcc_mem_FP
      machineBinaryMulShift_mem_FP
  have hadd : (fun state => machineBinaryAddBits
      (pair (machineBinaryMulAcc state) (machineBinaryMulShift state))) ∈
      Complexity.FP :=
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP
  exact machineIfHead_mem_FP hflag hadd machineBinaryMulAcc_mem_FP

theorem machineBinaryMulStep_mem_FP :
    machineBinaryMulStep ∈ Complexity.FP := by
  apply machineBinaryMulPack_mem_FP
  · exact machineCompose_mem_FP machineBinaryMulRemaining_mem_FP
      machineTail_mem_FP
  · exact machineBinaryMulNextShift_mem_FP
  · exact machineBinaryMulNextAcc_mem_FP

theorem machineBinaryMulInit_mem_FP :
    machineBinaryMulInit ∈ Complexity.FP := by
  exact machineBinaryMulPack_mem_FP machinePairSecond_mem_FP
    machinePairFirst_mem_FP (machineConst_mem_FP [])

theorem machineBinaryMulRuler_mem_FP :
    machineBinaryMulRuler ∈ Complexity.FP := by
  simpa only [machineBinaryMulRuler] using! machinePairSecond_mem_FP

theorem machineBinaryMulWidth_mem_FP :
    machineBinaryMulWidth ∈ Complexity.FP := by
  let padded : List Bool → List Bool :=
    fun word => List.replicate 16 false ++ word
  have hpadded : padded ∈ Complexity.FP :=
    machineAppend_mem_FP (machineConst_mem_FP (List.replicate 16 false))
      id_mem_FP
  simpa only [machineBinaryMulWidth, padded] using!
    Cobham.mulLenFn_mem_FP hpadded hpadded

@[simp] theorem machineBinaryMulRemaining_pack (remaining shift acc) :
    machineBinaryMulRemaining (machineBinaryMulPack remaining shift acc) =
      remaining := by
  simp [machineBinaryMulRemaining, machineBinaryMulPack]

@[simp] theorem machineBinaryMulShift_pack (remaining shift acc) :
    machineBinaryMulShift (machineBinaryMulPack remaining shift acc) =
      shift := by
  simp [machineBinaryMulShift, machineBinaryMulPack]

@[simp] theorem machineBinaryMulAcc_pack (remaining shift acc) :
    machineBinaryMulAcc (machineBinaryMulPack remaining shift acc) = acc := by
  simp [machineBinaryMulAcc, machineBinaryMulPack]

@[simp] theorem machineBinaryMulStep_pack
    (bit : Bool) (remaining shift acc : List Bool) :
    machineBinaryMulStep
        (machineBinaryMulPack (bit :: remaining) shift acc) =
      machineBinaryMulPack remaining
        (machineBinaryAddBits (pair shift shift))
        (if bit then machineBinaryAddBits (pair acc shift) else acc) := by
  cases bit <;>
    simp [machineBinaryMulStep, machineBinaryMulNextShift,
      machineBinaryMulNextAcc]

/-- Pure list-level fold mirrored by the bounded machine loop. -/
def binaryMulFold : List Bool → List Bool → List Bool →
    List Bool × List Bool
  | [], shift, acc => (shift, acc)
  | bit :: remaining, shift, acc =>
      binaryMulFold remaining
        (machineBinaryAddBits (pair shift shift))
        (if bit then machineBinaryAddBits (pair acc shift) else acc)

theorem machineBinaryMulIterate_length
    (bits shift acc : List Bool) :
    machineBinaryMulStep^[bits.length]
        (machineBinaryMulPack bits shift acc) =
      machineBinaryMulPack []
        (binaryMulFold bits shift acc).1
        (binaryMulFold bits shift acc).2 := by
  induction bits generalizing shift acc with
  | nil => rfl
  | cons bit remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        machineBinaryMulStep_pack, ih]
      rfl

def MachineBinaryMulReachable
    (lhs rhs : List Bool) (iterations : ℕ) (state : List Bool) : Prop :=
  ∃ remaining shift acc,
    state = machineBinaryMulPack remaining shift acc ∧
    remaining.length ≤ rhs.length ∧
    shift.length ≤ lhs.length + iterations ∧
    acc.length ≤ lhs.length + iterations + 1

theorem machineBinaryMulInit_reachable (word : List Bool) :
    MachineBinaryMulReachable (machinePairFirst word)
      (machinePairSecond word) 0 (machineBinaryMulInit word) := by
  refine ⟨machinePairSecond word, machinePairFirst word, [], rfl,
    le_rfl, ?_, ?_⟩ <;> simp

theorem machineBinaryMulStep_reachable
    {lhs rhs : List Bool} {iterations : ℕ} {state : List Bool}
    (hstate : MachineBinaryMulReachable lhs rhs iterations state) :
    MachineBinaryMulReachable lhs rhs (iterations + 1)
      (machineBinaryMulStep state) := by
  obtain ⟨remaining, shift, acc, rfl, hremaining, hshift, hacc⟩ := hstate
  cases remaining with
  | nil =>
      refine ⟨[], machineBinaryAddBits (pair shift shift),
        machineBinaryMulNextAcc (machineBinaryMulPack [] shift acc),
        ?_, by simp, ?_, ?_⟩
      · simp [machineBinaryMulStep, machineBinaryMulNextShift]
      · have hadd := machineBinaryAddBits_pair_length_le shift shift
        omega
      · simp [machineBinaryMulNextAcc]
        omega
  | cons bit remaining =>
      refine ⟨remaining, machineBinaryAddBits (pair shift shift),
        (if bit then machineBinaryAddBits (pair acc shift) else acc),
        machineBinaryMulStep_pack bit remaining shift acc,
        ?_, ?_, ?_⟩
      · simp only [List.length_cons] at hremaining
        omega
      · have hadd := machineBinaryAddBits_pair_length_le shift shift
        omega
      · cases bit with
        | false => simp; omega
        | true =>
            simp only [Bool.true_eq, if_true]
            have hadd := machineBinaryAddBits_pair_length_le acc shift
            omega

theorem machineBinaryMulIterate_reachable (word : List Bool) :
    ∀ iterations,
    MachineBinaryMulReachable (machinePairFirst word)
      (machinePairSecond word) iterations
      (machineBinaryMulStep^[iterations] (machineBinaryMulInit word)) := by
  intro iterations
  induction iterations with
  | zero => exact machineBinaryMulInit_reachable word
  | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.succ_eq_add_one] using! machineBinaryMulStep_reachable ih

theorem machineBinaryMulIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (machineBinaryMulRuler word).length) :
    (machineBinaryMulStep^[iterations]
      (machineBinaryMulInit word)).length ≤
        (machineBinaryMulWidth word).length := by
  obtain ⟨remaining, shift, acc, hstate, hremaining, hshift, hacc⟩ :=
    machineBinaryMulIterate_reachable word iterations
  rw [hstate]
  have hlhs := machinePairFirst_length_le word
  have hrhs := machinePairSecond_length_le word
  have hit : iterations ≤ word.length := by
    exact hiterations.trans hrhs
  simp only [machineBinaryMulPack, pair_length, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineBinaryMulFinalState_mem_FP :
    machineBinaryMulFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBinaryMulStep_mem_FP
    machineBinaryMulInit_mem_FP machineBinaryMulRuler_mem_FP
    machineBinaryMulWidth_mem_FP machineBinaryMulIterate_length_le_width

theorem machineBinaryMulBits_mem_FP :
    machineBinaryMulBits ∈ Complexity.FP := by
  simpa only [machineBinaryMulBits] using!
    machineCompose_mem_FP machineBinaryMulFinalState_mem_FP
      machineBinaryMulAcc_mem_FP

theorem binaryMulFold_natBits (bits : List Bool) (shift acc : ℕ) :
    (binaryMulFold bits shift.bits acc.bits).2 =
      (acc + shift * Nat.fromBitsLE bits).bits := by
  induction bits generalizing shift acc with
  | nil =>
      have hempty : Nat.fromBitsLE [] = 0 := rfl
      simp [binaryMulFold, hempty]
  | cons bit remaining ih =>
      cases bit with
      | false =>
          simp only [binaryMulFold, machineBinaryAddBits_pair_natBits]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ih (shift + shift) acc]
          simp only [Nat.fromBitsLE_cons]
          congr 1
          simp only [Bool.false_eq_true, ite_false]
          ring
      | true =>
          simp only [binaryMulFold, machineBinaryAddBits_pair_natBits]
          simp only [↓reduceIte]
          rw [ih (shift + shift) (acc + shift)]
          simp only [Nat.fromBitsLE_cons]
          congr 1
          simp only [eq_self, if_true]
          ring

/-- The concrete multiplier returns the canonical binary expansion of the
product of two canonically encoded natural numbers. -/
theorem machineBinaryMulBits_pair_natBits (lhs rhs : ℕ) :
    machineBinaryMulBits (pair lhs.bits rhs.bits) = (lhs * rhs).bits := by
  simp only [machineBinaryMulBits, machineBinaryMulFinalState,
    machineBinaryMulRuler, machineBinaryMulInit, machinePairFirst_pair,
    machinePairSecond_pair]
  rw [machineBinaryMulIterate_length]
  simp only [machineBinaryMulAcc_pack]
  have hfold := binaryMulFold_natBits rhs.bits lhs 0
  calc
    (binaryMulFold rhs.bits lhs.bits []).2 =
        (lhs * Nat.fromBitsLE rhs.bits).bits := by simpa using! hfold
    _ = (lhs * rhs).bits := by rw [Nat.fromBitsLE_bits]

end BeyondBethe

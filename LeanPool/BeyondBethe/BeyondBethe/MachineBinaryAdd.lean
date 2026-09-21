/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBool

/-!
# A composed polynomial-time binary adder

The adder uses little-endian words, matching `Nat.bits`.  Its state is
`pair x (pair y (pair carry accRev))`.  One verified `FP` step consumes at
most one bit from each operand and prepends one result bit to `accRev`.
Complexitylib's proved bounded-iteration machine runs this step for the
length of a linear ruler; the final reversal restores little-endian order.
-/

namespace BeyondBethe

open Complexity

def machineBinaryAddPack
    (x y carry accRev : List Bool) : List Bool :=
  pair x (pair y (pair carry accRev))

def machineBinaryAddX (state : List Bool) : List Bool :=
  machinePairFirst state

def machineBinaryAddY (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineBinaryAddCarry (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineBinaryAddAccRev (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

theorem machineBinaryAddPack_mem_FP
    {x y carry accRev : List Bool → List Bool}
    (hx : x ∈ Complexity.FP) (hy : y ∈ Complexity.FP)
    (hcarry : carry ∈ Complexity.FP) (hacc : accRev ∈ Complexity.FP) :
    (fun word => machineBinaryAddPack (x word) (y word)
      (carry word) (accRev word)) ∈ Complexity.FP := by
  exact machinePair_mem_FP hx
    (machinePair_mem_FP hy (machinePair_mem_FP hcarry hacc))

theorem machineBinaryAddX_mem_FP : machineBinaryAddX ∈ Complexity.FP := by
  simpa only [machineBinaryAddX] using machinePairFirst_mem_FP

theorem machineBinaryAddY_mem_FP : machineBinaryAddY ∈ Complexity.FP := by
  simpa only [machineBinaryAddY] using
    (machineCompose_mem_FP (f := machinePairSecond) (g := machinePairFirst)
      machinePairSecond_mem_FP machinePairFirst_mem_FP)

theorem machineBinaryAddCarry_mem_FP :
    machineBinaryAddCarry ∈ Complexity.FP := by
  have hsecond :
      (fun word => machinePairSecond (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP (f := machinePairSecond) (g := machinePairSecond)
      machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineBinaryAddCarry] using
    (machineCompose_mem_FP (f := fun word =>
        machinePairSecond (machinePairSecond word))
      (g := machinePairFirst) hsecond machinePairFirst_mem_FP)

theorem machineBinaryAddAccRev_mem_FP :
    machineBinaryAddAccRev ∈ Complexity.FP := by
  have hsecond :
      (fun word => machinePairSecond (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP (f := machinePairSecond) (g := machinePairSecond)
      machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineBinaryAddAccRev] using
    (machineCompose_mem_FP (f := fun word =>
        machinePairSecond (machinePairSecond word))
      (g := machinePairSecond) hsecond machinePairSecond_mem_FP)

@[simp] theorem machineBinaryAddX_pack (x y carry accRev : List Bool) :
    machineBinaryAddX (machineBinaryAddPack x y carry accRev) = x := by
  simp [machineBinaryAddX, machineBinaryAddPack]

@[simp] theorem machineBinaryAddY_pack (x y carry accRev : List Bool) :
    machineBinaryAddY (machineBinaryAddPack x y carry accRev) = y := by
  simp [machineBinaryAddY, machineBinaryAddPack]

@[simp] theorem machineBinaryAddCarry_pack (x y carry accRev : List Bool) :
    machineBinaryAddCarry (machineBinaryAddPack x y carry accRev) = carry := by
  simp [machineBinaryAddCarry, machineBinaryAddPack]

@[simp] theorem machineBinaryAddAccRev_pack (x y carry accRev : List Bool) :
    machineBinaryAddAccRev (machineBinaryAddPack x y carry accRev) = accRev := by
  simp [machineBinaryAddAccRev, machineBinaryAddPack]

/-- One-bit flag saying that an addition step remains: an operand is
nonempty, or both operands are empty and the carry is true. -/
def machineBinaryAddActive (state : List Bool) : List Bool :=
  machineIfEmpty (machineBinaryAddX state)
    (machineIfEmpty (machineBinaryAddY state)
      (machineBinaryAddCarry state) [true])
    [true]

def machineBinaryAddSumBit (state : List Bool) : List Bool :=
  machineFullAdderSum
    (machineHeadBit (machineBinaryAddX state))
    (machineHeadBit (machineBinaryAddY state))
    (machineBinaryAddCarry state)

def machineBinaryAddNextCarry (state : List Bool) : List Bool :=
  machineFullAdderCarry
    (machineHeadBit (machineBinaryAddX state))
    (machineHeadBit (machineBinaryAddY state))
    (machineBinaryAddCarry state)

def machineBinaryAddAdvanced (state : List Bool) : List Bool :=
  machineBinaryAddPack
    (machineBinaryAddX state).tail
    (machineBinaryAddY state).tail
    (machineBinaryAddNextCarry state)
    (machineBinaryAddSumBit state ++ machineBinaryAddAccRev state)

/-- Total addition transition.  A completed state is a fixed point. -/
def machineBinaryAddStep (state : List Bool) : List Bool :=
  machineIfHead (machineBinaryAddActive state)
    (machineBinaryAddAdvanced state) state

theorem machineBinaryAddActive_mem_FP :
    machineBinaryAddActive ∈ Complexity.FP := by
  apply machineIfEmpty_mem_FP machineBinaryAddX_mem_FP
  · apply machineIfEmpty_mem_FP machineBinaryAddY_mem_FP
    · exact machineBinaryAddCarry_mem_FP
    · exact machineConst_mem_FP [true]
  · exact machineConst_mem_FP [true]

theorem machineBinaryAddSumBit_mem_FP :
    machineBinaryAddSumBit ∈ Complexity.FP := by
  apply machineFullAdderSum_mem_FP
  · exact machineCompose_mem_FP machineBinaryAddX_mem_FP machineHeadBit_mem_FP
  · exact machineCompose_mem_FP machineBinaryAddY_mem_FP machineHeadBit_mem_FP
  · exact machineBinaryAddCarry_mem_FP

theorem machineBinaryAddNextCarry_mem_FP :
    machineBinaryAddNextCarry ∈ Complexity.FP := by
  apply machineFullAdderCarry_mem_FP
  · exact machineCompose_mem_FP machineBinaryAddX_mem_FP machineHeadBit_mem_FP
  · exact machineCompose_mem_FP machineBinaryAddY_mem_FP machineHeadBit_mem_FP
  · exact machineBinaryAddCarry_mem_FP

theorem machineBinaryAddAdvanced_mem_FP :
    machineBinaryAddAdvanced ∈ Complexity.FP := by
  apply machineBinaryAddPack_mem_FP
  · exact machineCompose_mem_FP machineBinaryAddX_mem_FP machineTail_mem_FP
  · exact machineCompose_mem_FP machineBinaryAddY_mem_FP machineTail_mem_FP
  · exact machineBinaryAddNextCarry_mem_FP
  · exact machineAppend_mem_FP machineBinaryAddSumBit_mem_FP
      machineBinaryAddAccRev_mem_FP

theorem machineBinaryAddStep_mem_FP :
    machineBinaryAddStep ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineBinaryAddActive_mem_FP
    machineBinaryAddAdvanced_mem_FP id_mem_FP

/-- Initial state from a paired pair of operand words. -/
def machineBinaryAddInit (word : List Bool) : List Bool :=
  machineBinaryAddPack (machinePairFirst word) (machinePairSecond word)
    [false] []

/-- A linear-length iteration ruler. -/
def machineBinaryAddRuler (word : List Bool) : List Bool :=
  machinePairFirst word ++ machinePairSecond word ++ [false]

/-- A quadratic-width zero word.  This is intentionally generous and makes
the bounded-iteration proof independent of fine fixedValue accounting. -/
def machineBinaryAddWidth (word : List Bool) : List Bool :=
  let padded := List.replicate 8 false ++ word
  List.replicate (padded.length * padded.length) false

theorem machineBinaryAddInit_mem_FP :
    machineBinaryAddInit ∈ Complexity.FP := by
  exact machineBinaryAddPack_mem_FP machinePairFirst_mem_FP
    machinePairSecond_mem_FP (machineConst_mem_FP [false])
    (machineConst_mem_FP [])

theorem machineBinaryAddRuler_mem_FP :
    machineBinaryAddRuler ∈ Complexity.FP := by
  apply machineAppend_mem_FP
  · exact machineAppend_mem_FP machinePairFirst_mem_FP machinePairSecond_mem_FP
  · exact machineConst_mem_FP [false]

theorem machineBinaryAddWidth_mem_FP :
    machineBinaryAddWidth ∈ Complexity.FP := by
  let padded : List Bool → List Bool :=
    fun word => List.replicate 8 false ++ word
  have hpadded : padded ∈ Complexity.FP := by
    exact machineAppend_mem_FP (machineConst_mem_FP (List.replicate 8 false))
      id_mem_FP
  simpa only [machineBinaryAddWidth, padded] using
    Cobham.mulLenFn_mem_FP hpadded hpadded

@[simp] theorem machineBinaryAddStep_pack
    (x y accRev : List Bool) (carry : Bool) :
    machineBinaryAddStep (machineBinaryAddPack x y [carry] accRev) =
      if x = [] ∧ y = [] ∧ carry = false then
        machineBinaryAddPack x y [carry] accRev
      else
        machineBinaryAddPack x.tail y.tail
          [((x.head?.getD false && y.head?.getD false) ||
              (x.head?.getD false && carry) ||
              (y.head?.getD false && carry))]
          (xor (xor (x.head?.getD false) (y.head?.getD false)) carry ::
            accRev) := by
  cases x with
  | nil =>
      cases y with
      | nil => cases carry <;> rfl
      | cons y ys =>
          cases y <;> cases carry <;>
            simp [machineBinaryAddStep, machineBinaryAddActive,
              machineBinaryAddAdvanced, machineBinaryAddSumBit,
              machineBinaryAddNextCarry, machineFullAdderSum,
              machineFullAdderCarry, machineMajorityBit, machineXorBit,
              machineAndBit, machineOrBit, machineNotBit]
  | cons x xs =>
      cases x <;> cases y with
      | nil =>
          cases carry <;>
            simp [machineBinaryAddStep, machineBinaryAddActive,
              machineBinaryAddAdvanced, machineBinaryAddSumBit,
              machineBinaryAddNextCarry, machineFullAdderSum,
              machineFullAdderCarry, machineMajorityBit, machineXorBit,
              machineAndBit, machineOrBit, machineNotBit]
      | cons y ys =>
          cases y <;> cases carry <;>
            simp [machineBinaryAddStep, machineBinaryAddActive,
              machineBinaryAddAdvanced, machineBinaryAddSumBit,
              machineBinaryAddNextCarry, machineFullAdderSum,
              machineFullAdderCarry, machineMajorityBit, machineXorBit,
              machineAndBit, machineOrBit, machineNotBit]

theorem machineBinaryAddStep_pack_length_le
    (x y accRev : List Bool) (carry : Bool) :
    (machineBinaryAddStep (machineBinaryAddPack x y [carry] accRev)).length ≤
      (machineBinaryAddPack x y [carry] accRev).length + 1 := by
  rw [machineBinaryAddStep_pack]
  split
  · omega
  · simp only [machineBinaryAddPack, pair_length, List.length_cons]
    simp only [List.length_tail]
    omega

theorem machinePairFirst_length_le (word : List Bool) :
    (machinePairFirst word).length ≤ word.length := by
  change (Cobham.fstBlock word).length ≤ word.length
  have hstrong : ∀ n : ℕ, ∀ word : List Bool, word.length = n →
      (Cobham.fstBlock word).length ≤ word.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro word hlength
        cases word with
        | nil => rfl
        | cons a word =>
            cases word with
            | nil => simp [Cobham.fstBlock]
            | cons b word =>
                have hrest := ih word.length (by simp at hlength; omega)
                  word rfl
                cases a <;> cases b <;>
                  simp [Cobham.fstBlock, hrest] <;> omega
  exact hstrong word.length word rfl

theorem machinePairSecond_length_le (word : List Bool) :
    (machinePairSecond word).length ≤ word.length := by
  unfold machinePairSecond Cobham.sndBlock
  cases hpair : unpair? word with
  | none => simp
  | some components =>
      obtain ⟨left, right⟩ := components
      have hword : word = pair left right :=
        eq_pair_of_unpair?_eq_some hpair
      subst word
      simp

/-- States reachable from the canonical pack retain a one-bit carry. -/
def MachineBinaryAddWellFormed (state : List Bool) : Prop :=
  ∃ x y accRev : List Bool, ∃ carry : Bool,
    state = machineBinaryAddPack x y [carry] accRev

theorem machineBinaryAddInit_wellFormed (word : List Bool) :
    MachineBinaryAddWellFormed (machineBinaryAddInit word) := by
  exact ⟨machinePairFirst word, machinePairSecond word, [], false, rfl⟩

theorem machineBinaryAddStep_wellFormed {state : List Bool}
    (hstate : MachineBinaryAddWellFormed state) :
    MachineBinaryAddWellFormed (machineBinaryAddStep state) := by
  obtain ⟨x, y, accRev, carry, rfl⟩ := hstate
  rw [machineBinaryAddStep_pack]
  split
  · exact ⟨x, y, accRev, carry, rfl⟩
  · exact ⟨x.tail, y.tail,
      xor (xor (x.head?.getD false) (y.head?.getD false)) carry :: accRev,
      ((x.head?.getD false && y.head?.getD false) ||
        (x.head?.getD false && carry) ||
        (y.head?.getD false && carry)), rfl⟩

theorem machineBinaryAddIterate_wellFormed_length_le
    {state : List Bool} (hstate : MachineBinaryAddWellFormed state) :
    ∀ iterations : ℕ,
      MachineBinaryAddWellFormed (machineBinaryAddStep^[iterations] state) ∧
      (machineBinaryAddStep^[iterations] state).length ≤
        state.length + iterations := by
  intro iterations
  induction iterations with
  | zero => simpa using And.intro hstate (Nat.le_refl state.length)
  | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hwell, hlength⟩ := ih
      have hnext := machineBinaryAddStep_wellFormed hwell
      obtain ⟨x, y, accRev, carry, hrepr⟩ := hwell
      have hstep := machineBinaryAddStep_pack_length_le x y accRev carry
      rw [← hrepr] at hstep
      refine ⟨hnext, ?_⟩
      omega

theorem machineBinaryAddInit_length_le (word : List Bool) :
    (machineBinaryAddInit word).length ≤ 4 * word.length + 8 := by
  simp only [machineBinaryAddInit, machineBinaryAddPack, pair_length,
    List.length_cons, List.length_nil]
  have hfirst := machinePairFirst_length_le word
  have hsecond := machinePairSecond_length_le word
  omega

theorem machineBinaryAddRuler_length_le (word : List Bool) :
    (machineBinaryAddRuler word).length ≤ 2 * word.length + 1 := by
  simp only [machineBinaryAddRuler, List.length_append, List.length_cons,
    List.length_nil]
  have hfirst := machinePairFirst_length_le word
  have hsecond := machinePairSecond_length_le word
  omega

theorem machineBinaryAddWidth_length (word : List Bool) :
    (machineBinaryAddWidth word).length = (word.length + 8) ^ 2 := by
  simp [machineBinaryAddWidth, pow_two]

theorem machineBinaryAddIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (machineBinaryAddRuler word).length) :
    (machineBinaryAddStep^[iterations] (machineBinaryAddInit word)).length ≤
      (machineBinaryAddWidth word).length := by
  have hiter :=
    (machineBinaryAddIterate_wellFormed_length_le
      (machineBinaryAddInit_wellFormed word) iterations).2
  have hinit := machineBinaryAddInit_length_le word
  have hruler := machineBinaryAddRuler_length_le word
  rw [machineBinaryAddWidth_length]
  nlinarith [sq_nonneg (word.length : ℤ)]

/-- Final bounded-iteration state. -/
def machineBinaryAddFinalState (word : List Bool) : List Bool :=
  machineBinaryAddStep^[(machineBinaryAddRuler word).length]
    (machineBinaryAddInit word)

/-- Machine-level binary addition.  The final accumulator is reversed from
the transition-friendly most-recent-bit-first representation. -/
def machineBinaryAddBits (word : List Bool) : List Bool :=
  (machineBinaryAddAccRev (machineBinaryAddFinalState word)).reverse

theorem machineBinaryAddFinalState_mem_FP :
    machineBinaryAddFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBinaryAddStep_mem_FP
    machineBinaryAddInit_mem_FP machineBinaryAddRuler_mem_FP
    machineBinaryAddWidth_mem_FP machineBinaryAddIterate_length_le_width

theorem machineBinaryAddBits_mem_FP :
    machineBinaryAddBits ∈ Complexity.FP := by
  have hacc :
      (fun word => machineBinaryAddAccRev
        (machineBinaryAddFinalState word)) ∈ Complexity.FP :=
    machineCompose_mem_FP machineBinaryAddFinalState_mem_FP
      machineBinaryAddAccRev_mem_FP
  simpa only [machineBinaryAddBits] using
    (machineCompose_mem_FP hacc machineReverse_mem_FP)

end BeyondBethe

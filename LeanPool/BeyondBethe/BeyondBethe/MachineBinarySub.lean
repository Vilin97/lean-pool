/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineTrimHighZeros
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub

/-!
# A composed polynomial-time binary subtractor

The state is `pair x (pair y (pair borrow accRev))`.  A bounded ripple-borrow
scan produces a fixed-width difference; a verified final branch maps
underflow to zero and otherwise removes redundant high zeroes.  Thus the
machine implements truncated subtraction on canonical natural words.
-/

namespace BeyondBethe

open Complexity

def machineBinarySubPack
    (x y borrow accRev : List Bool) : List Bool :=
  pair x (pair y (pair borrow accRev))

def machineBinarySubX (state : List Bool) : List Bool :=
  machinePairFirst state

def machineBinarySubY (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineBinarySubBorrow (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineBinarySubAccRev (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineBinarySubActive (state : List Bool) : List Bool :=
  machineIfEmpty (machineBinarySubX state)
    (machineIfEmpty (machineBinarySubY state) [false] [true]) [true]

def machineBinarySubDiffBit (state : List Bool) : List Bool :=
  machineFullAdderSum
    (machineHeadBit (machineBinarySubX state))
    (machineHeadBit (machineBinarySubY state))
    (machineBinarySubBorrow state)

def machineBinarySubNextBorrow (state : List Bool) : List Bool :=
  let lhs := machineHeadBit (machineBinarySubX state)
  let rhs := machineHeadBit (machineBinarySubY state)
  let borrow := machineBinarySubBorrow state
  machineOrBit (machineAndBit (machineNotBit lhs) rhs)
    (machineOrBit (machineAndBit (machineNotBit lhs) borrow)
      (machineAndBit rhs borrow))

def machineBinarySubAdvanced (state : List Bool) : List Bool :=
  machineBinarySubPack
    (machineBinarySubX state).tail
    (machineBinarySubY state).tail
    (machineBinarySubNextBorrow state)
    (machineBinarySubDiffBit state ++ machineBinarySubAccRev state)

def machineBinarySubStep (state : List Bool) : List Bool :=
  machineIfHead (machineBinarySubActive state)
    (machineBinarySubAdvanced state) state

def machineBinarySubInit (word : List Bool) : List Bool :=
  machineBinarySubPack (machinePairFirst word) (machinePairSecond word)
    [false] []

def machineBinarySubRuler (word : List Bool) : List Bool :=
  machinePairFirst word ++ machinePairSecond word

def machineBinarySubWidth (word : List Bool) : List Bool :=
  let padded := List.replicate 8 false ++ word
  List.replicate (padded.length * padded.length) false

def machineBinarySubFinalState (word : List Bool) : List Bool :=
  machineBinarySubStep^[(machineBinarySubRuler word).length]
    (machineBinarySubInit word)

def machineBinarySubBits (word : List Bool) : List Bool :=
  let state := machineBinarySubFinalState word
  machineIfHead (machineBinarySubBorrow state) []
    (machineTrimHighZeros (machineBinarySubAccRev state).reverse)

theorem machineBinarySubX_mem_FP : machineBinarySubX ∈ Complexity.FP := by
  simpa only [machineBinarySubX] using machinePairFirst_mem_FP

theorem machineBinarySubY_mem_FP : machineBinarySubY ∈ Complexity.FP := by
  simpa only [machineBinarySubY] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBinarySubBorrow_mem_FP :
    machineBinarySubBorrow ∈ Complexity.FP := by
  have hsecond2 : (fun word =>
      machinePairSecond (machinePairSecond word)) ∈ Complexity.FP :=
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineBinarySubBorrow] using
    machineCompose_mem_FP hsecond2 machinePairFirst_mem_FP

theorem machineBinarySubAccRev_mem_FP :
    machineBinarySubAccRev ∈ Complexity.FP := by
  have hsecond2 : (fun word =>
      machinePairSecond (machinePairSecond word)) ∈ Complexity.FP :=
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineBinarySubAccRev] using
    machineCompose_mem_FP hsecond2 machinePairSecond_mem_FP

theorem machineBinarySubPack_mem_FP
    {x y borrow accRev : List Bool → List Bool}
    (hx : x ∈ Complexity.FP) (hy : y ∈ Complexity.FP)
    (hborrow : borrow ∈ Complexity.FP) (hacc : accRev ∈ Complexity.FP) :
    (fun word => machineBinarySubPack (x word) (y word)
      (borrow word) (accRev word)) ∈ Complexity.FP := by
  exact machinePair_mem_FP hx
    (machinePair_mem_FP hy (machinePair_mem_FP hborrow hacc))

theorem machineBinarySubActive_mem_FP :
    machineBinarySubActive ∈ Complexity.FP := by
  apply machineIfEmpty_mem_FP machineBinarySubX_mem_FP
  · exact machineIfEmpty_mem_FP machineBinarySubY_mem_FP
      (machineConst_mem_FP [false]) (machineConst_mem_FP [true])
  · exact machineConst_mem_FP [true]

theorem machineBinarySubDiffBit_mem_FP :
    machineBinarySubDiffBit ∈ Complexity.FP := by
  apply machineFullAdderSum_mem_FP
  · exact machineCompose_mem_FP machineBinarySubX_mem_FP
      machineHeadBit_mem_FP
  · exact machineCompose_mem_FP machineBinarySubY_mem_FP
      machineHeadBit_mem_FP
  · exact machineBinarySubBorrow_mem_FP

theorem machineBinarySubNextBorrow_mem_FP :
    machineBinarySubNextBorrow ∈ Complexity.FP := by
  have hlhs : (fun state => machineHeadBit (machineBinarySubX state)) ∈
      Complexity.FP :=
    machineCompose_mem_FP machineBinarySubX_mem_FP machineHeadBit_mem_FP
  have hrhs : (fun state => machineHeadBit (machineBinarySubY state)) ∈
      Complexity.FP :=
    machineCompose_mem_FP machineBinarySubY_mem_FP machineHeadBit_mem_FP
  apply machineOrBit_mem_FP
  · exact machineAndBit_mem_FP (machineNotBit_mem_FP hlhs) hrhs
  · apply machineOrBit_mem_FP
    · exact machineAndBit_mem_FP (machineNotBit_mem_FP hlhs)
        machineBinarySubBorrow_mem_FP
    · exact machineAndBit_mem_FP hrhs machineBinarySubBorrow_mem_FP

theorem machineBinarySubAdvanced_mem_FP :
    machineBinarySubAdvanced ∈ Complexity.FP := by
  apply machineBinarySubPack_mem_FP
  · exact machineCompose_mem_FP machineBinarySubX_mem_FP machineTail_mem_FP
  · exact machineCompose_mem_FP machineBinarySubY_mem_FP machineTail_mem_FP
  · exact machineBinarySubNextBorrow_mem_FP
  · exact machineAppend_mem_FP machineBinarySubDiffBit_mem_FP
      machineBinarySubAccRev_mem_FP

theorem machineBinarySubStep_mem_FP :
    machineBinarySubStep ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineBinarySubActive_mem_FP
    machineBinarySubAdvanced_mem_FP id_mem_FP

theorem machineBinarySubInit_mem_FP :
    machineBinarySubInit ∈ Complexity.FP := by
  exact machineBinarySubPack_mem_FP machinePairFirst_mem_FP
    machinePairSecond_mem_FP (machineConst_mem_FP [false])
    (machineConst_mem_FP [])

theorem machineBinarySubRuler_mem_FP :
    machineBinarySubRuler ∈ Complexity.FP := by
  exact machineAppend_mem_FP machinePairFirst_mem_FP machinePairSecond_mem_FP

theorem machineBinarySubWidth_mem_FP :
    machineBinarySubWidth ∈ Complexity.FP := by
  let padded : List Bool → List Bool :=
    fun word => List.replicate 8 false ++ word
  have hpadded : padded ∈ Complexity.FP :=
    machineAppend_mem_FP (machineConst_mem_FP (List.replicate 8 false))
      id_mem_FP
  simpa only [machineBinarySubWidth, padded] using
    Cobham.mulLenFn_mem_FP hpadded hpadded

@[simp] theorem machineBinarySubX_pack (x y borrow accRev) :
    machineBinarySubX (machineBinarySubPack x y borrow accRev) = x := by
  simp [machineBinarySubX, machineBinarySubPack]

@[simp] theorem machineBinarySubY_pack (x y borrow accRev) :
    machineBinarySubY (machineBinarySubPack x y borrow accRev) = y := by
  simp [machineBinarySubY, machineBinarySubPack]

@[simp] theorem machineBinarySubBorrow_pack (x y borrow accRev) :
    machineBinarySubBorrow (machineBinarySubPack x y borrow accRev) =
      borrow := by
  simp [machineBinarySubBorrow, machineBinarySubPack]

@[simp] theorem machineBinarySubAccRev_pack (x y borrow accRev) :
    machineBinarySubAccRev (machineBinarySubPack x y borrow accRev) =
      accRev := by
  simp [machineBinarySubAccRev, machineBinarySubPack]

@[simp] theorem machineBinarySubStep_pack
    (x y accRev : List Bool) (borrow : Bool) :
    machineBinarySubStep (machineBinarySubPack x y [borrow] accRev) =
      if x = [] ∧ y = [] then
        machineBinarySubPack x y [borrow] accRev
      else
        machineBinarySubPack x.tail y.tail
          [BinaryRippleSub.borrowBit borrow
            (x.head?.getD false) (y.head?.getD false)]
          (BinaryRippleSub.diffBit borrow
              (x.head?.getD false) (y.head?.getD false) :: accRev) := by
  cases x with
  | nil =>
      cases y with
      | nil => cases borrow <;> rfl
      | cons y ys =>
          cases y <;> cases borrow <;>
            simp [machineBinarySubStep, machineBinarySubActive,
              machineBinarySubAdvanced, machineBinarySubDiffBit,
              machineBinarySubNextBorrow, BinaryRippleSub.diffBit,
              BinaryRippleSub.borrowBit, machineFullAdderSum,
              machineXorBit, machineOrBit, machineAndBit, machineNotBit]
  | cons x xs =>
      cases x <;> cases y with
      | nil =>
          cases borrow <;>
            simp [machineBinarySubStep, machineBinarySubActive,
              machineBinarySubAdvanced, machineBinarySubDiffBit,
              machineBinarySubNextBorrow, BinaryRippleSub.diffBit,
              BinaryRippleSub.borrowBit, machineFullAdderSum,
              machineXorBit, machineOrBit, machineAndBit, machineNotBit]
      | cons y ys =>
          cases y <;> cases borrow <;>
            simp [machineBinarySubStep, machineBinarySubActive,
              machineBinarySubAdvanced, machineBinarySubDiffBit,
              machineBinarySubNextBorrow, BinaryRippleSub.diffBit,
              BinaryRippleSub.borrowBit, machineFullAdderSum,
              machineXorBit, machineOrBit, machineAndBit, machineNotBit]

theorem machineBinarySubStep_pack_length_le
    (x y accRev : List Bool) (borrow : Bool) :
    (machineBinarySubStep
      (machineBinarySubPack x y [borrow] accRev)).length ≤
      (machineBinarySubPack x y [borrow] accRev).length + 1 := by
  rw [machineBinarySubStep_pack]
  split
  · omega
  · simp only [machineBinarySubPack, pair_length, List.length_cons,
      List.length_tail]
    omega

def MachineBinarySubWellFormed (state : List Bool) : Prop :=
  ∃ x y accRev : List Bool, ∃ borrow : Bool,
    state = machineBinarySubPack x y [borrow] accRev

theorem machineBinarySubInit_wellFormed (word : List Bool) :
    MachineBinarySubWellFormed (machineBinarySubInit word) := by
  exact ⟨machinePairFirst word, machinePairSecond word, [], false, rfl⟩

theorem machineBinarySubStep_wellFormed {state : List Bool}
    (hstate : MachineBinarySubWellFormed state) :
    MachineBinarySubWellFormed (machineBinarySubStep state) := by
  obtain ⟨x, y, accRev, borrow, rfl⟩ := hstate
  rw [machineBinarySubStep_pack]
  split
  · exact ⟨x, y, accRev, borrow, rfl⟩
  · exact ⟨x.tail, y.tail,
      BinaryRippleSub.diffBit borrow (x.head?.getD false)
        (y.head?.getD false) :: accRev,
      BinaryRippleSub.borrowBit borrow (x.head?.getD false)
        (y.head?.getD false), rfl⟩

theorem machineBinarySubIterate_wellFormed_length_le
    {state : List Bool} (hstate : MachineBinarySubWellFormed state) :
    ∀ iterations,
      MachineBinarySubWellFormed (machineBinarySubStep^[iterations] state) ∧
      (machineBinarySubStep^[iterations] state).length ≤
        state.length + iterations := by
  intro iterations
  induction iterations with
  | zero => simpa using And.intro hstate (Nat.le_refl state.length)
  | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hwell, hlength⟩ := ih
      have hnext := machineBinarySubStep_wellFormed hwell
      obtain ⟨x, y, accRev, borrow, hrepr⟩ := hwell
      have hstep := machineBinarySubStep_pack_length_le x y accRev borrow
      rw [← hrepr] at hstep
      exact ⟨hnext, by omega⟩

theorem machineBinarySubInit_length_le (word : List Bool) :
    (machineBinarySubInit word).length ≤ 4 * word.length + 8 := by
  simp only [machineBinarySubInit, machineBinarySubPack, pair_length,
    List.length_cons, List.length_nil]
  have hfirst := machinePairFirst_length_le word
  have hsecond := machinePairSecond_length_le word
  omega

theorem machineBinarySubRuler_length_le (word : List Bool) :
    (machineBinarySubRuler word).length ≤ 2 * word.length := by
  simp only [machineBinarySubRuler, List.length_append]
  have hfirst := machinePairFirst_length_le word
  have hsecond := machinePairSecond_length_le word
  omega

@[simp] theorem machineBinarySubWidth_length (word : List Bool) :
    (machineBinarySubWidth word).length = (word.length + 8) ^ 2 := by
  simp [machineBinarySubWidth, pow_two]

theorem machineBinarySubIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (machineBinarySubRuler word).length) :
    (machineBinarySubStep^[iterations]
      (machineBinarySubInit word)).length ≤
        (machineBinarySubWidth word).length := by
  have hrun := (machineBinarySubIterate_wellFormed_length_le
    (machineBinarySubInit_wellFormed word) iterations).2
  have hinit := machineBinarySubInit_length_le word
  have hruler := machineBinarySubRuler_length_le word
  rw [machineBinarySubWidth_length]
  nlinarith

theorem machineBinarySubFinalState_mem_FP :
    machineBinarySubFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBinarySubStep_mem_FP
    machineBinarySubInit_mem_FP machineBinarySubRuler_mem_FP
    machineBinarySubWidth_mem_FP machineBinarySubIterate_length_le_width

theorem machineBinarySubBits_mem_FP :
    machineBinarySubBits ∈ Complexity.FP := by
  have hborrow : (fun word => machineBinarySubBorrow
      (machineBinarySubFinalState word)) ∈ Complexity.FP :=
    machineCompose_mem_FP machineBinarySubFinalState_mem_FP
      machineBinarySubBorrow_mem_FP
  have hacc : (fun word => machineBinarySubAccRev
      (machineBinarySubFinalState word)) ∈ Complexity.FP :=
    machineCompose_mem_FP machineBinarySubFinalState_mem_FP
      machineBinarySubAccRev_mem_FP
  have hrev := machineCompose_mem_FP hacc machineReverse_mem_FP
  have htrim := machineCompose_mem_FP hrev machineTrimHighZeros_mem_FP
  simpa only [machineBinarySubBits] using machineIfHead_mem_FP hborrow
    (machineConst_mem_FP []) htrim

private theorem machineBinarySubStep_done (borrow : Bool)
    (accRev : List Bool) :
    machineBinarySubStep
        (machineBinarySubPack [] [] [borrow] accRev) =
      machineBinarySubPack [] [] [borrow] accRev := by
  rw [machineBinarySubStep_pack]
  simp

private theorem machineBinarySubIterate_done (borrow : Bool)
    (accRev : List Bool) (k : ℕ) :
    machineBinarySubStep^[k]
        (machineBinarySubPack [] [] [borrow] accRev) =
      machineBinarySubPack [] [] [borrow] accRev := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, machineBinarySubStep_done, ih]

private theorem machineBinarySubIterate_max
    (x y accRev : List Bool) (borrow : Bool) :
    machineBinarySubStep^[max x.length y.length]
        (machineBinarySubPack x y [borrow] accRev) =
      let raw := BinaryRippleSub.scan borrow x y
      machineBinarySubPack [] [] [raw.borrow]
        (raw.bits.reverse ++ accRev) := by
  induction hmeasure : x.length + y.length using Nat.strongRecOn
      generalizing x y borrow accRev with
  | ind measure ih =>
      cases x with
      | nil =>
          cases y with
          | nil =>
              simp [BinaryRippleSub.scan]
          | cons y ys =>
              simp only [List.length_nil, List.length_cons, Nat.zero_add]
                at hmeasure
              have hrec := ih ys.length (by omega) [] ys
                (BinaryRippleSub.diffBit borrow false y :: accRev)
                (BinaryRippleSub.borrowBit borrow false y) (by simp)
              have hrec' := hrec
              simp only [List.length_nil] at hrec'
              simp only [List.length_nil, List.length_cons]
              rw [show max 0 (ys.length + 1) =
                  (max 0 ys.length).succ by omega,
                Function.iterate_succ_apply, machineBinarySubStep_pack]
              simp only [List.nil_eq, List.cons_ne_nil, and_false,
                ↓reduceIte, List.tail_nil, List.tail_cons, List.head?_nil,
                Option.getD_none, List.head?_cons, Option.getD_some]
              rw [hrec']
              simp [BinaryRippleSub.scan, List.reverse_cons,
                List.append_assoc]
      | cons x xs =>
          cases y with
          | nil =>
              simp only [List.length_nil, List.length_cons, Nat.add_zero]
                at hmeasure
              have hrec := ih xs.length (by omega) xs []
                (BinaryRippleSub.diffBit borrow x false :: accRev)
                (BinaryRippleSub.borrowBit borrow x false) (by simp)
              have hrec' := hrec
              simp only [List.length_nil] at hrec'
              simp only [List.length_nil, List.length_cons]
              rw [show max (xs.length + 1) 0 =
                  (max xs.length 0).succ by omega,
                Function.iterate_succ_apply, machineBinarySubStep_pack]
              simp only [List.cons_ne_nil, List.nil_eq, and_false,
                ↓reduceIte, List.tail_cons, List.tail_nil, List.head?_cons,
                Option.getD_some, List.head?_nil, Option.getD_none]
              simp only [false_and, if_false]
              rw [hrec']
              simp [BinaryRippleSub.scan, List.reverse_cons,
                List.append_assoc]
          | cons y ys =>
              simp only [List.length_cons] at hmeasure
              have hrec := ih (xs.length + ys.length) (by omega) xs ys
                (BinaryRippleSub.diffBit borrow x y :: accRev)
                (BinaryRippleSub.borrowBit borrow x y) rfl
              simp only [List.length_cons]
              rw [show max (xs.length + 1) (ys.length + 1) =
                  (max xs.length ys.length).succ by omega,
                Function.iterate_succ_apply, machineBinarySubStep_pack]
              simp only [List.cons_ne_nil, and_false, ↓reduceIte,
                List.tail_cons, List.head?_cons, Option.getD_some]
              rw [hrec]
              simp [BinaryRippleSub.scan, List.reverse_cons,
                List.append_assoc]

/-- The machine agrees with the library's canonical ripple-borrow semantics
on arbitrary operand words. -/
theorem machineBinarySubBits_pair_lists (x y : List Bool) :
    machineBinarySubBits (pair x y) = BinaryRippleSub.subtract x y := by
  simp only [machineBinarySubBits, machineBinarySubFinalState,
    machineBinarySubRuler, machineBinarySubInit, machinePairFirst_pair,
    machinePairSecond_pair, List.length_append]
  rw [show x.length + y.length =
      min x.length y.length + max x.length y.length by
        have hminmax := min_add_max x.length y.length
        exact hminmax.symm,
    Function.iterate_add_apply, machineBinarySubIterate_max,
    machineBinarySubIterate_done]
  simp only [machineBinarySubBorrow_pack, machineBinarySubAccRev_pack]
  let raw := BinaryRippleSub.scan false x y
  change machineIfHead [raw.borrow] []
      (machineTrimHighZeros (raw.bits.reverse ++ []).reverse) = _
  simp only [List.append_nil, List.reverse_reverse]
  rw [machineTrimHighZeros_eq]
  cases hborrow : raw.borrow with
  | false =>
      rw [machineIfHead_false]
      simp [BinaryRippleSub.subtract, raw, hborrow]
  | true =>
      rw [machineIfHead_true]
      simp [BinaryRippleSub.subtract, raw, hborrow]

theorem binaryRippleSub_scan_bits_length :
    ∀ (borrow : Bool) (x y : List Bool),
      (BinaryRippleSub.scan borrow x y).bits.length =
        max x.length y.length := by
  intro borrow x y
  induction x generalizing borrow y with
  | nil =>
      induction y generalizing borrow with
      | nil => simp [BinaryRippleSub.scan]
      | cons bit rest ih =>
          simp [BinaryRippleSub.scan, ih]
  | cons bit rest ih =>
      cases y with
      | nil =>
          simp [BinaryRippleSub.scan, ih]
      | cons other tail =>
          simp [BinaryRippleSub.scan, ih]

theorem binaryRippleSub_trimHighZeros_length_le : ∀ bits : List Bool,
    (BinaryRippleSub.trimHighZeros bits).length ≤ bits.length := by
  intro bits
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp only [BinaryRippleSub.trimHighZeros]
      cases htrim : BinaryRippleSub.trimHighZeros rest with
      | nil => cases bit <;> simp
      | cons high tail =>
          simp only [htrim, List.length_cons] at ih ⊢
          omega

theorem binaryRippleSub_subtract_length_le (x y : List Bool) :
    (BinaryRippleSub.subtract x y).length ≤ max x.length y.length := by
  rw [BinaryRippleSub.subtract]
  let raw := BinaryRippleSub.scan false x y
  cases raw.borrow
  · exact (binaryRippleSub_trimHighZeros_length_le raw.bits).trans_eq
      (binaryRippleSub_scan_bits_length false x y)
  · simp

theorem machineBinarySubBits_pair_length_le (x y : List Bool) :
    (machineBinarySubBits (pair x y)).length ≤ max x.length y.length := by
  rw [machineBinarySubBits_pair_lists]
  exact binaryRippleSub_subtract_length_le x y

theorem machineBinarySubBits_pair_natBits (lhs rhs : ℕ) :
    machineBinarySubBits (pair lhs.bits rhs.bits) = (lhs - rhs).bits := by
  rw [machineBinarySubBits_pair_lists,
    BinaryRippleSub.subtract_natBits]

end BeyondBethe

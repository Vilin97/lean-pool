/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorSum
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidEncoding

/-!
# Polynomial-time dot products of rational vectors

The central ellipsoid update repeatedly forms rational dot products.  This
module implements the basic operation directly on two right-nested lists of
canonical rational entries.  The accumulator is an unreduced rational.  A
quadratic clamp makes the transducer polynomially bounded on every bitstring;
the semantic invariant proves that the clamp is inactive on canonical vector
inputs.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineRationalVectorDotPack
    (left right acc bound : List Bool) : List Bool :=
  pair left (pair right (pair acc bound))

def machineRationalVectorDotLeft (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRationalVectorDotRight (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRationalVectorDotAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineRationalVectorDotBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineRationalVectorDotLeftEntry (state : List Bool) : List Bool :=
  machineListHead (machineRationalVectorDotLeft state)

def machineRationalVectorDotRightEntry (state : List Bool) : List Bool :=
  machineListHead (machineRationalVectorDotRight state)

def machineRationalVectorDotProduct (state : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineRationalVectorDotLeftEntry state)
      (machineRationalVectorDotRightEntry state))

def machineRationalVectorDotCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineRationalVectorDotAcc state)
      (machineRationalVectorDotProduct state))

def machineRationalVectorDotNextAcc (state : List Bool) : List Bool :=
  (machineRationalVectorDotCandidate state).take
    (machineRationalVectorDotBound state).length

def machineRationalVectorDotAdvance (state : List Bool) : List Bool :=
  machineRationalVectorDotPack
    (machineListTail (machineRationalVectorDotLeft state))
    (machineListTail (machineRationalVectorDotRight state))
    (machineRationalVectorDotNextAcc state)
    (machineRationalVectorDotBound state)

/-- Stop as soon as either input list is exhausted. -/
def machineRationalVectorDotStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalVectorDotLeft state) state
    (machineIfEmpty (machineRationalVectorDotRight state) state
      (machineRationalVectorDotAdvance state))

def machineRationalVectorDotInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineRationalVectorDotInit (word : List Bool) : List Bool :=
  machineRationalVectorDotPack (machinePairFirst word)
    (machinePairSecond word) (rawRatBinaryCode RawRat.zero)
    (machineRationalVectorDotInputBound word)

def machineRationalVectorDotWidth (word : List Bool) : List Bool :=
  let bound := machineRationalVectorDotInputBound word
  machineRationalVectorDotPack word word bound bound

def machineRationalVectorDotFinalState (word : List Bool) : List Bool :=
  (machineRationalVectorDotStep)^[word.length]
    (machineRationalVectorDotInit word)

/-- Unreduced rational code of the dot product. -/
def machineRationalVectorDotRawCode (word : List Bool) : List Bool :=
  machineRationalVectorDotAcc
    (machineRationalVectorDotFinalState word)

/-- Canonical rational-entry code of the dot product. -/
def machineRationalVectorDotEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRationalVectorDotRawCode word)

theorem machineRationalVectorDotLeft_mem_FP :
    machineRationalVectorDotLeft ∈ FP := machinePairFirst_mem_FP

theorem machineRationalVectorDotRight_mem_FP :
    machineRationalVectorDotRight ∈ FP := by
  simpa only [machineRationalVectorDotRight] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRationalVectorDotAcc_mem_FP :
    machineRationalVectorDotAcc ∈ FP := by
  simpa only [machineRationalVectorDotAcc] using!
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP
        machinePairSecond_mem_FP)
      machinePairFirst_mem_FP

theorem machineRationalVectorDotBound_mem_FP :
    machineRationalVectorDotBound ∈ FP := by
  simpa only [machineRationalVectorDotBound] using!
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP
        machinePairSecond_mem_FP)
      machinePairSecond_mem_FP

theorem machineRationalVectorDotLeftEntry_mem_FP :
    machineRationalVectorDotLeftEntry ∈ FP := by
  simpa only [machineRationalVectorDotLeftEntry] using!
    machineCompose_mem_FP machineRationalVectorDotLeft_mem_FP
      machineListHead_mem_FP

theorem machineRationalVectorDotRightEntry_mem_FP :
    machineRationalVectorDotRightEntry ∈ FP := by
  simpa only [machineRationalVectorDotRightEntry] using!
    machineCompose_mem_FP machineRationalVectorDotRight_mem_FP
      machineListHead_mem_FP

theorem machineRationalVectorDotProduct_mem_FP :
    machineRationalVectorDotProduct ∈ FP := by
  have hp := machinePair_mem_FP machineRationalVectorDotLeftEntry_mem_FP
    machineRationalVectorDotRightEntry_mem_FP
  simpa only [machineRationalVectorDotProduct] using!
    machineCompose_mem_FP hp machineRawRatMulCode_mem_FP

theorem machineRationalVectorDotCandidate_mem_FP :
    machineRationalVectorDotCandidate ∈ FP := by
  have hp := machinePair_mem_FP machineRationalVectorDotAcc_mem_FP
    machineRationalVectorDotProduct_mem_FP
  simpa only [machineRationalVectorDotCandidate] using!
    machineCompose_mem_FP hp machineRawRatAddCode_mem_FP

theorem machineRationalVectorDotNextAcc_mem_FP :
    machineRationalVectorDotNextAcc ∈ FP := by
  simpa only [machineRationalVectorDotNextAcc] using!
    machineTake_mem_FP machineRationalVectorDotBound_mem_FP
      machineRationalVectorDotCandidate_mem_FP

theorem machineRationalVectorDotAdvance_mem_FP :
    machineRationalVectorDotAdvance ∈ FP := by
  have hl := machineCompose_mem_FP machineRationalVectorDotLeft_mem_FP
    machineListTail_mem_FP
  have hr := machineCompose_mem_FP machineRationalVectorDotRight_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP hl
    (machinePair_mem_FP hr
      (machinePair_mem_FP machineRationalVectorDotNextAcc_mem_FP
        machineRationalVectorDotBound_mem_FP))

theorem machineRationalVectorDotStep_mem_FP :
    machineRationalVectorDotStep ∈ FP := by
  have hinner := machineIfEmpty_mem_FP
    machineRationalVectorDotRight_mem_FP id_mem_FP
    machineRationalVectorDotAdvance_mem_FP
  exact machineIfEmpty_mem_FP machineRationalVectorDotLeft_mem_FP
    id_mem_FP hinner

theorem machineRationalVectorDotInputBound_mem_FP :
    machineRationalVectorDotInputBound ∈ FP :=
  machineBinaryMulWidth_mem_FP

theorem machineRationalVectorDotInit_mem_FP :
    machineRationalVectorDotInit ∈ FP := by
  exact machinePair_mem_FP machinePairFirst_mem_FP
    (machinePair_mem_FP machinePairSecond_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
        machineRationalVectorDotInputBound_mem_FP))

theorem machineRationalVectorDotWidth_mem_FP :
    machineRationalVectorDotWidth ∈ FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP machineRationalVectorDotInputBound_mem_FP
        machineRationalVectorDotInputBound_mem_FP))

@[simp] theorem machineRationalVectorDotLeft_pack (left right acc bound) :
    machineRationalVectorDotLeft
      (machineRationalVectorDotPack left right acc bound) = left := by
  simp [machineRationalVectorDotLeft, machineRationalVectorDotPack]

@[simp] theorem machineRationalVectorDotRight_pack (left right acc bound) :
    machineRationalVectorDotRight
      (machineRationalVectorDotPack left right acc bound) = right := by
  simp [machineRationalVectorDotRight, machineRationalVectorDotPack]

@[simp] theorem machineRationalVectorDotAcc_pack (left right acc bound) :
    machineRationalVectorDotAcc
      (machineRationalVectorDotPack left right acc bound) = acc := by
  simp [machineRationalVectorDotAcc, machineRationalVectorDotPack]

@[simp] theorem machineRationalVectorDotBound_pack (left right acc bound) :
    machineRationalVectorDotBound
      (machineRationalVectorDotPack left right acc bound) = bound := by
  simp [machineRationalVectorDotBound, machineRationalVectorDotPack]

def MachineRationalVectorDotStateBound
    (word state : List Bool) : Prop :=
  state = machineRationalVectorDotPack
      (machineRationalVectorDotLeft state)
      (machineRationalVectorDotRight state)
      (machineRationalVectorDotAcc state)
      (machineRationalVectorDotBound state) ∧
    (machineRationalVectorDotLeft state).length ≤ word.length ∧
    (machineRationalVectorDotRight state).length ≤ word.length ∧
    (machineRationalVectorDotAcc state).length ≤
      (machineRationalVectorDotInputBound word).length ∧
    machineRationalVectorDotBound state =
      machineRationalVectorDotInputBound word

theorem machineRationalVectorDotInit_bound (word : List Bool) :
    MachineRationalVectorDotStateBound word
      (machineRationalVectorDotInit word) := by
  simp only [MachineRationalVectorDotStateBound,
    machineRationalVectorDotInit, machineRationalVectorDotLeft_pack,
    machineRationalVectorDotRight_pack, machineRationalVectorDotAcc_pack,
    machineRationalVectorDotBound_pack]
  refine ⟨trivial, machinePairFirst_length_le word,
    machinePairSecond_length_le word, ?_, trivial⟩
  simp [machineRationalVectorDotInputBound, machineBinaryMulWidth,
    rawRatBinaryCode, RawRat.zero, integerBinaryCode]
  nlinarith [sq_nonneg (word.length + 16)]

theorem machineRationalVectorDotStep_bound {word state : List Bool}
    (hs : MachineRationalVectorDotStateBound word state) :
    MachineRationalVectorDotStateBound word
      (machineRationalVectorDotStep state) := by
  rcases hs with ⟨hdecomp, hl, hr, hacc, hbound⟩
  by_cases hleft : machineRationalVectorDotLeft state = []
  · rw [machineRationalVectorDotStep, hleft, machineIfEmpty_nil]
    exact ⟨hdecomp, hl, hr, hacc, hbound⟩
  · rw [machineRationalVectorDotStep]
    cases hleftCode : machineRationalVectorDotLeft state with
    | nil => exact False.elim (hleft hleftCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons]
        by_cases hright : machineRationalVectorDotRight state = []
        · rw [hright, machineIfEmpty_nil]
          exact ⟨hdecomp, hl, hr, hacc, hbound⟩
        · cases hrightCode : machineRationalVectorDotRight state with
          | nil => exact False.elim (hright hrightCode)
          | cons bit' tail' =>
              rw [machineIfEmpty_cons,
                machineRationalVectorDotAdvance]
              simp only [MachineRationalVectorDotStateBound,
                machineRationalVectorDotLeft_pack,
                machineRationalVectorDotRight_pack,
                machineRationalVectorDotAcc_pack,
                machineRationalVectorDotBound_pack]
              refine ⟨trivial, ?_, ?_, ?_, hbound⟩
              · exact (machineListTail_length_le
                  (machineRationalVectorDotLeft state)).trans hl
              · exact (machineListTail_length_le
                  (machineRationalVectorDotRight state)).trans hr
              · rw [machineRationalVectorDotNextAcc, hbound]
                exact List.length_take_le _ _

theorem machineRationalVectorDotIterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalVectorDotStateBound word
      ((machineRationalVectorDotStep)^[k]
        (machineRationalVectorDotInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalVectorDotInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalVectorDotStep_bound ih

theorem machineRationalVectorDotIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalVectorDotStep)^[iterations]
      (machineRationalVectorDotInit word)).length ≤
        (machineRationalVectorDotWidth word).length := by
  rcases machineRationalVectorDotIterate_bound word iterations with
    ⟨hdecomp, hl, hr, hacc, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalVectorDotPack,
    machineRationalVectorDotWidth, pair_length]
  omega

theorem machineRationalVectorDotFinalState_mem_FP :
    machineRationalVectorDotFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalVectorDotStep_mem_FP
    machineRationalVectorDotInit_mem_FP id_mem_FP
    machineRationalVectorDotWidth_mem_FP
    machineRationalVectorDotIterate_length_le_width

theorem machineRationalVectorDotRawCode_mem_FP :
    machineRationalVectorDotRawCode ∈ FP := by
  simpa only [machineRationalVectorDotRawCode] using!
    machineCompose_mem_FP machineRationalVectorDotFinalState_mem_FP
      machineRationalVectorDotAcc_mem_FP

theorem machineRationalVectorDotEntryCode_mem_FP :
    machineRationalVectorDotEntryCode ∈ FP := by
  simpa only [machineRationalVectorDotEntryCode] using!
    machineCompose_mem_FP machineRationalVectorDotRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

/-! ## Exact semantics -/

def rawRatListDotCost : List ℚ → List ℚ → ℕ
  | q :: qs, r :: rs =>
      rawRatWidth (rawRatOfRat q) + rawRatWidth (rawRatOfRat r) + 2 +
        rawRatListDotCost qs rs
  | _, _ => 0

def rawRatListDot : RawRat → List ℚ → List ℚ → RawRat
  | acc, q :: qs, r :: rs =>
      rawRatListDot
        (acc.add ((rawRatOfRat q).mul (rawRatOfRat r))) qs rs
  | acc, _, _ => acc

theorem rawRatWidth_listDot_le (acc : RawRat) : ∀ xs ys,
    rawRatWidth (rawRatListDot acc xs ys) ≤
      rawRatWidth acc + rawRatListDotCost xs ys := by
  intro xs
  induction xs generalizing acc with
  | nil => intro ys; simp [rawRatListDot, rawRatListDotCost]
  | cons q qs ih =>
      intro ys
      cases ys with
      | nil => simp [rawRatListDot, rawRatListDotCost]
      | cons r rs =>
          rw [rawRatListDot, rawRatListDotCost]
          have hmul := rawRatWidth_mul_le
            (rawRatOfRat q) (rawRatOfRat r)
          have hadd := rawRatWidth_add_le acc
            ((rawRatOfRat q).mul (rawRatOfRat r))
          have htail := ih
            (acc.add ((rawRatOfRat q).mul (rawRatOfRat r))) rs
          omega

theorem rawRatListDotCost_le_codeLength : ∀ xs ys : List ℚ,
    rawRatListDotCost xs ys ≤
      (binaryListCode rationalEntryBinaryCode xs).length +
      (binaryListCode rationalEntryBinaryCode ys).length := by
  intro xs
  induction xs with
  | nil => intro ys; simp [rawRatListDotCost]
  | cons q qs ih =>
      intro ys
      cases ys with
      | nil => simp [rawRatListDotCost]
      | cons r rs =>
          rw [rawRatListDotCost, binaryListCode, binaryListCode,
            pair_length, pair_length]
          have hq : rawRatWidth (rawRatOfRat q) ≤
              (rationalEntryBinaryCode q).length := by
            rw [← rawRatBinaryCode_rawRatOfRat]
            exact rawRatWidth_le_binaryCode_length _
          have hr : rawRatWidth (rawRatOfRat r) ≤
              (rationalEntryBinaryCode r).length := by
            rw [← rawRatBinaryCode_rawRatOfRat]
            exact rawRatWidth_le_binaryCode_length _
          have htail := ih rs
          omega

structure RationalVectorDotSemState where
  left : List ℚ
  right : List ℚ
  acc : RawRat

def rationalVectorDotSemStep
    (s : RationalVectorDotSemState) : RationalVectorDotSemState :=
  match s.left, s.right with
  | q :: qs, r :: rs =>
      ⟨qs, rs, s.acc.add ((rawRatOfRat q).mul (rawRatOfRat r))⟩
  | _, _ => s

def rationalVectorDotSemCode (bound : List Bool)
    (s : RationalVectorDotSemState) : List Bool :=
  machineRationalVectorDotPack
    (binaryListCode rationalEntryBinaryCode s.left)
    (binaryListCode rationalEntryBinaryCode s.right)
    (rawRatBinaryCode s.acc) bound

def RationalVectorDotSemInvariant (budget : ℕ)
    (s : RationalVectorDotSemState) : Prop :=
  rawRatWidth s.acc + rawRatListDotCost s.left s.right ≤ budget

theorem rationalVectorDotSemStep_invariant {budget : ℕ}
    {s : RationalVectorDotSemState}
    (hs : RationalVectorDotSemInvariant budget s) :
    RationalVectorDotSemInvariant budget
      (rationalVectorDotSemStep s) := by
  rcases s with ⟨left, right, acc⟩
  cases left with
  | nil => exact hs
  | cons q qs =>
      cases right with
      | nil => exact hs
      | cons r rs =>
          have hmul := rawRatWidth_mul_le
            (rawRatOfRat q) (rawRatOfRat r)
          have hadd := rawRatWidth_add_le acc
            ((rawRatOfRat q).mul (rawRatOfRat r))
          simp only [RationalVectorDotSemInvariant,
            rationalVectorDotSemStep, rawRatListDotCost] at hs ⊢
          omega

theorem rationalVectorDotBound_large (word : List Bool) :
    4 + 3 * (1 + word.length) ≤
      (machineRationalVectorDotInputBound word).length := by
  simp only [machineRationalVectorDotInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  nlinarith

theorem machineRationalVectorDotStep_semantics
    (word : List Bool) (s : RationalVectorDotSemState)
    (hs : RationalVectorDotSemInvariant (1 + word.length) s) :
    machineRationalVectorDotStep
        (rationalVectorDotSemCode
          (machineRationalVectorDotInputBound word) s) =
      rationalVectorDotSemCode
        (machineRationalVectorDotInputBound word)
        (rationalVectorDotSemStep s) := by
  rcases s with ⟨left, right, acc⟩
  cases left with
  | nil =>
      simp [rationalVectorDotSemCode, rationalVectorDotSemStep,
        machineRationalVectorDotStep, binaryListCode]
  | cons q qs =>
      cases right with
      | nil =>
          rw [rationalVectorDotSemCode, rationalVectorDotSemStep,
            machineRationalVectorDotStep]
          simp only [machineRationalVectorDotLeft_pack]
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _
            (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
          simp [binaryListCode, rationalVectorDotSemCode]
      | cons r rs =>
          have hnext :
              rawRatWidth
                (acc.add ((rawRatOfRat q).mul (rawRatOfRat r))) ≤
                1 + word.length := by
            have hinv := rationalVectorDotSemStep_invariant hs
            have hinv' : rawRatWidth
                (acc.add ((rawRatOfRat q).mul (rawRatOfRat r))) +
                  rawRatListDotCost qs rs ≤ 1 + word.length := by
              simpa only [RationalVectorDotSemInvariant,
              rationalVectorDotSemStep, rawRatListDotCost,
                Nat.add_zero] using! hinv
            omega
          have hcode :
              (rawRatBinaryCode
                (acc.add ((rawRatOfRat q).mul
                  (rawRatOfRat r)))).length ≤
                (machineRationalVectorDotInputBound word).length :=
            (rawRatBinaryCode_length_le_width _).trans
              ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnext) 4).trans
                (rationalVectorDotBound_large word))
          rw [rationalVectorDotSemCode, rationalVectorDotSemStep,
            machineRationalVectorDotStep]
          simp only [machineRationalVectorDotLeft_pack]
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _
            (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
          simp only [machineRationalVectorDotRight_pack]
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _
            (binaryListCode_cons_ne_nil rationalEntryBinaryCode r rs)]
          simp only [machineRationalVectorDotAdvance,
            machineRationalVectorDotLeft_pack,
            machineRationalVectorDotRight_pack,
            machineRationalVectorDotAcc_pack,
            machineRationalVectorDotBound_pack,
            machineListTail_cons, machineRationalVectorDotNextAcc,
            machineRationalVectorDotCandidate,
            machineRationalVectorDotProduct,
            machineRationalVectorDotLeftEntry,
            machineRationalVectorDotRightEntry, machineListHead_cons]
          rw [← rawRatBinaryCode_rawRatOfRat q,
            ← rawRatBinaryCode_rawRatOfRat r,
            machineRawRatMulCode_encode,
            machineRawRatAddCode_encode,
            (List.take_eq_self_iff _).mpr hcode]
          rfl

theorem machineRationalVectorDotIterate_semantics
    (word : List Bool) (s : RationalVectorDotSemState)
    (hs : RationalVectorDotSemInvariant (1 + word.length) s) : ∀ k,
    (machineRationalVectorDotStep)^[k]
        (rationalVectorDotSemCode
          (machineRationalVectorDotInputBound word) s) =
      rationalVectorDotSemCode
        (machineRationalVectorDotInputBound word)
        ((rationalVectorDotSemStep)^[k] s) := by
  intro k
  have hinv : ∀ t : ℕ,
      RationalVectorDotSemInvariant (1 + word.length)
        ((rationalVectorDotSemStep)^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact rationalVectorDotSemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineRationalVectorDotStep_semantics word _ (hinv k)

theorem rationalVectorDotSem_process : ∀ (xs ys : List ℚ)
    (acc : RawRat), xs.length = ys.length →
    (rationalVectorDotSemStep)^[xs.length]
        ⟨xs, ys, acc⟩ = ⟨[], [], rawRatListDot acc xs ys⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro ys acc hlen
      cases ys with
      | nil => rfl
      | cons r rs => simp at hlen
  | cons q qs ih =>
      intro ys acc hlen
      cases ys with
      | nil => simp at hlen
      | cons r rs =>
          rw [List.length_cons, Function.iterate_succ_apply,
            rationalVectorDotSemStep, ih]
          · rfl
          · simpa using! Nat.succ.inj hlen

theorem rationalVectorDotSem_done_iterate
    (extra : ℕ) (acc : RawRat) :
    (rationalVectorDotSemStep)^[extra]
      ⟨[], [], acc⟩ = ⟨[], [], acc⟩ := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem machineRationalVectorDot_done_iterate
    (extra : ℕ) (acc : RawRat) (bound : List Bool) :
    (machineRationalVectorDotStep)^[extra]
      (machineRationalVectorDotPack [] []
        (rawRatBinaryCode acc) bound) =
      machineRationalVectorDotPack [] []
        (rawRatBinaryCode acc) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalVectorDotStep]

theorem machineRationalVectorDotFinalState_encode {n : ℕ}
    (v w : Fin n → ℚ) :
    let word := pair (rationalFiniteVectorCode v)
      (rationalFiniteVectorCode w)
    machineRationalVectorDotFinalState word =
      machineRationalVectorDotPack [] []
        (rawRatBinaryCode
          (rawRatListDot RawRat.zero (List.ofFn v) (List.ofFn w)))
        (machineRationalVectorDotInputBound word) := by
  let left := List.ofFn v
  let right := List.ofFn w
  let word := pair (rationalFiniteVectorCode v)
    (rationalFiniteVectorCode w)
  let s : RationalVectorDotSemState := ⟨left, right, RawRat.zero⟩
  have hleftCode :
      (binaryListCode rationalEntryBinaryCode left).length ≤
        word.length := by
    calc
      _ = (machinePairFirst word).length := by
        simp [word, left, rationalFiniteVectorCode]
      _ ≤ word.length := machinePairFirst_length_le word
  have hrightCode :
      (binaryListCode rationalEntryBinaryCode right).length ≤
        word.length := by
    calc
      _ = (machinePairSecond word).length := by
        simp [word, right, rationalFiniteVectorCode]
      _ ≤ word.length := machinePairSecond_length_le word
  have hinv : RationalVectorDotSemInvariant (1 + word.length) s := by
    simp only [RationalVectorDotSemInvariant, s,
      rawRatWidth_zero]
    have hcost := rawRatListDotCost_le_codeLength left right
    have hcodes :
        (binaryListCode rationalEntryBinaryCode left).length +
            (binaryListCode rationalEntryBinaryCode right).length ≤
          word.length := by
      simp only [word, rationalFiniteVectorCode, left, right, pair_length]
      omega
    omega
  have hn : n ≤ word.length := by
    have hlist := list_length_le_binaryListCode_length
      rationalEntryBinaryCode left
    simpa only [left, List.length_ofFn] using! hlist.trans hleftCode
  have hsplit : word.length = (word.length - n) + n := by omega
  have hinit : machineRationalVectorDotInit word =
      rationalVectorDotSemCode
        (machineRationalVectorDotInputBound word) s := by
    simp [machineRationalVectorDotInit, rationalVectorDotSemCode,
      s, word, left, right, rationalFiniteVectorCode]
  have hprocess :
      (rationalVectorDotSemStep)^[n] s =
        ⟨[], [], rawRatListDot RawRat.zero left right⟩ := by
    simpa [s, left, right] using!
      (rationalVectorDotSem_process left right RawRat.zero
        (by simp [left, right]))
  change machineRationalVectorDotFinalState word = _
  rw [machineRationalVectorDotFinalState, hsplit,
    Function.iterate_add_apply, hinit,
    machineRationalVectorDotIterate_semantics word s hinv, hprocess]
  simp only [rationalVectorDotSemCode, binaryListCode]
  rw [machineRationalVectorDot_done_iterate]

@[simp] theorem machineRationalVectorDotRawCode_encode {n : ℕ}
    (v w : Fin n → ℚ) :
    machineRationalVectorDotRawCode
        (pair (rationalFiniteVectorCode v)
          (rationalFiniteVectorCode w)) =
      rawRatBinaryCode
        (rawRatListDot RawRat.zero (List.ofFn v) (List.ofFn w)) := by
  rw [machineRationalVectorDotRawCode,
    machineRationalVectorDotFinalState_encode]
  simp

theorem rawRatListDot_value (acc : RawRat) : ∀ xs ys : List ℚ,
    (rawRatListDot acc xs ys).value =
      acc.value + (List.zipWith (fun q r : ℚ => q * r) xs ys).sum := by
  intro xs ys
  induction xs generalizing acc ys with
  | nil => simp [rawRatListDot]
  | cons q qs ih =>
      cases ys with
      | nil => simp [rawRatListDot]
      | cons r rs =>
          rw [rawRatListDot, ih]
          simp [RawRat.value_add, RawRat.value_mul,
            rawRatOfRat_value, add_assoc]

theorem rawRatListDot_ofFn_value {n : ℕ} (v w : Fin n → ℚ) :
    (rawRatListDot RawRat.zero (List.ofFn v) (List.ofFn w)).value =
      ∑ i, v i * w i := by
  rw [rawRatListDot_value, RawRat.value_zero, zero_add]
  have hzip :
      List.zipWith (fun q r : ℚ => q * r)
          (List.ofFn v) (List.ofFn w) =
        List.ofFn (fun i : Fin n => v i * w i) := by
    apply List.ext_getElem
    · simp
    · intro i hiLeft hiRight
      simp
  rw [hzip, List.sum_ofFn]

@[simp] theorem machineRationalVectorDotEntryCode_encode {n : ℕ}
    (v w : Fin n → ℚ) :
    machineRationalVectorDotEntryCode
        (pair (rationalFiniteVectorCode v)
          (rationalFiniteVectorCode w)) =
      rationalEntryBinaryCode (∑ i, v i * w i) := by
  rw [machineRationalVectorDotEntryCode,
    machineRationalVectorDotRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawRatListDot_ofFn_value]

end BeyondBethe

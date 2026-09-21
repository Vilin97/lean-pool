/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRowPairDisjoint

/-!
# The deterministic greedy row matcher as a finite-word function

The matcher scans rows and columns in reverse lexicographic order, exactly the
order induced by `greedyRowMatchingList`.  Its state stores the selected
ordered row pairs as a self-delimiting list.  Disjointness is delegated to the
verified list scanner, avoiding a separate mutable-memory invariant.
-/

namespace BeyondBethe

open Complexity

def machineMatchingDimensionRuler (optimizer : List Bool) : List Bool :=
  machineCertificateDimensionUnary optimizer

def machineMatchingForwardRange (optimizer : List Bool) : List Bool :=
  machineUnaryRangeCode (machineMatchingDimensionRuler optimizer)

def machineMatchingReverseRange (optimizer : List Bool) : List Bool :=
  machineListReverse (machineMatchingForwardRange optimizer)

theorem machineMatchingDimensionRuler_mem_FP :
    machineMatchingDimensionRuler ∈ FP :=
  machineCertificateDimensionUnary_mem_FP

theorem machineMatchingForwardRange_mem_FP :
    machineMatchingForwardRange ∈ FP := by
  simpa only [machineMatchingForwardRange] using machineCompose_mem_FP
    machineMatchingDimensionRuler_mem_FP machineUnaryRangeCode_mem_FP

theorem machineMatchingReverseRange_mem_FP :
    machineMatchingReverseRange ∈ FP := by
  simpa only [machineMatchingReverseRange] using machineCompose_mem_FP
    machineMatchingForwardRange_mem_FP machineListReverse_mem_FP

@[simp] theorem machineMatchingDimensionRuler_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineMatchingDimensionRuler (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      List.replicate n true := by
  exact machineCertificateDimensionUnary_encode X R C

@[simp] theorem machineMatchingForwardRange_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineMatchingForwardRange (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      finRangeUnaryCode n := by
  rw [machineMatchingForwardRange, machineMatchingDimensionRuler_encode,
    machineUnaryRangeCode_encode]

@[simp] theorem machineMatchingReverseRange_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineMatchingReverseRange (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      binaryListCode finUnaryCode (List.finRange n).reverse := by
  rw [machineMatchingReverseRange, machineMatchingForwardRange_encode]
  exact machineListReverse_encode finUnaryCode (List.finRange n)

/-! ## The inner scan over second rows -/

/-- Inner input: `pair iUnary (pair selectedList optimizerWord)`. -/
def machineMatchingInnerFirstRow (word : List Bool) : List Bool :=
  machinePairFirst word

def machineMatchingInnerRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineMatchingInnerSelectedInput (word : List Bool) : List Bool :=
  machinePairFirst (machineMatchingInnerRest word)

def machineMatchingInnerOptimizer (word : List Bool) : List Bool :=
  machinePairSecond (machineMatchingInnerRest word)

def machineMatchingInnerPack
    (remaining selected source : List Bool) : List Bool :=
  pair remaining (pair selected source)

def machineMatchingInnerRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineMatchingInnerSelected (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineMatchingInnerSource (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineMatchingInnerCurrentSecondRow (state : List Bool) : List Bool :=
  machineListHead (machineMatchingInnerRemaining state)

def machineMatchingInnerFirstLessSecondBit (state : List Bool) : List Bool :=
  machineBinaryNatLtBit
    (pair (machineLengthBits
        (machineMatchingInnerFirstRow (machineMatchingInnerSource state)))
      (machineLengthBits (machineMatchingInnerCurrentSecondRow state)))

def machineMatchingInnerEligibilityInput (state : List Bool) : List Bool :=
  pair (machineMatchingInnerFirstRow (machineMatchingInnerSource state))
    (pair (machineMatchingInnerCurrentSecondRow state)
      (machineMatchingInnerOptimizer (machineMatchingInnerSource state)))

def machineMatchingInnerEligibleBit (state : List Bool) : List Bool :=
  machineCertifiedRowPairEligibilityBit
    (machineMatchingInnerEligibilityInput state)

def machineMatchingInnerDisjointInput (state : List Bool) : List Bool :=
  pair (machineMatchingInnerFirstRow (machineMatchingInnerSource state))
    (pair (machineMatchingInnerCurrentSecondRow state)
      (machineMatchingInnerSelected state))

def machineMatchingInnerDisjointBit (state : List Bool) : List Bool :=
  machineRowPairDisjointBit (machineMatchingInnerDisjointInput state)

def machineMatchingInnerSelectBit (state : List Bool) : List Bool :=
  machineAndBit (machineMatchingInnerFirstLessSecondBit state)
    (machineAndBit (machineMatchingInnerEligibleBit state)
      (machineMatchingInnerDisjointBit state))

def machineMatchingInnerSelectedCandidate (state : List Bool) : List Bool :=
  pair (pair (machineMatchingInnerFirstRow (machineMatchingInnerSource state))
      (machineMatchingInnerCurrentSecondRow state))
    (machineMatchingInnerSelected state)

def machineMatchingInnerInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth
    (pair word (machineMatchingReverseRange
      (machineMatchingInnerOptimizer word))))

def machineMatchingInnerBound (state : List Bool) : List Bool :=
  machineMatchingInnerInputBound (machineMatchingInnerSource state)

def machineMatchingInnerSelectedCandidateClamped
    (state : List Bool) : List Bool :=
  (machineMatchingInnerSelectedCandidate state).take
    (machineMatchingInnerBound state).length

def machineMatchingInnerNextSelected (state : List Bool) : List Bool :=
  machineIfHead (machineMatchingInnerSelectBit state)
    (machineMatchingInnerSelectedCandidateClamped state)
    (machineMatchingInnerSelected state)

def machineMatchingInnerProcess (state : List Bool) : List Bool :=
  machineMatchingInnerPack
    (machineListTail (machineMatchingInnerRemaining state))
    (machineMatchingInnerNextSelected state)
    (machineMatchingInnerSource state)

def machineMatchingInnerStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatchingInnerRemaining state) state
    (machineMatchingInnerProcess state)

def machineMatchingInnerInit (word : List Bool) : List Bool :=
  machineMatchingInnerPack
    (machineMatchingReverseRange (machineMatchingInnerOptimizer word))
    (machineMatchingInnerSelectedInput word) word

def machineMatchingInnerWidth (word : List Bool) : List Bool :=
  let bound := machineMatchingInnerInputBound word
  machineMatchingInnerPack bound bound bound

def machineMatchingInnerFinalState (word : List Bool) : List Bool :=
  (machineMatchingInnerStep)^[(machineMatchingDimensionRuler
      (machineMatchingInnerOptimizer word)).length]
    (machineMatchingInnerInit word)

def machineMatchingInnerOutputSelected (word : List Bool) : List Bool :=
  machineMatchingInnerSelected (machineMatchingInnerFinalState word)

theorem machineMatchingInnerFirstRow_mem_FP :
    machineMatchingInnerFirstRow ∈ FP := machinePairFirst_mem_FP

theorem machineMatchingInnerRest_mem_FP : machineMatchingInnerRest ∈ FP :=
  machinePairSecond_mem_FP

theorem machineMatchingInnerSelectedInput_mem_FP :
    machineMatchingInnerSelectedInput ∈ FP := by
  simpa only [machineMatchingInnerSelectedInput] using machineCompose_mem_FP
    machineMatchingInnerRest_mem_FP machinePairFirst_mem_FP

theorem machineMatchingInnerOptimizer_mem_FP :
    machineMatchingInnerOptimizer ∈ FP := by
  simpa only [machineMatchingInnerOptimizer] using machineCompose_mem_FP
    machineMatchingInnerRest_mem_FP machinePairSecond_mem_FP

theorem machineMatchingInnerRemaining_mem_FP :
    machineMatchingInnerRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineMatchingInnerSelected_mem_FP :
    machineMatchingInnerSelected ∈ FP := by
  simpa only [machineMatchingInnerSelected] using machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatchingInnerSource_mem_FP : machineMatchingInnerSource ∈ FP := by
  simpa only [machineMatchingInnerSource] using machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineMatchingInnerCurrentSecondRow_mem_FP :
    machineMatchingInnerCurrentSecondRow ∈ FP := by
  simpa only [machineMatchingInnerCurrentSecondRow] using machineCompose_mem_FP
    machineMatchingInnerRemaining_mem_FP machineListHead_mem_FP

theorem machineMatchingInnerFirstLessSecondBit_mem_FP :
    machineMatchingInnerFirstLessSecondBit ∈ FP := by
  have hfirst := machineCompose_mem_FP
    (machineCompose_mem_FP machineMatchingInnerSource_mem_FP
      machineMatchingInnerFirstRow_mem_FP) machineLengthBits_mem_FP
  have hsecond := machineCompose_mem_FP
    machineMatchingInnerCurrentSecondRow_mem_FP machineLengthBits_mem_FP
  have hinput := machinePair_mem_FP hfirst hsecond
  simpa only [machineMatchingInnerFirstLessSecondBit] using
    machineCompose_mem_FP hinput machineBinaryNatLtBit_mem_FP

theorem machineMatchingInnerEligibilityInput_mem_FP :
    machineMatchingInnerEligibilityInput ∈ FP := by
  have hfirst := machineCompose_mem_FP machineMatchingInnerSource_mem_FP
    machineMatchingInnerFirstRow_mem_FP
  have hoptimizer := machineCompose_mem_FP machineMatchingInnerSource_mem_FP
    machineMatchingInnerOptimizer_mem_FP
  exact machinePair_mem_FP hfirst
    (machinePair_mem_FP machineMatchingInnerCurrentSecondRow_mem_FP hoptimizer)

theorem machineMatchingInnerEligibleBit_mem_FP :
    machineMatchingInnerEligibleBit ∈ FP := by
  simpa only [machineMatchingInnerEligibleBit] using machineCompose_mem_FP
    machineMatchingInnerEligibilityInput_mem_FP
    machineCertifiedRowPairEligibilityBit_mem_FP

theorem machineMatchingInnerDisjointInput_mem_FP :
    machineMatchingInnerDisjointInput ∈ FP := by
  have hfirst := machineCompose_mem_FP machineMatchingInnerSource_mem_FP
    machineMatchingInnerFirstRow_mem_FP
  exact machinePair_mem_FP hfirst
    (machinePair_mem_FP machineMatchingInnerCurrentSecondRow_mem_FP
      machineMatchingInnerSelected_mem_FP)

theorem machineMatchingInnerDisjointBit_mem_FP :
    machineMatchingInnerDisjointBit ∈ FP := by
  simpa only [machineMatchingInnerDisjointBit] using machineCompose_mem_FP
    machineMatchingInnerDisjointInput_mem_FP machineRowPairDisjointBit_mem_FP

theorem machineMatchingInnerSelectBit_mem_FP :
    machineMatchingInnerSelectBit ∈ FP :=
  machineAndBit_mem_FP machineMatchingInnerFirstLessSecondBit_mem_FP
    (machineAndBit_mem_FP machineMatchingInnerEligibleBit_mem_FP
      machineMatchingInnerDisjointBit_mem_FP)

theorem machineMatchingInnerSelectedCandidate_mem_FP :
    machineMatchingInnerSelectedCandidate ∈ FP := by
  have hfirst := machineCompose_mem_FP machineMatchingInnerSource_mem_FP
    machineMatchingInnerFirstRow_mem_FP
  exact machinePair_mem_FP
    (machinePair_mem_FP hfirst machineMatchingInnerCurrentSecondRow_mem_FP)
    machineMatchingInnerSelected_mem_FP

theorem machineMatchingInnerInputBound_mem_FP :
    machineMatchingInnerInputBound ∈ FP := by
  have hoptimizerRange := machineCompose_mem_FP
    machineMatchingInnerOptimizer_mem_FP machineMatchingReverseRange_mem_FP
  have hbase := machinePair_mem_FP id_mem_FP hoptimizerRange
  have hfirstWidth :
      (fun word => machineBinaryMulWidth
        (pair word (machineMatchingReverseRange
          (machineMatchingInnerOptimizer word)))) ∈ FP :=
    machineCompose_mem_FP hbase machineBinaryMulWidth_mem_FP
  simpa only [machineMatchingInnerInputBound] using
    machineCompose_mem_FP hfirstWidth machineBinaryMulWidth_mem_FP

theorem machineMatchingInnerBound_mem_FP : machineMatchingInnerBound ∈ FP := by
  simpa only [machineMatchingInnerBound] using machineCompose_mem_FP
    machineMatchingInnerSource_mem_FP machineMatchingInnerInputBound_mem_FP

theorem machineMatchingInnerSelectedCandidateClamped_mem_FP :
    machineMatchingInnerSelectedCandidateClamped ∈ FP := by
  simpa only [machineMatchingInnerSelectedCandidateClamped] using
    machineTake_mem_FP machineMatchingInnerBound_mem_FP
      machineMatchingInnerSelectedCandidate_mem_FP

theorem machineMatchingInnerNextSelected_mem_FP :
    machineMatchingInnerNextSelected ∈ FP := by
  exact machineIfHead_mem_FP machineMatchingInnerSelectBit_mem_FP
    machineMatchingInnerSelectedCandidateClamped_mem_FP
    machineMatchingInnerSelected_mem_FP

theorem machineMatchingInnerProcess_mem_FP :
    machineMatchingInnerProcess ∈ FP := by
  have htail := machineCompose_mem_FP machineMatchingInnerRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineMatchingInnerNextSelected_mem_FP
      machineMatchingInnerSource_mem_FP)

theorem machineMatchingInnerStep_mem_FP : machineMatchingInnerStep ∈ FP := by
  simpa only [machineMatchingInnerStep] using machineIfEmpty_mem_FP
    machineMatchingInnerRemaining_mem_FP id_mem_FP
    machineMatchingInnerProcess_mem_FP

theorem machineMatchingInnerInit_mem_FP : machineMatchingInnerInit ∈ FP := by
  have hrange := machineCompose_mem_FP machineMatchingInnerOptimizer_mem_FP
    machineMatchingReverseRange_mem_FP
  exact machinePair_mem_FP hrange
    (machinePair_mem_FP machineMatchingInnerSelectedInput_mem_FP id_mem_FP)

theorem machineMatchingInnerWidth_mem_FP : machineMatchingInnerWidth ∈ FP :=
  machinePair_mem_FP machineMatchingInnerInputBound_mem_FP
    (machinePair_mem_FP machineMatchingInnerInputBound_mem_FP
      machineMatchingInnerInputBound_mem_FP)

@[simp] theorem machineMatchingInnerRemaining_pack (remaining selected source) :
    machineMatchingInnerRemaining
        (machineMatchingInnerPack remaining selected source) = remaining := by
  simp [machineMatchingInnerRemaining, machineMatchingInnerPack]

@[simp] theorem machineMatchingInnerSelected_pack (remaining selected source) :
    machineMatchingInnerSelected
        (machineMatchingInnerPack remaining selected source) = selected := by
  simp [machineMatchingInnerSelected, machineMatchingInnerPack]

@[simp] theorem machineMatchingInnerSource_pack (remaining selected source) :
    machineMatchingInnerSource
        (machineMatchingInnerPack remaining selected source) = source := by
  simp [machineMatchingInnerSource, machineMatchingInnerPack]

def MachineMatchingInnerStateBound (word state : List Bool) : Prop :=
  let B := (machineMatchingInnerInputBound word).length
  state = machineMatchingInnerPack (machineMatchingInnerRemaining state)
      (machineMatchingInnerSelected state) (machineMatchingInnerSource state) ∧
    (machineMatchingInnerRemaining state).length ≤ B ∧
    (machineMatchingInnerSelected state).length ≤ B ∧
    machineMatchingInnerSource state = word

theorem machineMatchingInner_base_le_bound (word : List Bool) :
    (pair word (machineMatchingReverseRange
      (machineMatchingInnerOptimizer word))).length ≤
      (machineMatchingInnerInputBound word).length := by
  simp only [machineMatchingInnerInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineMatchingInner_word_le_bound (word : List Bool) :
    word.length ≤ (machineMatchingInnerInputBound word).length := by
  simpa only [machinePairFirst_pair] using (machinePairFirst_length_le
    (pair word (machineMatchingReverseRange
      (machineMatchingInnerOptimizer word)))).trans
        (machineMatchingInner_base_le_bound word)

theorem machineMatchingInner_range_le_bound (word : List Bool) :
    (machineMatchingReverseRange
      (machineMatchingInnerOptimizer word)).length ≤
      (machineMatchingInnerInputBound word).length := by
  simpa only [machinePairSecond_pair] using (machinePairSecond_length_le
    (pair word (machineMatchingReverseRange
      (machineMatchingInnerOptimizer word)))).trans
        (machineMatchingInner_base_le_bound word)

theorem machineMatchingInner_selectedInput_le_bound (word : List Bool) :
    (machineMatchingInnerSelectedInput word).length ≤
      (machineMatchingInnerInputBound word).length := by
  exact ((machinePairFirst_length_le (machineMatchingInnerRest word)).trans
    (machinePairSecond_length_le word)).trans
      (machineMatchingInner_word_le_bound word)

theorem machineMatchingInnerInit_bound (word : List Bool) :
    MachineMatchingInnerStateBound word (machineMatchingInnerInit word) := by
  simp only [MachineMatchingInnerStateBound, machineMatchingInnerInit,
    machineMatchingInnerRemaining_pack, machineMatchingInnerSelected_pack,
    machineMatchingInnerSource_pack]
  exact ⟨trivial, machineMatchingInner_range_le_bound word,
    machineMatchingInner_selectedInput_le_bound word, trivial⟩

theorem machineMatchingInnerStep_bound {word state : List Bool}
    (hstate : MachineMatchingInnerStateBound word state) :
    MachineMatchingInnerStateBound word (machineMatchingInnerStep state) := by
  rcases hstate with ⟨hpack, hremaining, hselected, hsource⟩
  by_cases hrem : machineMatchingInnerRemaining state = []
  · rw [machineMatchingInnerStep, hrem, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hselected, hsource⟩
  · rw [machineMatchingInnerStep]
    cases hcode : machineMatchingInnerRemaining state with
    | nil => exact False.elim (hrem hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatchingInnerProcess]
        simp only [MachineMatchingInnerStateBound,
          machineMatchingInnerRemaining_pack, machineMatchingInnerSelected_pack,
          machineMatchingInnerSource_pack]
        refine ⟨trivial, ?_, ?_, hsource⟩
        · exact (machinePairSecond_length_le
            (machineMatchingInnerRemaining state)).trans hremaining
        · rw [machineMatchingInnerNextSelected]
          cases hs : machineMatchingInnerSelectBit state with
          | nil =>
              simpa [machineIfHead, Cobham.selectHead] using hselected
          | cons select rest =>
              cases select with
              | false =>
                  simpa using hselected
              | true =>
                simp only [machineIfHead_true,
                  machineMatchingInnerSelectedCandidateClamped,
                  List.length_take]
                rw [machineMatchingInnerBound, hsource]
                exact Nat.min_le_left _ _

theorem machineMatchingInnerIterate_bound (word : List Bool) : ∀ k,
    MachineMatchingInnerStateBound word
      ((machineMatchingInnerStep)^[k] (machineMatchingInnerInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatchingInnerInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatchingInnerStep_bound ih

theorem machineMatchingInnerIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineMatchingDimensionRuler
      (machineMatchingInnerOptimizer word)).length) :
    ((machineMatchingInnerStep)^[iterations]
        (machineMatchingInnerInit word)).length ≤
      (machineMatchingInnerWidth word).length := by
  rcases machineMatchingInnerIterate_bound word iterations with
    ⟨hpack, hremaining, hselected, hsource⟩
  have hsourceLength : (machineMatchingInnerSource
      ((machineMatchingInnerStep)^[iterations]
        (machineMatchingInnerInit word))).length ≤
      (machineMatchingInnerInputBound word).length := by
    rw [hsource]
    exact machineMatchingInner_word_le_bound word
  rw [hpack]
  simp only [machineMatchingInnerPack, machineMatchingInnerWidth, pair_length]
  omega

theorem machineMatchingInnerFinalState_mem_FP :
    machineMatchingInnerFinalState ∈ FP := by
  have hruler := machineCompose_mem_FP machineMatchingInnerOptimizer_mem_FP
    machineMatchingDimensionRuler_mem_FP
  exact Cobham.iterate_mem_FP machineMatchingInnerStep_mem_FP
    machineMatchingInnerInit_mem_FP hruler machineMatchingInnerWidth_mem_FP
    machineMatchingInnerIterate_length_le_width

theorem machineMatchingInnerOutputSelected_mem_FP :
    machineMatchingInnerOutputSelected ∈ FP := by
  simpa only [machineMatchingInnerOutputSelected] using machineCompose_mem_FP
    machineMatchingInnerFinalState_mem_FP machineMatchingInnerSelected_mem_FP

/-! ## Canonical one-step facts -/

def matchingInnerMachineInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (selected : List (Fin n × Fin n)) : List Bool :=
  pair (finUnaryCode i)
    (pair (binaryListCode orderedRowPairCode selected)
      (rationalOptimizerOutputCode ⟨X, R, C⟩))

@[simp] theorem machineMatchingInnerOptimizer_matchingInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (selected : List (Fin n × Fin n)) :
    machineMatchingInnerOptimizer
        (matchingInnerMachineInput X R C i selected) =
      rationalOptimizerOutputCode ⟨X, R, C⟩ := by
  simp [machineMatchingInnerOptimizer, machineMatchingInnerRest,
    matchingInnerMachineInput]

@[simp] theorem machineMatchingInnerSelectedInput_matchingInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (selected : List (Fin n × Fin n)) :
    machineMatchingInnerSelectedInput
        (matchingInnerMachineInput X R C i selected) =
      binaryListCode orderedRowPairCode selected := by
  simp [machineMatchingInnerSelectedInput, machineMatchingInnerRest,
    matchingInnerMachineInput]

@[simp] theorem machineMatchingInnerFirstRow_canonical {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n))
    (remaining stateSelected : List Bool) :
    machineMatchingInnerFirstRow (machineMatchingInnerSource
        (machineMatchingInnerPack remaining
          stateSelected
          (matchingInnerMachineInput X R C i sourceSelected))) =
      finUnaryCode i := by
  simp [machineMatchingInnerFirstRow, machineMatchingInnerSource,
    machineMatchingInnerPack, matchingInnerMachineInput]

@[simp] theorem machineMatchingInnerOptimizer_canonical {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n))
    (remaining stateSelected : List Bool) :
    machineMatchingInnerOptimizer (machineMatchingInnerSource
        (machineMatchingInnerPack remaining
          stateSelected
          (matchingInnerMachineInput X R C i sourceSelected))) =
      rationalOptimizerOutputCode ⟨X, R, C⟩ := by
  simp [machineMatchingInnerOptimizer, machineMatchingInnerRest,
    machineMatchingInnerSource, machineMatchingInnerPack,
    matchingInnerMachineInput]

@[simp] theorem machineMatchingInnerCurrentSecondRow_canonical {n : ℕ}
    (j : Fin n) (js : List (Fin n)) (selected source : List Bool) :
    machineMatchingInnerCurrentSecondRow
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          selected source) = finUnaryCode j := by
  simp [machineMatchingInnerCurrentSecondRow,
    machineMatchingInnerRemaining, machineMatchingInnerPack]

@[simp] theorem machineMatchingInnerSelected_canonical {n : ℕ}
    (j : Fin n) (js : List (Fin n))
    (selected : List (Fin n × Fin n)) (source : List Bool) :
    machineMatchingInnerSelected
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected) source) =
      binaryListCode orderedRowPairCode selected := by
  simp [machineMatchingInnerSelected, machineMatchingInnerPack]

@[simp] theorem machineMatchingInnerFirstLessSecondBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n)) :
    machineMatchingInnerFirstLessSecondBit
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      [decide (i < j)] := by
  rw [machineMatchingInnerFirstLessSecondBit]
  simp only [machineMatchingInnerFirstRow_canonical,
    machineMatchingInnerCurrentSecondRow_canonical,
    machineLengthBits_encode, finUnaryCode, List.length_replicate]
  exact machineBinaryNatLtBit_pair_natBits i.val j.val

@[simp] theorem machineMatchingInnerEligibilityInput_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n)) :
    machineMatchingInnerEligibilityInput
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      certifiedRowPairMachineInput X R C i j := by
  simp only [machineMatchingInnerEligibilityInput,
    machineMatchingInnerFirstRow_canonical,
    machineMatchingInnerCurrentSecondRow_canonical,
    machineMatchingInnerOptimizer_canonical,
    certifiedRowPairMachineInput]

@[simp] theorem machineMatchingInnerEligibleBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n))
    (hij : i < j) :
    machineMatchingInnerEligibleBit
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      [decide (HasCertifiedCorePair (explicitRegularizationScale n) X
        explicitKappa (directedPairCostPrecision n)
          (rowPairOfLT i j hij))] := by
  rw [machineMatchingInnerEligibleBit,
    machineMatchingInnerEligibilityInput_encode]
  have hinput : certifiedRowPairMachineInput X R C i j =
      certifiedRowPairEligibilityMachineInput X R C
        (rowPairOfLT i j hij) := by
    simp [certifiedRowPairEligibilityMachineInput,
      rowPairRow_rowPairOfLT_zero, rowPairRow_rowPairOfLT_one]
  rw [hinput, machineCertifiedRowPairEligibilityBit_encode]

@[simp] theorem machineMatchingInnerDisjointInput_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n)) :
    machineMatchingInnerDisjointInput
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      machineDisjointInput i j selected := by
  simp only [machineMatchingInnerDisjointInput,
    machineMatchingInnerFirstRow_canonical,
    machineMatchingInnerCurrentSecondRow_canonical,
    machineMatchingInnerSelected_canonical, machineDisjointInput]

@[simp] theorem machineMatchingInnerDisjointBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n)) :
    machineMatchingInnerDisjointBit
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      [!orderedPairsConflict i j selected] := by
  rw [machineMatchingInnerDisjointBit,
    machineMatchingInnerDisjointInput_encode]
  exact machineRowPairDisjointBit_encode i j selected

/-! ## Pure semantics of one inner pass -/

/-- The mathematical update performed on one ordered candidate.  The first
test fixes the canonical orientation, the second is the certified four-core
test, and the third says that neither endpoint has already been selected. -/
def certifiedGreedyOrderedStep {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (Fin n × Fin n)) (j : Fin n) :
    List (Fin n × Fin n) :=
  if hij : i < j then
    if HasCertifiedCorePair (explicitRegularizationScale n) X explicitKappa
        (directedPairCostPrecision n) (rowPairOfLT i j hij) ∧
        orderedPairsConflict i j selected = false then
      (i, j) :: selected
    else selected
  else selected

@[simp] theorem machineMatchingInnerSelectBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n)) :
    machineMatchingInnerSelectBit
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      [if hij : i < j then
        decide (HasCertifiedCorePair (explicitRegularizationScale n) X
          explicitKappa (directedPairCostPrecision n)
            (rowPairOfLT i j hij) ∧
          orderedPairsConflict i j selected = false)
        else false] := by
  by_cases hij : i < j
  · rw [machineMatchingInnerSelectBit,
      machineMatchingInnerFirstLessSecondBit_encode,
      machineMatchingInnerEligibleBit_encode X R C i j sourceSelected
        selected js hij,
      machineMatchingInnerDisjointBit_encode,
      machineAndBit_one, machineAndBit_one]
    simp [hij]
  · rw [machineMatchingInnerSelectBit,
      machineMatchingInnerFirstLessSecondBit_encode]
    simp [hij, machineAndBit, machineIfHead, Cobham.selectHead]

theorem orderedRowPairCode_length_lt_three_mul {n : ℕ}
    (i j : Fin n) :
    (orderedRowPairCode (i, j)).length < 3 * n := by
  simp only [orderedRowPairCode, pair_length, finUnaryCode,
    List.length_replicate]
  omega

theorem binaryListCode_ordered_cons_length_le {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) :
    (binaryListCode orderedRowPairCode ((i, j) :: selected)).length ≤
      (binaryListCode orderedRowPairCode selected).length + 6 * n := by
  rw [binaryListCode, pair_length]
  have h := orderedRowPairCode_length_lt_three_mul i j
  omega

/-- Fold the one-candidate update over a list of possible second rows. -/
def certifiedGreedyOrderedScan {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (Fin n × Fin n)) (js : List (Fin n)) :
    List (Fin n × Fin n) :=
  js.foldl (certifiedGreedyOrderedStep X i) selected

theorem certifiedGreedyOrderedScan_code_length_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (Fin n × Fin n)) (js : List (Fin n)) :
    (binaryListCode orderedRowPairCode
      (certifiedGreedyOrderedScan X i selected js)).length ≤
      (binaryListCode orderedRowPairCode selected).length +
        js.length * (6 * n) := by
  induction js generalizing selected with
  | nil => simp [certifiedGreedyOrderedScan]
  | cons j js ih =>
      rw [certifiedGreedyOrderedScan, List.foldl_cons]
      change (binaryListCode orderedRowPairCode
          (certifiedGreedyOrderedScan X i
            (certifiedGreedyOrderedStep X i selected j) js)).length ≤ _
      have htail := ih (certifiedGreedyOrderedStep X i selected j)
      have hstep : (binaryListCode orderedRowPairCode
          (certifiedGreedyOrderedStep X i selected j)).length ≤
          (binaryListCode orderedRowPairCode selected).length + 6 * n := by
        simp only [certifiedGreedyOrderedStep]
        split_ifs
        · exact binaryListCode_ordered_cons_length_le i j selected
        · omega
        · omega
      simp only [List.length_cons]
      calc
        _ ≤ (binaryListCode orderedRowPairCode
              (certifiedGreedyOrderedStep X i selected j)).length +
            js.length * (6 * n) := htail
        _ ≤ ((binaryListCode orderedRowPairCode selected).length + 6 * n) +
            js.length * (6 * n) := Nat.add_le_add_right hstep _
        _ = (binaryListCode orderedRowPairCode selected).length +
            (js.length + 1) * (6 * n) := by ring

@[simp] theorem machineMatchingInnerSelectedCandidate_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n)) :
    machineMatchingInnerSelectedCandidate
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      binaryListCode orderedRowPairCode ((i, j) :: selected) := by
  rw [machineMatchingInnerSelectedCandidate,
    machineMatchingInnerFirstRow_canonical,
    machineMatchingInnerCurrentSecondRow_canonical,
    machineMatchingInnerSelected_canonical]
  rfl

/-- The quadratic-of-quadratic clamp is inactive throughout a canonical inner
pass.  The hypothesis allows at most `n` preceding insertions, each of encoded
length at most `6n`; this is the only size invariant used by the semantic
proof. -/
theorem canonical_inner_candidate_length_le_bound {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (hselected : (binaryListCode orderedRowPairCode selected).length ≤
      (binaryListCode orderedRowPairCode sourceSelected).length +
        n * (6 * n)) :
    (binaryListCode orderedRowPairCode ((i, j) :: selected)).length ≤
      (machineMatchingInnerInputBound
        (matchingInnerMachineInput X R C i sourceSelected)).length := by
  let source := matchingInnerMachineInput X R C i sourceSelected
  let range := machineMatchingReverseRange
    (machineMatchingInnerOptimizer source)
  let base := pair source range
  let P := base.length
  have hinitialSource :
      (binaryListCode orderedRowPairCode sourceSelected).length ≤
        source.length := by
    dsimp only [source, matchingInnerMachineInput]
    simp only [pair_length]
    omega
  have hsourceP : source.length ≤ P := by
    simpa only [P, base, machinePairFirst_pair] using
      machinePairFirst_length_le base
  have hrangeP : range.length ≤ P := by
    simpa only [P, base, machinePairSecond_pair] using
      machinePairSecond_length_le base
  have hnrange : n ≤ range.length := by
    have hop : machineMatchingInnerOptimizer source =
        rationalOptimizerOutputCode ⟨X, R, C⟩ := by
      simp [source, matchingInnerMachineInput,
        machineMatchingInnerOptimizer, machineMatchingInnerRest]
    dsimp only [range]
    rw [hop, machineMatchingReverseRange_encode]
    simpa using binaryListCode_listLength_le finUnaryCode
      (List.finRange n).reverse
  have hnP : n ≤ P := hnrange.trans hrangeP
  have hinitialP :
      (binaryListCode orderedRowPairCode sourceSelected).length ≤ P :=
    hinitialSource.trans hsourceP
  have hcandidate := binaryListCode_ordered_cons_length_le i j selected
  have hnpos : 0 < n := by
    have := i.isLt
    omega
  have hPpos : 0 < P := lt_of_lt_of_le hnpos hnP
  have hcoarse :
      (binaryListCode orderedRowPairCode ((i, j) :: selected)).length ≤
        6 * P * P + 7 * P := by
    calc
      _ ≤ (binaryListCode orderedRowPairCode selected).length + 6 * n :=
        hcandidate
      _ ≤ ((binaryListCode orderedRowPairCode sourceSelected).length +
          n * (6 * n)) + 6 * n := Nat.add_le_add_right hselected _
      _ ≤ (P + P * (6 * P)) + 6 * P := by
        exact Nat.add_le_add
          (Nat.add_le_add hinitialP
            (Nat.mul_le_mul hnP (Nat.mul_le_mul_left 6 hnP)))
          (Nat.mul_le_mul_left 6 hnP)
      _ = 6 * P * P + 7 * P := by ring
  change (binaryListCode orderedRowPairCode ((i, j) :: selected)).length ≤
    (machineBinaryMulWidth (machineBinaryMulWidth base)).length
  simp only [machineBinaryMulWidth, List.length_replicate,
    List.length_append]
  let W := (16 + P) * (16 + P)
  have hPone : 1 ≤ P := hPpos
  have hfirst : 6 * P * P + 7 * P ≤ 13 * P * P := by
    nlinarith
  have hPW : P * P ≤ W := by
    dsimp only [W]
    nlinarith
  have hsecond : 13 * P * P ≤ 16 * W := by
    nlinarith
  have hthird : 16 * W ≤ (16 + W) * (16 + W) := by
    nlinarith
  exact hcoarse.trans (hfirst.trans (hsecond.trans hthird))

theorem machineMatchingInnerNextSelected_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) (sourceSelected selected : List (Fin n × Fin n))
    (js : List (Fin n))
    (hcandidate :
      (binaryListCode orderedRowPairCode ((i, j) :: selected)).length ≤
        (machineMatchingInnerInputBound
          (matchingInnerMachineInput X R C i sourceSelected)).length) :
    machineMatchingInnerNextSelected
        (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
          (binaryListCode orderedRowPairCode selected)
          (matchingInnerMachineInput X R C i sourceSelected)) =
      binaryListCode orderedRowPairCode
        (certifiedGreedyOrderedStep X i selected j) := by
  rw [machineMatchingInnerNextSelected,
    machineMatchingInnerSelectBit_encode]
  by_cases hij : i < j
  · by_cases haccept :
        HasCertifiedCorePair (explicitRegularizationScale n) X explicitKappa
            (directedPairCostPrecision n) (rowPairOfLT i j hij) ∧
          orderedPairsConflict i j selected = false
    · have hclamp : machineMatchingInnerSelectedCandidateClamped
          (machineMatchingInnerPack (binaryListCode finUnaryCode (j :: js))
            (binaryListCode orderedRowPairCode selected)
            (matchingInnerMachineInput X R C i sourceSelected)) =
          binaryListCode orderedRowPairCode ((i, j) :: selected) := by
        rw [machineMatchingInnerSelectedCandidateClamped,
        machineMatchingInnerSelectedCandidate_encode,
        machineMatchingInnerBound,
        machineMatchingInnerSource_pack,
        (List.take_eq_self_iff _).2 hcandidate]
      rw [hclamp]
      simp [certifiedGreedyOrderedStep, hij, haccept]
    · simp [certifiedGreedyOrderedStep, hij, haccept]
  · simp only [dite_eq_right hij, machineIfHead_false,
      certifiedGreedyOrderedStep, machineMatchingInnerSelected_pack]

theorem certifiedGreedyOrderedScan_take_succ {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (Fin n × Fin n)) (js : List (Fin n))
    (k : ℕ) (hk : k < js.length) :
    certifiedGreedyOrderedScan X i selected (js.take (k + 1)) =
      certifiedGreedyOrderedStep X i
        (certifiedGreedyOrderedScan X i selected (js.take k)) js[k] := by
  have htake : js.take (k + 1) = js.take k ++ [js[k]] := by
    simpa only [List.concat_eq_append] using (List.take_concat_get hk).symm
  unfold certifiedGreedyOrderedScan
  calc
    List.foldl (certifiedGreedyOrderedStep X i) selected (js.take (k + 1)) =
        List.foldl (certifiedGreedyOrderedStep X i) selected
          (js.take k ++ [js[k]]) := congrArg _ htake
    _ = _ := by rw [List.foldl_append]; rfl

/-- Canonical state after consuming the first `k` second-row candidates. -/
def machineMatchingInnerSemanticState {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n))
    (js : List (Fin n)) (k : ℕ) : List Bool :=
  machineMatchingInnerPack
    (binaryListCode finUnaryCode (js.drop k))
    (binaryListCode orderedRowPairCode
      (certifiedGreedyOrderedScan X i sourceSelected (js.take k)))
    (matchingInnerMachineInput X R C i sourceSelected)

theorem machineMatchingInnerSemanticState_step {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n))
    (js : List (Fin n)) (hjs : js.length ≤ n)
    (k : ℕ) (hk : k < js.length) :
    machineMatchingInnerStep
        (machineMatchingInnerSemanticState X R C i sourceSelected js k) =
      machineMatchingInnerSemanticState X R C i sourceSelected js (k + 1) := by
  rw [machineMatchingInnerSemanticState, List.drop_eq_getElem_cons hk,
    machineMatchingInnerStep]
  simp only [machineMatchingInnerRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil finUnaryCode js[k] (js.drop (k + 1))),
    machineMatchingInnerProcess]
  simp only [machineMatchingInnerRemaining_pack, machineListTail_cons,
    machineMatchingInnerSource_pack]
  let selected := certifiedGreedyOrderedScan X i sourceSelected (js.take k)
  have hscan := certifiedGreedyOrderedScan_code_length_le
    X i sourceSelected (js.take k)
  have htake : (js.take k).length ≤ n :=
    by rw [List.length_take]; omega
  have hselected :
      (binaryListCode orderedRowPairCode selected).length ≤
        (binaryListCode orderedRowPairCode sourceSelected).length +
          n * (6 * n) := by
    dsimp only [selected]
    exact hscan.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (6 * n) htake) _)
  have hcandidate := canonical_inner_candidate_length_le_bound
    X R C i js[k] sourceSelected selected hselected
  rw [machineMatchingInnerNextSelected_encode
    X R C i js[k] sourceSelected selected (js.drop (k + 1)) hcandidate]
  rw [machineMatchingInnerSemanticState]
  apply congrArg (fun chosen : List (Fin n × Fin n) ↦
    machineMatchingInnerPack
      (binaryListCode finUnaryCode (js.drop (k + 1)))
      (binaryListCode orderedRowPairCode chosen)
      (matchingInnerMachineInput X R C i sourceSelected))
  exact (certifiedGreedyOrderedScan_take_succ
    X i sourceSelected js k hk).symm

@[simp] theorem machineMatchingInnerSemanticState_zero {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n)) :
    machineMatchingInnerSemanticState X R C i sourceSelected
        (List.finRange n).reverse 0 =
      machineMatchingInnerInit
        (matchingInnerMachineInput X R C i sourceSelected) := by
  simp [machineMatchingInnerSemanticState, machineMatchingInnerInit,
    certifiedGreedyOrderedScan, machineMatchingReverseRange_encode]

theorem machineMatchingInnerIterate_semantics {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n)) : ∀ k ≤ n,
    (machineMatchingInnerStep)^[k]
        (machineMatchingInnerInit
          (matchingInnerMachineInput X R C i sourceSelected)) =
      machineMatchingInnerSemanticState X R C i sourceSelected
        (List.finRange n).reverse k := by
  intro k hk
  induction k with
  | zero => exact (machineMatchingInnerSemanticState_zero
      X R C i sourceSelected).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineMatchingInnerSemanticState_step X R C i sourceSelected
        (List.finRange n).reverse (by simp) k (by simp; omega)

@[simp] theorem machineMatchingInnerOutputSelected_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (sourceSelected : List (Fin n × Fin n)) :
    machineMatchingInnerOutputSelected
        (matchingInnerMachineInput X R C i sourceSelected) =
      binaryListCode orderedRowPairCode
        (certifiedGreedyOrderedScan X i sourceSelected
          (List.finRange n).reverse) := by
  rw [machineMatchingInnerOutputSelected,
    machineMatchingInnerFinalState,
    machineMatchingInnerOptimizer_matchingInput,
    machineMatchingDimensionRuler_encode, List.length_replicate,
    machineMatchingInnerIterate_semantics X R C i sourceSelected n le_rfl]
  simp only [machineMatchingInnerSemanticState,
    machineMatchingInnerSelected_pack]
  rw [(List.take_eq_self_iff _).2 (by simp)]

/-! ## The outer scan over first rows -/

def machineMatchingOuterPack
    (remaining selected source : List Bool) : List Bool :=
  pair remaining (pair selected source)

def machineMatchingOuterRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineMatchingOuterSelected (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineMatchingOuterSource (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineMatchingOuterCurrentFirstRow (state : List Bool) : List Bool :=
  machineListHead (machineMatchingOuterRemaining state)

def machineMatchingOuterInnerInput (state : List Bool) : List Bool :=
  pair (machineMatchingOuterCurrentFirstRow state)
    (pair (machineMatchingOuterSelected state)
      (machineMatchingOuterSource state))

def machineMatchingOuterNextSelectedRaw (state : List Bool) : List Bool :=
  machineMatchingInnerOutputSelected (machineMatchingOuterInnerInput state)

def machineMatchingOuterInputBound (optimizer : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth (machineBinaryMulWidth
    (pair optimizer (machineMatchingReverseRange optimizer))))

def machineMatchingOuterBound (state : List Bool) : List Bool :=
  machineMatchingOuterInputBound (machineMatchingOuterSource state)

def machineMatchingOuterNextSelected (state : List Bool) : List Bool :=
  (machineMatchingOuterNextSelectedRaw state).take
    (machineMatchingOuterBound state).length

def machineMatchingOuterProcess (state : List Bool) : List Bool :=
  machineMatchingOuterPack
    (machineListTail (machineMatchingOuterRemaining state))
    (machineMatchingOuterNextSelected state)
    (machineMatchingOuterSource state)

def machineMatchingOuterStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatchingOuterRemaining state) state
    (machineMatchingOuterProcess state)

def machineMatchingOuterInit (optimizer : List Bool) : List Bool :=
  machineMatchingOuterPack (machineMatchingReverseRange optimizer) [] optimizer

def machineMatchingOuterWidth (optimizer : List Bool) : List Bool :=
  let bound := machineMatchingOuterInputBound optimizer
  machineMatchingOuterPack bound bound bound

def machineMatchingOuterFinalState (optimizer : List Bool) : List Bool :=
  (machineMatchingOuterStep)^[(machineMatchingDimensionRuler optimizer).length]
    (machineMatchingOuterInit optimizer)

/-- Encoded selected ordered row pairs produced by the complete matcher. -/
def machineGreedyMatchingSelected (optimizer : List Bool) : List Bool :=
  machineMatchingOuterSelected (machineMatchingOuterFinalState optimizer)

theorem machineMatchingOuterRemaining_mem_FP :
    machineMatchingOuterRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineMatchingOuterSelected_mem_FP :
    machineMatchingOuterSelected ∈ FP := by
  simpa only [machineMatchingOuterSelected] using machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatchingOuterSource_mem_FP :
    machineMatchingOuterSource ∈ FP := by
  simpa only [machineMatchingOuterSource] using machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineMatchingOuterCurrentFirstRow_mem_FP :
    machineMatchingOuterCurrentFirstRow ∈ FP := by
  simpa only [machineMatchingOuterCurrentFirstRow] using machineCompose_mem_FP
    machineMatchingOuterRemaining_mem_FP machineListHead_mem_FP

theorem machineMatchingOuterInnerInput_mem_FP :
    machineMatchingOuterInnerInput ∈ FP :=
  machinePair_mem_FP machineMatchingOuterCurrentFirstRow_mem_FP
    (machinePair_mem_FP machineMatchingOuterSelected_mem_FP
      machineMatchingOuterSource_mem_FP)

theorem machineMatchingOuterNextSelectedRaw_mem_FP :
    machineMatchingOuterNextSelectedRaw ∈ FP := by
  simpa only [machineMatchingOuterNextSelectedRaw] using machineCompose_mem_FP
    machineMatchingOuterInnerInput_mem_FP
    machineMatchingInnerOutputSelected_mem_FP

theorem machineMatchingOuterInputBound_mem_FP :
    machineMatchingOuterInputBound ∈ FP := by
  have hrange := machineCompose_mem_FP id_mem_FP
    machineMatchingReverseRange_mem_FP
  have hbase := machinePair_mem_FP id_mem_FP hrange
  have h1 := machineCompose_mem_FP hbase machineBinaryMulWidth_mem_FP
  have h2 := machineCompose_mem_FP h1 machineBinaryMulWidth_mem_FP
  simpa only [machineMatchingOuterInputBound] using
    machineCompose_mem_FP h2 machineBinaryMulWidth_mem_FP

theorem machineMatchingOuterBound_mem_FP :
    machineMatchingOuterBound ∈ FP := by
  simpa only [machineMatchingOuterBound] using machineCompose_mem_FP
    machineMatchingOuterSource_mem_FP machineMatchingOuterInputBound_mem_FP

theorem machineMatchingOuterNextSelected_mem_FP :
    machineMatchingOuterNextSelected ∈ FP := by
  simpa only [machineMatchingOuterNextSelected] using
    machineTake_mem_FP machineMatchingOuterBound_mem_FP
      machineMatchingOuterNextSelectedRaw_mem_FP

theorem machineMatchingOuterProcess_mem_FP :
    machineMatchingOuterProcess ∈ FP := by
  have htail := machineCompose_mem_FP machineMatchingOuterRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineMatchingOuterNextSelected_mem_FP
      machineMatchingOuterSource_mem_FP)

theorem machineMatchingOuterStep_mem_FP :
    machineMatchingOuterStep ∈ FP := by
  simpa only [machineMatchingOuterStep] using machineIfEmpty_mem_FP
    machineMatchingOuterRemaining_mem_FP id_mem_FP
    machineMatchingOuterProcess_mem_FP

theorem machineMatchingOuterInit_mem_FP :
    machineMatchingOuterInit ∈ FP :=
  machinePair_mem_FP machineMatchingReverseRange_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP []) id_mem_FP)

theorem machineMatchingOuterWidth_mem_FP :
    machineMatchingOuterWidth ∈ FP :=
  machinePair_mem_FP machineMatchingOuterInputBound_mem_FP
    (machinePair_mem_FP machineMatchingOuterInputBound_mem_FP
      machineMatchingOuterInputBound_mem_FP)

@[simp] theorem machineMatchingOuterRemaining_pack (remaining selected source) :
    machineMatchingOuterRemaining
        (machineMatchingOuterPack remaining selected source) = remaining := by
  simp [machineMatchingOuterRemaining, machineMatchingOuterPack]

@[simp] theorem machineMatchingOuterSelected_pack (remaining selected source) :
    machineMatchingOuterSelected
        (machineMatchingOuterPack remaining selected source) = selected := by
  simp [machineMatchingOuterSelected, machineMatchingOuterPack]

@[simp] theorem machineMatchingOuterSource_pack (remaining selected source) :
    machineMatchingOuterSource
        (machineMatchingOuterPack remaining selected source) = source := by
  simp [machineMatchingOuterSource, machineMatchingOuterPack]

def MachineMatchingOuterStateBound (optimizer state : List Bool) : Prop :=
  let B := (machineMatchingOuterInputBound optimizer).length
  state = machineMatchingOuterPack (machineMatchingOuterRemaining state)
      (machineMatchingOuterSelected state) (machineMatchingOuterSource state) ∧
    (machineMatchingOuterRemaining state).length ≤ B ∧
    (machineMatchingOuterSelected state).length ≤ B ∧
    machineMatchingOuterSource state = optimizer

theorem machineMatchingOuter_base_le_bound (optimizer : List Bool) :
    (pair optimizer (machineMatchingReverseRange optimizer)).length ≤
      (machineMatchingOuterInputBound optimizer).length := by
  simp only [machineMatchingOuterInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineMatchingOuter_optimizer_le_bound (optimizer : List Bool) :
    optimizer.length ≤ (machineMatchingOuterInputBound optimizer).length := by
  simpa only [machinePairFirst_pair] using
    (machinePairFirst_length_le
      (pair optimizer (machineMatchingReverseRange optimizer))).trans
        (machineMatchingOuter_base_le_bound optimizer)

theorem machineMatchingOuter_range_le_bound (optimizer : List Bool) :
    (machineMatchingReverseRange optimizer).length ≤
      (machineMatchingOuterInputBound optimizer).length := by
  simpa only [machinePairSecond_pair] using
    (machinePairSecond_length_le
      (pair optimizer (machineMatchingReverseRange optimizer))).trans
        (machineMatchingOuter_base_le_bound optimizer)

theorem machineMatchingOuterInit_bound (optimizer : List Bool) :
    MachineMatchingOuterStateBound optimizer
      (machineMatchingOuterInit optimizer) := by
  simp only [MachineMatchingOuterStateBound, machineMatchingOuterInit,
    machineMatchingOuterRemaining_pack, machineMatchingOuterSelected_pack,
    machineMatchingOuterSource_pack, List.length_nil]
  exact ⟨trivial, machineMatchingOuter_range_le_bound optimizer,
    Nat.zero_le _, trivial⟩

theorem machineMatchingOuterStep_bound {optimizer state : List Bool}
    (hstate : MachineMatchingOuterStateBound optimizer state) :
    MachineMatchingOuterStateBound optimizer
      (machineMatchingOuterStep state) := by
  rcases hstate with ⟨hpack, hremaining, hselected, hsource⟩
  by_cases hrem : machineMatchingOuterRemaining state = []
  · rw [machineMatchingOuterStep, hrem, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hselected, hsource⟩
  · rw [machineMatchingOuterStep]
    cases hcode : machineMatchingOuterRemaining state with
    | nil => exact False.elim (hrem hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatchingOuterProcess]
        simp only [MachineMatchingOuterStateBound,
          machineMatchingOuterRemaining_pack,
          machineMatchingOuterSelected_pack,
          machineMatchingOuterSource_pack]
        refine ⟨trivial, ?_, ?_, hsource⟩
        · exact (machinePairSecond_length_le
            (machineMatchingOuterRemaining state)).trans hremaining
        · simp only [machineMatchingOuterNextSelected,
            List.length_take, machineMatchingOuterBound, hsource]
          exact Nat.min_le_left _ _

theorem machineMatchingOuterIterate_bound (optimizer : List Bool) : ∀ k,
    MachineMatchingOuterStateBound optimizer
      ((machineMatchingOuterStep)^[k]
        (machineMatchingOuterInit optimizer)) := by
  intro k
  induction k with
  | zero => exact machineMatchingOuterInit_bound optimizer
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatchingOuterStep_bound ih

theorem machineMatchingOuterIterate_length_le_width
    (optimizer : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineMatchingDimensionRuler optimizer).length) :
    ((machineMatchingOuterStep)^[iterations]
        (machineMatchingOuterInit optimizer)).length ≤
      (machineMatchingOuterWidth optimizer).length := by
  rcases machineMatchingOuterIterate_bound optimizer iterations with
    ⟨hpack, hremaining, hselected, hsource⟩
  have hsourceLength : (machineMatchingOuterSource
      ((machineMatchingOuterStep)^[iterations]
        (machineMatchingOuterInit optimizer))).length ≤
      (machineMatchingOuterInputBound optimizer).length := by
    rw [hsource]
    exact machineMatchingOuter_optimizer_le_bound optimizer
  rw [hpack]
  simp only [machineMatchingOuterPack, machineMatchingOuterWidth, pair_length]
  omega

theorem machineMatchingOuterFinalState_mem_FP :
    machineMatchingOuterFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineMatchingOuterStep_mem_FP
    machineMatchingOuterInit_mem_FP machineMatchingDimensionRuler_mem_FP
    machineMatchingOuterWidth_mem_FP
    machineMatchingOuterIterate_length_le_width

theorem machineGreedyMatchingSelected_mem_FP :
    machineGreedyMatchingSelected ∈ FP := by
  simpa only [machineGreedyMatchingSelected] using machineCompose_mem_FP
    machineMatchingOuterFinalState_mem_FP
    machineMatchingOuterSelected_mem_FP

/-! ## Exact outer-scan semantics -/

def certifiedGreedyOuterStep {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (Fin n × Fin n)) (i : Fin n) :
    List (Fin n × Fin n) :=
  certifiedGreedyOrderedScan X i selected (List.finRange n).reverse

def certifiedGreedyOuterScan {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (Fin n × Fin n)) (is : List (Fin n)) :
    List (Fin n × Fin n) :=
  is.foldl (certifiedGreedyOuterStep X) selected

theorem certifiedGreedyOuterStep_code_length_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (Fin n × Fin n)) (i : Fin n) :
    (binaryListCode orderedRowPairCode
      (certifiedGreedyOuterStep X selected i)).length ≤
      (binaryListCode orderedRowPairCode selected).length + n * (6 * n) := by
  simpa [certifiedGreedyOuterStep] using
    certifiedGreedyOrderedScan_code_length_le X i selected
      (List.finRange n).reverse

theorem certifiedGreedyOuterScan_code_length_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (Fin n × Fin n)) (is : List (Fin n)) :
    (binaryListCode orderedRowPairCode
      (certifiedGreedyOuterScan X selected is)).length ≤
      (binaryListCode orderedRowPairCode selected).length +
        is.length * (n * (6 * n)) := by
  induction is generalizing selected with
  | nil => simp [certifiedGreedyOuterScan]
  | cons i is ih =>
      rw [certifiedGreedyOuterScan, List.foldl_cons]
      change (binaryListCode orderedRowPairCode
          (certifiedGreedyOuterScan X
            (certifiedGreedyOuterStep X selected i) is)).length ≤ _
      have htail := ih (certifiedGreedyOuterStep X selected i)
      have hstep := certifiedGreedyOuterStep_code_length_le X selected i
      simp only [List.length_cons]
      calc
        _ ≤ (binaryListCode orderedRowPairCode
              (certifiedGreedyOuterStep X selected i)).length +
            is.length * (n * (6 * n)) := htail
        _ ≤ ((binaryListCode orderedRowPairCode selected).length +
              n * (6 * n)) + is.length * (n * (6 * n)) :=
          Nat.add_le_add_right hstep _
        _ = (binaryListCode orderedRowPairCode selected).length +
            (is.length + 1) * (n * (6 * n)) := by ring

@[simp] theorem machineMatchingOuterInnerInput_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (is : List (Fin n))
    (selected : List (Fin n × Fin n)) :
    machineMatchingOuterInnerInput
        (machineMatchingOuterPack (binaryListCode finUnaryCode (i :: is))
          (binaryListCode orderedRowPairCode selected)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      matchingInnerMachineInput X R C i selected := by
  simp [machineMatchingOuterInnerInput,
    machineMatchingOuterCurrentFirstRow,
    machineMatchingOuterRemaining, machineMatchingOuterSelected,
    machineMatchingOuterSource, machineMatchingOuterPack,
    matchingInnerMachineInput]

@[simp] theorem machineMatchingOuterNextSelectedRaw_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (is : List (Fin n))
    (selected : List (Fin n × Fin n)) :
    machineMatchingOuterNextSelectedRaw
        (machineMatchingOuterPack (binaryListCode finUnaryCode (i :: is))
          (binaryListCode orderedRowPairCode selected)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      binaryListCode orderedRowPairCode
        (certifiedGreedyOuterStep X selected i) := by
  rw [machineMatchingOuterNextSelectedRaw,
    machineMatchingOuterInnerInput_encode,
    machineMatchingInnerOutputSelected_encode]
  rfl

theorem canonical_outer_selected_length_le_bound {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (selected : List (Fin n × Fin n))
    (hselected : (binaryListCode orderedRowPairCode selected).length ≤
      n * (n * (6 * n))) :
    (binaryListCode orderedRowPairCode selected).length ≤
      (machineMatchingOuterInputBound
        (rationalOptimizerOutputCode ⟨X, R, C⟩)).length := by
  let optimizer := rationalOptimizerOutputCode ⟨X, R, C⟩
  let range := machineMatchingReverseRange optimizer
  let base := pair optimizer range
  let P := base.length
  have hrangeP : range.length ≤ P := by
    simpa only [P, base, machinePairSecond_pair] using
      machinePairSecond_length_le base
  have hnrange : n ≤ range.length := by
    dsimp only [range, optimizer]
    rw [machineMatchingReverseRange_encode]
    simpa using binaryListCode_listLength_le finUnaryCode
      (List.finRange n).reverse
  have hnP : n ≤ P := hnrange.trans hrangeP
  have hcoarse : (binaryListCode orderedRowPairCode selected).length ≤
      P * (P * (6 * P)) :=
    hselected.trans (Nat.mul_le_mul hnP
      (Nat.mul_le_mul hnP (Nat.mul_le_mul_left 6 hnP)))
  change (binaryListCode orderedRowPairCode selected).length ≤
    (machineBinaryMulWidth
      (machineBinaryMulWidth (machineBinaryMulWidth base))).length
  simp only [machineBinaryMulWidth, List.length_replicate,
    List.length_append]
  let W₁ := (16 + P) * (16 + P)
  let W₂ := (16 + W₁) * (16 + W₁)
  have hPone : 1 ≤ P := by
    dsimp only [P, base]
    simp only [pair_length]
    omega
  have hPP : P * P ≤ W₁ := by
    dsimp only [W₁]
    nlinarith
  have hfour : (P * P) * (P * P) ≤ W₁ * W₁ :=
    Nat.mul_le_mul hPP hPP
  have hcube : P * (P * (6 * P)) ≤
      6 * ((P * P) * (P * P)) := by
    nlinarith
  have hW₁sq : W₁ * W₁ ≤ W₂ := by
    dsimp only [W₂]
    nlinarith
  have htoW₂ : P * (P * (6 * P)) ≤ 16 * W₂ := by
    calc
      _ ≤ 6 * ((P * P) * (P * P)) := hcube
      _ ≤ 6 * (W₁ * W₁) := Nat.mul_le_mul_left 6 hfour
      _ ≤ 6 * W₂ := Nat.mul_le_mul_left 6 hW₁sq
      _ ≤ 16 * W₂ := Nat.mul_le_mul_right W₂ (by omega)
  have hfinal : 16 * W₂ ≤ (16 + W₂) * (16 + W₂) := by
    nlinarith
  exact hcoarse.trans (htoW₂.trans hfinal)

theorem machineMatchingOuterNextSelected_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) (is : List (Fin n))
    (selected : List (Fin n × Fin n))
    (hselected : (binaryListCode orderedRowPairCode
      (certifiedGreedyOuterStep X selected i)).length ≤
      n * (n * (6 * n))) :
    machineMatchingOuterNextSelected
        (machineMatchingOuterPack (binaryListCode finUnaryCode (i :: is))
          (binaryListCode orderedRowPairCode selected)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      binaryListCode orderedRowPairCode
        (certifiedGreedyOuterStep X selected i) := by
  rw [machineMatchingOuterNextSelected,
    machineMatchingOuterNextSelectedRaw_encode,
    machineMatchingOuterBound, machineMatchingOuterSource_pack,
    (List.take_eq_self_iff _).2
      (canonical_outer_selected_length_le_bound X R C _ hselected)]

theorem certifiedGreedyOuterScan_take_succ {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (Fin n × Fin n)) (is : List (Fin n))
    (k : ℕ) (hk : k < is.length) :
    certifiedGreedyOuterScan X selected (is.take (k + 1)) =
      certifiedGreedyOuterStep X
        (certifiedGreedyOuterScan X selected (is.take k)) is[k] := by
  have htake : is.take (k + 1) = is.take k ++ [is[k]] := by
    simpa only [List.concat_eq_append] using (List.take_concat_get hk).symm
  unfold certifiedGreedyOuterScan
  calc
    List.foldl (certifiedGreedyOuterStep X) selected (is.take (k + 1)) =
        List.foldl (certifiedGreedyOuterStep X) selected
          (is.take k ++ [is[k]]) := congrArg _ htake
    _ = _ := by rw [List.foldl_append]; rfl

def machineMatchingOuterSemanticState {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (is : List (Fin n)) (k : ℕ) : List Bool :=
  machineMatchingOuterPack
    (binaryListCode finUnaryCode (is.drop k))
    (binaryListCode orderedRowPairCode
      (certifiedGreedyOuterScan X [] (is.take k)))
    (rationalOptimizerOutputCode ⟨X, R, C⟩)

theorem machineMatchingOuterSemanticState_step {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (is : List (Fin n)) (his : is.length ≤ n)
    (k : ℕ) (hk : k < is.length) :
    machineMatchingOuterStep (machineMatchingOuterSemanticState X R C is k) =
      machineMatchingOuterSemanticState X R C is (k + 1) := by
  rw [machineMatchingOuterSemanticState, List.drop_eq_getElem_cons hk,
    machineMatchingOuterStep]
  simp only [machineMatchingOuterRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil finUnaryCode is[k] (is.drop (k + 1))),
    machineMatchingOuterProcess]
  simp only [machineMatchingOuterRemaining_pack, machineListTail_cons,
    machineMatchingOuterSource_pack]
  let selected := certifiedGreedyOuterScan X [] (is.take k)
  have hscan := certifiedGreedyOuterScan_code_length_le X [] (is.take k)
  have htake : (is.take k).length ≤ k := List.length_take_le _ _
  have hklt : k < n := lt_of_lt_of_le hk his
  have hselectedCode :
      (binaryListCode orderedRowPairCode selected).length ≤
        k * (n * (6 * n)) := by
    dsimp only [selected]
    simpa [binaryListCode] using hscan.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (n * (6 * n)) htake) _)
  have hstep := certifiedGreedyOuterStep_code_length_le X selected is[k]
  have hcandidate :
      (binaryListCode orderedRowPairCode
        (certifiedGreedyOuterStep X selected is[k])).length ≤
        n * (n * (6 * n)) := by
    calc
      _ ≤ (binaryListCode orderedRowPairCode selected).length +
          n * (6 * n) := hstep
      _ ≤ k * (n * (6 * n)) + n * (6 * n) :=
        Nat.add_le_add_right hselectedCode _
      _ = (k + 1) * (n * (6 * n)) := by ring
      _ ≤ n * (n * (6 * n)) :=
        Nat.mul_le_mul_right (n * (6 * n)) (by omega)
  rw [machineMatchingOuterNextSelected_encode
    X R C is[k] (is.drop (k + 1)) selected hcandidate]
  rw [machineMatchingOuterSemanticState]
  apply congrArg (fun chosen : List (Fin n × Fin n) ↦
    machineMatchingOuterPack
      (binaryListCode finUnaryCode (is.drop (k + 1)))
      (binaryListCode orderedRowPairCode chosen)
      (rationalOptimizerOutputCode ⟨X, R, C⟩))
  exact (certifiedGreedyOuterScan_take_succ X [] is k hk).symm

@[simp] theorem machineMatchingOuterSemanticState_zero {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineMatchingOuterSemanticState X R C (List.finRange n).reverse 0 =
      machineMatchingOuterInit (rationalOptimizerOutputCode ⟨X, R, C⟩) := by
  simp [machineMatchingOuterSemanticState, machineMatchingOuterInit,
    certifiedGreedyOuterScan, machineMatchingReverseRange_encode,
    binaryListCode]

theorem machineMatchingOuterIterate_semantics {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) : ∀ k ≤ n,
    (machineMatchingOuterStep)^[k]
        (machineMatchingOuterInit (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      machineMatchingOuterSemanticState X R C
        (List.finRange n).reverse k := by
  intro k hk
  induction k with
  | zero => exact (machineMatchingOuterSemanticState_zero X R C).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineMatchingOuterSemanticState_step X R C
        (List.finRange n).reverse (by simp) k (by simp; omega)

@[simp] theorem machineGreedyMatchingSelected_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineGreedyMatchingSelected (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      binaryListCode orderedRowPairCode
        (certifiedGreedyOuterScan X [] (List.finRange n).reverse) := by
  rw [machineGreedyMatchingSelected, machineMatchingOuterFinalState,
    machineMatchingDimensionRuler_encode, List.length_replicate,
    machineMatchingOuterIterate_semantics X R C n le_rfl]
  simp only [machineMatchingOuterSemanticState,
    machineMatchingOuterSelected_pack]
  rw [(List.take_eq_self_iff _).2 (by simp)]

/-! ## Identification with the mathematical greedy matching -/

def rowPairEndpoints {n : ℕ} (q : RowPair n) : Fin n × Fin n :=
  (rowPairRow q 0, rowPairRow q 1)

theorem rowPair_eq_pair_rows {n : ℕ} (q : RowPair n) :
    q.1 = {rowPairRow q 0, rowPairRow q 1} := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, hk⟩ := (q.1.orderIsoOfFin q.2).surjective ⟨x, hx⟩
    have hxrow : x = rowPairRow q k := by
      exact congrArg Subtype.val hk.symm
    fin_cases k <;> simp [hxrow]
  · simp [q.2, rowPairRow_ne q]

@[simp] theorem rowPairEndpoints_rowPairOfLT {n : ℕ}
    (i j : Fin n) (hij : i < j) :
    rowPairEndpoints (rowPairOfLT i j hij) = (i, j) := by
  simp [rowPairEndpoints]

theorem orderedPairsConflict_map_endpoints_eq_false_iff {n : ℕ}
    (i j : Fin n) (hij : i < j) (selected : List (RowPair n)) :
    orderedPairsConflict i j (selected.map rowPairEndpoints) = false ↔
      ∀ q ∈ selected, Disjoint (rowPairOfLT i j hij).1 q.1 := by
  induction selected with
  | nil => simp [orderedPairsConflict]
  | cons q selected ih =>
      rw [List.map_cons]
      change (decide (i = (rowPairEndpoints q).1 ∨
          i = (rowPairEndpoints q).2 ∨
          j = (rowPairEndpoints q).1 ∨ j = (rowPairEndpoints q).2) ||
          orderedPairsConflict i j (selected.map rowPairEndpoints)) = false ↔ _
      rw [Bool.or_eq_false_iff, ih]
      constructor
      · rintro ⟨hhead, htail⟩ r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · rw [rowPair_eq_pair_rows (rowPairOfLT i j hij),
            rowPair_eq_pair_rows r,
            rowPairRow_rowPairOfLT_zero,
            rowPairRow_rowPairOfLT_one]
          simpa [rowPairEndpoints, Finset.disjoint_left, and_assoc] using hhead
        · exact htail r hr
      · intro hall
        refine ⟨?_, fun r hr ↦ hall r (List.mem_cons_of_mem _ hr)⟩
        have hdisj := hall q (by simp)
        rw [rowPair_eq_pair_rows (rowPairOfLT i j hij),
          rowPair_eq_pair_rows q,
          rowPairRow_rowPairOfLT_zero,
          rowPairRow_rowPairOfLT_one] at hdisj
        simpa [rowPairEndpoints, rowPairOfLT,
          Finset.disjoint_left, and_assoc] using hdisj

/-- The same greedy update, now retaining the proof-carrying unordered row
pair.  This is the bridge from the machine's endpoint representation to the
mathematical matching. -/
def certifiedGreedyTypedStep {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (RowPair n)) (j : Fin n) : List (RowPair n) :=
  if hij : i < j then
    let q := rowPairOfLT i j hij
    if HasCertifiedCorePair (explicitRegularizationScale n) X explicitKappa
          (directedPairCostPrecision n) q ∧
        ∀ r ∈ selected, Disjoint q.1 r.1 then
      q :: selected
    else selected
  else selected

theorem certifiedGreedyOrderedStep_map_endpoints {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    (selected : List (RowPair n)) :
    certifiedGreedyOrderedStep X i (selected.map rowPairEndpoints) j =
      (certifiedGreedyTypedStep X i selected j).map rowPairEndpoints := by
  by_cases hij : i < j
  · rw [certifiedGreedyOrderedStep, dif_pos hij,
      certifiedGreedyTypedStep, dif_pos hij]
    have hiff := orderedPairsConflict_map_endpoints_eq_false_iff
      i j hij selected
    by_cases h : HasCertifiedCorePair (explicitRegularizationScale n) X
          explicitKappa (directedPairCostPrecision n) (rowPairOfLT i j hij) ∧
        orderedPairsConflict i j (selected.map rowPairEndpoints) = false
    · have htyped : HasCertifiedCorePair (explicitRegularizationScale n) X
          explicitKappa (directedPairCostPrecision n) (rowPairOfLT i j hij) ∧
          ∀ r ∈ selected, Disjoint (rowPairOfLT i j hij).1 r.1 :=
        ⟨h.1, hiff.mp h.2⟩
      rw [ite_eq_left h, ite_eq_left htyped, List.map_cons,
        rowPairEndpoints_rowPairOfLT]
    · have htyped : ¬(HasCertifiedCorePair
          (explicitRegularizationScale n) X explicitKappa
            (directedPairCostPrecision n) (rowPairOfLT i j hij) ∧
          ∀ r ∈ selected, Disjoint (rowPairOfLT i j hij).1 r.1) := by
        intro ht
        exact h ⟨ht.1, hiff.mpr ht.2⟩
      rw [ite_eq_right h, ite_eq_right htyped]
  · simp [certifiedGreedyOrderedStep, certifiedGreedyTypedStep, hij]

def certifiedGreedyTypedInnerScan {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (RowPair n)) (js : List (Fin n)) : List (RowPair n) :=
  js.foldl (certifiedGreedyTypedStep X i) selected

theorem certifiedGreedyOrderedScan_map_endpoints {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (RowPair n)) (js : List (Fin n)) :
    certifiedGreedyOrderedScan X i (selected.map rowPairEndpoints) js =
      (certifiedGreedyTypedInnerScan X i selected js).map
        rowPairEndpoints := by
  induction js generalizing selected with
  | nil => rfl
  | cons j js ih =>
      rw [certifiedGreedyOrderedScan, certifiedGreedyTypedInnerScan,
        List.foldl_cons, List.foldl_cons,
        certifiedGreedyOrderedStep_map_endpoints]
      exact ih (certifiedGreedyTypedStep X i selected j)

def certifiedGreedyTypedOuterStep {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (RowPair n)) (i : Fin n) : List (RowPair n) :=
  certifiedGreedyTypedInnerScan X i selected (List.finRange n).reverse

def certifiedGreedyTypedOuterScan {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (RowPair n)) (is : List (Fin n)) : List (RowPair n) :=
  is.foldl (certifiedGreedyTypedOuterStep X) selected

theorem certifiedGreedyOuterScan_map_endpoints {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (RowPair n)) (is : List (Fin n)) :
    certifiedGreedyOuterScan X (selected.map rowPairEndpoints) is =
      (certifiedGreedyTypedOuterScan X selected is).map
        rowPairEndpoints := by
  induction is generalizing selected with
  | nil => rfl
  | cons i is ih =>
      rw [certifiedGreedyOuterScan, certifiedGreedyTypedOuterScan,
        List.foldl_cons, List.foldl_cons]
      change certifiedGreedyOuterScan X
          (certifiedGreedyOrderedScan X i
            (selected.map rowPairEndpoints) (List.finRange n).reverse) is = _
      rw [certifiedGreedyOrderedScan_map_endpoints]
      exact ih (certifiedGreedyTypedOuterStep X selected i)

def canonicalRowPairCandidate {n : ℕ} (i j : Fin n) : Option (RowPair n) :=
  if hij : i < j then some (rowPairOfLT i j hij) else none

def certifiedRowPairEligibleBit {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (q : RowPair n) : Bool :=
  decide (HasCertifiedCorePair (explicitRegularizationScale n) X
    explicitKappa (directedPairCostPrecision n) q)

def greedyRowListStep {n : ℕ}
    (selected : List (RowPair n)) (q : RowPair n) : List (RowPair n) :=
  if ∀ r ∈ selected, Disjoint q.1 r.1 then q :: selected else selected

def certifiedGreedyEdgeStep {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (RowPair n)) (q : RowPair n) : List (RowPair n) :=
  if certifiedRowPairEligibleBit X q then greedyRowListStep selected q
  else selected

theorem certifiedGreedyTypedStep_eq_candidate {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    (selected : List (RowPair n)) :
    certifiedGreedyTypedStep X i selected j =
      match canonicalRowPairCandidate i j with
      | some q => certifiedGreedyEdgeStep X selected q
      | none => selected := by
  by_cases hij : i < j
  · simp only [certifiedGreedyTypedStep, canonicalRowPairCandidate,
      dif_pos hij, certifiedGreedyEdgeStep, certifiedRowPairEligibleBit,
      greedyRowListStep]
    by_cases heligible : HasCertifiedCorePair (explicitRegularizationScale n) X
        explicitKappa (directedPairCostPrecision n) (rowPairOfLT i j hij)
    · simp [heligible]
    · simp [heligible]
  · simp [certifiedGreedyTypedStep, canonicalRowPairCandidate, hij]

theorem certifiedGreedyTypedInnerScan_eq_filterMap_fold {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (selected : List (RowPair n)) (js : List (Fin n)) :
    certifiedGreedyTypedInnerScan X i selected js =
      (js.filterMap (canonicalRowPairCandidate i)).foldl
        (certifiedGreedyEdgeStep X) selected := by
  rw [List.foldl_filterMap]
  unfold certifiedGreedyTypedInnerScan
  congr 1
  funext acc j
  by_cases hij : i < j
  · by_cases heligible : HasCertifiedCorePair
        (explicitRegularizationScale n) X explicitKappa
          (directedPairCostPrecision n) (rowPairOfLT i j hij)
    · by_cases hdisjoint : ∀ r ∈ acc,
          Disjoint (rowPairOfLT i j hij).1 r.1
      · simp [certifiedGreedyTypedStep, canonicalRowPairCandidate,
          certifiedGreedyEdgeStep, certifiedRowPairEligibleBit,
          greedyRowListStep, hij, heligible, hdisjoint]
      · simp [certifiedGreedyTypedStep, canonicalRowPairCandidate,
          certifiedGreedyEdgeStep, certifiedRowPairEligibleBit,
          greedyRowListStep, hij, heligible, hdisjoint]
    · simp [certifiedGreedyTypedStep, canonicalRowPairCandidate,
        certifiedGreedyEdgeStep, certifiedRowPairEligibleBit,
        greedyRowListStep, hij, heligible]
  · simp [certifiedGreedyTypedStep, canonicalRowPairCandidate, hij]

theorem reverse_allRowPairsList {n : ℕ} :
    (allRowPairsList n).reverse =
      (List.finRange n).reverse.flatMap fun i ↦
        (List.finRange n).reverse.filterMap
          (canonicalRowPairCandidate i) := by
  rw [allRowPairsList, List.reverse_flatMap]
  apply congrArg (fun f ↦ (List.finRange n).reverse.flatMap f)
  funext i
  change ((List.finRange n).filterMap
      (canonicalRowPairCandidate i)).reverse =
    (List.finRange n).reverse.filterMap (canonicalRowPairCandidate i)
  exact (List.filterMap_reverse).symm

theorem certifiedGreedyTypedOuterScan_eq_edgeFold {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (RowPair n)) (is : List (Fin n)) :
    certifiedGreedyTypedOuterScan X selected is =
      (is.flatMap fun i ↦ (List.finRange n).reverse.filterMap
          (canonicalRowPairCandidate i)).foldl
        (certifiedGreedyEdgeStep X) selected := by
  rw [List.foldl_flatMap]
  unfold certifiedGreedyTypedOuterScan
  congr 1
  funext acc i
  exact certifiedGreedyTypedInnerScan_eq_filterMap_fold
    X i acc (List.finRange n).reverse

theorem certifiedGreedyTypedOuterScan_full_eq_edgeFold {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    certifiedGreedyTypedOuterScan X [] (List.finRange n).reverse =
      (allRowPairsList n).reverse.foldl (certifiedGreedyEdgeStep X) [] := by
  rw [certifiedGreedyTypedOuterScan_eq_edgeFold,
    ← reverse_allRowPairsList]

theorem certifiedGreedyEdgeFold_eq_filter {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (selected : List (RowPair n)) (edges : List (RowPair n)) :
    edges.foldl (certifiedGreedyEdgeStep X) selected =
      (edges.filter (certifiedRowPairEligibleBit X)).foldl
        greedyRowListStep selected := by
  rw [List.foldl_filter]
  congr 1

theorem explicitThresholdRowPairsList_eq_certifiedFilter {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    thresholdRowPairsList (explicitCertifiedRowWeight X) explicitGamma =
      (allRowPairsList n).filter (certifiedRowPairEligibleBit X) := by
  rw [thresholdRowPairsList]
  apply List.filter_congr
  intro q _
  by_cases h : HasCertifiedCorePair (explicitRegularizationScale n) X
      explicitKappa (directedPairCostPrecision n) q
  · simp [explicitCertifiedRowWeight, certifiedConstantRowWeight,
      certifiedRowPairEligibleBit, h]
  · simp [explicitCertifiedRowWeight, certifiedConstantRowWeight,
      certifiedRowPairEligibleBit, explicitGamma, h]

def greedyRowFinsetStep {n : ℕ}
    (selected : Finset (RowPair n)) (q : RowPair n) : Finset (RowPair n) :=
  if ∀ r ∈ selected, Disjoint q.1 r.1 then insert q selected else selected

@[simp] theorem greedyRowListStep_toFinset {n : ℕ}
    (selected : List (RowPair n)) (q : RowPair n) :
    (greedyRowListStep selected q).toFinset =
      greedyRowFinsetStep selected.toFinset q := by
  by_cases h : ∀ r ∈ selected, Disjoint q.1 r.1
  · have hfin : ∀ r ∈ selected.toFinset, Disjoint q.1 r.1 := by
      simpa using h
    rw [greedyRowListStep, ite_eq_left h,
      greedyRowFinsetStep, ite_eq_left hfin]
    simp
  · have hfin : ¬(∀ r ∈ selected.toFinset, Disjoint q.1 r.1) := by
      simpa using h
    rw [greedyRowListStep, ite_eq_right h,
      greedyRowFinsetStep, ite_eq_right hfin]

theorem greedyRowListFold_toFinset {n : ℕ}
    (selected : List (RowPair n)) (edges : List (RowPair n)) :
    (edges.foldl greedyRowListStep selected).toFinset =
      edges.foldl greedyRowFinsetStep selected.toFinset := by
  induction edges generalizing selected with
  | nil => rfl
  | cons q edges ih =>
      rw [List.foldl_cons, List.foldl_cons, ih,
        greedyRowListStep_toFinset]

theorem greedyRowMatchingList_eq_finsetFoldReverse {n : ℕ}
    (edges : List (RowPair n)) :
    greedyRowMatchingList edges =
      edges.reverse.foldl greedyRowFinsetStep ∅ := by
  induction edges with
  | nil => rfl
  | cons q edges ih =>
      rw [greedyRowMatchingList, List.reverse_cons,
        List.foldl_append, ih]
      simp [greedyRowFinsetStep]

theorem certifiedGreedyTypedOuterScan_toFinset {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    (certifiedGreedyTypedOuterScan X []
      (List.finRange n).reverse).toFinset =
      greedyThresholdRowMatching (explicitCertifiedRowWeight X)
        explicitGamma := by
  rw [certifiedGreedyTypedOuterScan_full_eq_edgeFold,
    certifiedGreedyEdgeFold_eq_filter,
    List.filter_reverse,
    ← explicitThresholdRowPairsList_eq_certifiedFilter,
    greedyRowListFold_toFinset]
  simp only [List.toFinset_nil]
  rw [← greedyRowMatchingList_eq_finsetFoldReverse]
  rfl

theorem rowPair_not_disjoint_self {n : ℕ} (q : RowPair n) :
    ¬Disjoint q.1 q.1 := by
  apply Finset.not_disjoint_iff.mpr
  exact ⟨rowPairRow q 0, rowPairRow_mem q 0, rowPairRow_mem q 0⟩

theorem certifiedGreedyTypedStep_nodup {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    {selected : List (RowPair n)} (hselected : selected.Nodup) :
    (certifiedGreedyTypedStep X i selected j).Nodup := by
  by_cases hij : i < j
  · rw [certifiedGreedyTypedStep, dif_pos hij]
    dsimp only
    split_ifs with haccept
    · rw [List.nodup_cons]
      refine ⟨?_, hselected⟩
      intro hmem
      exact rowPair_not_disjoint_self _ (haccept.2 _ hmem)
    · exact hselected
  · rw [certifiedGreedyTypedStep, dite_eq_right hij]
    exact hselected

theorem certifiedGreedyTypedInnerScan_nodup {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    {selected : List (RowPair n)} (hselected : selected.Nodup)
    (js : List (Fin n)) :
    (certifiedGreedyTypedInnerScan X i selected js).Nodup := by
  induction js generalizing selected with
  | nil => exact hselected
  | cons j js ih =>
      rw [certifiedGreedyTypedInnerScan, List.foldl_cons]
      exact ih (certifiedGreedyTypedStep_nodup X i j hselected)

theorem certifiedGreedyTypedOuterStep_nodup {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    {selected : List (RowPair n)} (hselected : selected.Nodup) (i : Fin n) :
    (certifiedGreedyTypedOuterStep X selected i).Nodup := by
  exact certifiedGreedyTypedInnerScan_nodup X i hselected _

theorem certifiedGreedyTypedOuterScan_nodup {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    {selected : List (RowPair n)} (hselected : selected.Nodup)
    (is : List (Fin n)) :
    (certifiedGreedyTypedOuterScan X selected is).Nodup := by
  induction is generalizing selected with
  | nil => exact hselected
  | cons i is ih =>
      rw [certifiedGreedyTypedOuterScan, List.foldl_cons]
      exact ih (certifiedGreedyTypedOuterStep_nodup X hselected i)

theorem certifiedGreedyTypedOuterScan_full_nodup {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    (certifiedGreedyTypedOuterScan X []
      (List.finRange n).reverse).Nodup :=
  certifiedGreedyTypedOuterScan_nodup X (by simp) _

@[simp] theorem machineGreedyMatchingSelected_typed_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineGreedyMatchingSelected (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      binaryListCode orderedRowPairCode
        ((certifiedGreedyTypedOuterScan X []
          (List.finRange n).reverse).map rowPairEndpoints) := by
  rw [machineGreedyMatchingSelected_encode,
    ← certifiedGreedyOuterScan_map_endpoints X []
      (List.finRange n).reverse]
  rfl

end BeyondBethe

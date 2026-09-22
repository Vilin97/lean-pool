/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineFourCoreCost
import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryRange
import LeanPool.BeyondBethe.BeyondBethe.MachineLengthBits

/-!
# Executable column-pair eligibility

For a fixed row pair, the certificate asks whether two distinct columns pass
the directed four-core test.  This file implements the two bounded scans:
first over the second column for a fixed first column, and then over the first
column.  Both loops are driven by the unary matrix dimension, and all state is
clamped on arbitrary bitstrings.
-/

namespace BeyondBethe

open Complexity

def rawExplicitKappa : RawRat := rawRatOfRat explicitKappa

def machineExplicitKappaRawCode (_word : List Bool) : List Bool :=
  rawRatBinaryCode rawExplicitKappa

theorem machineExplicitKappaRawCode_mem_FP :
    machineExplicitKappaRawCode ∈ FP :=
  machineConst_mem_FP (rawRatBinaryCode rawExplicitKappa)

/-! ## The inner scan: second columns for a fixed first column -/

def machineFixedAFirstRowRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineFixedARest₁ (word : List Bool) : List Bool :=
  machinePairSecond word

def machineFixedASecondRowRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFixedARest₁ word)

def machineFixedARest₂ (word : List Bool) : List Bool :=
  machinePairSecond (machineFixedARest₁ word)

def machineFixedAFirstColumnRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFixedARest₂ word)

def machineFixedAOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond (machineFixedARest₂ word)

def machineFixedADimensionRuler (word : List Bool) : List Bool :=
  machineCertificateDimensionUnary (machineFixedAOptimizerWord word)

def machineFixedAColumnRange (word : List Bool) : List Bool :=
  machineUnaryRangeCode (machineFixedADimensionRuler word)

def machineFixedAPack
    (remaining found source : List Bool) : List Bool :=
  pair remaining (pair found source)

def machineFixedARemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineFixedAFound (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineFixedASource (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineFixedACurrentSecondColumn (state : List Bool) : List Bool :=
  machineListHead (machineFixedARemaining state)

def machineFixedAColumnsEqualBit (state : List Bool) : List Bool :=
  machineBinaryNatEqBit
    (pair (machineLengthBits
        (machineFixedAFirstColumnRuler (machineFixedASource state)))
      (machineLengthBits (machineFixedACurrentSecondColumn state)))

def machineFixedAColumnsDistinctBit (state : List Bool) : List Bool :=
  machineNotBit (machineFixedAColumnsEqualBit state)

def machineFixedAFourCoreInput (state : List Bool) : List Bool :=
  pair (machineFixedAFirstRowRuler (machineFixedASource state))
    (pair (machineFixedASecondRowRuler (machineFixedASource state))
      (pair (machineFixedAFirstColumnRuler (machineFixedASource state))
        (pair (machineFixedACurrentSecondColumn state)
          (machineFixedAOptimizerWord (machineFixedASource state)))))

def machineFixedAFourCoreRawCode (state : List Bool) : List Bool :=
  machineDirectedFourCoreCostUpperRawCode
    (machineFixedAFourCoreInput state)

def machineFixedACostPassesBit (state : List Bool) : List Bool :=
  machineRawRatLeBit
    (pair (machineFixedAFourCoreRawCode state)
      (rawRatBinaryCode rawExplicitKappa))

def machineFixedACandidateBit (state : List Bool) : List Bool :=
  machineAndBit (machineFixedAColumnsDistinctBit state)
    (machineFixedACostPassesBit state)

def machineFixedAInputBound (word : List Bool) : List Bool :=
  pair word (machineFixedAColumnRange word)

def machineFixedANextFound (state : List Bool) : List Bool :=
  (machineOrBit (machineFixedAFound state)
      (machineFixedACandidateBit state)).take
    (machineFixedAInputBound (machineFixedASource state)).length

def machineFixedAProcess (state : List Bool) : List Bool :=
  machineFixedAPack (machineListTail (machineFixedARemaining state))
    (machineFixedANextFound state) (machineFixedASource state)

def machineFixedAStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineFixedARemaining state) state
    (machineFixedAProcess state)

def machineFixedAInit (word : List Bool) : List Bool :=
  machineFixedAPack (machineFixedAColumnRange word) [false] word

def machineFixedAWidth (word : List Bool) : List Bool :=
  let bound := machineFixedAInputBound word
  machineFixedAPack bound bound bound

def machineFixedAFinalState (word : List Bool) : List Bool :=
  (machineFixedAStep)^[(machineFixedADimensionRuler word).length]
    (machineFixedAInit word)

/-- One bit indicating whether some second column completes a certified pair
with the fixed first column. -/
def machineFixedAEligibilityBit (word : List Bool) : List Bool :=
  machineFixedAFound (machineFixedAFinalState word)

theorem machineFixedAFirstRowRuler_mem_FP :
    machineFixedAFirstRowRuler ∈ FP := machinePairFirst_mem_FP

theorem machineFixedARest₁_mem_FP : machineFixedARest₁ ∈ FP :=
  machinePairSecond_mem_FP

theorem machineFixedASecondRowRuler_mem_FP :
    machineFixedASecondRowRuler ∈ FP := by
  simpa only [machineFixedASecondRowRuler] using! machineCompose_mem_FP
    machineFixedARest₁_mem_FP machinePairFirst_mem_FP

theorem machineFixedARest₂_mem_FP : machineFixedARest₂ ∈ FP := by
  simpa only [machineFixedARest₂] using! machineCompose_mem_FP
    machineFixedARest₁_mem_FP machinePairSecond_mem_FP

theorem machineFixedAFirstColumnRuler_mem_FP :
    machineFixedAFirstColumnRuler ∈ FP := by
  simpa only [machineFixedAFirstColumnRuler] using! machineCompose_mem_FP
    machineFixedARest₂_mem_FP machinePairFirst_mem_FP

theorem machineFixedAOptimizerWord_mem_FP :
    machineFixedAOptimizerWord ∈ FP := by
  simpa only [machineFixedAOptimizerWord] using! machineCompose_mem_FP
    machineFixedARest₂_mem_FP machinePairSecond_mem_FP

theorem machineFixedADimensionRuler_mem_FP :
    machineFixedADimensionRuler ∈ FP := by
  simpa only [machineFixedADimensionRuler] using! machineCompose_mem_FP
    machineFixedAOptimizerWord_mem_FP machineCertificateDimensionUnary_mem_FP

theorem machineFixedAColumnRange_mem_FP : machineFixedAColumnRange ∈ FP := by
  simpa only [machineFixedAColumnRange] using! machineCompose_mem_FP
    machineFixedADimensionRuler_mem_FP machineUnaryRangeCode_mem_FP

theorem machineFixedARemaining_mem_FP : machineFixedARemaining ∈ FP :=
  machinePairFirst_mem_FP

theorem machineFixedAFound_mem_FP : machineFixedAFound ∈ FP := by
  simpa only [machineFixedAFound] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineFixedASource_mem_FP : machineFixedASource ∈ FP := by
  simpa only [machineFixedASource] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineFixedACurrentSecondColumn_mem_FP :
    machineFixedACurrentSecondColumn ∈ FP := by
  simpa only [machineFixedACurrentSecondColumn] using! machineCompose_mem_FP
    machineFixedARemaining_mem_FP machineListHead_mem_FP

theorem machineFixedAColumnsEqualBit_mem_FP :
    machineFixedAColumnsEqualBit ∈ FP := by
  have hfirst := machineCompose_mem_FP
    (machineCompose_mem_FP machineFixedASource_mem_FP
      machineFixedAFirstColumnRuler_mem_FP) machineLengthBits_mem_FP
  have hsecond := machineCompose_mem_FP
    machineFixedACurrentSecondColumn_mem_FP machineLengthBits_mem_FP
  have hinput := machinePair_mem_FP hfirst hsecond
  simpa only [machineFixedAColumnsEqualBit] using! machineCompose_mem_FP hinput
    machineBinaryNatEqBit_mem_FP

theorem machineFixedAColumnsDistinctBit_mem_FP :
    machineFixedAColumnsDistinctBit ∈ FP := by
  exact machineNotBit_mem_FP machineFixedAColumnsEqualBit_mem_FP

theorem machineFixedAFourCoreInput_mem_FP :
    machineFixedAFourCoreInput ∈ FP := by
  have hsourceFirst := machineCompose_mem_FP machineFixedASource_mem_FP
    machineFixedAFirstRowRuler_mem_FP
  have hsourceSecond := machineCompose_mem_FP machineFixedASource_mem_FP
    machineFixedASecondRowRuler_mem_FP
  have hsourceA := machineCompose_mem_FP machineFixedASource_mem_FP
    machineFixedAFirstColumnRuler_mem_FP
  have hsourceOptimizer := machineCompose_mem_FP machineFixedASource_mem_FP
    machineFixedAOptimizerWord_mem_FP
  exact machinePair_mem_FP hsourceFirst
    (machinePair_mem_FP hsourceSecond
      (machinePair_mem_FP hsourceA
        (machinePair_mem_FP machineFixedACurrentSecondColumn_mem_FP
          hsourceOptimizer)))

theorem machineFixedAFourCoreRawCode_mem_FP :
    machineFixedAFourCoreRawCode ∈ FP := by
  simpa only [machineFixedAFourCoreRawCode] using! machineCompose_mem_FP
    machineFixedAFourCoreInput_mem_FP
    machineDirectedFourCoreCostUpperRawCode_mem_FP

theorem machineFixedACostPassesBit_mem_FP :
    machineFixedACostPassesBit ∈ FP := by
  have hinput := machinePair_mem_FP machineFixedAFourCoreRawCode_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawExplicitKappa))
  simpa only [machineFixedACostPassesBit] using! machineCompose_mem_FP hinput
    machineRawRatLeBit_mem_FP

theorem machineFixedACandidateBit_mem_FP :
    machineFixedACandidateBit ∈ FP :=
  machineAndBit_mem_FP machineFixedAColumnsDistinctBit_mem_FP
    machineFixedACostPassesBit_mem_FP

theorem machineFixedAInputBound_mem_FP : machineFixedAInputBound ∈ FP :=
  machinePair_mem_FP id_mem_FP machineFixedAColumnRange_mem_FP

theorem machineFixedANextFound_mem_FP : machineFixedANextFound ∈ FP := by
  have hdata := machineOrBit_mem_FP machineFixedAFound_mem_FP
    machineFixedACandidateBit_mem_FP
  have hbound := machineCompose_mem_FP machineFixedASource_mem_FP
    machineFixedAInputBound_mem_FP
  simpa only [machineFixedANextFound] using! machineTake_mem_FP hbound hdata

theorem machineFixedAProcess_mem_FP : machineFixedAProcess ∈ FP := by
  have htail := machineCompose_mem_FP machineFixedARemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineFixedANextFound_mem_FP
      machineFixedASource_mem_FP)

theorem machineFixedAStep_mem_FP : machineFixedAStep ∈ FP := by
  simpa only [machineFixedAStep] using! machineIfEmpty_mem_FP
    machineFixedARemaining_mem_FP id_mem_FP machineFixedAProcess_mem_FP

theorem machineFixedAInit_mem_FP : machineFixedAInit ∈ FP :=
  machinePair_mem_FP machineFixedAColumnRange_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP)

theorem machineFixedAWidth_mem_FP : machineFixedAWidth ∈ FP := by
  exact machinePair_mem_FP machineFixedAInputBound_mem_FP
    (machinePair_mem_FP machineFixedAInputBound_mem_FP
      machineFixedAInputBound_mem_FP)

@[simp] theorem machineFixedARemaining_pack (remaining found source) :
    machineFixedARemaining (machineFixedAPack remaining found source) =
      remaining := by simp [machineFixedARemaining, machineFixedAPack]

@[simp] theorem machineFixedAFound_pack (remaining found source) :
    machineFixedAFound (machineFixedAPack remaining found source) = found := by
  simp [machineFixedAFound, machineFixedAPack]

@[simp] theorem machineFixedASource_pack (remaining found source) :
    machineFixedASource (machineFixedAPack remaining found source) = source := by
  simp [machineFixedASource, machineFixedAPack]

def MachineFixedAStateBound (word state : List Bool) : Prop :=
  let B := (machineFixedAInputBound word).length
  state = machineFixedAPack (machineFixedARemaining state)
      (machineFixedAFound state) (machineFixedASource state) ∧
    (machineFixedARemaining state).length ≤ B ∧
    (machineFixedAFound state).length ≤ B ∧
    machineFixedASource state = word

theorem machineFixedAInput_le_bound (word : List Bool) :
    word.length ≤ (machineFixedAInputBound word).length := by
  simpa only [machineFixedAInputBound, machinePairFirst_pair] using!
    machinePairFirst_length_le (pair word (machineFixedAColumnRange word))

theorem machineFixedARange_le_bound (word : List Bool) :
    (machineFixedAColumnRange word).length ≤
      (machineFixedAInputBound word).length := by
  simpa only [machineFixedAInputBound, machinePairSecond_pair] using!
    machinePairSecond_length_le (pair word (machineFixedAColumnRange word))

theorem machineFixedA_one_le_bound (word : List Bool) :
    1 ≤ (machineFixedAInputBound word).length := by
  simp only [machineFixedAInputBound, pair_length]
  omega

theorem machineFixedAInit_bound (word : List Bool) :
    MachineFixedAStateBound word (machineFixedAInit word) := by
  simp only [MachineFixedAStateBound, machineFixedAInit,
    machineFixedARemaining_pack, machineFixedAFound_pack,
    machineFixedASource_pack]
  exact ⟨trivial, machineFixedARange_le_bound word,
    machineFixedA_one_le_bound word, trivial⟩

theorem machineFixedAStep_bound {word state : List Bool}
    (hstate : MachineFixedAStateBound word state) :
    MachineFixedAStateBound word (machineFixedAStep state) := by
  rcases hstate with ⟨hpack, hremaining, hfound, hsource⟩
  by_cases hrem : machineFixedARemaining state = []
  · rw [machineFixedAStep, hrem, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hfound, hsource⟩
  · rw [machineFixedAStep]
    cases hcode : machineFixedARemaining state with
    | nil => exact False.elim (hrem hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineFixedAProcess]
        simp only [MachineFixedAStateBound, machineFixedARemaining_pack,
          machineFixedAFound_pack, machineFixedASource_pack]
        refine ⟨trivial, ?_, ?_, hsource⟩
        · exact (machinePairSecond_length_le
            (machineFixedARemaining state)).trans hremaining
        · simp only [machineFixedANextFound, List.length_take]
          rw [hsource]
          exact Nat.min_le_left _ _

theorem machineFixedAIterate_bound (word : List Bool) : ∀ k,
    MachineFixedAStateBound word
      ((machineFixedAStep)^[k] (machineFixedAInit word)) := by
  intro k
  induction k with
  | zero => exact machineFixedAInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineFixedAStep_bound ih

theorem machineFixedAIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineFixedADimensionRuler word).length) :
    ((machineFixedAStep)^[iterations] (machineFixedAInit word)).length ≤
      (machineFixedAWidth word).length := by
  have h := machineFixedAIterate_bound word iterations
  rcases h with ⟨hpack, hremaining, hfound, hsource⟩
  rw [hpack]
  simp only [machineFixedAPack, machineFixedAWidth, pair_length]
  have hsourceLength : (machineFixedASource
      ((machineFixedAStep)^[iterations] (machineFixedAInit word))).length ≤
      (machineFixedAInputBound word).length := by
    rw [hsource]
    exact machineFixedAInput_le_bound word
  omega

theorem machineFixedAFinalState_mem_FP : machineFixedAFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineFixedAStep_mem_FP
    machineFixedAInit_mem_FP machineFixedADimensionRuler_mem_FP
    machineFixedAWidth_mem_FP machineFixedAIterate_length_le_width

theorem machineFixedAEligibilityBit_mem_FP :
    machineFixedAEligibilityBit ∈ FP := by
  simpa only [machineFixedAEligibilityBit] using! machineCompose_mem_FP
    machineFixedAFinalState_mem_FP machineFixedAFound_mem_FP

/-! ## Exact inner-scan semantics -/

def fixedAMachineInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) : List Bool :=
  pair (finUnaryCode r)
    (pair (finUnaryCode s)
      (pair (finUnaryCode a) (rationalOptimizerOutputCode ⟨X, R, C⟩)))

def certifiedColumnPairTest {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s a b : Fin n) : Bool :=
  decide (a ≠ b ∧
    directedFourCoreCostUpper (explicitRegularizationScale n) X r s a b
      (directedPairCostPrecision n) ≤ explicitKappa)

@[simp] theorem machineFixedAColumnsDistinctBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) (found : Bool) (bs : List (Fin n)) :
    machineFixedAColumnsDistinctBit
        (machineFixedAPack (binaryListCode finUnaryCode (b :: bs)) [found]
          (fixedAMachineInput X R C r s a)) =
      [decide (a ≠ b)] := by
  rw [machineFixedAColumnsDistinctBit, machineFixedAColumnsEqualBit]
  simp only [machineFixedASource_pack, machineFixedARemaining_pack,
    machineFixedACurrentSecondColumn, machineListHead_cons,
    machineFixedAFirstColumnRuler, fixedAMachineInput,
    machineFixedARest₁, machineFixedARest₂,
    machinePairFirst_pair, machinePairSecond_pair,
    machineLengthBits_encode, finUnaryCode, List.length_replicate,
    machineBinaryNatEqBit_pair_natBits, machineNotBit_one]
  by_cases hval : a.1 = b.1
  · have hab : a = b := Fin.ext hval
    simp [hval, hab]
  · have hab : a ≠ b := fun h ↦ hval (congrArg Fin.val h)
    simp [hval, hab]

@[simp] theorem machineFixedAFourCoreRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) (found : Bool) (bs : List (Fin n)) :
    machineFixedAFourCoreRawCode
        (machineFixedAPack (binaryListCode finUnaryCode (b :: bs)) [found]
          (fixedAMachineInput X R C r s a)) =
      rawRatBinaryCode (rawDirectedFourCoreCostUpper X r s a b) := by
  simp [machineFixedAFourCoreRawCode, machineFixedAFourCoreInput,
    machineFixedASource, machineFixedARemaining,
    machineFixedACurrentSecondColumn, machineFixedAFirstRowRuler,
    machineFixedASecondRowRuler, machineFixedAFirstColumnRuler,
    machineFixedAOptimizerWord, machineFixedARest₁, machineFixedARest₂,
    machineFixedAPack, fixedAMachineInput]
  change machineDirectedFourCoreCostUpperRawCode
      (fourCoreMachineInput X R C r s a b) = _
  exact machineDirectedFourCoreCostUpperRawCode_encode X R C r s a b

@[simp] theorem machineFixedACostPassesBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) (found : Bool) (bs : List (Fin n)) :
    machineFixedACostPassesBit
        (machineFixedAPack (binaryListCode finUnaryCode (b :: bs)) [found]
          (fixedAMachineInput X R C r s a)) =
      [decide (directedFourCoreCostUpper (explicitRegularizationScale n) X
        r s a b (directedPairCostPrecision n) ≤ explicitKappa)] := by
  rw [machineFixedACostPassesBit,
    machineFixedAFourCoreRawCode_encode]
  change machineRawRatLeBit
      (pair (rawRatBinaryCode (rawDirectedFourCoreCostUpper X r s a b))
        (rawRatBinaryCode rawExplicitKappa)) = _
  rw [machineRawRatLeBit_encode, rawDirectedFourCoreCostUpper_value]
  simp only [rawExplicitKappa, rawRatOfRat_value]

@[simp] theorem machineFixedADimensionRuler_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) :
    machineFixedADimensionRuler (fixedAMachineInput X R C r s a) =
      List.replicate n true := by
  simp [machineFixedADimensionRuler, fixedAMachineInput,
    machineFixedAOptimizerWord, machineFixedARest₁, machineFixedARest₂]

@[simp] theorem machineFixedAColumnRange_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) :
    machineFixedAColumnRange (fixedAMachineInput X R C r s a) =
      finRangeUnaryCode n := by
  rw [machineFixedAColumnRange, machineFixedADimensionRuler_encode,
    machineUnaryRangeCode_encode]

@[simp] theorem machineFixedACandidateBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) (found : Bool) (bs : List (Fin n)) :
    machineFixedACandidateBit
        (machineFixedAPack (binaryListCode finUnaryCode (b :: bs)) [found]
          (fixedAMachineInput X R C r s a)) =
      [certifiedColumnPairTest X r s a b] := by
  rw [machineFixedACandidateBit, machineFixedAColumnsDistinctBit_encode,
    machineFixedACostPassesBit_encode, machineAndBit_one]
  simp only [certifiedColumnPairTest]
  by_cases hdistinct : a ≠ b <;>
    by_cases hcost : directedFourCoreCostUpper (explicitRegularizationScale n)
      X r s a b (directedPairCostPrecision n) ≤ explicitKappa <;>
      simp [hdistinct, hcost]

def fixedAScanFound {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s a : Fin n) (k : ℕ) : Bool :=
  ((List.finRange n).take k).any (certifiedColumnPairTest X r s a)

def machineFixedASemanticState {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) (k : ℕ) : List Bool :=
  machineFixedAPack
    (binaryListCode finUnaryCode ((List.finRange n).drop k))
    [fixedAScanFound X r s a k] (fixedAMachineInput X R C r s a)

@[simp] theorem machineFixedASemanticState_zero {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) :
    machineFixedASemanticState X R C r s a 0 =
      machineFixedAInit (fixedAMachineInput X R C r s a) := by
  simp [machineFixedASemanticState, machineFixedAInit, fixedAScanFound,
    machineFixedAColumnRange_encode, finRangeUnaryCode]

theorem machineFixedASemanticState_step {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) (k : ℕ) (hk : k < n) :
    machineFixedAStep (machineFixedASemanticState X R C r s a k) =
      machineFixedASemanticState X R C r s a (k + 1) := by
  have hklen : k < (List.finRange n).length := by simpa using! hk
  rw [machineFixedASemanticState,
    List.drop_eq_getElem_cons hklen]
  rw [machineFixedAStep]
  simp only [machineFixedARemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil finUnaryCode (List.finRange n)[k]
      ((List.finRange n).drop (k + 1)))]
  rw [machineFixedAProcess]
  simp only [machineFixedARemaining_pack, machineListTail_cons,
    machineFixedASource_pack, machineFixedANextFound,
    machineFixedAFound_pack, machineFixedACandidateBit_encode,
    machineOrBit_one]
  have hbound : 1 ≤
      (machineFixedAInputBound (fixedAMachineInput X R C r s a)).length :=
    machineFixedA_one_le_bound _
  rw [(List.take_eq_self_iff _).2 (by simpa using! hbound)]
  rw [machineFixedASemanticState]
  apply congrArg (fun z : Bool ↦
    machineFixedAPack
      (binaryListCode finUnaryCode ((List.finRange n).drop (k + 1))) [z]
      (fixedAMachineInput X R C r s a))
  rw [fixedAScanFound, fixedAScanFound,
    ← List.take_concat_get hklen, List.concat_eq_append, List.any_append]
  simp

theorem machineFixedAIterate_semantics {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) (k : ℕ) (hk : k ≤ n) :
    (machineFixedAStep)^[k] (machineFixedAInit
        (fixedAMachineInput X R C r s a)) =
      machineFixedASemanticState X R C r s a k := by
  induction k with
  | zero => exact (machineFixedASemanticState_zero X R C r s a).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega),
        machineFixedASemanticState_step X R C r s a k (by omega)]

@[simp] theorem machineFixedAEligibilityBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) :
    machineFixedAEligibilityBit (fixedAMachineInput X R C r s a) =
      [(List.finRange n).any (certifiedColumnPairTest X r s a)] := by
  rw [machineFixedAEligibilityBit, machineFixedAFinalState,
    machineFixedADimensionRuler_encode, List.length_replicate,
    machineFixedAIterate_semantics X R C r s a n le_rfl,
    machineFixedASemanticState, machineFixedAFound_pack, fixedAScanFound]
  rw [(List.take_eq_self_iff _).2 (by simp)]

/-! ## The outer scan: first columns for a fixed row pair -/

def machineRowPairFirstRowRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRowPairRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRowPairSecondRowRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineRowPairRest word)

def machineRowPairOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond (machineRowPairRest word)

def machineRowPairDimensionRuler (word : List Bool) : List Bool :=
  machineCertificateDimensionUnary (machineRowPairOptimizerWord word)

def machineRowPairColumnRange (word : List Bool) : List Bool :=
  machineUnaryRangeCode (machineRowPairDimensionRuler word)

def machineRowPairScanPack
    (remaining found source : List Bool) : List Bool :=
  pair remaining (pair found source)

def machineRowPairScanRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRowPairScanFound (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRowPairScanSource (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineRowPairCurrentFirstColumn (state : List Bool) : List Bool :=
  machineListHead (machineRowPairScanRemaining state)

def machineRowPairFixedAInput (state : List Bool) : List Bool :=
  pair (machineRowPairFirstRowRuler (machineRowPairScanSource state))
    (pair (machineRowPairSecondRowRuler (machineRowPairScanSource state))
      (pair (machineRowPairCurrentFirstColumn state)
        (machineRowPairOptimizerWord (machineRowPairScanSource state))))

def machineRowPairCandidateBit (state : List Bool) : List Bool :=
  machineFixedAEligibilityBit (machineRowPairFixedAInput state)

def machineRowPairInputBound (word : List Bool) : List Bool :=
  pair word (machineRowPairColumnRange word)

def machineRowPairNextFound (state : List Bool) : List Bool :=
  (machineOrBit (machineRowPairScanFound state)
      (machineRowPairCandidateBit state)).take
    (machineRowPairInputBound (machineRowPairScanSource state)).length

def machineRowPairProcess (state : List Bool) : List Bool :=
  machineRowPairScanPack
    (machineListTail (machineRowPairScanRemaining state))
    (machineRowPairNextFound state) (machineRowPairScanSource state)

def machineRowPairScanStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRowPairScanRemaining state) state
    (machineRowPairProcess state)

def machineRowPairScanInit (word : List Bool) : List Bool :=
  machineRowPairScanPack (machineRowPairColumnRange word) [false] word

def machineRowPairScanWidth (word : List Bool) : List Bool :=
  let bound := machineRowPairInputBound word
  machineRowPairScanPack bound bound bound

def machineRowPairScanFinalState (word : List Bool) : List Bool :=
  (machineRowPairScanStep)^[(machineRowPairDimensionRuler word).length]
    (machineRowPairScanInit word)

/-- One-bit result of the complete existential column-pair scan. -/
def machineCertifiedRowPairEligibilityBit (word : List Bool) : List Bool :=
  machineRowPairScanFound (machineRowPairScanFinalState word)

theorem machineRowPairFirstRowRuler_mem_FP :
    machineRowPairFirstRowRuler ∈ FP := machinePairFirst_mem_FP

theorem machineRowPairRest_mem_FP : machineRowPairRest ∈ FP :=
  machinePairSecond_mem_FP

theorem machineRowPairSecondRowRuler_mem_FP :
    machineRowPairSecondRowRuler ∈ FP := by
  simpa only [machineRowPairSecondRowRuler] using! machineCompose_mem_FP
    machineRowPairRest_mem_FP machinePairFirst_mem_FP

theorem machineRowPairOptimizerWord_mem_FP :
    machineRowPairOptimizerWord ∈ FP := by
  simpa only [machineRowPairOptimizerWord] using! machineCompose_mem_FP
    machineRowPairRest_mem_FP machinePairSecond_mem_FP

theorem machineRowPairDimensionRuler_mem_FP :
    machineRowPairDimensionRuler ∈ FP := by
  simpa only [machineRowPairDimensionRuler] using! machineCompose_mem_FP
    machineRowPairOptimizerWord_mem_FP machineCertificateDimensionUnary_mem_FP

theorem machineRowPairColumnRange_mem_FP : machineRowPairColumnRange ∈ FP := by
  simpa only [machineRowPairColumnRange] using! machineCompose_mem_FP
    machineRowPairDimensionRuler_mem_FP machineUnaryRangeCode_mem_FP

theorem machineRowPairScanRemaining_mem_FP :
    machineRowPairScanRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineRowPairScanFound_mem_FP : machineRowPairScanFound ∈ FP := by
  simpa only [machineRowPairScanFound] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRowPairScanSource_mem_FP : machineRowPairScanSource ∈ FP := by
  simpa only [machineRowPairScanSource] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineRowPairCurrentFirstColumn_mem_FP :
    machineRowPairCurrentFirstColumn ∈ FP := by
  simpa only [machineRowPairCurrentFirstColumn] using! machineCompose_mem_FP
    machineRowPairScanRemaining_mem_FP machineListHead_mem_FP

theorem machineRowPairFixedAInput_mem_FP :
    machineRowPairFixedAInput ∈ FP := by
  have hfirst := machineCompose_mem_FP machineRowPairScanSource_mem_FP
    machineRowPairFirstRowRuler_mem_FP
  have hsecond := machineCompose_mem_FP machineRowPairScanSource_mem_FP
    machineRowPairSecondRowRuler_mem_FP
  have hoptimizer := machineCompose_mem_FP machineRowPairScanSource_mem_FP
    machineRowPairOptimizerWord_mem_FP
  exact machinePair_mem_FP hfirst
    (machinePair_mem_FP hsecond
      (machinePair_mem_FP machineRowPairCurrentFirstColumn_mem_FP hoptimizer))

theorem machineRowPairCandidateBit_mem_FP :
    machineRowPairCandidateBit ∈ FP := by
  simpa only [machineRowPairCandidateBit] using! machineCompose_mem_FP
    machineRowPairFixedAInput_mem_FP machineFixedAEligibilityBit_mem_FP

theorem machineRowPairInputBound_mem_FP : machineRowPairInputBound ∈ FP :=
  machinePair_mem_FP id_mem_FP machineRowPairColumnRange_mem_FP

theorem machineRowPairNextFound_mem_FP : machineRowPairNextFound ∈ FP := by
  have hdata := machineOrBit_mem_FP machineRowPairScanFound_mem_FP
    machineRowPairCandidateBit_mem_FP
  have hbound := machineCompose_mem_FP machineRowPairScanSource_mem_FP
    machineRowPairInputBound_mem_FP
  simpa only [machineRowPairNextFound] using! machineTake_mem_FP hbound hdata

theorem machineRowPairProcess_mem_FP : machineRowPairProcess ∈ FP := by
  have htail := machineCompose_mem_FP machineRowPairScanRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRowPairNextFound_mem_FP
      machineRowPairScanSource_mem_FP)

theorem machineRowPairScanStep_mem_FP : machineRowPairScanStep ∈ FP := by
  simpa only [machineRowPairScanStep] using! machineIfEmpty_mem_FP
    machineRowPairScanRemaining_mem_FP id_mem_FP machineRowPairProcess_mem_FP

theorem machineRowPairScanInit_mem_FP : machineRowPairScanInit ∈ FP :=
  machinePair_mem_FP machineRowPairColumnRange_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP)

theorem machineRowPairScanWidth_mem_FP : machineRowPairScanWidth ∈ FP :=
  machinePair_mem_FP machineRowPairInputBound_mem_FP
    (machinePair_mem_FP machineRowPairInputBound_mem_FP
      machineRowPairInputBound_mem_FP)

@[simp] theorem machineRowPairScanRemaining_pack (remaining found source) :
    machineRowPairScanRemaining
        (machineRowPairScanPack remaining found source) = remaining := by
  simp [machineRowPairScanRemaining, machineRowPairScanPack]

@[simp] theorem machineRowPairScanFound_pack (remaining found source) :
    machineRowPairScanFound
        (machineRowPairScanPack remaining found source) = found := by
  simp [machineRowPairScanFound, machineRowPairScanPack]

@[simp] theorem machineRowPairScanSource_pack (remaining found source) :
    machineRowPairScanSource
        (machineRowPairScanPack remaining found source) = source := by
  simp [machineRowPairScanSource, machineRowPairScanPack]

def MachineRowPairScanStateBound (word state : List Bool) : Prop :=
  let B := (machineRowPairInputBound word).length
  state = machineRowPairScanPack (machineRowPairScanRemaining state)
      (machineRowPairScanFound state) (machineRowPairScanSource state) ∧
    (machineRowPairScanRemaining state).length ≤ B ∧
    (machineRowPairScanFound state).length ≤ B ∧
    machineRowPairScanSource state = word

theorem machineRowPairInput_le_bound (word : List Bool) :
    word.length ≤ (machineRowPairInputBound word).length := by
  simpa only [machineRowPairInputBound, machinePairFirst_pair] using!
    machinePairFirst_length_le (pair word (machineRowPairColumnRange word))

theorem machineRowPairRange_le_bound (word : List Bool) :
    (machineRowPairColumnRange word).length ≤
      (machineRowPairInputBound word).length := by
  simpa only [machineRowPairInputBound, machinePairSecond_pair] using!
    machinePairSecond_length_le (pair word (machineRowPairColumnRange word))

theorem machineRowPair_one_le_bound (word : List Bool) :
    1 ≤ (machineRowPairInputBound word).length := by
  simp only [machineRowPairInputBound, pair_length]
  omega

theorem machineRowPairScanInit_bound (word : List Bool) :
    MachineRowPairScanStateBound word (machineRowPairScanInit word) := by
  simp only [MachineRowPairScanStateBound, machineRowPairScanInit,
    machineRowPairScanRemaining_pack, machineRowPairScanFound_pack,
    machineRowPairScanSource_pack]
  exact ⟨trivial, machineRowPairRange_le_bound word,
    machineRowPair_one_le_bound word, trivial⟩

theorem machineRowPairScanStep_bound {word state : List Bool}
    (hstate : MachineRowPairScanStateBound word state) :
    MachineRowPairScanStateBound word (machineRowPairScanStep state) := by
  rcases hstate with ⟨hpack, hremaining, hfound, hsource⟩
  by_cases hrem : machineRowPairScanRemaining state = []
  · rw [machineRowPairScanStep, hrem, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hfound, hsource⟩
  · rw [machineRowPairScanStep]
    cases hcode : machineRowPairScanRemaining state with
    | nil => exact False.elim (hrem hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineRowPairProcess]
        simp only [MachineRowPairScanStateBound,
          machineRowPairScanRemaining_pack, machineRowPairScanFound_pack,
          machineRowPairScanSource_pack]
        refine ⟨trivial, ?_, ?_, hsource⟩
        · exact (machinePairSecond_length_le
            (machineRowPairScanRemaining state)).trans hremaining
        · simp only [machineRowPairNextFound, List.length_take]
          rw [hsource]
          exact Nat.min_le_left _ _

theorem machineRowPairScanIterate_bound (word : List Bool) : ∀ k,
    MachineRowPairScanStateBound word
      ((machineRowPairScanStep)^[k] (machineRowPairScanInit word)) := by
  intro k
  induction k with
  | zero => exact machineRowPairScanInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRowPairScanStep_bound ih

theorem machineRowPairScanIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineRowPairDimensionRuler word).length) :
    ((machineRowPairScanStep)^[iterations]
        (machineRowPairScanInit word)).length ≤
      (machineRowPairScanWidth word).length := by
  have h := machineRowPairScanIterate_bound word iterations
  rcases h with ⟨hpack, hremaining, hfound, hsource⟩
  have hsourceLength : (machineRowPairScanSource
      ((machineRowPairScanStep)^[iterations]
        (machineRowPairScanInit word))).length ≤
      (machineRowPairInputBound word).length := by
    rw [hsource]
    exact machineRowPairInput_le_bound word
  rw [hpack]
  simp only [machineRowPairScanPack, machineRowPairScanWidth, pair_length]
  omega

theorem machineRowPairScanFinalState_mem_FP :
    machineRowPairScanFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRowPairScanStep_mem_FP
    machineRowPairScanInit_mem_FP machineRowPairDimensionRuler_mem_FP
    machineRowPairScanWidth_mem_FP
    machineRowPairScanIterate_length_le_width

theorem machineCertifiedRowPairEligibilityBit_mem_FP :
    machineCertifiedRowPairEligibilityBit ∈ FP := by
  simpa only [machineCertifiedRowPairEligibilityBit] using!
    machineCompose_mem_FP machineRowPairScanFinalState_mem_FP
      machineRowPairScanFound_mem_FP

/-! ## Exact outer-scan semantics -/

def certifiedRowPairMachineInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) : List Bool :=
  pair (finUnaryCode r)
    (pair (finUnaryCode s) (rationalOptimizerOutputCode ⟨X, R, C⟩))

def certifiedFirstColumnTest {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s a : Fin n) : Bool :=
  (List.finRange n).any (certifiedColumnPairTest X r s a)

def certifiedRowPairEligibilityTest {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s : Fin n) : Bool :=
  (List.finRange n).any (certifiedFirstColumnTest X r s)

@[simp] theorem machineRowPairDimensionRuler_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) :
    machineRowPairDimensionRuler (certifiedRowPairMachineInput X R C r s) =
      List.replicate n true := by
  simp [machineRowPairDimensionRuler, machineRowPairOptimizerWord,
    machineRowPairRest, certifiedRowPairMachineInput]

@[simp] theorem machineRowPairColumnRange_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) :
    machineRowPairColumnRange (certifiedRowPairMachineInput X R C r s) =
      finRangeUnaryCode n := by
  rw [machineRowPairColumnRange, machineRowPairDimensionRuler_encode,
    machineUnaryRangeCode_encode]

@[simp] theorem machineRowPairCandidateBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a : Fin n) (found : Bool) (as : List (Fin n)) :
    machineRowPairCandidateBit
        (machineRowPairScanPack
          (binaryListCode finUnaryCode (a :: as)) [found]
          (certifiedRowPairMachineInput X R C r s)) =
      [certifiedFirstColumnTest X r s a] := by
  simp [machineRowPairCandidateBit, machineRowPairFixedAInput,
    machineRowPairScanSource, machineRowPairScanRemaining,
    machineRowPairCurrentFirstColumn, machineRowPairFirstRowRuler,
    machineRowPairSecondRowRuler, machineRowPairOptimizerWord,
    machineRowPairRest, machineRowPairScanPack,
    certifiedRowPairMachineInput,
    certifiedFirstColumnTest]
  change machineFixedAEligibilityBit (fixedAMachineInput X R C r s a) = _
  exact machineFixedAEligibilityBit_encode X R C r s a

def outerScanFound {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s : Fin n) (k : ℕ) : Bool :=
  ((List.finRange n).take k).any (certifiedFirstColumnTest X r s)

def machineRowPairSemanticState {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) (k : ℕ) : List Bool :=
  machineRowPairScanPack
    (binaryListCode finUnaryCode ((List.finRange n).drop k))
    [outerScanFound X r s k] (certifiedRowPairMachineInput X R C r s)

@[simp] theorem machineRowPairSemanticState_zero {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) :
    machineRowPairSemanticState X R C r s 0 =
      machineRowPairScanInit (certifiedRowPairMachineInput X R C r s) := by
  simp [machineRowPairSemanticState, machineRowPairScanInit, outerScanFound,
    machineRowPairColumnRange_encode, finRangeUnaryCode]

theorem machineRowPairSemanticState_step {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) (k : ℕ) (hk : k < n) :
    machineRowPairScanStep (machineRowPairSemanticState X R C r s k) =
      machineRowPairSemanticState X R C r s (k + 1) := by
  have hklen : k < (List.finRange n).length := by simpa using! hk
  rw [machineRowPairSemanticState, List.drop_eq_getElem_cons hklen,
    machineRowPairScanStep]
  simp only [machineRowPairScanRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil finUnaryCode (List.finRange n)[k]
      ((List.finRange n).drop (k + 1)))]
  rw [machineRowPairProcess]
  simp only [machineRowPairScanRemaining_pack, machineListTail_cons,
    machineRowPairScanSource_pack, machineRowPairNextFound,
    machineRowPairScanFound_pack, machineRowPairCandidateBit_encode,
    machineOrBit_one]
  have hbound : 1 ≤ (machineRowPairInputBound
      (certifiedRowPairMachineInput X R C r s)).length :=
    machineRowPair_one_le_bound _
  rw [(List.take_eq_self_iff _).2 (by simpa using! hbound),
    machineRowPairSemanticState]
  apply congrArg (fun z : Bool ↦
    machineRowPairScanPack
      (binaryListCode finUnaryCode ((List.finRange n).drop (k + 1))) [z]
      (certifiedRowPairMachineInput X R C r s))
  rw [outerScanFound, outerScanFound,
    ← List.take_concat_get hklen, List.concat_eq_append, List.any_append]
  simp

theorem machineRowPairScanIterate_semantics {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) (k : ℕ) (hk : k ≤ n) :
    (machineRowPairScanStep)^[k] (machineRowPairScanInit
        (certifiedRowPairMachineInput X R C r s)) =
      machineRowPairSemanticState X R C r s k := by
  induction k with
  | zero => exact (machineRowPairSemanticState_zero X R C r s).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega),
        machineRowPairSemanticState_step X R C r s k (by omega)]

@[simp] theorem machineCertifiedRowPairEligibilityBit_rows_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s : Fin n) :
    machineCertifiedRowPairEligibilityBit
        (certifiedRowPairMachineInput X R C r s) =
      [certifiedRowPairEligibilityTest X r s] := by
  rw [machineCertifiedRowPairEligibilityBit, machineRowPairScanFinalState,
    machineRowPairDimensionRuler_encode, List.length_replicate,
    machineRowPairScanIterate_semantics X R C r s n le_rfl,
    machineRowPairSemanticState, machineRowPairScanFound_pack, outerScanFound,
    (List.take_eq_self_iff _).2 (by simp)]
  rfl

theorem certifiedRowPairEligibilityTest_eq_true_iff {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s : Fin n) :
    certifiedRowPairEligibilityTest X r s = true ↔
      ∃ a b : Fin n, a ≠ b ∧
        directedFourCoreCostUpper (explicitRegularizationScale n) X r s a b
          (directedPairCostPrecision n) ≤ explicitKappa := by
  rw [certifiedRowPairEligibilityTest, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hinner⟩
    rw [certifiedFirstColumnTest, List.any_eq_true] at hinner
    obtain ⟨b, hb, htest⟩ := hinner
    refine ⟨a, b, ?_⟩
    simpa only [certifiedColumnPairTest, decide_eq_true_eq] using! htest
  · rintro ⟨a, b, hab, hcost⟩
    refine ⟨a, by simp, ?_⟩
    rw [certifiedFirstColumnTest, List.any_eq_true]
    refine ⟨b, by simp, ?_⟩
    simp [certifiedColumnPairTest, hab, hcost]

def certifiedRowPairEligibilityMachineInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (q : RowPair n) : List Bool :=
  certifiedRowPairMachineInput X R C (rowPairRow q 0) (rowPairRow q 1)

@[simp] theorem machineCertifiedRowPairEligibilityBit_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (q : RowPair n) :
    machineCertifiedRowPairEligibilityBit
        (certifiedRowPairEligibilityMachineInput X R C q) =
      [decide (HasCertifiedCorePair (explicitRegularizationScale n) X
        explicitKappa (directedPairCostPrecision n) q)] := by
  rw [certifiedRowPairEligibilityMachineInput,
    machineCertifiedRowPairEligibilityBit_rows_encode]
  apply congrArg List.singleton
  apply (Bool.eq_iff_iff).2
  rw [certifiedRowPairEligibilityTest_eq_true_iff, decide_eq_true_eq]
  rfl

end BeyondBethe

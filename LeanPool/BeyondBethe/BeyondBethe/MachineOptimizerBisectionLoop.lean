/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerFeasibilityCall
public import LeanPool.BeyondBethe.BeyondBethe.ScannedBetheBisection
public import Mathlib.Tactic

/-!
# A finite-word dyadic bisection loop for the Bethe optimizer

Rather than storing two rational endpoints whose concrete representations
change at every step, the machine stores a natural interval index `k` and a
unary depth `t`.  They represent the adjacent dyadic endpoints

`L + k (H - L) / 2^t` and `L + (k + 1) (H - L) / 2^t`.

An exhausted midpoint appends a one bit to the branch index; an accepted
midpoint appends a zero bit.  Consequently the persistent state grows by at
most one bit in each of its two mutable fields.  This gives a direct global
polynomial state envelope for the bounded iteration.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Exact dyadic thresholds -/

/-- The raw-rational initial lower objective bound `-2*n^2`. -/
def rawOptimizerInitialLow (n : ℕ) : RawRat :=
  (rawOptimizerTwiceNSquare n).neg

/-- The threshold at dyadic position `k/2^t` within the initial objective interval. -/
def optimizerDyadicThreshold {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (k t : ℕ) : ℚ :=
  betheNegativeObjectiveLower m +
    (k : ℚ) / 2 ^ t * explicitOptimizerInitialWidth A

/-- Normalizes the encoded initial lower objective bound `-2*n^2`. -/
def machineOptimizerInitialLowEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRawRatNegCode
      (machineOptimizerTwiceNSquareForWidthRawCode word))

/-- Normalizes the initial interval width for use in the bisection loop. -/
def machineOptimizerInitialWidthEntryCodeForBisection
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineExplicitOptimizerInitialWidthRawCode word)

/-! ## Persistent state -/

/-- Encodes a bisection state as source matrix, iteration ruler, binary index, and unary depth. -/
def machineOptimizerBisectionStatePack
    (source ruler index depth : List Bool) : List Bool :=
  pair source (pair ruler (pair index depth))

/-- Extracts the source matrix from the bisection state. -/
def machineOptimizerBisectionStateSource
    (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the fixed bisection-iteration ruler from the state. -/
def machineOptimizerBisectionStateRuler
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the binary index of the current dyadic interval. -/
def machineOptimizerBisectionStateIndex
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the unary depth of the current dyadic interval. -/
def machineOptimizerBisectionStateDepth
    (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

/-- Initializes bisection with the source matrix, scheduled ruler, and zero index and depth. -/
def machineOptimizerBisectionInit (word : List Bool) : List Bool :=
  machineOptimizerBisectionStatePack word
    (machineExplicitOptimizerBisectionStepsRuler word) [] []

/-! ## Reconstruct the queried midpoint -/

/-- Doubles the current dyadic interval index in binary. -/
def machineOptimizerBisectionEvenIndexBits
    (state : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerBisectionStateIndex state) [false, true])

/-- Computes the odd midpoint index `2*k + 1` in binary. -/
def machineOptimizerBisectionOddIndexBits
    (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineOptimizerBisectionEvenIndexBits state) [true])

/-- Increments the unary bisection depth. -/
def machineOptimizerBisectionNextDepth
    (state : List Bool) : List Bool :=
  true :: machineOptimizerBisectionStateDepth state

/-- Computes the binary denominator `2^(t + 1)` for the next midpoint. -/
def machineOptimizerBisectionDenominatorBits
    (state : List Bool) : List Bool :=
  machineDirectedLogPowerTwoBits
    (machineOptimizerBisectionNextDepth state)

/-- Encodes the raw dyadic midpoint fraction `(2*k + 1)/2^(t + 1)`. -/
def machineOptimizerBisectionFractionRawCode
    (state : List Bool) : List Bool :=
  pair
    (machineNaturalIntegerCode
      (machineOptimizerBisectionOddIndexBits state))
    (machineOptimizerBisectionDenominatorBits state)

/-- Multiplies the dyadic midpoint fraction by the initial objective-interval width. -/
def machineOptimizerBisectionScaledFractionRawCode
    (state : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerBisectionFractionRawCode state)
      (machineOptimizerInitialWidthEntryCodeForBisection
        (machineOptimizerBisectionStateSource state)))

/-- Adds the initial lower objective bound to the scaled midpoint fraction. -/
def machineOptimizerBisectionMidpointUnnormalizedRawCode
    (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair
      (machineOptimizerInitialLowEntryCode
        (machineOptimizerBisectionStateSource state))
      (machineOptimizerBisectionScaledFractionRawCode state))

/-- Normalizes the encoded midpoint threshold. -/
def machineOptimizerBisectionMidpointRawCode
    (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineOptimizerBisectionMidpointUnnormalizedRawCode state)

/-- Pairs the source matrix with the current midpoint threshold for a feasibility query. -/
def machineOptimizerBisectionFeasibilityCall
    (state : List Bool) : List Bool :=
  pair (machineOptimizerBisectionStateSource state)
    (machineOptimizerBisectionMidpointRawCode state)

/-- Runs the explicit threshold-feasibility machine at the current bisection midpoint. -/
def machineOptimizerBisectionFeasibilityResult
    (state : List Bool) : List Bool :=
  machineExplicitBetheThresholdFeasibilityCode
    (machineOptimizerBisectionFeasibilityCall state)

/-- Reads the exhausted flag from the midpoint feasibility result. -/
def machineOptimizerBisectionExhaustedBit
    (state : List Bool) : List Bool :=
  machineHeadBit
    (machinePairFirst
      (machineOptimizerBisectionFeasibilityResult state))

/-! ## One branch and the bounded iteration -/

/-- Chooses index `2*k + 1` on exhaustion and `2*k` on acceptance. -/
def machineOptimizerBisectionNextIndexBits
    (state : List Bool) : List Bool :=
  machineIfHead (machineOptimizerBisectionExhaustedBit state)
    (machineOptimizerBisectionOddIndexBits state)
    (machineOptimizerBisectionEvenIndexBits state)

/-- Updates the dyadic interval index and depth while preserving the source and iteration ruler. -/
def machineOptimizerBisectionStep (state : List Bool) : List Bool :=
  machineOptimizerBisectionStatePack
    (machineOptimizerBisectionStateSource state)
    (machineOptimizerBisectionStateRuler state)
    (machineOptimizerBisectionNextIndexBits state)
    (machineOptimizerBisectionNextDepth state)

/-- Runs bisection for the scheduled number of iterations. -/
def machineOptimizerBisectionFinalState
    (word : List Bool) : List Bool :=
  (machineOptimizerBisectionStep)^[(
      machineExplicitOptimizerBisectionStepsRuler word).length]
    (machineOptimizerBisectionInit word)

/-! ## Re-query the certified upper endpoint -/

/-- Computes the upper endpoint index `k + 1` of the current dyadic interval. -/
def machineOptimizerBisectionHighIndexBits
    (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineOptimizerBisectionStateIndex state) [true])

/-- Encodes the current upper endpoint fraction `(k + 1)/2^t`. -/
def machineOptimizerBisectionHighFractionRawCode
    (state : List Bool) : List Bool :=
  pair
    (machineNaturalIntegerCode
      (machineOptimizerBisectionHighIndexBits state))
    (machineDirectedLogPowerTwoBits
      (machineOptimizerBisectionStateDepth state))

/-- Scales the upper endpoint fraction by the initial interval width. -/
def machineOptimizerBisectionHighScaledRawCode
    (state : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerBisectionHighFractionRawCode state)
      (machineOptimizerInitialWidthEntryCodeForBisection
        (machineOptimizerBisectionStateSource state)))

/-- Adds the initial lower bound to the scaled upper endpoint fraction. -/
def machineOptimizerBisectionHighUnnormalizedRawCode
    (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair
      (machineOptimizerInitialLowEntryCode
        (machineOptimizerBisectionStateSource state))
      (machineOptimizerBisectionHighScaledRawCode state))

/-- Normalizes the encoded upper endpoint threshold. -/
def machineOptimizerBisectionHighRawCode
    (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineOptimizerBisectionHighUnnormalizedRawCode state)

/-- Runs threshold feasibility once more at the final bisection interval's upper endpoint. -/
def machineExplicitBetheOptimizerFeasibilityResultCode
    (word : List Bool) : List Bool :=
  let state := machineOptimizerBisectionFinalState word
  machineExplicitBetheThresholdFeasibilityCode
    (pair word (machineOptimizerBisectionHighRawCode state))

/-- Extracts the point payload returned by the final optimizer feasibility call. -/
def machineExplicitBetheOptimizerPointCode
    (word : List Bool) : List Bool :=
  machinePairSecond
    (machineExplicitBetheOptimizerFeasibilityResultCode word)

/-! ## Polynomial-time closure -/

theorem machineOptimizerInitialLowEntryCode_mem_FP :
    machineOptimizerInitialLowEntryCode ∈ FP := by
  have hneg := machineCompose_mem_FP
    machineOptimizerTwiceNSquareForWidthRawCode_mem_FP
    machineRawRatNegCode_mem_FP
  simpa only [machineOptimizerInitialLowEntryCode] using!
    machineCompose_mem_FP hneg machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerInitialWidthEntryCodeForBisection_mem_FP :
    machineOptimizerInitialWidthEntryCodeForBisection ∈ FP := by
  simpa only [machineOptimizerInitialWidthEntryCodeForBisection] using!
    machineCompose_mem_FP machineExplicitOptimizerInitialWidthRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerBisectionStateSource_mem_FP :
    machineOptimizerBisectionStateSource ∈ FP := machinePairFirst_mem_FP

theorem machineOptimizerBisectionStateRuler_mem_FP :
    machineOptimizerBisectionStateRuler ∈ FP := by
  simpa only [machineOptimizerBisectionStateRuler] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineOptimizerBisectionStateIndex_mem_FP :
    machineOptimizerBisectionStateIndex ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineOptimizerBisectionStateIndex] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineOptimizerBisectionStateDepth_mem_FP :
    machineOptimizerBisectionStateDepth ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineOptimizerBisectionStateDepth] using!
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineOptimizerBisectionInit_mem_FP :
    machineOptimizerBisectionInit ∈ FP := by
  simpa only [machineOptimizerBisectionInit] using!
    machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP machineExplicitOptimizerBisectionStepsRuler_mem_FP
        (machinePair_mem_FP (machineConst_mem_FP [])
          (machineConst_mem_FP [])))

theorem machineOptimizerBisectionEvenIndexBits_mem_FP :
    machineOptimizerBisectionEvenIndexBits ∈ FP := by
  simpa only [machineOptimizerBisectionEvenIndexBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerBisectionStateIndex_mem_FP
        (machineConst_mem_FP [false, true]))
      machineBinaryMulBits_mem_FP

theorem machineOptimizerBisectionOddIndexBits_mem_FP :
    machineOptimizerBisectionOddIndexBits ∈ FP := by
  simpa only [machineOptimizerBisectionOddIndexBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerBisectionEvenIndexBits_mem_FP
        (machineConst_mem_FP [true]))
      machineBinaryAddBits_mem_FP

theorem machineOptimizerBisectionNextDepth_mem_FP :
    machineOptimizerBisectionNextDepth ∈ FP := by
  simpa only [machineOptimizerBisectionNextDepth] using!
    machineCompose_mem_FP machineOptimizerBisectionStateDepth_mem_FP
      (machinePrepend_mem_FP true)

theorem machineOptimizerBisectionDenominatorBits_mem_FP :
    machineOptimizerBisectionDenominatorBits ∈ FP := by
  simpa only [machineOptimizerBisectionDenominatorBits] using!
    machineCompose_mem_FP machineOptimizerBisectionNextDepth_mem_FP
      machineDirectedLogPowerTwoBits_mem_FP

theorem machineOptimizerBisectionFractionRawCode_mem_FP :
    machineOptimizerBisectionFractionRawCode ∈ FP := by
  have hnum := machineCompose_mem_FP
    machineOptimizerBisectionOddIndexBits_mem_FP
    machineNaturalIntegerCode_mem_FP
  exact machinePair_mem_FP hnum
    machineOptimizerBisectionDenominatorBits_mem_FP

theorem machineOptimizerBisectionScaledFractionRawCode_mem_FP :
    machineOptimizerBisectionScaledFractionRawCode ∈ FP := by
  have hwidth := machineCompose_mem_FP
    machineOptimizerBisectionStateSource_mem_FP
    machineOptimizerInitialWidthEntryCodeForBisection_mem_FP
  simpa only [machineOptimizerBisectionScaledFractionRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerBisectionFractionRawCode_mem_FP hwidth)
      machineRawRatMulCode_mem_FP

theorem machineOptimizerBisectionMidpointUnnormalizedRawCode_mem_FP :
    machineOptimizerBisectionMidpointUnnormalizedRawCode ∈ FP := by
  have hlow := machineCompose_mem_FP
    machineOptimizerBisectionStateSource_mem_FP
    machineOptimizerInitialLowEntryCode_mem_FP
  simpa only [machineOptimizerBisectionMidpointUnnormalizedRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP hlow
        machineOptimizerBisectionScaledFractionRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerBisectionMidpointRawCode_mem_FP :
    machineOptimizerBisectionMidpointRawCode ∈ FP := by
  simpa only [machineOptimizerBisectionMidpointRawCode] using!
    machineCompose_mem_FP
      machineOptimizerBisectionMidpointUnnormalizedRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerBisectionFeasibilityCall_mem_FP :
    machineOptimizerBisectionFeasibilityCall ∈ FP :=
  machinePair_mem_FP machineOptimizerBisectionStateSource_mem_FP
    machineOptimizerBisectionMidpointRawCode_mem_FP

theorem machineOptimizerBisectionFeasibilityResult_mem_FP :
    machineOptimizerBisectionFeasibilityResult ∈ FP := by
  simpa only [machineOptimizerBisectionFeasibilityResult] using!
    machineCompose_mem_FP machineOptimizerBisectionFeasibilityCall_mem_FP
      machineExplicitBetheThresholdFeasibilityCode_mem_FP

theorem machineOptimizerBisectionExhaustedBit_mem_FP :
    machineOptimizerBisectionExhaustedBit ∈ FP := by
  have htag := machineCompose_mem_FP
    machineOptimizerBisectionFeasibilityResult_mem_FP
    machinePairFirst_mem_FP
  simpa only [machineOptimizerBisectionExhaustedBit] using!
    machineCompose_mem_FP htag machineHeadBit_mem_FP

theorem machineOptimizerBisectionNextIndexBits_mem_FP :
    machineOptimizerBisectionNextIndexBits ∈ FP := by
  exact machineIfHead_mem_FP machineOptimizerBisectionExhaustedBit_mem_FP
    machineOptimizerBisectionOddIndexBits_mem_FP
    machineOptimizerBisectionEvenIndexBits_mem_FP

theorem machineOptimizerBisectionStep_mem_FP :
    machineOptimizerBisectionStep ∈ FP := by
  exact machinePair_mem_FP machineOptimizerBisectionStateSource_mem_FP
    (machinePair_mem_FP machineOptimizerBisectionStateRuler_mem_FP
      (machinePair_mem_FP machineOptimizerBisectionNextIndexBits_mem_FP
        machineOptimizerBisectionNextDepth_mem_FP))

/-! ## A global state envelope for Cobham iteration -/

@[simp] theorem machineOptimizerBisectionStateSource_pack
    (source ruler index depth : List Bool) :
    machineOptimizerBisectionStateSource
        (machineOptimizerBisectionStatePack source ruler index depth) =
      source := by
  simp [machineOptimizerBisectionStateSource,
    machineOptimizerBisectionStatePack]

@[simp] theorem machineOptimizerBisectionStateRuler_pack
    (source ruler index depth : List Bool) :
    machineOptimizerBisectionStateRuler
        (machineOptimizerBisectionStatePack source ruler index depth) =
      ruler := by
  simp [machineOptimizerBisectionStateRuler,
    machineOptimizerBisectionStatePack]

@[simp] theorem machineOptimizerBisectionStateIndex_pack
    (source ruler index depth : List Bool) :
    machineOptimizerBisectionStateIndex
        (machineOptimizerBisectionStatePack source ruler index depth) =
      index := by
  simp [machineOptimizerBisectionStateIndex,
    machineOptimizerBisectionStatePack]

@[simp] theorem machineOptimizerBisectionStateDepth_pack
    (source ruler index depth : List Bool) :
    machineOptimizerBisectionStateDepth
        (machineOptimizerBisectionStatePack source ruler index depth) =
      depth := by
  simp [machineOptimizerBisectionStateDepth,
    machineOptimizerBisectionStatePack]

/-- Records canonical state packing, fixed source and ruler, index below `2^iterations`, and
matching depth. -/
def MachineOptimizerBisectionStateBound
    (word : List Bool) (iterations : ℕ) (state : List Bool) : Prop :=
  state = machineOptimizerBisectionStatePack
      (machineOptimizerBisectionStateSource state)
      (machineOptimizerBisectionStateRuler state)
      (machineOptimizerBisectionStateIndex state)
      (machineOptimizerBisectionStateDepth state) ∧
    machineOptimizerBisectionStateSource state = word ∧
    machineOptimizerBisectionStateRuler state =
      machineExplicitOptimizerBisectionStepsRuler word ∧
    (∃ k : ℕ,
      machineOptimizerBisectionStateIndex state = k.bits ∧
      k < 2 ^ iterations) ∧
    (machineOptimizerBisectionStateDepth state).length = iterations

theorem machineOptimizerBisectionInit_bound (word : List Bool) :
    MachineOptimizerBisectionStateBound word 0
      (machineOptimizerBisectionInit word) := by
  simp only [MachineOptimizerBisectionStateBound,
    machineOptimizerBisectionInit,
    machineOptimizerBisectionStateSource_pack,
    machineOptimizerBisectionStateRuler_pack,
    machineOptimizerBisectionStateIndex_pack,
    machineOptimizerBisectionStateDepth_pack, List.length_nil]
  exact ⟨trivial, trivial, trivial, ⟨0, rfl, by norm_num⟩, trivial⟩

theorem machineOptimizerBisectionStep_bound
    {word state : List Bool} {iterations : ℕ}
    (hs : MachineOptimizerBisectionStateBound word iterations state) :
    MachineOptimizerBisectionStateBound word (iterations + 1)
      (machineOptimizerBisectionStep state) := by
  rcases hs with ⟨hdecomp, hsource, hruler,
    ⟨k, hindex, hk⟩, hdepth⟩
  have heven : machineOptimizerBisectionEvenIndexBits state =
      (2 * k).bits := by
    rw [machineOptimizerBisectionEvenIndexBits, hindex]
    change machineBinaryMulBits (pair k.bits (2 : ℕ).bits) = _
    rw [machineBinaryMulBits_pair_natBits]
    congr 1
    omega
  have hodd : machineOptimizerBisectionOddIndexBits state =
      (2 * k + 1).bits := by
    rw [machineOptimizerBisectionOddIndexBits, heven]
    change machineBinaryAddBits (pair (2 * k).bits (1 : ℕ).bits) = _
    rw [machineBinaryAddBits_pair_natBits]
  simp only [machineOptimizerBisectionStep,
    MachineOptimizerBisectionStateBound,
    machineOptimizerBisectionStateSource_pack,
    machineOptimizerBisectionStateRuler_pack,
    machineOptimizerBisectionStateIndex_pack,
    machineOptimizerBisectionStateDepth_pack]
  refine ⟨by trivial, hsource, hruler, ?_, ?_⟩
  · rw [machineOptimizerBisectionNextIndexBits,
      machineOptimizerBisectionExhaustedBit]
    cases hflag : machinePairFirst
        (machineOptimizerBisectionFeasibilityResult state) with
    | nil =>
        rw [machineHeadBit_nil, machineIfHead_false]
        refine ⟨2 * k, heven, ?_⟩
        rw [pow_succ]
        omega
    | cons bit tail =>
        cases bit with
        | false =>
            rw [machineHeadBit_cons, machineIfHead_false]
            refine ⟨2 * k, heven, ?_⟩
            rw [pow_succ]
            omega
        | true =>
            rw [machineHeadBit_cons, machineIfHead_true]
            refine ⟨2 * k + 1, hodd, ?_⟩
            rw [pow_succ]
            omega
  · simp [machineOptimizerBisectionNextDepth, hdepth]

theorem machineOptimizerBisectionIterate_bound (word : List Bool) : ∀ k,
    MachineOptimizerBisectionStateBound word k
      ((machineOptimizerBisectionStep)^[k]
        (machineOptimizerBisectionInit word)) := by
  intro k
  induction k with
  | zero => exact machineOptimizerBisectionInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simpa only [Nat.succ_eq_add_one] using!
        machineOptimizerBisectionStep_bound ih

/-- Packs four copies of a source-and-ruler envelope to bound a bisection state. -/
def machineOptimizerBisectionWidth (word : List Bool) : List Bool :=
  let envelope := false ::
    (word ++ machineExplicitOptimizerBisectionStepsRuler word)
  machineOptimizerBisectionStatePack envelope envelope envelope envelope

theorem machineOptimizerBisectionWidth_mem_FP :
    machineOptimizerBisectionWidth ∈ FP := by
  have happend := machineAppend_mem_FP id_mem_FP
    machineExplicitOptimizerBisectionStepsRuler_mem_FP
  have henvelope : (fun word : List Bool ↦
      false :: (word ++ machineExplicitOptimizerBisectionStepsRuler word))
      ∈ FP := machineCompose_mem_FP happend (machinePrepend_mem_FP false)
  simpa only [machineOptimizerBisectionWidth] using!
    machinePair_mem_FP henvelope
      (machinePair_mem_FP henvelope
        (machinePair_mem_FP henvelope henvelope))

theorem machineOptimizerBisectionIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤
      (machineExplicitOptimizerBisectionStepsRuler word).length) :
    ((machineOptimizerBisectionStep)^[iterations]
      (machineOptimizerBisectionInit word)).length ≤
        (machineOptimizerBisectionWidth word).length := by
  rcases machineOptimizerBisectionIterate_bound word iterations with
    ⟨hdecomp, hsource, hruler, ⟨k, hindex, hk⟩, hdepth⟩
  have hkbits : k.bits.length ≤ iterations := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact hk
  rw [hdecomp]
  simp only [machineOptimizerBisectionStatePack,
    machineOptimizerBisectionWidth, pair_length, List.length_cons,
    List.length_append]
  rw [hsource, hruler, hindex, hdepth]
  omega

theorem machineOptimizerBisectionFinalState_mem_FP :
    machineOptimizerBisectionFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineOptimizerBisectionStep_mem_FP
    machineOptimizerBisectionInit_mem_FP
    machineExplicitOptimizerBisectionStepsRuler_mem_FP
    machineOptimizerBisectionWidth_mem_FP
    machineOptimizerBisectionIterate_length_le_width

/-! ## Polynomial-time closure of the final upper-endpoint query -/

theorem machineOptimizerBisectionHighIndexBits_mem_FP :
    machineOptimizerBisectionHighIndexBits ∈ FP := by
  simpa only [machineOptimizerBisectionHighIndexBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerBisectionStateIndex_mem_FP
        (machineConst_mem_FP [true]))
      machineBinaryAddBits_mem_FP

theorem machineOptimizerBisectionHighFractionRawCode_mem_FP :
    machineOptimizerBisectionHighFractionRawCode ∈ FP := by
  have hnum := machineCompose_mem_FP
    machineOptimizerBisectionHighIndexBits_mem_FP
    machineNaturalIntegerCode_mem_FP
  have hden := machineCompose_mem_FP
    machineOptimizerBisectionStateDepth_mem_FP
    machineDirectedLogPowerTwoBits_mem_FP
  exact machinePair_mem_FP hnum hden

theorem machineOptimizerBisectionHighScaledRawCode_mem_FP :
    machineOptimizerBisectionHighScaledRawCode ∈ FP := by
  have hwidth := machineCompose_mem_FP
    machineOptimizerBisectionStateSource_mem_FP
    machineOptimizerInitialWidthEntryCodeForBisection_mem_FP
  simpa only [machineOptimizerBisectionHighScaledRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerBisectionHighFractionRawCode_mem_FP hwidth)
      machineRawRatMulCode_mem_FP

theorem machineOptimizerBisectionHighUnnormalizedRawCode_mem_FP :
    machineOptimizerBisectionHighUnnormalizedRawCode ∈ FP := by
  have hlow := machineCompose_mem_FP
    machineOptimizerBisectionStateSource_mem_FP
    machineOptimizerInitialLowEntryCode_mem_FP
  simpa only [machineOptimizerBisectionHighUnnormalizedRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP hlow
        machineOptimizerBisectionHighScaledRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerBisectionHighRawCode_mem_FP :
    machineOptimizerBisectionHighRawCode ∈ FP := by
  simpa only [machineOptimizerBisectionHighRawCode] using!
    machineCompose_mem_FP
      machineOptimizerBisectionHighUnnormalizedRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineExplicitBetheOptimizerFeasibilityResultCode_mem_FP :
    machineExplicitBetheOptimizerFeasibilityResultCode ∈ FP := by
  have hhigh := machineCompose_mem_FP
    machineOptimizerBisectionFinalState_mem_FP
    machineOptimizerBisectionHighRawCode_mem_FP
  have hcall := machinePair_mem_FP id_mem_FP hhigh
  simpa only [machineExplicitBetheOptimizerFeasibilityResultCode] using!
    machineCompose_mem_FP hcall
      machineExplicitBetheThresholdFeasibilityCode_mem_FP

theorem machineExplicitBetheOptimizerPointCode_mem_FP :
    machineExplicitBetheOptimizerPointCode ∈ FP := by
  simpa only [machineExplicitBetheOptimizerPointCode] using!
    machineCompose_mem_FP
      machineExplicitBetheOptimizerFeasibilityResultCode_mem_FP
      machinePairSecond_mem_FP

end BeyondBethe

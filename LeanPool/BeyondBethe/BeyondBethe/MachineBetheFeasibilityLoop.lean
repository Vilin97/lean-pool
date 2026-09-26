/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheEpigraphOracle
public import LeanPool.BeyondBethe.BeyondBethe.MachineScheduledRoundedEllipsoid
public import LeanPool.BeyondBethe.BeyondBethe.ScannedBetheThresholdFeasibility
public import Mathlib.Tactic

/-!
# A finite-word fixed-precision Bethe feasibility loop

The loop stores the immutable call word beside the current ellipsoid.  Every
new ellipsoid word is clamped to an explicit ruler stored in the call.  This
makes the iteration polynomial-time on every malformed input.  A separate
semantic predicate records that the clamp is inactive on the canonical run.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Call layout -/

/-- Call layout:
`pair budgetUnary (pair stateBound (pair roundingPrecisionUnary
  (pair oracleStatic initialEllipsoid)))`.

The oracle-static word has layout
`pair mUnary (pair oraclePrecisionUnary (pair tauRaw
  (pair deltaRaw (pair upperRaw matrixCode))))`. -/
def machineBetheFeasibilityBudget (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the feasibility input payload following its iteration budget. -/
def machineBetheFeasibilityAfterBudget (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the state-code bound word from a feasibility input. -/
def machineBetheFeasibilityBound (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityAfterBudget word)

/-- Extract the feasibility payload following the state-code bound word. -/
def machineBetheFeasibilityAfterBound (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityAfterBudget word)

/-- Extract the rounding-precision ruler from a feasibility input. -/
def machineBetheFeasibilityRoundingPrecision
    (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityAfterBound word)

/-- Extract the static oracle data and initial ellipsoid payload. -/
def machineBetheFeasibilityStaticAndInitial
    (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityAfterBound word)

/-- Extract the static oracle data retained throughout the feasibility iteration. -/
def machineBetheFeasibilityOracleStatic
    (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityStaticAndInitial word)

/-- Extract the initial ellipsoid code from the feasibility input. -/
def machineBetheFeasibilityInitialEllipsoid
    (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityStaticAndInitial word)

/-! ## Iteration state -/

/-- Encode the acceptance flag, original input, current ellipsoid, and bound as a feasibility
state. -/
def machineBetheFeasibilityStatePack
    (accepted source ellipsoid bound : List Bool) : List Bool :=
  pair accepted (pair source (pair ellipsoid bound))

/-- Extract the acceptance-flag word from a feasibility state. -/
def machineBetheFeasibilityStateAccepted
    (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extract the original feasibility input retained in the state. -/
def machineBetheFeasibilityStateSource
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extract the current ellipsoid code from a feasibility state. -/
def machineBetheFeasibilityStateEllipsoid
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extract the stored bound word from a feasibility state. -/
def machineBetheFeasibilityStateBound
    (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

/-- Initialize feasibility with a false acceptance flag and the supplied initial ellipsoid and
code bound. -/
def machineBetheFeasibilityInit (word : List Bool) : List Bool :=
  machineBetheFeasibilityStatePack [false] word
    (machineBetheFeasibilityInitialEllipsoid word)
    (machineBetheFeasibilityBound word)

/-! ## One oracle/update step -/

/-- Extract the static oracle dimension ruler from a feasibility state. -/
def machineBetheFeasibilityStaticDimension
    (state : List Bool) : List Bool :=
  machinePairFirst
    (machineBetheFeasibilityOracleStatic
      (machineBetheFeasibilityStateSource state))

/-- Extract the static oracle payload following the dimension ruler. -/
def machineBetheFeasibilityStaticRest
    (state : List Bool) : List Bool :=
  machinePairSecond
    (machineBetheFeasibilityOracleStatic
      (machineBetheFeasibilityStateSource state))

/-- Extract the static oracle precision ruler from a feasibility state. -/
def machineBetheFeasibilityStaticOraclePrecision
    (state : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityStaticRest state)

/-- Extract the static oracle payload following its precision ruler. -/
def machineBetheFeasibilityStaticAfterPrecision
    (state : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityStaticRest state)

/-- Extract the static regularization parameter from a feasibility state. -/
def machineBetheFeasibilityStaticTau
    (state : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityStaticAfterPrecision state)

/-- Extract the static oracle payload following the regularization parameter. -/
def machineBetheFeasibilityStaticAfterTau
    (state : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityStaticAfterPrecision state)

/-- Extract the raw-rational floor parameter from the immutable feasibility oracle data. -/
def machineBetheFeasibilityStaticDelta
    (state : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityStaticAfterTau state)

/-- The immutable oracle payload following the floor parameter, containing the upper threshold
and matrix. -/
def machineBetheFeasibilityStaticAfterDelta
    (state : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityStaticAfterTau state)

/-- Extract the raw-rational objective upper threshold from the immutable oracle data. -/
def machineBetheFeasibilityStaticUpper
    (state : List Bool) : List Bool :=
  machinePairFirst (machineBetheFeasibilityStaticAfterDelta state)

/-- Extract the encoded rational matrix from the immutable oracle data. -/
def machineBetheFeasibilityStaticMatrix
    (state : List Bool) : List Bool :=
  machinePairSecond (machineBetheFeasibilityStaticAfterDelta state)

/-- Package the static dimension, precision, regularization, floor, upper threshold, and matrix
with the current ellipsoid for an oracle call. -/
def machineBetheFeasibilityOracleInput
    (state : List Bool) : List Bool :=
  pair (machineBetheFeasibilityStaticDimension state)
    (pair (machineBetheFeasibilityStaticOraclePrecision state)
      (pair (machineBetheFeasibilityStaticTau state)
        (pair (machineBetheFeasibilityStaticDelta state)
          (pair (machineBetheFeasibilityStaticUpper state)
            (pair (machineBetheFeasibilityStaticMatrix state)
              (machineBetheFeasibilityStateEllipsoid state))))))

/-- Run the encoded bounded Bethe epigraph oracle on the current feasibility state. -/
def machineBetheFeasibilityOracleResponse
    (state : List Bool) : List Bool :=
  machineBetheEpigraphOracleResponseCode
    (machineBetheFeasibilityOracleInput state)

/-- The oracle response bit, which selects a cut when true and acceptance when false. -/
def machineBetheFeasibilityResponseTag
    (state : List Bool) : List Bool :=
  machineHeadBit (machineRationalTaggedResultTag
    (machineBetheFeasibilityOracleResponse state))

/-- Extract the payload of the tagged oracle response, used as the cut normal when a cut is
returned. -/
def machineBetheFeasibilityResponsePayload
    (state : List Bool) : List Bool :=
  machineRationalTaggedResultPayload
    (machineBetheFeasibilityOracleResponse state)

/-- Package the stored rounding precision, current ellipsoid, and oracle cut payload for the
scheduled update. -/
def machineBetheFeasibilityScheduledUpdateInput
    (state : List Bool) : List Bool :=
  pair (machineBetheFeasibilityRoundingPrecision
      (machineBetheFeasibilityStateSource state))
    (pair (machineBetheFeasibilityStateEllipsoid state)
      (machineBetheFeasibilityResponsePayload state))

/-- Compute the scheduled rounded central-cut ellipsoid before imposing the stored code-length
bound. -/
def machineBetheFeasibilityUpdatedEllipsoidCandidate
    (state : List Bool) : List Bool :=
  machineScheduledRoundedEllipsoidCentralUpdateCode
    (machineBetheFeasibilityScheduledUpdateInput state)

/-- Truncate the candidate ellipsoid code to the length of the state-bound word. -/
def machineBetheFeasibilityUpdatedEllipsoid
    (state : List Bool) : List Bool :=
  (machineBetheFeasibilityUpdatedEllipsoidCandidate state).take
    (machineBetheFeasibilityStateBound state).length

/-- Store an unaccepted state with the truncated updated ellipsoid, retaining the source call
and bound. -/
def machineBetheFeasibilityCutState
    (state : List Bool) : List Bool :=
  machineBetheFeasibilityStatePack [false]
    (machineBetheFeasibilityStateSource state)
    (machineBetheFeasibilityUpdatedEllipsoid state)
    (machineBetheFeasibilityStateBound state)

/-- Mark the current state accepted while retaining its source call, ellipsoid, and bound. -/
def machineBetheFeasibilityAcceptState
    (state : List Bool) : List Bool :=
  machineBetheFeasibilityStatePack [true]
    (machineBetheFeasibilityStateSource state)
    (machineBetheFeasibilityStateEllipsoid state)
    (machineBetheFeasibilityStateBound state)

/-- Leave an accepted state fixed; otherwise perform the oracle's cut update or mark the current
ellipsoid accepted. -/
def machineBetheFeasibilityStep (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit
      (machineBetheFeasibilityStateAccepted state)) state
    (machineIfHead (machineBetheFeasibilityResponseTag state)
      (machineBetheFeasibilityCutState state)
      (machineBetheFeasibilityAcceptState state))

/-! ## Final result -/

/-- Iterate the feasibility transition from its initial state for the length of the supplied
budget word. -/
def machineBetheFeasibilityFinalState (word : List Bool) : List Bool :=
  (machineBetheFeasibilityStep)^[(machineBetheFeasibilityBudget word).length]
    (machineBetheFeasibilityInit word)

/-- Encode an accepted center with the false tag, or the final unaccepted ellipsoid with the
true tag. -/
def machineBetheFeasibilityStateResultCode
    (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit
      (machineBetheFeasibilityStateAccepted state))
    (pair [false]
      (machineRationalEllipsoidCenterWord
        (machineBetheFeasibilityStateEllipsoid state)))
    (pair [true] (machineBetheFeasibilityStateEllipsoid state))

/-- Extract the tagged feasibility result after the prescribed number of encoded transitions. -/
def machineBetheFeasibilityResultCode (word : List Bool) : List Bool :=
  machineBetheFeasibilityStateResultCode
    (machineBetheFeasibilityFinalState word)

/-! ## Polynomial-time closure of accessors and one step -/

theorem machineBetheFeasibilityBudget_mem_FP :
    machineBetheFeasibilityBudget ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFeasibilityAfterBudget_mem_FP :
    machineBetheFeasibilityAfterBudget ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFeasibilityBound_mem_FP :
    machineBetheFeasibilityBound ∈ FP := by
  simpa only [machineBetheFeasibilityBound] using!
    machineCompose_mem_FP machineBetheFeasibilityAfterBudget_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityAfterBound_mem_FP :
    machineBetheFeasibilityAfterBound ∈ FP := by
  simpa only [machineBetheFeasibilityAfterBound] using!
    machineCompose_mem_FP machineBetheFeasibilityAfterBudget_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityRoundingPrecision_mem_FP :
    machineBetheFeasibilityRoundingPrecision ∈ FP := by
  simpa only [machineBetheFeasibilityRoundingPrecision] using!
    machineCompose_mem_FP machineBetheFeasibilityAfterBound_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityStaticAndInitial_mem_FP :
    machineBetheFeasibilityStaticAndInitial ∈ FP := by
  simpa only [machineBetheFeasibilityStaticAndInitial] using!
    machineCompose_mem_FP machineBetheFeasibilityAfterBound_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityOracleStatic_mem_FP :
    machineBetheFeasibilityOracleStatic ∈ FP := by
  simpa only [machineBetheFeasibilityOracleStatic] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAndInitial_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityInitialEllipsoid_mem_FP :
    machineBetheFeasibilityInitialEllipsoid ∈ FP := by
  simpa only [machineBetheFeasibilityInitialEllipsoid] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAndInitial_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityStateAccepted_mem_FP :
    machineBetheFeasibilityStateAccepted ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFeasibilityStateSource_mem_FP :
    machineBetheFeasibilityStateSource ∈ FP := by
  simpa only [machineBetheFeasibilityStateSource] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBetheFeasibilityStateEllipsoid_mem_FP :
    machineBetheFeasibilityStateEllipsoid ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheFeasibilityStateEllipsoid] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheFeasibilityStateBound_mem_FP :
    machineBetheFeasibilityStateBound ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheFeasibilityStateBound] using!
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineBetheFeasibilityInit_mem_FP :
    machineBetheFeasibilityInit ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP machineBetheFeasibilityInitialEllipsoid_mem_FP
        machineBetheFeasibilityBound_mem_FP))

theorem machineBetheFeasibilityStaticDimension_mem_FP :
    machineBetheFeasibilityStaticDimension ∈ FP := by
  have hstatic := machineCompose_mem_FP
    machineBetheFeasibilityStateSource_mem_FP
    machineBetheFeasibilityOracleStatic_mem_FP
  simpa only [machineBetheFeasibilityStaticDimension] using!
    machineCompose_mem_FP hstatic machinePairFirst_mem_FP

theorem machineBetheFeasibilityStaticRest_mem_FP :
    machineBetheFeasibilityStaticRest ∈ FP := by
  have hstatic := machineCompose_mem_FP
    machineBetheFeasibilityStateSource_mem_FP
    machineBetheFeasibilityOracleStatic_mem_FP
  simpa only [machineBetheFeasibilityStaticRest] using!
    machineCompose_mem_FP hstatic machinePairSecond_mem_FP

theorem machineBetheFeasibilityStaticOraclePrecision_mem_FP :
    machineBetheFeasibilityStaticOraclePrecision ∈ FP := by
  simpa only [machineBetheFeasibilityStaticOraclePrecision] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityStaticAfterPrecision_mem_FP :
    machineBetheFeasibilityStaticAfterPrecision ∈ FP := by
  simpa only [machineBetheFeasibilityStaticAfterPrecision] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticRest_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityStaticTau_mem_FP :
    machineBetheFeasibilityStaticTau ∈ FP := by
  simpa only [machineBetheFeasibilityStaticTau] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAfterPrecision_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityStaticAfterTau_mem_FP :
    machineBetheFeasibilityStaticAfterTau ∈ FP := by
  simpa only [machineBetheFeasibilityStaticAfterTau] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAfterPrecision_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityStaticDelta_mem_FP :
    machineBetheFeasibilityStaticDelta ∈ FP := by
  simpa only [machineBetheFeasibilityStaticDelta] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAfterTau_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityStaticAfterDelta_mem_FP :
    machineBetheFeasibilityStaticAfterDelta ∈ FP := by
  simpa only [machineBetheFeasibilityStaticAfterDelta] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAfterTau_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityStaticUpper_mem_FP :
    machineBetheFeasibilityStaticUpper ∈ FP := by
  simpa only [machineBetheFeasibilityStaticUpper] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAfterDelta_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFeasibilityStaticMatrix_mem_FP :
    machineBetheFeasibilityStaticMatrix ∈ FP := by
  simpa only [machineBetheFeasibilityStaticMatrix] using!
    machineCompose_mem_FP machineBetheFeasibilityStaticAfterDelta_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFeasibilityOracleInput_mem_FP :
    machineBetheFeasibilityOracleInput ∈ FP :=
  machinePair_mem_FP machineBetheFeasibilityStaticDimension_mem_FP
    (machinePair_mem_FP
      machineBetheFeasibilityStaticOraclePrecision_mem_FP
      (machinePair_mem_FP machineBetheFeasibilityStaticTau_mem_FP
        (machinePair_mem_FP machineBetheFeasibilityStaticDelta_mem_FP
          (machinePair_mem_FP machineBetheFeasibilityStaticUpper_mem_FP
            (machinePair_mem_FP machineBetheFeasibilityStaticMatrix_mem_FP
              machineBetheFeasibilityStateEllipsoid_mem_FP)))))

theorem machineBetheFeasibilityOracleResponse_mem_FP :
    machineBetheFeasibilityOracleResponse ∈ FP := by
  simpa only [machineBetheFeasibilityOracleResponse] using!
    machineCompose_mem_FP machineBetheFeasibilityOracleInput_mem_FP
      machineBetheEpigraphOracleResponseCode_mem_FP

theorem machineBetheFeasibilityResponseTag_mem_FP :
    machineBetheFeasibilityResponseTag ∈ FP := by
  have htag := machineCompose_mem_FP
    machineBetheFeasibilityOracleResponse_mem_FP
    machineRationalTaggedResultTag_mem_FP
  simpa only [machineBetheFeasibilityResponseTag] using!
    machineCompose_mem_FP htag machineHeadBit_mem_FP

theorem machineBetheFeasibilityResponsePayload_mem_FP :
    machineBetheFeasibilityResponsePayload ∈ FP := by
  simpa only [machineBetheFeasibilityResponsePayload] using!
    machineCompose_mem_FP machineBetheFeasibilityOracleResponse_mem_FP
      machineRationalTaggedResultPayload_mem_FP

theorem machineBetheFeasibilityScheduledUpdateInput_mem_FP :
    machineBetheFeasibilityScheduledUpdateInput ∈ FP := by
  have hp := machineCompose_mem_FP
    machineBetheFeasibilityStateSource_mem_FP
    machineBetheFeasibilityRoundingPrecision_mem_FP
  exact machinePair_mem_FP hp
    (machinePair_mem_FP machineBetheFeasibilityStateEllipsoid_mem_FP
      machineBetheFeasibilityResponsePayload_mem_FP)

theorem machineBetheFeasibilityUpdatedEllipsoidCandidate_mem_FP :
    machineBetheFeasibilityUpdatedEllipsoidCandidate ∈ FP := by
  simpa only [machineBetheFeasibilityUpdatedEllipsoidCandidate] using!
    machineCompose_mem_FP
      machineBetheFeasibilityScheduledUpdateInput_mem_FP
      machineScheduledRoundedEllipsoidCentralUpdateCode_mem_FP

theorem machineBetheFeasibilityUpdatedEllipsoid_mem_FP :
    machineBetheFeasibilityUpdatedEllipsoid ∈ FP := by
  simpa only [machineBetheFeasibilityUpdatedEllipsoid] using!
    machineTake_mem_FP machineBetheFeasibilityStateBound_mem_FP
      machineBetheFeasibilityUpdatedEllipsoidCandidate_mem_FP

theorem machineBetheFeasibilityCutState_mem_FP :
    machineBetheFeasibilityCutState ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP machineBetheFeasibilityStateSource_mem_FP
      (machinePair_mem_FP machineBetheFeasibilityUpdatedEllipsoid_mem_FP
        machineBetheFeasibilityStateBound_mem_FP))

theorem machineBetheFeasibilityAcceptState_mem_FP :
    machineBetheFeasibilityAcceptState ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [true])
    (machinePair_mem_FP machineBetheFeasibilityStateSource_mem_FP
      (machinePair_mem_FP machineBetheFeasibilityStateEllipsoid_mem_FP
        machineBetheFeasibilityStateBound_mem_FP))

theorem machineBetheFeasibilityStep_mem_FP :
    machineBetheFeasibilityStep ∈ FP := by
  have haccepted := machineCompose_mem_FP
    machineBetheFeasibilityStateAccepted_mem_FP machineHeadBit_mem_FP
  have hbranch := machineIfHead_mem_FP
    machineBetheFeasibilityResponseTag_mem_FP
    machineBetheFeasibilityCutState_mem_FP
    machineBetheFeasibilityAcceptState_mem_FP
  simpa only [machineBetheFeasibilityStep] using!
    machineIfHead_mem_FP haccepted id_mem_FP hbranch

theorem machineBetheFeasibilityStateResultCode_mem_FP :
    machineBetheFeasibilityStateResultCode ∈ FP := by
  have htest := machineCompose_mem_FP
    machineBetheFeasibilityStateAccepted_mem_FP machineHeadBit_mem_FP
  have hcenter := machineCompose_mem_FP
    machineBetheFeasibilityStateEllipsoid_mem_FP
    machineRationalEllipsoidCenterWord_mem_FP
  exact machineIfHead_mem_FP htest
    (machinePair_mem_FP (machineConst_mem_FP [false]) hcenter)
    (machinePair_mem_FP (machineConst_mem_FP [true])
      machineBetheFeasibilityStateEllipsoid_mem_FP)

/-! ## Global state envelope and polynomial iteration -/

@[simp] theorem machineBetheFeasibilityStateAccepted_pack
    (accepted source ellipsoid bound : List Bool) :
    machineBetheFeasibilityStateAccepted
        (machineBetheFeasibilityStatePack accepted source ellipsoid bound) =
      accepted := by
  simp [machineBetheFeasibilityStateAccepted,
    machineBetheFeasibilityStatePack]

@[simp] theorem machineBetheFeasibilityStateSource_pack
    (accepted source ellipsoid bound : List Bool) :
    machineBetheFeasibilityStateSource
        (machineBetheFeasibilityStatePack accepted source ellipsoid bound) =
      source := by
  simp [machineBetheFeasibilityStateSource,
    machineBetheFeasibilityStatePack]

@[simp] theorem machineBetheFeasibilityStateEllipsoid_pack
    (accepted source ellipsoid bound : List Bool) :
    machineBetheFeasibilityStateEllipsoid
        (machineBetheFeasibilityStatePack accepted source ellipsoid bound) =
      ellipsoid := by
  simp [machineBetheFeasibilityStateEllipsoid,
    machineBetheFeasibilityStatePack]

@[simp] theorem machineBetheFeasibilityStateBound_pack
    (accepted source ellipsoid bound : List Bool) :
    machineBetheFeasibilityStateBound
        (machineBetheFeasibilityStatePack accepted source ellipsoid bound) =
      bound := by
  simp [machineBetheFeasibilityStateBound,
    machineBetheFeasibilityStatePack]

/-- The state has the canonical four-field layout, an acceptance word of length at most one, and
source, ellipsoid, and bound words no longer than the original input. -/
def MachineBetheFeasibilityStateBound
    (word state : List Bool) : Prop :=
  state = machineBetheFeasibilityStatePack
      (machineBetheFeasibilityStateAccepted state)
      (machineBetheFeasibilityStateSource state)
      (machineBetheFeasibilityStateEllipsoid state)
      (machineBetheFeasibilityStateBound state) ∧
    (machineBetheFeasibilityStateAccepted state).length ≤ 1 ∧
    (machineBetheFeasibilityStateSource state).length ≤ word.length ∧
    (machineBetheFeasibilityStateEllipsoid state).length ≤ word.length ∧
    (machineBetheFeasibilityStateBound state).length ≤ word.length

theorem machineBetheFeasibilityBound_length_le (word : List Bool) :
    (machineBetheFeasibilityBound word).length ≤ word.length := by
  exact (machinePairFirst_length_le
    (machineBetheFeasibilityAfterBudget word)).trans
      (machinePairSecond_length_le word)

theorem machineBetheFeasibilityInitialEllipsoid_length_le
    (word : List Bool) :
    (machineBetheFeasibilityInitialEllipsoid word).length ≤ word.length := by
  exact (machinePairSecond_length_le
      (machineBetheFeasibilityStaticAndInitial word)).trans
    ((machinePairSecond_length_le
      (machineBetheFeasibilityAfterBound word)).trans
    ((machinePairSecond_length_le
      (machineBetheFeasibilityAfterBudget word)).trans
      (machinePairSecond_length_le word)))

theorem machineBetheFeasibilityInit_bound (word : List Bool) :
    MachineBetheFeasibilityStateBound word
      (machineBetheFeasibilityInit word) := by
  simp only [machineBetheFeasibilityInit,
    MachineBetheFeasibilityStateBound,
    machineBetheFeasibilityStateAccepted_pack,
    machineBetheFeasibilityStateSource_pack,
    machineBetheFeasibilityStateEllipsoid_pack,
    machineBetheFeasibilityStateBound_pack, List.length_singleton]
  exact ⟨trivial, by simp, le_rfl,
    machineBetheFeasibilityInitialEllipsoid_length_le word,
    machineBetheFeasibilityBound_length_le word⟩

theorem machineBetheFeasibilityCutState_bound {word state : List Bool}
    (hs : MachineBetheFeasibilityStateBound word state) :
    MachineBetheFeasibilityStateBound word
      (machineBetheFeasibilityCutState state) := by
  rcases hs with ⟨hdecomp, haccepted, hsource, hellipsoid, hbound⟩
  simp only [machineBetheFeasibilityCutState,
    MachineBetheFeasibilityStateBound,
    machineBetheFeasibilityStateAccepted_pack,
    machineBetheFeasibilityStateSource_pack,
    machineBetheFeasibilityStateEllipsoid_pack,
    machineBetheFeasibilityStateBound_pack, List.length_singleton]
  refine ⟨trivial, by simp, hsource, ?_, hbound⟩
  exact (List.length_take_le _ _).trans hbound

theorem machineBetheFeasibilityAcceptState_bound {word state : List Bool}
    (hs : MachineBetheFeasibilityStateBound word state) :
    MachineBetheFeasibilityStateBound word
      (machineBetheFeasibilityAcceptState state) := by
  rcases hs with ⟨hdecomp, haccepted, hsource, hellipsoid, hbound⟩
  simp only [machineBetheFeasibilityAcceptState,
    MachineBetheFeasibilityStateBound,
    machineBetheFeasibilityStateAccepted_pack,
    machineBetheFeasibilityStateSource_pack,
    machineBetheFeasibilityStateEllipsoid_pack,
    machineBetheFeasibilityStateBound_pack, List.length_singleton]
  exact ⟨trivial, by simp, hsource, hellipsoid, hbound⟩

theorem machineBetheFeasibilityStep_bound {word state : List Bool}
    (hs : MachineBetheFeasibilityStateBound word state) :
    MachineBetheFeasibilityStateBound word
      (machineBetheFeasibilityStep state) := by
  rw [machineBetheFeasibilityStep]
  cases ha : machineBetheFeasibilityStateAccepted state with
  | nil =>
      rw [machineHeadBit_nil, machineIfHead_false]
      rw [machineBetheFeasibilityResponseTag]
      cases hr : machineRationalTaggedResultTag
          (machineBetheFeasibilityOracleResponse state) with
      | nil =>
          rw [machineHeadBit_nil, machineIfHead_false]
          exact machineBetheFeasibilityAcceptState_bound hs
      | cons responseBit responseTail =>
          rw [machineHeadBit_cons]
          cases responseBit
          · rw [machineIfHead_false]
            exact machineBetheFeasibilityAcceptState_bound hs
          · rw [machineIfHead_true]
            exact machineBetheFeasibilityCutState_bound hs
  | cons acceptedBit acceptedTail =>
      rw [machineHeadBit_cons]
      cases acceptedBit
      · rw [machineIfHead_false]
        rw [machineBetheFeasibilityResponseTag]
        cases hr : machineRationalTaggedResultTag
            (machineBetheFeasibilityOracleResponse state) with
        | nil =>
            rw [machineHeadBit_nil, machineIfHead_false]
            exact machineBetheFeasibilityAcceptState_bound hs
        | cons responseBit responseTail =>
            rw [machineHeadBit_cons]
            cases responseBit
            · rw [machineIfHead_false]
              exact machineBetheFeasibilityAcceptState_bound hs
            · rw [machineIfHead_true]
              exact machineBetheFeasibilityCutState_bound hs
      · rw [machineIfHead_true]
        exact hs

theorem machineBetheFeasibilityIterate_bound (word : List Bool) : ∀ k,
    MachineBetheFeasibilityStateBound word
      ((machineBetheFeasibilityStep)^[k]
        (machineBetheFeasibilityInit word)) := by
  intro k
  induction k with
  | zero => exact machineBetheFeasibilityInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineBetheFeasibilityStep_bound ih

/-- A uniform state-width envelope obtained by packing four copies of the input prefixed by one
false bit. -/
def machineBetheFeasibilityWidth (word : List Bool) : List Bool :=
  let envelope := [false] ++ word
  machineBetheFeasibilityStatePack envelope envelope envelope envelope

theorem machineBetheFeasibilityWidth_mem_FP :
    machineBetheFeasibilityWidth ∈ FP := by
  have henvelope : (fun word : List Bool ↦ false :: word) ∈ FP :=
    by simpa only [List.singleton_append] using!
      machineAppend_mem_FP (machineConst_mem_FP [false]) id_mem_FP
  simpa only [machineBetheFeasibilityWidth] using!
    machinePair_mem_FP henvelope
      (machinePair_mem_FP henvelope
        (machinePair_mem_FP henvelope henvelope))

theorem machineBetheFeasibilityIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_hiterations : iterations ≤
      (machineBetheFeasibilityBudget word).length) :
    ((machineBetheFeasibilityStep)^[iterations]
      (machineBetheFeasibilityInit word)).length ≤
        (machineBetheFeasibilityWidth word).length := by
  rcases machineBetheFeasibilityIterate_bound word iterations with
    ⟨hdecomp, haccepted, hsource, hellipsoid, hbound⟩
  rw [hdecomp]
  simp only [machineBetheFeasibilityStatePack,
    machineBetheFeasibilityWidth, pair_length, List.length_append,
    List.length_singleton]
  omega

theorem machineBetheFeasibilityFinalState_mem_FP :
    machineBetheFeasibilityFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineBetheFeasibilityStep_mem_FP
    machineBetheFeasibilityInit_mem_FP machineBetheFeasibilityBudget_mem_FP
    machineBetheFeasibilityWidth_mem_FP
    machineBetheFeasibilityIterate_length_le_width

theorem machineBetheFeasibilityResultCode_mem_FP :
    machineBetheFeasibilityResultCode ∈ FP := by
  simpa only [machineBetheFeasibilityResultCode] using!
    machineCompose_mem_FP machineBetheFeasibilityFinalState_mem_FP
      machineBetheFeasibilityStateResultCode_mem_FP

end BeyondBethe

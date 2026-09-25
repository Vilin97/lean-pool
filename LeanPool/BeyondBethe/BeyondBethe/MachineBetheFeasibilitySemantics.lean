/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFeasibilityLoop
public import Mathlib.Tactic

/-!
# Semantics of the finite-word Bethe feasibility loop

This file connects the finite-word iterator to the recursive rational
feasibility algorithm.  The only intermediate side condition is the explicit
statement that every canonical updated ellipsoid fits the ruler carried by the
call word.  A later encoding-bound theorem discharges that condition for the
public schedule.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Canonical calls and states -/

/-- Encode the fixed oracle data with unary dimension and precision, raw-rational parameters,
and the rational matrix code. -/
def machineBetheFeasibilityCanonicalStaticWord {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat) : List Bool :=
  pair (List.replicate m true)
    (pair (List.replicate oraclePrecision true)
      (pair (rawRatBinaryCode (rawRatOfRat tau))
        (pair (rawRatBinaryCode delta)
          (pair (rawRatBinaryCode upper)
            (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩)))))

/-- Encode a feasibility call with unary iteration, state-length, and rounding bounds, followed
by its static oracle data and initial ellipsoid. -/
def machineBetheFeasibilityCanonicalWord {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) : List Bool :=
  pair (List.replicate budget true)
    (pair (List.replicate stateBound true)
      (pair (List.replicate roundingPrecision true)
        (pair
          (machineBetheFeasibilityCanonicalStaticWord
            tau A oraclePrecision delta upper)
          (rationalEllipsoidStateBinaryCode initial))))

/-- Encode a semantic feasibility state with its acceptance bit, original canonical call,
current ellipsoid, and unary length bound. -/
def machineBetheFeasibilityCanonicalState {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) : List Bool :=
  machineBetheFeasibilityStatePack [accepted]
    (machineBetheFeasibilityCanonicalWord tau A oraclePrecision delta upper
      roundingPrecision budget stateBound initial)
    (rationalEllipsoidStateBinaryCode current)
    (List.replicate stateBound true)

@[simp] theorem machineBetheFeasibilityBudget_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityBudget
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      List.replicate budget true := by
  rw [machineBetheFeasibilityBudget,
    machineBetheFeasibilityCanonicalWord, machinePairFirst_pair]

@[simp] theorem machineBetheFeasibilityBound_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityBound
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      List.replicate stateBound true := by
  rw [machineBetheFeasibilityBound, machineBetheFeasibilityAfterBudget,
    machineBetheFeasibilityCanonicalWord, machinePairSecond_pair,
    machinePairFirst_pair]

@[simp] theorem machineBetheFeasibilityRoundingPrecision_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityRoundingPrecision
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      List.replicate roundingPrecision true := by
  rw [machineBetheFeasibilityRoundingPrecision,
    machineBetheFeasibilityAfterBound,
    machineBetheFeasibilityAfterBudget,
    machineBetheFeasibilityCanonicalWord]
  simp only [machinePairSecond_pair, machinePairFirst_pair]

@[simp] theorem machineBetheFeasibilityOracleStatic_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityOracleStatic
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      machineBetheFeasibilityCanonicalStaticWord
        tau A oraclePrecision delta upper := by
  rw [machineBetheFeasibilityOracleStatic,
    machineBetheFeasibilityStaticAndInitial,
    machineBetheFeasibilityAfterBound,
    machineBetheFeasibilityAfterBudget,
    machineBetheFeasibilityCanonicalWord]
  simp only [machinePairSecond_pair, machinePairFirst_pair]

@[simp] theorem machineBetheFeasibilityInitialEllipsoid_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityInitialEllipsoid
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      rationalEllipsoidStateBinaryCode initial := by
  rw [machineBetheFeasibilityInitialEllipsoid,
    machineBetheFeasibilityStaticAndInitial,
    machineBetheFeasibilityAfterBound,
    machineBetheFeasibilityAfterBudget,
    machineBetheFeasibilityCanonicalWord]
  simp only [machinePairSecond_pair]

@[simp] theorem machineBetheFeasibilityInit_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityInit
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      machineBetheFeasibilityCanonicalState false tau A oraclePrecision
        delta upper roundingPrecision budget stateBound initial initial := by
  rw [machineBetheFeasibilityInit,
    machineBetheFeasibilityInitialEllipsoid_encode,
    machineBetheFeasibilityBound_encode]
  rfl

@[simp] theorem machineBetheFeasibilityStateAccepted_encode {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStateAccepted
        (machineBetheFeasibilityCanonicalState accepted tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      [accepted] := by
  rw [machineBetheFeasibilityCanonicalState,
    machineBetheFeasibilityStateAccepted_pack]

@[simp] theorem machineBetheFeasibilityStateSource_encode {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStateSource
        (machineBetheFeasibilityCanonicalState accepted tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      machineBetheFeasibilityCanonicalWord tau A oraclePrecision delta upper
        roundingPrecision budget stateBound initial := by
  rw [machineBetheFeasibilityCanonicalState,
    machineBetheFeasibilityStateSource_pack]

@[simp] theorem machineBetheFeasibilityStateEllipsoid_encode {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStateEllipsoid
        (machineBetheFeasibilityCanonicalState accepted tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      rationalEllipsoidStateBinaryCode current := by
  rw [machineBetheFeasibilityCanonicalState,
    machineBetheFeasibilityStateEllipsoid_pack]

@[simp] theorem machineBetheFeasibilityStateBound_encode {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStateBound
        (machineBetheFeasibilityCanonicalState accepted tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      List.replicate stateBound true := by
  rw [machineBetheFeasibilityCanonicalState,
    machineBetheFeasibilityStateBound_pack]

@[simp] theorem machineBetheFeasibilityOracleInput_encode {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityOracleInput
        (machineBetheFeasibilityCanonicalState accepted tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      machineBetheOracleCanonicalWord
        tau A oraclePrecision delta upper current := by
  simp only [machineBetheFeasibilityOracleInput,
    machineBetheFeasibilityStaticDimension,
    machineBetheFeasibilityStaticRest,
    machineBetheFeasibilityStaticOraclePrecision,
    machineBetheFeasibilityStaticAfterPrecision,
    machineBetheFeasibilityStaticTau,
    machineBetheFeasibilityStaticAfterTau,
    machineBetheFeasibilityStaticDelta,
    machineBetheFeasibilityStaticAfterDelta,
    machineBetheFeasibilityStaticUpper,
    machineBetheFeasibilityStaticMatrix,
    machineBetheFeasibilityStateSource_encode,
    machineBetheFeasibilityOracleStatic_encode,
    machineBetheFeasibilityStateEllipsoid_encode,
    machineBetheFeasibilityCanonicalStaticWord,
    machineBetheOracleCanonicalWord, machinePairFirst_pair,
    machinePairSecond_pair]

@[simp] theorem machineBetheFeasibilityOracleResponse_encode {m : ℕ}
    (accepted : Bool)
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityOracleResponse
        (machineBetheFeasibilityCanonicalState accepted tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      rationalCentralOracleResponseBinaryCode
        (scannedBetheBoundedEpigraphOracle
          tau A oraclePrecision delta upper current) := by
  rw [machineBetheFeasibilityOracleResponse,
    machineBetheFeasibilityOracleInput_encode,
    machineBetheEpigraphOracleResponseCode_encode]

/-! ## Exact one-step behavior -/

@[simp] theorem machineBetheFeasibilityStep_accepted_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStep
        (machineBetheFeasibilityCanonicalState true tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      machineBetheFeasibilityCanonicalState true tau A oraclePrecision
        delta upper roundingPrecision budget stateBound initial current := by
  rw [machineBetheFeasibilityStep]
  simp only [machineBetheFeasibilityStateAccepted_encode,
    machineHeadBit_cons, machineIfHead_true]

theorem machineBetheFeasibilityResponseTag_accept_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (hresponse : scannedBetheBoundedEpigraphOracle
      tau A oraclePrecision delta upper current = .accept) :
    machineBetheFeasibilityResponseTag
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      [false] := by
  rw [machineBetheFeasibilityResponseTag,
    machineBetheFeasibilityOracleResponse_encode, hresponse]
  rfl

theorem machineBetheFeasibilityStep_accept_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (hresponse : scannedBetheBoundedEpigraphOracle
      tau A oraclePrecision delta upper current = .accept) :
    machineBetheFeasibilityStep
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      machineBetheFeasibilityCanonicalState true tau A oraclePrecision
        delta upper roundingPrecision budget stateBound initial current := by
  rw [machineBetheFeasibilityStep]
  simp only [machineBetheFeasibilityStateAccepted_encode,
    machineHeadBit_cons, machineIfHead_false]
  rw [machineBetheFeasibilityResponseTag_accept_encode tau A
    oraclePrecision delta upper roundingPrecision budget stateBound
    initial current hresponse]
  rw [machineIfHead_false, machineBetheFeasibilityAcceptState,
    machineBetheFeasibilityStateSource_encode,
    machineBetheFeasibilityStateEllipsoid_encode,
    machineBetheFeasibilityStateBound_encode]
  rfl

theorem machineBetheFeasibilityResponseTag_cut_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (a : Fin (m * m + 1) → ℚ)
    (hresponse : scannedBetheBoundedEpigraphOracle
      tau A oraclePrecision delta upper current = .cut a) :
    machineBetheFeasibilityResponseTag
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      [true] := by
  rw [machineBetheFeasibilityResponseTag,
    machineBetheFeasibilityOracleResponse_encode, hresponse]
  rfl

theorem machineBetheFeasibilityResponsePayload_cut_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (a : Fin (m * m + 1) → ℚ)
    (hresponse : scannedBetheBoundedEpigraphOracle
      tau A oraclePrecision delta upper current = .cut a) :
    machineBetheFeasibilityResponsePayload
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      rationalFiniteVectorCode a := by
  rw [machineBetheFeasibilityResponsePayload,
    machineBetheFeasibilityOracleResponse_encode, hresponse]
  rfl

theorem machineBetheFeasibilityUpdatedCandidate_cut_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (a : Fin (m * m + 1) → ℚ)
    (hresponse : scannedBetheBoundedEpigraphOracle
      tau A oraclePrecision delta upper current = .cut a) :
    machineBetheFeasibilityUpdatedEllipsoidCandidate
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      rationalEllipsoidStateBinaryCode
    (scheduledRoundedEllipsoidCentralUpdate
          roundingPrecision current a) := by
  rw [machineBetheFeasibilityUpdatedEllipsoidCandidate,
    machineBetheFeasibilityScheduledUpdateInput]
  rw [machineBetheFeasibilityStateSource_encode,
    machineBetheFeasibilityRoundingPrecision_encode,
    machineBetheFeasibilityStateEllipsoid_encode,
    machineBetheFeasibilityResponsePayload_cut_encode tau A
      oraclePrecision delta upper roundingPrecision budget stateBound
      initial current a hresponse]
  exact machineScheduledRoundedEllipsoidCentralUpdateCode_encode
    roundingPrecision current a

theorem machineBetheFeasibilityStep_cut_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (a : Fin (m * m + 1) → ℚ)
    (hresponse : scannedBetheBoundedEpigraphOracle
      tau A oraclePrecision delta upper current = .cut a)
    (hfit : (rationalEllipsoidStateBinaryCode
      (scheduledRoundedEllipsoidCentralUpdate
        roundingPrecision current a)).length ≤ stateBound) :
    machineBetheFeasibilityStep
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      machineBetheFeasibilityCanonicalState false tau A oraclePrecision
        delta upper roundingPrecision budget stateBound initial
          (scheduledRoundedEllipsoidCentralUpdate
            roundingPrecision current a) := by
  have htag := machineBetheFeasibilityResponseTag_cut_encode tau A
    oraclePrecision delta upper roundingPrecision budget stateBound
    initial current a hresponse
  rw [machineBetheFeasibilityStep]
  rw [show machineHeadBit
      (machineBetheFeasibilityStateAccepted
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current)) =
        [false] by
      rw [machineBetheFeasibilityStateAccepted_encode]
      rfl]
  rw [machineIfHead_false, htag]
  rw [machineIfHead_true, machineBetheFeasibilityCutState]
  rw [machineBetheFeasibilityStateSource_encode,
    machineBetheFeasibilityStateBound_encode,
    machineBetheFeasibilityUpdatedEllipsoid,
    machineBetheFeasibilityUpdatedCandidate_cut_encode tau A
    oraclePrecision delta upper roundingPrecision budget stateBound
    initial current a hresponse]
  rw [machineBetheFeasibilityStateBound_encode, List.length_replicate]
  rw [List.take_of_length_le hfit]
  rfl

/-! ## The ruler condition and complete recursive semantics -/

/-- Every scheduled cut update reached during the remaining iterations fits the supplied
code-length bound; an accepted oracle response ends the requirement. -/
def MachineBetheFeasibilityFits {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision stateBound : ℕ) :
    ℕ → RationalEllipsoidState (m * m + 1) → Prop
  | 0, _ => True
  | iterations + 1, E =>
      match scannedBetheBoundedEpigraphOracle
          tau A oraclePrecision delta upper E with
      | .accept => True
      | .cut a =>
          (rationalEllipsoidStateBinaryCode
              (scheduledRoundedEllipsoidCentralUpdate
                roundingPrecision E a)).length ≤ stateBound ∧
            MachineBetheFeasibilityFits tau A oraclePrecision delta upper
              roundingPrecision stateBound iterations
              (scheduledRoundedEllipsoidCentralUpdate
                roundingPrecision E a)

theorem machineBetheFeasibilityIterate_accepted_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound iterations : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    (machineBetheFeasibilityStep^[iterations])
        (machineBetheFeasibilityCanonicalState true tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      machineBetheFeasibilityCanonicalState true tau A oraclePrecision
        delta upper roundingPrecision budget stateBound initial current := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      rw [Function.iterate_succ_apply]
      rw [machineBetheFeasibilityStep_accepted_encode]
      exact ih

theorem machineBetheFeasibilityStateResult_accepted_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStateResultCode
        (machineBetheFeasibilityCanonicalState true tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      rationalFeasibilityResultBinaryCode (.accepted current.center) := by
  simp [machineBetheFeasibilityStateResultCode,
    machineBetheFeasibilityCanonicalState,
    rationalFeasibilityResultBinaryCode]

theorem machineBetheFeasibilityStateResult_exhausted_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1)) :
    machineBetheFeasibilityStateResultCode
        (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial current) =
      rationalFeasibilityResultBinaryCode (.exhausted current) := by
  simp [machineBetheFeasibilityStateResultCode,
    machineBetheFeasibilityCanonicalState,
    rationalFeasibilityResultBinaryCode]

theorem machineBetheFeasibilityIterateResult_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound iterations : ℕ)
    (initial current : RationalEllipsoidState (m * m + 1))
    (hfit : MachineBetheFeasibilityFits tau A oraclePrecision delta upper
      roundingPrecision stateBound iterations current) :
    machineBetheFeasibilityStateResultCode
        ((machineBetheFeasibilityStep^[iterations])
          (machineBetheFeasibilityCanonicalState false tau A oraclePrecision
            delta upper roundingPrecision budget stateBound initial current)) =
      rationalFeasibilityResultBinaryCode
        (runFixedPrecisionRationalFeasibility roundingPrecision
          (scannedBetheBoundedEpigraphOracle
            tau A oraclePrecision delta upper) iterations current) := by
  induction iterations generalizing current with
  | zero =>
      simpa [runFixedPrecisionRationalFeasibility] using!
        machineBetheFeasibilityStateResult_exhausted_encode tau A
          oraclePrecision delta upper roundingPrecision budget stateBound
          initial current
  | succ iterations ih =>
      rw [Function.iterate_succ_apply]
      rw [runFixedPrecisionRationalFeasibility]
      cases hresponse : scannedBetheBoundedEpigraphOracle
          tau A oraclePrecision delta upper current with
      | accept =>
          rw [machineBetheFeasibilityStep_accept_encode tau A
            oraclePrecision delta upper roundingPrecision budget stateBound
            initial current hresponse]
          rw [machineBetheFeasibilityIterate_accepted_encode]
          exact machineBetheFeasibilityStateResult_accepted_encode tau A
            oraclePrecision delta upper roundingPrecision budget stateBound
            initial current
      | cut a =>
          have hfit' := hfit
          simp only [MachineBetheFeasibilityFits, hresponse] at hfit'
          rw [machineBetheFeasibilityStep_cut_encode tau A
            oraclePrecision delta upper roundingPrecision budget stateBound
            initial current a hresponse hfit'.1]
          exact ih _ hfit'.2

theorem machineBetheFeasibilityResultCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    (roundingPrecision budget stateBound : ℕ)
    (initial : RationalEllipsoidState (m * m + 1))
    (hfit : MachineBetheFeasibilityFits tau A oraclePrecision delta upper
      roundingPrecision stateBound budget initial) :
    machineBetheFeasibilityResultCode
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper roundingPrecision budget stateBound initial) =
      rationalFeasibilityResultBinaryCode
        (runFixedPrecisionRationalFeasibility roundingPrecision
          (scannedBetheBoundedEpigraphOracle
            tau A oraclePrecision delta upper) budget initial) := by
  rw [machineBetheFeasibilityResultCode,
    machineBetheFeasibilityFinalState,
    machineBetheFeasibilityBudget_encode,
    List.length_replicate,
    machineBetheFeasibilityInit_encode]
  exact machineBetheFeasibilityIterateResult_encode tau A oraclePrecision
    delta upper roundingPrecision budget stateBound budget initial initial hfit

end BeyondBethe

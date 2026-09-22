/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineKuhnEncoding

/-!
# One finite-word transition of the Kuhn evaluator

This is the bit-level implementation of `kuhnEvalStep`.  Every branch uses
only pairing, list access/update, Boolean gates, and the rational support
query already shown to lie in `FP`.
-/

namespace BeyondBethe

open Complexity

/-! ## State-level field access -/

def machineKuhnControl (state : List Bool) : List Bool :=
  machineKuhnStateControl state

def machineKuhnFuel (state : List Bool) : List Bool :=
  machineKuhnCallFuel (machineKuhnControl state)

def machineKuhnRemaining (state : List Bool) : List Bool :=
  machineKuhnCallRemaining (machineKuhnControl state)

def machineKuhnRow (state : List Bool) : List Bool :=
  machineKuhnCallRow (machineKuhnControl state)

def machineKuhnSeen (state : List Bool) : List Bool :=
  machineKuhnCallSeen (machineKuhnControl state)

def machineKuhnMate (state : List Bool) : List Bool :=
  machineKuhnCallMate (machineKuhnControl state)

def machineKuhnStack (state : List Bool) : List Bool :=
  machineKuhnCallStack (machineKuhnControl state)

def machineKuhnRetSuccess (state : List Bool) : List Bool :=
  machineKuhnReturnSuccess (machineKuhnControl state)

def machineKuhnRetSeen (state : List Bool) : List Bool :=
  machineKuhnReturnSeen (machineKuhnControl state)

def machineKuhnRetMate (state : List Bool) : List Bool :=
  machineKuhnReturnMate (machineKuhnControl state)

def machineKuhnRetStack (state : List Bool) : List Bool :=
  machineKuhnReturnStack (machineKuhnControl state)

def machineKuhnTopFrame (state : List Bool) : List Bool :=
  machineKuhnStackHead (machineKuhnRetStack state)

def machineKuhnRestStack (state : List Bool) : List Bool :=
  machineKuhnStackTail (machineKuhnRetStack state)

theorem machineKuhnControl_mem_FP : machineKuhnControl ∈ Complexity.FP :=
  machineKuhnStateControl_mem_FP

theorem machineKuhnFuel_mem_FP : machineKuhnFuel ∈ Complexity.FP := by
  simpa only [machineKuhnFuel] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnCallFuel_mem_FP
theorem machineKuhnRemaining_mem_FP : machineKuhnRemaining ∈ Complexity.FP := by
  simpa only [machineKuhnRemaining] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP
      machineKuhnCallRemaining_mem_FP
theorem machineKuhnRow_mem_FP : machineKuhnRow ∈ Complexity.FP := by
  simpa only [machineKuhnRow] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnCallRow_mem_FP
theorem machineKuhnSeen_mem_FP : machineKuhnSeen ∈ Complexity.FP := by
  simpa only [machineKuhnSeen] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnCallSeen_mem_FP
theorem machineKuhnMate_mem_FP : machineKuhnMate ∈ Complexity.FP := by
  simpa only [machineKuhnMate] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnCallMate_mem_FP
theorem machineKuhnStack_mem_FP : machineKuhnStack ∈ Complexity.FP := by
  simpa only [machineKuhnStack] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnCallStack_mem_FP
theorem machineKuhnRetSuccess_mem_FP : machineKuhnRetSuccess ∈ Complexity.FP := by
  simpa only [machineKuhnRetSuccess] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP
      machineKuhnReturnSuccess_mem_FP
theorem machineKuhnRetSeen_mem_FP : machineKuhnRetSeen ∈ Complexity.FP := by
  simpa only [machineKuhnRetSeen] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnReturnSeen_mem_FP
theorem machineKuhnRetMate_mem_FP : machineKuhnRetMate ∈ Complexity.FP := by
  simpa only [machineKuhnRetMate] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP machineKuhnReturnMate_mem_FP
theorem machineKuhnRetStack_mem_FP : machineKuhnRetStack ∈ Complexity.FP := by
  simpa only [machineKuhnRetStack] using!
    machineCompose_mem_FP machineKuhnControl_mem_FP
      machineKuhnReturnStack_mem_FP
theorem machineKuhnTopFrame_mem_FP : machineKuhnTopFrame ∈ Complexity.FP := by
  simpa only [machineKuhnTopFrame] using!
    machineCompose_mem_FP machineKuhnRetStack_mem_FP
      machineKuhnStackHead_mem_FP
theorem machineKuhnRestStack_mem_FP : machineKuhnRestStack ∈ Complexity.FP := by
  simpa only [machineKuhnRestStack] using!
    machineCompose_mem_FP machineKuhnRetStack_mem_FP
      machineKuhnStackTail_mem_FP

/-! ## Repacking with a fixed global clamp -/

def machineKuhnClamp (state candidate : List Bool) : List Bool :=
  candidate.take (machineKuhnStateBound state).length

def machineKuhnWithControl (state control : List Bool) : List Bool :=
  machineKuhnStatePack (machineKuhnClamp state control)
    (machineKuhnClamp state (machineKuhnStateMatrix state))
    (machineKuhnClamp state (machineKuhnStateDimension state))
    (machineKuhnClamp state (machineKuhnStateColumns state))
    (machineKuhnClamp state (machineKuhnStateFalseSeen state))
    (machineKuhnStateBound state)

theorem machineKuhnClamp_mem_FP
    {candidate : List Bool → List Bool} (hcandidate : candidate ∈ Complexity.FP) :
    (fun state ↦ machineKuhnClamp state (candidate state)) ∈ Complexity.FP := by
  simpa only [machineKuhnClamp] using!
    machineTake_mem_FP machineKuhnStateBound_mem_FP hcandidate

theorem machineKuhnWithControl_mem_FP
    {control : List Bool → List Bool} (hcontrol : control ∈ Complexity.FP) :
    (fun state ↦ machineKuhnWithControl state (control state)) ∈
      Complexity.FP := by
  have hc := machineKuhnClamp_mem_FP hcontrol
  have hm := machineKuhnClamp_mem_FP machineKuhnStateMatrix_mem_FP
  have hd := machineKuhnClamp_mem_FP machineKuhnStateDimension_mem_FP
  have hcols := machineKuhnClamp_mem_FP machineKuhnStateColumns_mem_FP
  have hfalse := machineKuhnClamp_mem_FP machineKuhnStateFalseSeen_mem_FP
  exact machinePair_mem_FP hc
    (machinePair_mem_FP hm
      (machinePair_mem_FP hd
        (machinePair_mem_FP hcols
          (machinePair_mem_FP hfalse machineKuhnStateBound_mem_FP))))

/-! ## Call transition -/

def machineKuhnCurrentColumn (state : List Bool) : List Bool :=
  machineListHead (machineKuhnRemaining state)

def machineKuhnRemainingTail (state : List Bool) : List Bool :=
  machineListTail (machineKuhnRemaining state)

def machineKuhnSeenBit (state : List Bool) : List Bool :=
  machineBoolVectorEntryAtUnary
    (pair (machineKuhnCurrentColumn state) (machineKuhnSeen state))

def machineKuhnSupportBit (state : List Bool) : List Bool :=
  machineRationalSupportBitAtUnary
    (pair (machineKuhnRow state)
      (pair (machineKuhnCurrentColumn state)
        (machineKuhnStateMatrix state)))

def machineKuhnSkipBit (state : List Bool) : List Bool :=
  machineOrBit (machineKuhnSeenBit state)
    (machineNotBit (machineKuhnSupportBit state))

def machineKuhnSeenUpdated (state : List Bool) : List Bool :=
  machineBoolVectorUpdateAtUnary
    (pair (machineKuhnCurrentColumn state)
      (pair [true] (machineKuhnSeen state)))

def machineKuhnMateValue (state : List Bool) : List Bool :=
  machineMateVectorGetAtUnary
    (pair (machineKuhnCurrentColumn state) (machineKuhnMate state))

def machineKuhnMateIsNoneBit (state : List Bool) : List Bool :=
  machineMateValueIsNoneBit (machineKuhnMateValue state)

def machineKuhnSomeCurrentRow (state : List Bool) : List Bool :=
  true :: machineKuhnRow state

def machineKuhnMateSetCurrent (state : List Bool) : List Bool :=
  machineMateVectorUpdateAtUnary
    (pair (machineKuhnCurrentColumn state)
      (pair (machineKuhnSomeCurrentRow state) (machineKuhnMate state)))

def machineKuhnMateClearCurrent (state : List Bool) : List Bool :=
  machineMateVectorUpdateAtUnary
    (pair (machineKuhnCurrentColumn state)
      (pair [false] (machineKuhnMate state)))

def machineKuhnFailureControl (state : List Bool) : List Bool :=
  machineKuhnControlReturn [false] (machineKuhnSeen state) []
    (machineKuhnStack state)

def machineKuhnSkipControl (state : List Bool) : List Bool :=
  machineKuhnControlCall (machineKuhnFuel state)
    (machineKuhnRemainingTail state) (machineKuhnRow state)
    (machineKuhnSeen state) (machineKuhnMate state) (machineKuhnStack state)

def machineKuhnFreeColumnControl (state : List Bool) : List Bool :=
  machineKuhnControlReturn [true] (machineKuhnSeenUpdated state)
    (machineKuhnMateSetCurrent state) (machineKuhnStack state)

def machineKuhnSearchFrameCurrent (state : List Bool) : List Bool :=
  pair [false]
    (machineKuhnSearchFramePack (machineKuhnFuel state)
      (machineKuhnRemainingTail state) (machineKuhnRow state)
      (machineKuhnMate state) (machineKuhnCurrentColumn state))

def machineKuhnPushedSearchStack (state : List Bool) : List Bool :=
  machineKuhnStackPush (machineKuhnSearchFrameCurrent state)
    (machineKuhnStack state)

def machineKuhnOccupiedColumnControl (state : List Bool) : List Bool :=
  machineKuhnControlCall (machineKuhnFuel state).tail
    (machineKuhnStateColumns state)
    (machineMateValueRowUnary (machineKuhnMateValue state))
    (machineKuhnSeenUpdated state) (machineKuhnMateClearCurrent state)
    (machineKuhnPushedSearchStack state)

def machineKuhnProceedControl (state : List Bool) : List Bool :=
  machineIfHead (machineKuhnMateIsNoneBit state)
    (machineKuhnFreeColumnControl state)
    (machineKuhnOccupiedColumnControl state)

def machineKuhnNonterminalCallControl (state : List Bool) : List Bool :=
  machineIfHead (machineKuhnSkipBit state)
    (machineKuhnSkipControl state) (machineKuhnProceedControl state)

def machineKuhnCallControl (state : List Bool) : List Bool :=
  machineIfEmpty (machineKuhnFuel state) (machineKuhnFailureControl state)
    (machineIfEmpty (machineKuhnRemaining state)
      (machineKuhnFailureControl state)
      (machineKuhnNonterminalCallControl state))

/-! ## Return transition -/

def machineKuhnSearchReturnSuccessControl (state : List Bool) : List Bool :=
  let frame := machineKuhnTopFrame state
  let mate := machineMateVectorUpdateAtUnary
    (pair (machineKuhnSearchFrameColumn frame)
      (pair (true :: machineKuhnSearchFrameRow frame)
        (machineKuhnRetMate state)))
  machineKuhnControlReturn [true] (machineKuhnRetSeen state) mate
    (machineKuhnRestStack state)

def machineKuhnSearchReturnFailureControl (state : List Bool) : List Bool :=
  let frame := machineKuhnTopFrame state
  machineKuhnControlCall (machineKuhnSearchFrameFuel frame)
    (machineKuhnSearchFrameRemaining frame)
    (machineKuhnSearchFrameRow frame) (machineKuhnRetSeen state)
    (machineKuhnSearchFrameMate frame) (machineKuhnRestStack state)

def machineKuhnSearchReturnControl (state : List Bool) : List Bool :=
  machineIfHead (machineKuhnRetSuccess state)
    (machineKuhnSearchReturnSuccessControl state)
    (machineKuhnSearchReturnFailureControl state)

def machineKuhnBuildChosenMate (state : List Bool) : List Bool :=
  let frame := machineKuhnTopFrame state
  machineIfHead (machineKuhnRetSuccess state) (machineKuhnRetMate state)
    (machineKuhnBuildFrameFallback frame)

def machineKuhnBuildRows (state : List Bool) : List Bool :=
  machineKuhnBuildFrameRows (machineKuhnTopFrame state)

def machineKuhnBuildNextFrame (state : List Bool) : List Bool :=
  pair [true]
    (machineKuhnBuildFramePack (machineListTail (machineKuhnBuildRows state))
      (machineKuhnBuildChosenMate state))

def machineKuhnBuildNextStack (state : List Bool) : List Bool :=
  machineKuhnStackPush (machineKuhnBuildNextFrame state)
    (machineKuhnRestStack state)

def machineKuhnBuildContinueControl (state : List Bool) : List Bool :=
  machineKuhnControlCall (true :: machineKuhnStateDimension state)
    (machineKuhnStateColumns state)
    (machineListHead (machineKuhnBuildRows state))
    (machineKuhnStateFalseSeen state) (machineKuhnBuildChosenMate state)
    (machineKuhnBuildNextStack state)

def machineKuhnBuildReturnControl (state : List Bool) : List Bool :=
  machineIfEmpty (machineKuhnBuildRows state)
    (machineKuhnControlDone (machineKuhnBuildChosenMate state))
    (machineKuhnBuildContinueControl state)

def machineKuhnNonemptyReturnControl (state : List Bool) : List Bool :=
  machineIfHead (machineKuhnFrameTag (machineKuhnTopFrame state))
    (machineKuhnBuildReturnControl state)
    (machineKuhnSearchReturnControl state)

def machineKuhnReturnControl (state : List Bool) : List Bool :=
  machineIfEmpty (machineKuhnRetStack state) (machineKuhnControl state)
    (machineKuhnNonemptyReturnControl state)

def machineKuhnDoneControl (state : List Bool) : List Bool :=
  machineKuhnControl state

/-- The un-clamped next control word. -/
def machineKuhnNextControl (state : List Bool) : List Bool :=
  machineIfHead (machineKuhnControlTag (machineKuhnControl state))
    (machineIfHead (machineKuhnControlIsDoneBit (machineKuhnControl state))
      (machineKuhnDoneControl state) (machineKuhnReturnControl state))
    (machineKuhnCallControl state)

/-- One total finite-word transition.  Every variable field is clamped to the
fixed bound carried by the input state. -/
def machineKuhnStep (state : List Bool) : List Bool :=
  machineKuhnWithControl state (machineKuhnNextControl state)

/-! ## Polynomial-time closure proof -/

theorem machineKuhnCurrentColumn_mem_FP :
    machineKuhnCurrentColumn ∈ Complexity.FP := by
  simpa only [machineKuhnCurrentColumn] using!
    machineCompose_mem_FP machineKuhnRemaining_mem_FP machineListHead_mem_FP

theorem machineKuhnRemainingTail_mem_FP :
    machineKuhnRemainingTail ∈ Complexity.FP := by
  simpa only [machineKuhnRemainingTail] using!
    machineCompose_mem_FP machineKuhnRemaining_mem_FP machineListTail_mem_FP

theorem machineKuhnSeenBit_mem_FP : machineKuhnSeenBit ∈ Complexity.FP := by
  have hp := machinePair_mem_FP machineKuhnCurrentColumn_mem_FP
    machineKuhnSeen_mem_FP
  simpa only [machineKuhnSeenBit] using!
    machineCompose_mem_FP hp machineBoolVectorEntryAtUnary_mem_FP

theorem machineKuhnSupportBit_mem_FP :
    machineKuhnSupportBit ∈ Complexity.FP := by
  have hp := machinePair_mem_FP machineKuhnRow_mem_FP
    (machinePair_mem_FP machineKuhnCurrentColumn_mem_FP
      machineKuhnStateMatrix_mem_FP)
  simpa only [machineKuhnSupportBit] using!
    machineCompose_mem_FP hp machineRationalSupportBitAtUnary_mem_FP

theorem machineKuhnSkipBit_mem_FP : machineKuhnSkipBit ∈ Complexity.FP := by
  have hnot := machineNotBit_mem_FP machineKuhnSupportBit_mem_FP
  exact machineOrBit_mem_FP machineKuhnSeenBit_mem_FP hnot

theorem machineKuhnSeenUpdated_mem_FP :
    machineKuhnSeenUpdated ∈ Complexity.FP := by
  have hp := machinePair_mem_FP machineKuhnCurrentColumn_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [true]) machineKuhnSeen_mem_FP)
  simpa only [machineKuhnSeenUpdated] using!
    machineCompose_mem_FP hp machineBoolVectorUpdateAtUnary_mem_FP

theorem machineKuhnMateValue_mem_FP : machineKuhnMateValue ∈ Complexity.FP := by
  have hp := machinePair_mem_FP machineKuhnCurrentColumn_mem_FP
    machineKuhnMate_mem_FP
  simpa only [machineKuhnMateValue] using!
    machineCompose_mem_FP hp machineMateVectorGetAtUnary_mem_FP

theorem machineKuhnMateIsNoneBit_mem_FP :
    machineKuhnMateIsNoneBit ∈ Complexity.FP := by
  simpa only [machineKuhnMateIsNoneBit] using!
    machineCompose_mem_FP machineKuhnMateValue_mem_FP
      machineMateValueIsNoneBit_mem_FP

theorem machineKuhnSomeCurrentRow_mem_FP :
    machineKuhnSomeCurrentRow ∈ Complexity.FP := by
  simpa only [machineKuhnSomeCurrentRow] using!
    machineCompose_mem_FP machineKuhnRow_mem_FP (machinePrepend_mem_FP true)

theorem machineKuhnMateSetCurrent_mem_FP :
    machineKuhnMateSetCurrent ∈ Complexity.FP := by
  have hp := machinePair_mem_FP machineKuhnCurrentColumn_mem_FP
    (machinePair_mem_FP machineKuhnSomeCurrentRow_mem_FP machineKuhnMate_mem_FP)
  simpa only [machineKuhnMateSetCurrent] using!
    machineCompose_mem_FP hp machineMateVectorUpdateAtUnary_mem_FP

theorem machineKuhnMateClearCurrent_mem_FP :
    machineKuhnMateClearCurrent ∈ Complexity.FP := by
  have hp := machinePair_mem_FP machineKuhnCurrentColumn_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [false]) machineKuhnMate_mem_FP)
  simpa only [machineKuhnMateClearCurrent] using!
    machineCompose_mem_FP hp machineMateVectorUpdateAtUnary_mem_FP

theorem machineKuhnFailureControl_mem_FP :
    machineKuhnFailureControl ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [true, false])
    (machinePair_mem_FP (machineConst_mem_FP [false])
      (machinePair_mem_FP machineKuhnSeen_mem_FP
        (machinePair_mem_FP (machineConst_mem_FP []) machineKuhnStack_mem_FP)))

theorem machineKuhnSkipControl_mem_FP : machineKuhnSkipControl ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP machineKuhnFuel_mem_FP
      (machinePair_mem_FP machineKuhnRemainingTail_mem_FP
        (machinePair_mem_FP machineKuhnRow_mem_FP
          (machinePair_mem_FP machineKuhnSeen_mem_FP
            (machinePair_mem_FP machineKuhnMate_mem_FP
              machineKuhnStack_mem_FP)))))

theorem machineKuhnFreeColumnControl_mem_FP :
    machineKuhnFreeColumnControl ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [true, false])
    (machinePair_mem_FP (machineConst_mem_FP [true])
      (machinePair_mem_FP machineKuhnSeenUpdated_mem_FP
        (machinePair_mem_FP machineKuhnMateSetCurrent_mem_FP
          machineKuhnStack_mem_FP)))

theorem machineKuhnSearchFrameCurrent_mem_FP :
    machineKuhnSearchFrameCurrent ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP machineKuhnFuel_mem_FP
      (machinePair_mem_FP machineKuhnRemainingTail_mem_FP
        (machinePair_mem_FP machineKuhnRow_mem_FP
          (machinePair_mem_FP machineKuhnMate_mem_FP
            machineKuhnCurrentColumn_mem_FP))))

theorem machineKuhnPushedSearchStack_mem_FP :
    machineKuhnPushedSearchStack ∈ Complexity.FP :=
  machinePair_mem_FP machineKuhnSearchFrameCurrent_mem_FP
    machineKuhnStack_mem_FP

theorem machineKuhnOccupiedColumnControl_mem_FP :
    machineKuhnOccupiedColumnControl ∈ Complexity.FP := by
  have hfuelTail := machineCompose_mem_FP machineKuhnFuel_mem_FP
    machineTail_mem_FP
  have holdRow := machineCompose_mem_FP machineKuhnMateValue_mem_FP
    machineMateValueRowUnary_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP hfuelTail
      (machinePair_mem_FP machineKuhnStateColumns_mem_FP
        (machinePair_mem_FP holdRow
          (machinePair_mem_FP machineKuhnSeenUpdated_mem_FP
            (machinePair_mem_FP machineKuhnMateClearCurrent_mem_FP
              machineKuhnPushedSearchStack_mem_FP)))))

theorem machineKuhnProceedControl_mem_FP :
    machineKuhnProceedControl ∈ Complexity.FP :=
  machineIfHead_mem_FP machineKuhnMateIsNoneBit_mem_FP
    machineKuhnFreeColumnControl_mem_FP machineKuhnOccupiedColumnControl_mem_FP

theorem machineKuhnNonterminalCallControl_mem_FP :
    machineKuhnNonterminalCallControl ∈ Complexity.FP :=
  machineIfHead_mem_FP machineKuhnSkipBit_mem_FP machineKuhnSkipControl_mem_FP
    machineKuhnProceedControl_mem_FP

theorem machineKuhnCallControl_mem_FP : machineKuhnCallControl ∈ Complexity.FP := by
  have hinner := machineIfEmpty_mem_FP machineKuhnRemaining_mem_FP
    machineKuhnFailureControl_mem_FP machineKuhnNonterminalCallControl_mem_FP
  exact machineIfEmpty_mem_FP machineKuhnFuel_mem_FP
    machineKuhnFailureControl_mem_FP hinner

theorem machineKuhnSearchReturnSuccessControl_mem_FP :
    machineKuhnSearchReturnSuccessControl ∈ Complexity.FP := by
  have hcol := machineCompose_mem_FP machineKuhnTopFrame_mem_FP
    machineKuhnSearchFrameColumn_mem_FP
  have hrow := machineCompose_mem_FP machineKuhnTopFrame_mem_FP
    machineKuhnSearchFrameRow_mem_FP
  have hsome := machineCompose_mem_FP hrow (machinePrepend_mem_FP true)
  have hp := machinePair_mem_FP hcol
    (machinePair_mem_FP hsome machineKuhnRetMate_mem_FP)
  have hmate := machineCompose_mem_FP hp machineMateVectorUpdateAtUnary_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [true, false])
    (machinePair_mem_FP (machineConst_mem_FP [true])
      (machinePair_mem_FP machineKuhnRetSeen_mem_FP
        (machinePair_mem_FP hmate machineKuhnRestStack_mem_FP)))

theorem machineKuhnSearchReturnFailureControl_mem_FP :
    machineKuhnSearchReturnFailureControl ∈ Complexity.FP := by
  have hfield (f : List Bool → List Bool) (hf : f ∈ Complexity.FP) :
      (fun state ↦ f (machineKuhnTopFrame state)) ∈ Complexity.FP :=
    by simpa only using!
      machineCompose_mem_FP machineKuhnTopFrame_mem_FP hf
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP
      (hfield machineKuhnSearchFrameFuel machineKuhnSearchFrameFuel_mem_FP)
      (machinePair_mem_FP
        (hfield machineKuhnSearchFrameRemaining
          machineKuhnSearchFrameRemaining_mem_FP)
        (machinePair_mem_FP
          (hfield machineKuhnSearchFrameRow machineKuhnSearchFrameRow_mem_FP)
          (machinePair_mem_FP machineKuhnRetSeen_mem_FP
            (machinePair_mem_FP
              (hfield machineKuhnSearchFrameMate
                machineKuhnSearchFrameMate_mem_FP)
              machineKuhnRestStack_mem_FP)))))

theorem machineKuhnSearchReturnControl_mem_FP :
    machineKuhnSearchReturnControl ∈ Complexity.FP :=
  machineIfHead_mem_FP machineKuhnRetSuccess_mem_FP
    machineKuhnSearchReturnSuccessControl_mem_FP
    machineKuhnSearchReturnFailureControl_mem_FP

theorem machineKuhnBuildChosenMate_mem_FP :
    machineKuhnBuildChosenMate ∈ Complexity.FP := by
  have hfallback := machineCompose_mem_FP machineKuhnTopFrame_mem_FP
    machineKuhnBuildFrameFallback_mem_FP
  exact machineIfHead_mem_FP machineKuhnRetSuccess_mem_FP
    machineKuhnRetMate_mem_FP hfallback

theorem machineKuhnBuildRows_mem_FP : machineKuhnBuildRows ∈ Complexity.FP := by
  simpa only [machineKuhnBuildRows] using!
    machineCompose_mem_FP machineKuhnTopFrame_mem_FP
      machineKuhnBuildFrameRows_mem_FP

theorem machineKuhnBuildNextFrame_mem_FP :
    machineKuhnBuildNextFrame ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineKuhnBuildRows_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [true])
    (machinePair_mem_FP htail machineKuhnBuildChosenMate_mem_FP)

theorem machineKuhnBuildNextStack_mem_FP :
    machineKuhnBuildNextStack ∈ Complexity.FP :=
  machinePair_mem_FP machineKuhnBuildNextFrame_mem_FP
    machineKuhnRestStack_mem_FP

theorem machineKuhnBuildContinueControl_mem_FP :
    machineKuhnBuildContinueControl ∈ Complexity.FP := by
  have hfuel := machineCompose_mem_FP machineKuhnStateDimension_mem_FP
    (machinePrepend_mem_FP true)
  have hrow := machineCompose_mem_FP machineKuhnBuildRows_mem_FP
    machineListHead_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP hfuel
      (machinePair_mem_FP machineKuhnStateColumns_mem_FP
        (machinePair_mem_FP hrow
          (machinePair_mem_FP machineKuhnStateFalseSeen_mem_FP
            (machinePair_mem_FP machineKuhnBuildChosenMate_mem_FP
              machineKuhnBuildNextStack_mem_FP)))))

theorem machineKuhnBuildReturnControl_mem_FP :
    machineKuhnBuildReturnControl ∈ Complexity.FP := by
  have hdone := machinePair_mem_FP (machineConst_mem_FP [true, true])
    machineKuhnBuildChosenMate_mem_FP
  exact machineIfEmpty_mem_FP machineKuhnBuildRows_mem_FP hdone
    machineKuhnBuildContinueControl_mem_FP

theorem machineKuhnNonemptyReturnControl_mem_FP :
    machineKuhnNonemptyReturnControl ∈ Complexity.FP := by
  have htag := machineCompose_mem_FP machineKuhnTopFrame_mem_FP
    machineKuhnFrameTag_mem_FP
  exact machineIfHead_mem_FP htag machineKuhnBuildReturnControl_mem_FP
    machineKuhnSearchReturnControl_mem_FP

theorem machineKuhnReturnControl_mem_FP :
    machineKuhnReturnControl ∈ Complexity.FP :=
  machineIfEmpty_mem_FP machineKuhnRetStack_mem_FP machineKuhnControl_mem_FP
    machineKuhnNonemptyReturnControl_mem_FP

theorem machineKuhnDoneControl_mem_FP :
    machineKuhnDoneControl ∈ Complexity.FP := machineKuhnControl_mem_FP

theorem machineKuhnNextControl_mem_FP :
    machineKuhnNextControl ∈ Complexity.FP := by
  have htag := machineCompose_mem_FP machineKuhnControl_mem_FP
    machineKuhnControlTag_mem_FP
  have hdoneBit := machineCompose_mem_FP machineKuhnControl_mem_FP
    machineKuhnControlIsDoneBit_mem_FP
  have hretOrDone := machineIfHead_mem_FP hdoneBit
    machineKuhnDoneControl_mem_FP machineKuhnReturnControl_mem_FP
  exact machineIfHead_mem_FP htag hretOrDone machineKuhnCallControl_mem_FP

theorem machineKuhnStep_mem_FP : machineKuhnStep ∈ Complexity.FP := by
  simpa only [machineKuhnStep] using!
    machineKuhnWithControl_mem_FP machineKuhnNextControl_mem_FP

end BeyondBethe

/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07D

/-! # GapCVP proof, part 07, continuation 05 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyForbiddenWholeClauseSourceCert

open Computability Turing GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.SourceFourFamilyBooleanPredicateTM

open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM

open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM

/-- GapCVP reduction support. -/
def fiveForbiddenRawSourceMinimumWord
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  if (fiveForbiddenRawSourceLessMarker
      first second input).headD false
    then first input else second input

/-- GapCVP reduction support. -/
def fiveForbiddenRawSourceMaximumWord
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  if (fiveForbiddenRawSourceLessMarker
      first second input).headD false
    then second input else first input

private noncomputable def fiveFamilyForbiddenRawSourceLessMarkerComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (fiveForbiddenRawSourceLessMarker first second) :=
  fourFamilyComputedUnaryLessBitComputable hfirst hsecond

private noncomputable def fiveForbiddenRawSourceMinimumComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (fiveForbiddenRawSourceMinimumWord first second) := by
  let marker := fiveForbiddenRawSourceLessMarker first second
  let opposite := fiveForbiddenRawSourceNotLessMarker first second
  have hmarker := fiveFamilyForbiddenRawSourceLessMarkerComputable
    hfirst hsecond
  have hopposite := fourFamilyBooleanNotOutputComputable hmarker
  have lower := fiveForbiddenOneBitGuardedComputable
    hmarker (fiveForbiddenRawSourceLessMarker_length
      first second) hfirst
  have upper := fiveForbiddenOneBitGuardedComputable
    hopposite (fiveFamilyForbiddenRawSourceNotLessMarker_length
      first second) hsecond
  have physical := pointwiseAppendComputable lower upper
  have hequality :
      (fun input : List Bool =>
        fiveForbiddenOneBitGuardedWord marker first input ++
          fiveForbiddenOneBitGuardedWord
            opposite second input) =
        fiveForbiddenRawSourceMinimumWord first second := by
    funext input
    obtain ⟨bit, hbit⟩ := fiveFamilyForbiddenOneBit_exists
      (fiveForbiddenRawSourceLessMarker first second)
      (fiveForbiddenRawSourceLessMarker_length
        first second) input
    have hnot := fourFamilyBooleanNotOutput_bit
      (fiveForbiddenRawSourceLessMarker first second)
      input bit hbit
    change opposite input = [!bit] at hnot
    cases bit <;>
      simp [fiveForbiddenOneBitGuardedWord,
        fiveForbiddenRawSourceMinimumWord,
        marker, hbit, hnot]
  rw [← hequality]
  exact physical

private noncomputable def fiveForbiddenRawSourceMaximumComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (fiveForbiddenRawSourceMaximumWord first second) := by
  let marker := fiveForbiddenRawSourceLessMarker first second
  let opposite := fiveForbiddenRawSourceNotLessMarker first second
  have hmarker := fiveFamilyForbiddenRawSourceLessMarkerComputable
    hfirst hsecond
  have hopposite := fourFamilyBooleanNotOutputComputable hmarker
  have upper := fiveForbiddenOneBitGuardedComputable
    hmarker (fiveForbiddenRawSourceLessMarker_length
      first second) hsecond
  have lower := fiveForbiddenOneBitGuardedComputable
    hopposite (fiveFamilyForbiddenRawSourceNotLessMarker_length
      first second) hfirst
  have physical := pointwiseAppendComputable upper lower
  have hequality :
      (fun input : List Bool =>
        fiveForbiddenOneBitGuardedWord marker second input ++
          fiveForbiddenOneBitGuardedWord
            opposite first input) =
        fiveForbiddenRawSourceMaximumWord first second := by
    funext input
    obtain ⟨bit, hbit⟩ := fiveFamilyForbiddenOneBit_exists
      (fiveForbiddenRawSourceLessMarker first second)
      (fiveForbiddenRawSourceLessMarker_length
        first second) input
    have hnot := fourFamilyBooleanNotOutput_bit
      (fiveForbiddenRawSourceLessMarker first second)
      input bit hbit
    change opposite input = [!bit] at hnot
    cases bit <;>
      simp [fiveForbiddenOneBitGuardedWord,
        fiveForbiddenRawSourceMaximumWord,
        marker, hbit, hnot]
  rw [← hequality]
  exact physical

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowSlotWord
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate)
    (symbol : ℕ) : List Bool → List Bool :=
  fiveForbiddenCoordinateSourceVariableCode
    grid coordinate symbol

private noncomputable def fiveForbiddenRawWindowSlotComputable
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate)
    (symbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowSlotWord
        grid coordinate symbol) :=
  fiveFamilyForbiddenCoordinateSourceVariableCodeComputable
    grid coordinate symbol

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowFirstLowWord
    (grid : Polynomial ℕ) (leftSymbol centerSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMinimumWord
    (fiveForbiddenRawWindowSlotWord grid .left leftSymbol)
    (fiveForbiddenRawWindowSlotWord grid .center centerSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowFirstLowComputable
    (grid : Polynomial ℕ) (leftSymbol centerSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowFirstLowWord
        grid leftSymbol centerSymbol) :=
  fiveForbiddenRawSourceMinimumComputable
    (fiveForbiddenRawWindowSlotComputable
      grid .left leftSymbol)
    (fiveForbiddenRawWindowSlotComputable
      grid .center centerSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowFirstHighWord
    (grid : Polynomial ℕ) (leftSymbol centerSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMaximumWord
    (fiveForbiddenRawWindowSlotWord grid .left leftSymbol)
    (fiveForbiddenRawWindowSlotWord grid .center centerSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowFirstHighComputable
    (grid : Polynomial ℕ) (leftSymbol centerSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowFirstHighWord
        grid leftSymbol centerSymbol) :=
  fiveForbiddenRawSourceMaximumComputable
    (fiveForbiddenRawWindowSlotComputable
      grid .left leftSymbol)
    (fiveForbiddenRawWindowSlotComputable
      grid .center centerSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowSecondLowWord
    (grid : Polynomial ℕ) (rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMinimumWord
    (fiveForbiddenRawWindowSlotWord grid .right rightSymbol)
    (fiveForbiddenRawWindowSlotWord grid .next nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowSecondLowComputable
    (grid : Polynomial ℕ) (rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowSecondLowWord
        grid rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMinimumComputable
    (fiveForbiddenRawWindowSlotComputable
      grid .right rightSymbol)
    (fiveForbiddenRawWindowSlotComputable
      grid .next nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowSecondHighWord
    (grid : Polynomial ℕ) (rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMaximumWord
    (fiveForbiddenRawWindowSlotWord grid .right rightSymbol)
    (fiveForbiddenRawWindowSlotWord grid .next nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowSecondHighComputable
    (grid : Polynomial ℕ) (rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowSecondHighWord
        grid rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMaximumComputable
    (fiveForbiddenRawWindowSlotComputable
      grid .right rightSymbol)
    (fiveForbiddenRawWindowSlotComputable
      grid .next nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowOuterLowWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMinimumWord
    (fiveForbiddenRawWindowFirstLowWord
      grid leftSymbol centerSymbol)
    (fiveForbiddenRawWindowSecondLowWord
      grid rightSymbol nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowOuterLowComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowOuterLowWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMinimumComputable
    (fiveFamilyForbiddenRawWindowFirstLowComputable
      grid leftSymbol centerSymbol)
    (fiveFamilyForbiddenRawWindowSecondLowComputable
      grid rightSymbol nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowMiddleLeftWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMaximumWord
    (fiveForbiddenRawWindowFirstLowWord
      grid leftSymbol centerSymbol)
    (fiveForbiddenRawWindowSecondLowWord
      grid rightSymbol nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowMiddleLeftComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowMiddleLeftWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMaximumComputable
    (fiveFamilyForbiddenRawWindowFirstLowComputable
      grid leftSymbol centerSymbol)
    (fiveFamilyForbiddenRawWindowSecondLowComputable
      grid rightSymbol nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowMiddleRightWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMinimumWord
    (fiveForbiddenRawWindowFirstHighWord
      grid leftSymbol centerSymbol)
    (fiveForbiddenRawWindowSecondHighWord
      grid rightSymbol nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowMiddleRightComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowMiddleRightWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMinimumComputable
    (fiveFamilyForbiddenRawWindowFirstHighComputable
      grid leftSymbol centerSymbol)
    (fiveFamilyForbiddenRawWindowSecondHighComputable
      grid rightSymbol nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowOuterHighWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMaximumWord
    (fiveForbiddenRawWindowFirstHighWord
      grid leftSymbol centerSymbol)
    (fiveForbiddenRawWindowSecondHighWord
      grid rightSymbol nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowOuterHighComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowOuterHighWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMaximumComputable
    (fiveFamilyForbiddenRawWindowFirstHighComputable
      grid leftSymbol centerSymbol)
    (fiveFamilyForbiddenRawWindowSecondHighComputable
      grid rightSymbol nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowMiddleLowWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMinimumWord
    (fiveForbiddenRawWindowMiddleLeftWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveForbiddenRawWindowMiddleRightWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowMiddleLowComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowMiddleLowWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMinimumComputable
    (fiveFamilyForbiddenRawWindowMiddleLeftComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveFamilyForbiddenRawWindowMiddleRightComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)

/-- GapCVP reduction support. -/
def fiveForbiddenRawWindowMiddleHighWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    List Bool → List Bool :=
  fiveForbiddenRawSourceMaximumWord
    (fiveForbiddenRawWindowMiddleLeftWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveForbiddenRawWindowMiddleRightWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)

private noncomputable def fiveFamilyForbiddenRawWindowMiddleHighComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenRawWindowMiddleHighWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) :=
  fiveForbiddenRawSourceMaximumComputable
    (fiveFamilyForbiddenRawWindowMiddleLeftComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveFamilyForbiddenRawWindowMiddleRightComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)

end CNFFiveFamilyForbiddenWholeClauseSourceCert

namespace CNFFiveFamilyForbiddenWholeClauseExactSourceTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert

private def fiveForbiddenRawStrictPayloadWord
    (previous current payload : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  fiveForbiddenOneBitGuardedWord
    (fiveForbiddenRawSourceLessMarker previous current)
    payload input

private noncomputable def fiveFamilyForbiddenRawStrictPayloadComputable
    {previous current payload : List Bool → List Bool}
    (hprevious : BitTM previous)
    (hcurrent : BitTM current)
    (hpayload : BitTM payload) :
    BitTM
      (fiveForbiddenRawStrictPayloadWord
        previous current payload) :=
  fiveForbiddenOneBitGuardedComputable
    (fiveFamilyForbiddenRawSourceLessMarkerComputable
      hprevious hcurrent)
    (fiveForbiddenRawSourceLessMarker_length
      previous current)
    hpayload

/-- GapCVP reduction support. -/
def fiveForbiddenRawDistinctPayloadWord
    (first second third fourth payload : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  payload (first input) ++
    fiveForbiddenRawStrictPayloadWord first second
      (fun source => payload (second source)) input ++
    fiveForbiddenRawStrictPayloadWord second third
      (fun source => payload (third source)) input ++
    fiveForbiddenRawStrictPayloadWord third fourth
      (fun source => payload (fourth source)) input

private noncomputable def fiveFamilyForbiddenRawDistinctPayloadComputable
    {first second third fourth payload : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second)
    (hthird : BitTM third)
    (hfourth : BitTM fourth)
    (hpayload : BitTM payload) :
    BitTM
      (fiveForbiddenRawDistinctPayloadWord
        first second third fourth payload) := by
  have firstPayload := GapCVP.TMComposition.computableInPolyTime
    hfirst hpayload
  have secondPayload := GapCVP.TMComposition.computableInPolyTime
    hsecond hpayload
  have thirdPayload := GapCVP.TMComposition.computableInPolyTime
    hthird hpayload
  have fourthPayload := GapCVP.TMComposition.computableInPolyTime
    hfourth hpayload
  have secondGuard := fiveFamilyForbiddenRawStrictPayloadComputable
    hfirst hsecond secondPayload
  have thirdGuard := fiveFamilyForbiddenRawStrictPayloadComputable
    hsecond hthird thirdPayload
  have fourthGuard := fiveFamilyForbiddenRawStrictPayloadComputable
    hthird hfourth fourthPayload
  have left := pointwiseAppendComputable
    firstPayload secondGuard
  have right := pointwiseAppendComputable
    thirdGuard fourthGuard
  have physical := pointwiseAppendComputable left right
  have hequality :
      (fun input : List Bool =>
        (payload (first input) ++
          fiveForbiddenRawStrictPayloadWord first second
            (fun source => payload (second source)) input) ++
        (fiveForbiddenRawStrictPayloadWord second third
            (fun source => payload (third source)) input ++
          fiveForbiddenRawStrictPayloadWord third fourth
            (fun source => payload (fourth source)) input)) =
        fiveForbiddenRawDistinctPayloadWord
          first second third fourth payload := by
    funext input
    simp only [List.append_assoc, fiveForbiddenRawDistinctPayloadWord]
  rw [← hequality]
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveForbiddenExactWindowDistinctPayloadWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ)
    (payload : List Bool → List Bool) : List Bool → List Bool :=
  fiveForbiddenRawDistinctPayloadWord
    (fiveForbiddenRawWindowOuterLowWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveForbiddenRawWindowMiddleLowWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveForbiddenRawWindowMiddleHighWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveForbiddenRawWindowOuterHighWord
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    payload

private noncomputable def fiveFamilyForbiddenExactWindowDistinctPayloadComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ)
    {payload : List Bool → List Bool}
    (hpayload : BitTM payload) :
    BitTM
      (fiveForbiddenExactWindowDistinctPayloadWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol payload) :=
  fiveFamilyForbiddenRawDistinctPayloadComputable
    (fiveFamilyForbiddenRawWindowOuterLowComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveFamilyForbiddenRawWindowMiddleLowComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveFamilyForbiddenRawWindowMiddleHighComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    (fiveFamilyForbiddenRawWindowOuterHighComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol)
    hpayload

/-- GapCVP reduction support. -/
def fiveForbiddenExactWindowWholeClauseRecordWord
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (fiveForbiddenExactWindowDistinctPayloadWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol
        (tableauSourceSignedLiteralDescriptorWord false) input) ++
    lengthPrefixedWord
      (fiveForbiddenExactWindowDistinctPayloadWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol
        (duplicatedUnarySignedLiteralCodeWord false) input) ++
    lengthPrefixedWord
      (fiveForbiddenExactWindowDistinctPayloadWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol
        (fun _ => [true]) input)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyForbiddenExactWindowWholeClauseRecordComputable
    (grid : Polynomial ℕ)
    (leftSymbol centerSymbol rightSymbol nextSymbol : ℕ) :
    BitTM
      (fiveForbiddenExactWindowWholeClauseRecordWord
        grid leftSymbol centerSymbol rightSymbol nextSymbol) := by
  have descriptors := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyForbiddenExactWindowDistinctPayloadComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol
      (tableauSourceSignedLiteralDescriptorComputable false))
    structuralPrefixWriterComputable
  have codes := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyForbiddenExactWindowDistinctPayloadComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol
      (duplicatedUnarySignedLiteralCodeComputable false))
    structuralPrefixWriterComputable
  have count := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyForbiddenExactWindowDistinctPayloadComputable
      grid leftSymbol centerSymbol rightSymbol nextSymbol
      (constantWordComputable [true]))
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable
    descriptors (pointwiseAppendComputable codes count)
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (fiveForbiddenExactWindowDistinctPayloadWord
            grid leftSymbol centerSymbol rightSymbol nextSymbol
            (tableauSourceSignedLiteralDescriptorWord false) input) ++
        lengthPrefixedWord
          (fiveForbiddenExactWindowDistinctPayloadWord
            grid leftSymbol centerSymbol rightSymbol nextSymbol
            (duplicatedUnarySignedLiteralCodeWord false) input) ++
        lengthPrefixedWord
          (fiveForbiddenExactWindowDistinctPayloadWord
            grid leftSymbol centerSymbol rightSymbol nextSymbol
            (fun _ => [true]) input))
  simpa only [List.append_assoc, Function.comp_apply] using physical

theorem fiveForbiddenRawSourceMinimumWord_valid
    {α : Type} [Encodable α]
    (first second : List Bool → List Bool)
    (input : List Bool) (firstAtom secondAtom : α)
    (hfirst : first input =
      List.replicate (Encodable.encode firstAtom) true)
    (hsecond : second input =
      List.replicate (Encodable.encode secondAtom) true) :
    fiveForbiddenRawSourceMinimumWord
      first second input =
      List.replicate
        (Encodable.encode
          (fiveFamilyForbiddenEncodedMinimum
            firstAtom secondAtom)) true := by
  have hmarker := fourFamilyComputedUnaryLessBitOutput_valid
    first second input
    (Encodable.encode firstAtom)
    (Encodable.encode secondAtom)
    hfirst hsecond
  unfold fiveForbiddenRawSourceMinimumWord
    fiveFamilyForbiddenEncodedMinimum
  change fiveForbiddenRawSourceLessMarker
    first second input =
      [decide (Encodable.encode firstAtom <
        Encodable.encode secondAtom)] at hmarker
  rw [hmarker]
  by_cases horder :
      Encodable.encode firstAtom < Encodable.encode secondAtom <;>
    simp [horder, hfirst, hsecond]

theorem fiveForbiddenRawSourceMaximumWord_valid
    {α : Type} [Encodable α]
    (first second : List Bool → List Bool)
    (input : List Bool) (firstAtom secondAtom : α)
    (hfirst : first input =
      List.replicate (Encodable.encode firstAtom) true)
    (hsecond : second input =
      List.replicate (Encodable.encode secondAtom) true) :
    fiveForbiddenRawSourceMaximumWord
      first second input =
      List.replicate
        (Encodable.encode
          (fiveFamilyForbiddenEncodedMaximum
            firstAtom secondAtom)) true := by
  have hmarker := fourFamilyComputedUnaryLessBitOutput_valid
    first second input
    (Encodable.encode firstAtom)
    (Encodable.encode secondAtom)
    hfirst hsecond
  unfold fiveForbiddenRawSourceMaximumWord
    fiveFamilyForbiddenEncodedMaximum
  change fiveForbiddenRawSourceLessMarker
    first second input =
      [decide (Encodable.encode firstAtom <
        Encodable.encode secondAtom)] at hmarker
  rw [hmarker]
  by_cases horder :
      Encodable.encode firstAtom < Encodable.encode secondAtom <;>
    simp [horder, hfirst, hsecond]

private theorem encodeLT_iff_ne_of_le
    {α : Type} [Encodable α] {first second : α}
    (ordered : Encodable.encode first ≤ Encodable.encode second) :
    Encodable.encode first < Encodable.encode second ↔ first ≠ second := by
  constructor
  · exact fun less equal => by subst second; omega
  · intro unequal
    have codesUnequal : Encodable.encode first ≠ Encodable.encode second :=
      fun equal => unequal (Encodable.encode_injective equal)
    omega

theorem fiveFamilyForbiddenRawDistinctPayloadWord_valid
    {α : Type} [Encodable α] [DecidableEq α]
    (first second third fourth payload : List Bool → List Bool)
    (input : List Bool)
    (firstAtom secondAtom thirdAtom fourthAtom : α)
    (output : α → List Bool)
    (hfirst : first input =
      List.replicate (Encodable.encode firstAtom) true)
    (hsecond : second input =
      List.replicate (Encodable.encode secondAtom) true)
    (hthird : third input =
      List.replicate (Encodable.encode thirdAtom) true)
    (hfourth : fourth input =
      List.replicate (Encodable.encode fourthAtom) true)
    (hpayload : ∀ atom : α,
      payload (List.replicate (Encodable.encode atom) true) =
        output atom)
    (hordered :
      [firstAtom, secondAtom, thirdAtom, fourthAtom].Pairwise
        (fun left right =>
          Encodable.encode left ≤ Encodable.encode right)) :
    fiveForbiddenRawDistinctPayloadWord
      first second third fourth payload input =
        [firstAtom, secondAtom, thirdAtom, fourthAtom].dedup.flatMap
          output := by
  have hfirstSecond := fourFamilyComputedUnaryLessBitOutput_valid
    first second input
    (Encodable.encode firstAtom) (Encodable.encode secondAtom)
    hfirst hsecond
  have hsecondThird := fourFamilyComputedUnaryLessBitOutput_valid
    second third input
    (Encodable.encode secondAtom) (Encodable.encode thirdAtom)
    hsecond hthird
  have hthirdFourth := fourFamilyComputedUnaryLessBitOutput_valid
    third fourth input
    (Encodable.encode thirdAtom) (Encodable.encode fourthAtom)
    hthird hfourth
  change fiveForbiddenRawSourceLessMarker
    first second input =
      [decide (Encodable.encode firstAtom <
        Encodable.encode secondAtom)] at hfirstSecond
  change fiveForbiddenRawSourceLessMarker
    second third input =
      [decide (Encodable.encode secondAtom <
        Encodable.encode thirdAtom)] at hsecondThird
  change fiveForbiddenRawSourceLessMarker
    third fourth input =
      [decide (Encodable.encode thirdAtom <
        Encodable.encode fourthAtom)] at hthirdFourth
  have hfirstSecondLE :
      Encodable.encode firstAtom ≤ Encodable.encode secondAtom :=
    (List.pairwise_cons.mp hordered).1
      secondAtom (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])
  have hsecondThirdLE :
      Encodable.encode secondAtom ≤ Encodable.encode thirdAtom :=
    (List.pairwise_cons.mp
      (List.pairwise_cons.mp hordered).2).1
      thirdAtom (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])
  have hthirdFourthLE :
      Encodable.encode thirdAtom ≤ Encodable.encode fourthAtom :=
    (List.pairwise_cons.mp
      (List.pairwise_cons.mp
        (List.pairwise_cons.mp hordered).2).2).1
      fourthAtom (by simp only [List.mem_cons, List.not_mem_nil, or_false])
  have hfirstSecondLT :
      (Encodable.encode firstAtom <
        Encodable.encode secondAtom) ↔
        firstAtom ≠ secondAtom :=
    encodeLT_iff_ne_of_le hfirstSecondLE
  have hsecondThirdLT :
      (Encodable.encode secondAtom <
        Encodable.encode thirdAtom) ↔
        secondAtom ≠ thirdAtom :=
    encodeLT_iff_ne_of_le hsecondThirdLE
  have hthirdFourthLT :
      (Encodable.encode thirdAtom <
        Encodable.encode fourthAtom) ↔
        thirdAtom ≠ fourthAtom :=
    encodeLT_iff_ne_of_le hthirdFourthLE
  have hfirstThirdEq : firstAtom = thirdAtom ↔
      firstAtom = secondAtom ∧ secondAtom = thirdAtom := by
    constructor
    · intro hequal
      have hcodes := congrArg Encodable.encode hequal
      have hfirst : Encodable.encode firstAtom =
          Encodable.encode secondAtom := by omega
      have hsecond : Encodable.encode secondAtom =
          Encodable.encode thirdAtom := by omega
      exact ⟨Encodable.encode_injective hfirst,
        Encodable.encode_injective hsecond⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hsecondFourthEq : secondAtom = fourthAtom ↔
      secondAtom = thirdAtom ∧ thirdAtom = fourthAtom := by
    constructor
    · intro hequal
      have hcodes := congrArg Encodable.encode hequal
      have hsecond : Encodable.encode secondAtom =
          Encodable.encode thirdAtom := by omega
      have hthird : Encodable.encode thirdAtom =
          Encodable.encode fourthAtom := by omega
      exact ⟨Encodable.encode_injective hsecond,
        Encodable.encode_injective hthird⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hfirstFourthEq : firstAtom = fourthAtom ↔
      firstAtom = secondAtom ∧
        secondAtom = thirdAtom ∧ thirdAtom = fourthAtom := by
    constructor
    · intro hequal
      have hcodes := congrArg Encodable.encode hequal
      have hfirst : Encodable.encode firstAtom =
          Encodable.encode secondAtom := by omega
      have hsecond : Encodable.encode secondAtom =
          Encodable.encode thirdAtom := by omega
      have hthird : Encodable.encode thirdAtom =
          Encodable.encode fourthAtom := by omega
      exact ⟨Encodable.encode_injective hfirst,
        Encodable.encode_injective hsecond,
        Encodable.encode_injective hthird⟩
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  simp only [fiveForbiddenRawDistinctPayloadWord,
    fiveForbiddenRawStrictPayloadWord,
    fiveForbiddenOneBitGuardedWord,
    hfirstSecond, hsecondThird, hthirdFourth,
    List.headD_cons, decide_eq_true_eq,
    hfirst, hsecond, hthird, hfourth,
    hpayload]
  simp only [hfirstSecondLT, hsecondThirdLT,
    hthirdFourthLT]
  by_cases hfirstSecondEqual : firstAtom = secondAtom
  · subst secondAtom
    by_cases hfirstThirdEqual : firstAtom = thirdAtom
    · subst thirdAtom
      by_cases hfirstFourthEqual : firstAtom = fourthAtom
      · subst fourthAtom
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.append_nil, List.mem_cons,
            List.not_mem_nil, or_false,
            or_self, List.dedup_cons_of_mem, not_false_eq_true, List.dedup_cons_of_notMem,
                List.dedup_nil, List.flatMap_cons,
            List.flatMap_nil]
      · simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.append_nil, hfirstFourthEqual,
          not_false_eq_true,
            List.mem_cons, List.not_mem_nil, or_self, or_false, List.dedup_cons_of_mem,
                List.dedup_cons_of_notMem,
            List.dedup_nil, List.flatMap_cons, List.flatMap_nil]
    · by_cases hthirdFourthEqual : thirdAtom = fourthAtom
      · subst fourthAtom
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.append_nil, hfirstThirdEqual,
            not_false_eq_true,
            List.mem_cons, List.not_mem_nil, or_self, or_false, List.dedup_cons_of_mem,
                List.dedup_cons_of_notMem,
            List.dedup_nil, List.flatMap_cons, List.flatMap_nil]
      · have hfirstFourthEqual : firstAtom ≠ fourthAtom := by
          intro hequal
          exact hfirstThirdEqual
            ((hfirstFourthEq.mp hequal).2.1)
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.append_nil, hfirstThirdEqual,
            not_false_eq_true,
            hthirdFourthEqual, List.append_assoc, List.mem_cons, hfirstFourthEqual,
                List.not_mem_nil, or_self, or_false,
            List.dedup_cons_of_mem, List.dedup_cons_of_notMem, List.dedup_nil, List.flatMap_cons,
                List.flatMap_nil]
  · by_cases hsecondThirdEqual : secondAtom = thirdAtom
    · subst thirdAtom
      by_cases hsecondFourthEqual : secondAtom = fourthAtom
      · subst fourthAtom
        simp only [ne_eq, hfirstSecondEqual, not_false_eq_true, ↓reduceIte, not_true_eq_false,
            List.append_nil,
            List.mem_cons, List.not_mem_nil, or_self, List.dedup_cons_of_notMem, or_false,
                List.dedup_cons_of_mem,
            List.dedup_nil, List.flatMap_cons, List.flatMap_nil]
      · have hfirstFourthEqual : firstAtom ≠ fourthAtom := by
          intro hequal
          exact hfirstSecondEqual
            (hfirstFourthEq.mp hequal).1
        simp only [ne_eq, hfirstSecondEqual, not_false_eq_true, ↓reduceIte, not_true_eq_false,
            List.append_nil,
            hsecondFourthEqual, List.append_assoc, List.mem_cons, hfirstFourthEqual,
                List.not_mem_nil, or_self,
            List.dedup_cons_of_notMem, or_false, List.dedup_cons_of_mem, List.dedup_nil,
                List.flatMap_cons, List.flatMap_nil]
    · have hfirstThirdEqual : firstAtom ≠ thirdAtom := by
        intro hequal
        exact hfirstSecondEqual
          (hfirstThirdEq.mp hequal).1
      by_cases hthirdFourthEqual : thirdAtom = fourthAtom
      · subst fourthAtom
        simp only [ne_eq, hfirstSecondEqual, not_false_eq_true, ↓reduceIte, hsecondThirdEqual,
            List.append_assoc,
            not_true_eq_false, List.append_nil, List.mem_cons, hfirstThirdEqual, List.not_mem_nil,
                or_self,
            List.dedup_cons_of_notMem, or_false, List.dedup_cons_of_mem, List.dedup_nil,
                List.flatMap_cons, List.flatMap_nil]
      · have hsecondFourthEqual : secondAtom ≠ fourthAtom := by
          intro hequal
          exact hsecondThirdEqual
            (hsecondFourthEq.mp hequal).1
        have hfirstFourthEqual : firstAtom ≠ fourthAtom := by
          intro hequal
          exact hfirstSecondEqual
            (hfirstFourthEq.mp hequal).1
        simp only [ne_eq, hfirstSecondEqual, not_false_eq_true, ↓reduceIte, hsecondThirdEqual,
            List.append_assoc,
            hthirdFourthEqual, List.mem_cons, hfirstThirdEqual, hfirstFourthEqual,
                List.not_mem_nil, or_self,
            List.dedup_cons_of_notMem, hsecondFourthEqual, List.dedup_nil, List.flatMap_cons,
                List.flatMap_nil, List.append_nil]

end CNFFiveFamilyForbiddenWholeClauseExactSourceTM

end GapCVP

end

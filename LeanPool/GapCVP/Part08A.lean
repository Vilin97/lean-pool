/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde

/-! # GapCVP proof, part 08 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

/-- Internal support shared across GapCVP continuation modules. -/
theorem ofClassicalDecide08 {proposition : Prop}
    (proof : @decide proposition (Classical.propDecidable proposition) = true) :
    proposition :=
  @of_decide_eq_true proposition (Classical.propDecidable proposition) proof

namespace CNFFiveFamilyForbiddenWindowGateSourceValidity

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM

private def fiveFamilyForbiddenValidWindowQuery
    {T : ℕ} (window : Window T)
    (original suffix : List Bool) : List Bool :=
  lengthPrefixedWord
    (List.replicate (fiveFamilyForbiddenWindowSourceRank window) true) ++
    lengthPrefixedWord original ++ suffix

private def fiveForbiddenWindowFirstLowAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMinimum
    (fiveForbiddenWindowSourceVariable window symbols .left)
    (fiveForbiddenWindowSourceVariable window symbols .center)

private def fiveForbiddenWindowFirstHighAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMaximum
    (fiveForbiddenWindowSourceVariable window symbols .left)
    (fiveForbiddenWindowSourceVariable window symbols .center)

private def fiveForbiddenWindowSecondLowAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMinimum
    (fiveForbiddenWindowSourceVariable window symbols .right)
    (fiveForbiddenWindowSourceVariable window symbols .next)

private def fiveForbiddenWindowSecondHighAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMaximum
    (fiveForbiddenWindowSourceVariable window symbols .right)
    (fiveForbiddenWindowSourceVariable window symbols .next)

private def fiveForbiddenWindowOuterLowAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMinimum
    (fiveForbiddenWindowFirstLowAtom window symbols)
    (fiveForbiddenWindowSecondLowAtom window symbols)

private def fiveForbiddenWindowMiddleLeftAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMaximum
    (fiveForbiddenWindowFirstLowAtom window symbols)
    (fiveForbiddenWindowSecondLowAtom window symbols)

private def fiveForbiddenWindowMiddleRightAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMinimum
    (fiveForbiddenWindowFirstHighAtom window symbols)
    (fiveForbiddenWindowSecondHighAtom window symbols)

private def fiveForbiddenWindowOuterHighAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMaximum
    (fiveForbiddenWindowFirstHighAtom window symbols)
    (fiveForbiddenWindowSecondHighAtom window symbols)

private def fiveForbiddenWindowMiddleLowAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMinimum
    (fiveForbiddenWindowMiddleLeftAtom window symbols)
    (fiveForbiddenWindowMiddleRightAtom window symbols)

private def fiveForbiddenWindowMiddleHighAtom
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    Variable T S :=
  fiveFamilyForbiddenEncodedMaximum
    (fiveForbiddenWindowMiddleLeftAtom window symbols)
    (fiveForbiddenWindowMiddleRightAtom window symbols)

private theorem fiveFamilyForbiddenWindowNamedSortedAtoms_eq
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    (fiveForbiddenWindowOuterLowAtom window symbols,
      fiveForbiddenWindowMiddleLowAtom window symbols,
      fiveForbiddenWindowMiddleHighAtom window symbols,
      fiveForbiddenWindowOuterHighAtom window symbols) =
      fiveForbiddenEncodedSortedAtoms
        (fiveForbiddenWindowSourceVariable window symbols .left)
        (fiveForbiddenWindowSourceVariable window symbols .center)
        (fiveForbiddenWindowSourceVariable window symbols .right)
        (fiveForbiddenWindowSourceVariable window symbols .next) := by
  rfl

private theorem fiveFamilyForbiddenWindowNamedSortedAtomList_eq
    {T S : ℕ} (window : Window T) (symbols : WindowSymbols S) :
    [fiveForbiddenWindowOuterLowAtom window symbols,
      fiveForbiddenWindowMiddleLowAtom window symbols,
      fiveForbiddenWindowMiddleHighAtom window symbols,
      fiveForbiddenWindowOuterHighAtom window symbols] =
      fiveForbiddenEncodedSortedAtomList
        (fiveForbiddenWindowSourceVariable window symbols .left)
        (fiveForbiddenWindowSourceVariable window symbols .center)
        (fiveForbiddenWindowSourceVariable window symbols .right)
        (fiveForbiddenWindowSourceVariable window symbols .next) := by
  have hnetwork := fiveFamilyForbiddenWindowNamedSortedAtoms_eq
    window symbols
  have hlist := congrArg
    (fun atoms : Variable T S × Variable T S × Variable T S × Variable T S =>
      [atoms.1, atoms.2.1, atoms.2.2.1, atoms.2.2.2]) hnetwork
  simpa only [fiveForbiddenEncodedSortedAtomList] using hlist

section

variable (bound : Polynomial ℕ)
variable {verifier : List Bool × List Bool → Bool}
variable (machine : VerifierTM verifier)
variable (original suffix : List Bool)
variable (window : Window (rowWidth bound machine original))
variable (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))

private theorem fiveForbiddenRawWindowSlotWord_valid
    (coordinate : FiveFamilyForbiddenWindowCoordinate) :
    fiveForbiddenRawWindowSlotWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      coordinate
      (fiveFamilyForbiddenWindowSlotSymbol symbols coordinate).val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowSourceVariable
            window symbols coordinate)) true := by
  simpa only [fiveForbiddenRawWindowSlotWord,
    fiveFamilyForbiddenValidWindowQuery] using
    fiveFamilyForbiddenCoordinateSourceVariableCode_valid
      bound machine original suffix window symbols coordinate

private theorem fiveFamilyForbiddenRawWindowFirstLowWord_valid :
    fiveForbiddenRawWindowFirstLowWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowFirstLowAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowFirstLowWord
    fiveForbiddenWindowFirstLowAtom
  apply fiveForbiddenRawSourceMinimumWord_valid
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .left
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .center

private theorem fiveFamilyForbiddenRawWindowFirstHighWord_valid :
    fiveForbiddenRawWindowFirstHighWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowFirstHighAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowFirstHighWord
    fiveForbiddenWindowFirstHighAtom
  apply fiveForbiddenRawSourceMaximumWord_valid
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .left
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .center

private theorem fiveFamilyForbiddenRawWindowSecondLowWord_valid :
    fiveForbiddenRawWindowSecondLowWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowSecondLowAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowSecondLowWord
    fiveForbiddenWindowSecondLowAtom
  apply fiveForbiddenRawSourceMinimumWord_valid
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .right
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .next

private theorem fiveFamilyForbiddenRawWindowSecondHighWord_valid :
    fiveForbiddenRawWindowSecondHighWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowSecondHighAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowSecondHighWord
    fiveForbiddenWindowSecondHighAtom
  apply fiveForbiddenRawSourceMaximumWord_valid
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .right
  · simpa only [fiveFamilyForbiddenWindowSlotSymbol] using
      fiveForbiddenRawWindowSlotWord_valid
        bound machine original suffix window symbols .next

private theorem fiveFamilyForbiddenRawWindowOuterLowWord_valid :
    fiveForbiddenRawWindowOuterLowWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowOuterLowAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowOuterLowWord
    fiveForbiddenWindowOuterLowAtom
  apply fiveForbiddenRawSourceMinimumWord_valid
  · exact fiveFamilyForbiddenRawWindowFirstLowWord_valid
      bound machine original suffix window symbols
  · exact fiveFamilyForbiddenRawWindowSecondLowWord_valid
      bound machine original suffix window symbols

private theorem fiveFamilyForbiddenRawWindowMiddleLeftWord_valid :
    fiveForbiddenRawWindowMiddleLeftWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowMiddleLeftAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowMiddleLeftWord
    fiveForbiddenWindowMiddleLeftAtom
  apply fiveForbiddenRawSourceMaximumWord_valid
  · exact fiveFamilyForbiddenRawWindowFirstLowWord_valid
      bound machine original suffix window symbols
  · exact fiveFamilyForbiddenRawWindowSecondLowWord_valid
      bound machine original suffix window symbols

private theorem fiveFamilyForbiddenRawWindowMiddleRightWord_valid :
    fiveForbiddenRawWindowMiddleRightWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowMiddleRightAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowMiddleRightWord
    fiveForbiddenWindowMiddleRightAtom
  apply fiveForbiddenRawSourceMinimumWord_valid
  · exact fiveFamilyForbiddenRawWindowFirstHighWord_valid
      bound machine original suffix window symbols
  · exact fiveFamilyForbiddenRawWindowSecondHighWord_valid
      bound machine original suffix window symbols

private theorem fiveFamilyForbiddenRawWindowOuterHighWord_valid :
    fiveForbiddenRawWindowOuterHighWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowOuterHighAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowOuterHighWord
    fiveForbiddenWindowOuterHighAtom
  apply fiveForbiddenRawSourceMaximumWord_valid
  · exact fiveFamilyForbiddenRawWindowFirstHighWord_valid
      bound machine original suffix window symbols
  · exact fiveFamilyForbiddenRawWindowSecondHighWord_valid
      bound machine original suffix window symbols

private theorem fiveFamilyForbiddenRawWindowMiddleLowWord_valid :
    fiveForbiddenRawWindowMiddleLowWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowMiddleLowAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowMiddleLowWord
    fiveForbiddenWindowMiddleLowAtom
  apply fiveForbiddenRawSourceMinimumWord_valid
  · exact fiveFamilyForbiddenRawWindowMiddleLeftWord_valid
      bound machine original suffix window symbols
  · exact fiveFamilyForbiddenRawWindowMiddleRightWord_valid
      bound machine original suffix window symbols

private theorem fiveFamilyForbiddenRawWindowMiddleHighWord_valid :
    fiveForbiddenRawWindowMiddleHighWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
      (fiveFamilyForbiddenValidWindowQuery window original suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowMiddleHighAtom window symbols)) true := by
  unfold fiveForbiddenRawWindowMiddleHighWord
    fiveForbiddenWindowMiddleHighAtom
  apply fiveForbiddenRawSourceMaximumWord_valid
  · exact fiveFamilyForbiddenRawWindowMiddleLeftWord_valid
      bound machine original suffix window symbols
  · exact fiveFamilyForbiddenRawWindowMiddleRightWord_valid
      bound machine original suffix window symbols

end

end CNFFiveFamilyForbiddenWindowGateSourceValidity

namespace CNFFiveFamilyForbiddenWholeClauseValidity

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM
open GapCVP.CNFFiveFamilyForbiddenWindowGateSourceValidity

private theorem fiveFamilyForbiddenExactWindowDistinctPayloadWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))
    (payload : List Bool → List Bool)
    (output : Variable
      (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm) → List Bool)
    (hpayload : ∀ atom,
      payload (List.replicate (Encodable.encode atom) true) =
        output atom) :
    fiveForbiddenExactWindowDistinctPayloadWord
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbols.1.val symbols.2.1.val
        symbols.2.2.1.val symbols.2.2.2.val payload
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyForbiddenWindowSourceRank window) true) ++
          lengthPrefixedWord original ++ suffix) =
      (fiveForbiddenEncodedSortedAtomList
        (fiveForbiddenWindowSourceVariable window symbols .left)
        (fiveForbiddenWindowSourceVariable window symbols .center)
        (fiveForbiddenWindowSourceVariable window symbols .right)
        (fiveForbiddenWindowSourceVariable
          window symbols .next)).dedup.flatMap output := by
  have hordered :
      [fiveForbiddenWindowOuterLowAtom window symbols,
        fiveForbiddenWindowMiddleLowAtom window symbols,
        fiveForbiddenWindowMiddleHighAtom window symbols,
        fiveForbiddenWindowOuterHighAtom window symbols].Pairwise
          (fun first second =>
            Encodable.encode first ≤ Encodable.encode second) := by
    rw [fiveFamilyForbiddenWindowNamedSortedAtomList_eq]
    exact fiveFamilyForbiddenEncodedSortedAtomList_pairwise
      (fiveForbiddenWindowSourceVariable window symbols .left)
      (fiveForbiddenWindowSourceVariable window symbols .center)
      (fiveForbiddenWindowSourceVariable window symbols .right)
      (fiveForbiddenWindowSourceVariable window symbols .next)
  have hresult := fiveFamilyForbiddenRawDistinctPayloadWord_valid
    (fiveForbiddenRawWindowOuterLowWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val)
    (fiveForbiddenRawWindowMiddleLowWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val)
    (fiveForbiddenRawWindowMiddleHighWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val)
    (fiveForbiddenRawWindowOuterHighWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val)
    payload (fiveFamilyForbiddenValidWindowQuery window original suffix)
    (fiveForbiddenWindowOuterLowAtom window symbols)
    (fiveForbiddenWindowMiddleLowAtom window symbols)
    (fiveForbiddenWindowMiddleHighAtom window symbols)
    (fiveForbiddenWindowOuterHighAtom window symbols)
    output
    (fiveFamilyForbiddenRawWindowOuterLowWord_valid
      bound machine original suffix window symbols)
    (fiveFamilyForbiddenRawWindowMiddleLowWord_valid
      bound machine original suffix window symbols)
    (fiveFamilyForbiddenRawWindowMiddleHighWord_valid
      bound machine original suffix window symbols)
    (fiveFamilyForbiddenRawWindowOuterHighWord_valid
      bound machine original suffix window symbols)
    hpayload hordered
  rw [fiveFamilyForbiddenWindowNamedSortedAtomList_eq
    window symbols] at hresult
  simpa only [fiveForbiddenExactWindowDistinctPayloadWord,
    fiveFamilyForbiddenValidWindowQuery] using hresult

private theorem fiveFamilyForbiddenExactWindowDescriptorPayloadWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    fiveForbiddenExactWindowDistinctPayloadWord
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbols.1.val symbols.2.1.val
        symbols.2.2.1.val symbols.2.2.2.val
        (tableauSourceSignedLiteralDescriptorWord false)
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyForbiddenWindowSourceRank window) true) ++
          lengthPrefixedWord original ++ suffix) =
      flatSourceClauseDescriptorPayload
        (transitionClause window symbols) := by
  have hphysical := fiveFamilyForbiddenExactWindowDistinctPayloadWord_valid
    bound machine original suffix window symbols
    (tableauSourceSignedLiteralDescriptorWord false)
    (fun atom => flatSignedLiteralDescriptor
      (sourceLiteral (negative atom)))
    (fun atom => by
      simpa only [sourceLiteral, negative] using
        tableauSourceSignedLiteralDescriptorWord_variable atom false)
  rw [hphysical]
  simp only [flatSourceClauseDescriptorPayload,
    sortedElements_transitionClause_eq_sortedNetwork,
    fiveForbiddenWindowSortedUniqueLiteralList,
    flatSignedLiteralDescriptorStream,
    List.flatMap_map, List.map_map, Function.comp_def]

private theorem fiveFamilyForbiddenExactWindowDuplicatedPayloadWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    fiveForbiddenExactWindowDistinctPayloadWord
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbols.1.val symbols.2.1.val
        symbols.2.2.1.val symbols.2.2.2.val
        (duplicatedUnarySignedLiteralCodeWord false)
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyForbiddenWindowSourceRank window) true) ++
          lengthPrefixedWord original ++ suffix) =
      flatSourceClauseDuplicatedCodePayload
        (transitionClause window symbols) := by
  have hphysical := fiveFamilyForbiddenExactWindowDistinctPayloadWord_valid
    bound machine original suffix window symbols
    (duplicatedUnarySignedLiteralCodeWord false)
    (fun atom => flatDuplicatedUnaryField
      (Encodable.encode (negative atom)))
    (fun atom => by
      simpa only [negative] using
        duplicatedUnarySignedLiteralCodeWord_sourceVariable atom false)
  rw [hphysical]
  simp only [flatSourceClauseDuplicatedCodePayload,
    flatSourceFinsetCodes,
    sortedElements_transitionClause_eq_sortedNetwork,
    fiveForbiddenWindowSortedUniqueLiteralList,
    flatDuplicatedUnarySourceStream,
    List.flatMap_map, List.map_map, Function.comp_def]

private theorem fiveFamilyForbiddenExactWindowUnaryCountWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    fiveForbiddenExactWindowDistinctPayloadWord
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbols.1.val symbols.2.1.val
        symbols.2.2.1.val symbols.2.2.2.val
        (fun _ => [true])
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyForbiddenWindowSourceRank window) true) ++
          lengthPrefixedWord original ++ suffix) =
      flatSourceClauseUnaryCountPayload
        (transitionClause window symbols) := by
  have hphysical := fiveFamilyForbiddenExactWindowDistinctPayloadWord_valid
    bound machine original suffix window symbols
    (fun _ => [true]) (fun _ => [true]) (fun _ => rfl)
  rw [hphysical]
  have hcard := congrArg List.length
    (sortedElements_transitionClause_eq_sortedNetwork window symbols)
  simp only [sortedElements_length,
    fiveForbiddenWindowSortedUniqueLiteralList,
    List.length_map] at hcard
  unfold flatSourceClauseUnaryCountPayload
  rw [← List.map_eq_flatMap, List.map_const', ← hcard]

private theorem fiveFamilyForbiddenExactWindowWholeClauseRecordWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    fiveForbiddenExactWindowWholeClauseRecordWord
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbols.1.val symbols.2.1.val
        symbols.2.2.1.val symbols.2.2.2.val
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyForbiddenWindowSourceRank window) true) ++
          lengthPrefixedWord original ++ suffix) =
      flatSourceClauseAnnotatedRecord
        (transitionClause window symbols) := by
  unfold fiveForbiddenExactWindowWholeClauseRecordWord
    flatSourceClauseAnnotatedRecord
  rw [fiveFamilyForbiddenExactWindowDescriptorPayloadWord_valid
      bound machine original suffix window symbols,
    fiveFamilyForbiddenExactWindowDuplicatedPayloadWord_valid
      bound machine original suffix window symbols,
    fiveFamilyForbiddenExactWindowUnaryCountWord_valid
      bound machine original suffix window symbols]

end CNFFiveFamilyForbiddenWholeClauseValidity

namespace CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseValidity
open GapCVP.CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM

private def fiveIndependentAtMostSourceClauses
    (T S : ℕ) : List (Clause T S) :=
  (fiveFamilyRowMajorSymbolPairs S).flatMap fun symbols =>
    (fiveFamilyRowMajorTimePositionSlots T).map fun position =>
      if symbols.1 < symbols.2 then
        atMostOneClause position.1 position.2 symbols.1 symbols.2
      else
        atLeastOneClause position.1 position.2

private def fiveIndependentForbiddenSourceClauses
    {T S : ℕ} (specification : Specification T S) :
    List (Clause T S) :=
  (fiveFamilyRowMajorWindowSymbols S).flatMap fun symbols =>
    (fiveFamilyRowMajorWindows T).map fun window =>
      if specification.allowed symbols = false then
        transitionClause window symbols
      else
        atLeastOneClause window.1.1 window.1.2

private def fiveIndependentActualSourceClauses
    {T S : ℕ} (specification : Specification T S) :
    List (Clause T S) :=
  fiveFamilyRowMajorAtLeastClauses T S ++
    (fiveIndependentAtMostSourceClauses T S ++
      (fiveFamilyRowMajorInitialClauses specification ++
        (fiveFamilyRowMajorAcceptanceClauses specification ++
          fiveIndependentForbiddenSourceClauses specification)))

private theorem mem_fiveFamilyIndependentAtMostSourceClauses
    {T S : ℕ} (clause : Clause T S) :
    clause ∈ fiveIndependentAtMostSourceClauses T S ↔
      clause ∈ fiveFamilyRowMajorAtMostClauses T S := by
  simp only [fiveIndependentAtMostSourceClauses,
    fiveFamilyRowMajorAtMostClauses,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨symbols, hsymbols, position, hposition, hequality⟩
    exact ⟨position, hposition, symbols, hsymbols, hequality⟩
  · rintro ⟨position, hposition, symbols, hsymbols, hequality⟩
    exact ⟨symbols, hsymbols, position, hposition, hequality⟩

private theorem mem_fiveFamilyIndependentForbiddenSourceClauses
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S) :
    clause ∈ fiveIndependentForbiddenSourceClauses
        specification ↔
      clause ∈ fiveFamilyRowMajorForbiddenClauses specification := by
  simp only [fiveIndependentForbiddenSourceClauses,
    fiveFamilyRowMajorForbiddenClauses,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨symbols, hsymbols, window, hwindow, hequality⟩
    exact ⟨window, hwindow, symbols, hsymbols, hequality⟩
  · rintro ⟨window, hwindow, symbols, hsymbols, hequality⟩
    exact ⟨symbols, hsymbols, window, hwindow, hequality⟩

private theorem fiveFamilyIndependentActualSourceClauses_toFinset
    {T S : ℕ} (specification : Specification T S) :
    (fiveIndependentActualSourceClauses
      specification).toFinset = tableauFormula specification := by
  rw [← fiveFamilyRowMajorSourceClauses_toFinset specification]
  ext clause
  simp only [List.mem_toFinset,
    fiveIndependentActualSourceClauses,
    fiveFamilyRowMajorSourceClauses,
    List.mem_append,
    mem_fiveFamilyIndependentAtMostSourceClauses,
    mem_fiveFamilyIndependentForbiddenSourceClauses,
    or_assoc]

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentActualSourceClauseCountPolynomial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    Polynomial ℕ :=
  let grid := fiveFamilyFlatIndexedGridPolynomial bound machine
  let symbols := completePhaseSymbolCount machine.tm + 1
  grid * grid +
    grid * grid * Polynomial.C (symbols ^ 2) +
    grid + 1 +
    nondeterministicTableauDimensionPolynomial bound machine *
      grid * Polynomial.C (symbols ^ 4)

/-- Internal support shared across GapCVP continuation modules. -/
def fiveFamilyIndependentSquareGridTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    Time (rowWidth bound machine original) :=
  ⟨rank.val / (rowWidth bound machine original + 1), by
    apply fiveFamilyFlatIndexedGridQuotient_lt
      bound machine original rank.val
    simpa only [pow_two, Polynomial.eval_mul, fiveFamilyFlatIndexedGridPolynomial_eval]
        using rank.isLt⟩

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentSquareGridPosition
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    Position (rowWidth bound machine original) :=
  ⟨rank.val % (rowWidth bound machine original + 1),
    fiveFamilyFlatIndexedGridRemainder_lt
      bound machine original rank.val⟩

private theorem fiveFamilyIndependentSquareGridRank_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    fiveFamilyFlatSourceRowMajorIndex
        (fiveFamilyIndependentSquareGridTime
          bound machine original rank)
        (fiveIndependentSquareGridPosition
          bound machine original rank) = rank.val := by
  unfold fiveFamilyFlatSourceRowMajorIndex
    fiveFamilyIndependentSquareGridTime
    fiveIndependentSquareGridPosition
  exact Nat.div_add_mod' rank.val
    (rowWidth bound machine original + 1)

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentSquareGridSlots
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Time (rowWidth bound machine original) ×
      Position (rowWidth bound machine original)) :=
  (List.finRange
    ((fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine).eval
        original.length)).map fun rank =>
      (fiveFamilyIndependentSquareGridTime
        bound machine original rank,
       fiveIndependentSquareGridPosition
        bound machine original rank)

@[simp] private theorem mem_fiveFamilyIndependentSquareGridSlots
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original)) :
    (time, position) ∈
      fiveIndependentSquareGridSlots
        bound machine original := by
  have htime : time.val < rowWidth bound machine original + 1 :=
    time.isLt
  have hposition : position.val <
      rowWidth bound machine original + 1 := position.isLt
  have hindex :
      fiveFamilyFlatSourceRowMajorIndex time position <
        (rowWidth bound machine original + 1) *
          (rowWidth bound machine original + 1) := by
    unfold fiveFamilyFlatSourceRowMajorIndex
    calc
      time.val * (rowWidth bound machine original + 1) +
          position.val <
        time.val * (rowWidth bound machine original + 1) +
          (rowWidth bound machine original + 1) :=
        Nat.add_lt_add_left hposition _
      _ = (time.val + 1) *
          (rowWidth bound machine original + 1) := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ (rowWidth bound machine original + 1) *
          (rowWidth bound machine original + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt htime)
  have hbound :
      fiveFamilyFlatSourceRowMajorIndex time position <
        (fiveFamilyFlatIndexedGridPolynomial bound machine *
          fiveFamilyFlatIndexedGridPolynomial bound machine).eval
            original.length := by
    simpa only [Polynomial.eval_mul, fiveFamilyFlatIndexedGridPolynomial_eval] using hindex
  let rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length) :=
    ⟨fiveFamilyFlatSourceRowMajorIndex time position, hbound⟩
  unfold fiveIndependentSquareGridSlots
  apply List.mem_map.mpr
  refine ⟨rank, by simp only [List.mem_finRange], ?_⟩
  apply Prod.ext
  · apply Fin.ext
    change fiveFamilyFlatSourceRowMajorIndex time position /
      (rowWidth bound machine original + 1) = time.val
    exact fiveFamilyFlatSourceRowMajorIndex_div time position
  · apply Fin.ext
    change fiveFamilyFlatSourceRowMajorIndex time position %
      (rowWidth bound machine original + 1) = position.val
    exact fiveFamilyFlatSourceRowMajorIndex_mod time position

private def fiveFamilyIndependentForbiddenGridTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((nondeterministicTableauDimensionPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    Fin (rowWidth bound machine original) :=
  ⟨rank.val / (rowWidth bound machine original + 1), by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    simpa only [rowWidth, Polynomial.eval_mul, fiveFamilyFlatIndexedGridPolynomial_eval]
        using rank.isLt⟩

private def fiveFamilyIndependentForbiddenGridPosition
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((nondeterministicTableauDimensionPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    Position (rowWidth bound machine original) :=
  ⟨rank.val % (rowWidth bound machine original + 1),
    fiveFamilyFlatIndexedGridRemainder_lt
      bound machine original rank.val⟩

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentForbiddenGridWindow
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((nondeterministicTableauDimensionPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    Window (rowWidth bound machine original) :=
  windowAt
    (fiveFamilyIndependentForbiddenGridTime
      bound machine original rank)
    (fiveFamilyIndependentForbiddenGridPosition
      bound machine original rank)

private theorem fiveFamilyIndependentForbiddenGridRank_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((nondeterministicTableauDimensionPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    fiveFamilyForbiddenWindowSourceRank
        (fiveIndependentForbiddenGridWindow
          bound machine original rank) = rank.val := by
  unfold fiveFamilyForbiddenWindowSourceRank
    fiveFamilyFlatSourceRowMajorIndex
    fiveIndependentForbiddenGridWindow
    fiveFamilyIndependentForbiddenGridTime
    fiveFamilyIndependentForbiddenGridPosition
  exact Nat.div_add_mod' rank.val
    (rowWidth bound machine original + 1)

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentForbiddenGridWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Window (rowWidth bound machine original)) :=
  (List.finRange
    ((nondeterministicTableauDimensionPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine).eval
        original.length)).map
      (fiveIndependentForbiddenGridWindow
        bound machine original)

@[simp] private theorem mem_fiveFamilyIndependentForbiddenGridWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (window : Window (rowWidth bound machine original)) :
    window ∈ fiveIndependentForbiddenGridWindows
      bound machine original := by
  have htime : window.1.1.val < rowWidth bound machine original := by
    have hwindow := window.2
    omega
  have hposition : window.1.2.val <
      rowWidth bound machine original + 1 := window.1.2.isLt
  have hindex :
      fiveFamilyForbiddenWindowSourceRank window <
        rowWidth bound machine original *
          (rowWidth bound machine original + 1) := by
    unfold fiveFamilyForbiddenWindowSourceRank
      fiveFamilyFlatSourceRowMajorIndex
    calc
      window.1.1.val * (rowWidth bound machine original + 1) +
          window.1.2.val <
        window.1.1.val * (rowWidth bound machine original + 1) +
          (rowWidth bound machine original + 1) :=
        Nat.add_lt_add_left hposition _
      _ = (window.1.1.val + 1) *
          (rowWidth bound machine original + 1) := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ rowWidth bound machine original *
          (rowWidth bound machine original + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt htime)
  have hbound :
      fiveFamilyForbiddenWindowSourceRank window <
        (nondeterministicTableauDimensionPolynomial bound machine *
          fiveFamilyFlatIndexedGridPolynomial bound machine).eval
            original.length := by
    simpa only [rowWidth, Polynomial.eval_mul, fiveFamilyFlatIndexedGridPolynomial_eval]
        using hindex
  let rank : Fin
      ((nondeterministicTableauDimensionPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length) :=
    ⟨fiveFamilyForbiddenWindowSourceRank window, hbound⟩
  unfold fiveIndependentForbiddenGridWindows
  apply List.mem_map.mpr
  refine ⟨rank, by simp only [List.mem_finRange], ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change fiveFamilyForbiddenWindowSourceRank window /
      (rowWidth bound machine original + 1) = window.1.1.val
    exact fiveFamilyFlatSourceRowMajorIndex_div
      window.1.1 window.1.2
  · apply Fin.ext
    change fiveFamilyForbiddenWindowSourceRank window %
      (rowWidth bound machine original + 1) = window.1.2.val
    exact fiveFamilyFlatSourceRowMajorIndex_mod
      window.1.1 window.1.2

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyIndependentAtLeastRankWorker_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    fiveFlatRowMajorAtLeastClauseRecordWord
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        (completePhaseSymbolCount machine.tm + 1)
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original) =
      flatSourceClauseAnnotatedRecord
        (atLeastOneClause
          (S := completePhaseSymbolCount machine.tm)
          (fiveFamilyIndependentSquareGridTime
            bound machine original rank)
          (fiveIndependentSquareGridPosition
            bound machine original rank)) := by
  have hphysical := fiveFamilyFlatRowMajorAtLeastClauseRecordWord_valid
    bound machine original
    (List.replicate
      ((flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)).eval
          original.length) true)
    (fiveFamilyIndependentSquareGridTime
      bound machine original rank)
    (fiveIndependentSquareGridPosition
      bound machine original rank)
  rw [fiveFamilyIndependentSquareGridRank_eq
    bound machine original rank] at hphysical
  simpa only [fiveFlatOriginalSourceAnchorWord,
    List.append_assoc] using hphysical

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyIndependentAtMostRankWorker_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm))
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    fiveIndependentAtMostFixedPairWorker
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        (completePhaseSymbolCount machine.tm + 1)
        pair.1.val pair.2.val
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original) =
      flatSourceClauseAnnotatedRecord
        (if pair.1 < pair.2 then
          atMostOneClause
            (fiveFamilyIndependentSquareGridTime
              bound machine original rank)
            (fiveIndependentSquareGridPosition
              bound machine original rank)
            pair.1 pair.2
         else
          atLeastOneClause
            (S := completePhaseSymbolCount machine.tm)
            (fiveFamilyIndependentSquareGridTime
              bound machine original rank)
            (fiveIndependentSquareGridPosition
              bound machine original rank)) := by
  by_cases hpair : pair.1.val < pair.2.val
  · have htyped : pair.1 < pair.2 := hpair
    simp only [fiveIndependentAtMostFixedPairWorker,
      hpair, htyped, ↓reduceIte]
    have hphysical := fiveFamilyFlatRowMajorAtMostClauseRecordWord_valid
      bound machine original
      (List.replicate
        ((flatSourceAnnotatedClauseLengthPolynomial
          (nondeterministicTableauDimensionPolynomial bound machine)
          (completePhaseSymbolCount machine.tm)).eval
            original.length) true)
      (fiveFamilyIndependentSquareGridTime
        bound machine original rank)
      (fiveIndependentSquareGridPosition
        bound machine original rank)
      pair.1 pair.2 htyped
    rw [fiveFamilyIndependentSquareGridRank_eq
      bound machine original rank] at hphysical
    simpa only [fiveFlatOriginalSourceAnchorWord,
      List.append_assoc] using hphysical
  · have htyped : ¬ pair.1 < pair.2 := hpair
    simp only [fiveIndependentAtMostFixedPairWorker,
      hpair, htyped, ↓reduceIte]
    exact fiveFamilyIndependentAtLeastRankWorker_valid
      bound machine original rank

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentInitialGridPosition
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine).eval
        original.length)) :
    Position (rowWidth bound machine original) :=
  ⟨rank.val, by
    simpa only [Order.lt_add_one_iff, fiveFamilyFlatIndexedGridPolynomial_eval] using rank.isLt⟩

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyIndependentInitialRankWorker_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine).eval
        original.length)) :
    fiveFlatWholePackedInitialClauseRecordWord
        bound machine
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original) =
      flatSourceClauseAnnotatedRecord
        (initialClause
          (paddedAcceptancePhaseSpecification
            bound machine original).input
          (fiveIndependentInitialGridPosition
            bound machine original rank)) := by
  have hphysical := fiveFamilyFlatWholePackedInitialClauseRecordWord_valid
    bound machine original
    (List.replicate
      ((flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)).eval
          original.length) true)
    (fiveIndependentInitialGridPosition
      bound machine original rank)
  simpa only [fiveFlatOriginalSourceAnchorWord,
    fiveIndependentInitialGridPosition,
    List.append_assoc] using hphysical

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyIndependentForbiddenRankWorker_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))
    (rank : Fin
      ((nondeterministicTableauDimensionPolynomial bound machine *
        fiveFamilyFlatIndexedGridPolynomial bound machine).eval
          original.length)) :
    fiveIndependentForbiddenFixedTupleWorker
        bound machine symbols
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original) =
      flatSourceClauseAnnotatedRecord
        (if paddedAcceptancePhaseSymbolAllowed machine symbols = false
         then transitionClause
           (fiveIndependentForbiddenGridWindow
             bound machine original rank) symbols
         else atLeastOneClause
           (S := completePhaseSymbolCount machine.tm)
           (fiveIndependentForbiddenGridWindow
             bound machine original rank).1.1
           (fiveIndependentForbiddenGridWindow
             bound machine original rank).1.2) := by
  by_cases hforbidden :
      paddedAcceptancePhaseSymbolAllowed machine symbols = false
  · simp only [fiveIndependentForbiddenFixedTupleWorker,
      hforbidden, ite_true]
    have hphysical := fiveFamilyForbiddenExactWindowWholeClauseRecordWord_valid
      bound machine original
      (List.replicate
        ((flatSourceAnnotatedClauseLengthPolynomial
          (nondeterministicTableauDimensionPolynomial bound machine)
          (completePhaseSymbolCount machine.tm)).eval
            original.length) true)
      (fiveIndependentForbiddenGridWindow
        bound machine original rank) symbols
    rw [fiveFamilyIndependentForbiddenGridRank_eq
      bound machine original rank] at hphysical
    simpa only [fiveFlatOriginalSourceAnchorWord,
      List.append_assoc] using hphysical
  · simp only [fiveIndependentForbiddenFixedTupleWorker, hforbidden, Bool.true_eq_false,
      ↓reduceIte]
    have hphysical := fiveFamilyFlatRowMajorAtLeastClauseRecordWord_valid
      bound machine original
      (List.replicate
        ((flatSourceAnnotatedClauseLengthPolynomial
          (nondeterministicTableauDimensionPolynomial bound machine)
          (completePhaseSymbolCount machine.tm)).eval
            original.length) true)
      (fiveIndependentForbiddenGridWindow
        bound machine original rank).1.1
      (fiveIndependentForbiddenGridWindow
        bound machine original rank).1.2
    have hrank := fiveFamilyIndependentForbiddenGridRank_eq
      bound machine original rank
    change fiveFamilyFlatSourceRowMajorIndex
      (fiveIndependentForbiddenGridWindow
        bound machine original rank).1.1
      (fiveIndependentForbiddenGridWindow
        bound machine original rank).1.2 = rank.val at hrank
    rw [hrank] at hphysical
    simpa only [fiveFlatOriginalSourceAnchorWord,
      List.append_assoc] using hphysical

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentPhysicalAtLeastSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  (fiveIndependentSquareGridSlots
    bound machine original).map fun position =>
      atLeastOneClause
        (S := completePhaseSymbolCount machine.tm)
        position.1 position.2

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentPhysicalAtMostSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  (fiveFamilyRowMajorSymbolPairs
    (completePhaseSymbolCount machine.tm)).flatMap fun symbols =>
      (fiveIndependentSquareGridSlots
        bound machine original).map fun position =>
        if symbols.1 < symbols.2 then
          atMostOneClause position.1 position.2 symbols.1 symbols.2
        else
          atLeastOneClause position.1 position.2

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentInitialGridPositions
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Position (rowWidth bound machine original)) :=
  (List.finRange
    ((fiveFamilyFlatIndexedGridPolynomial bound machine).eval
      original.length)).map
        (fiveIndependentInitialGridPosition
          bound machine original)

@[simp] private theorem mem_fiveFamilyIndependentInitialGridPositions
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original)) :
    position ∈ fiveIndependentInitialGridPositions
      bound machine original := by
  have hbound : position.val <
      (fiveFamilyFlatIndexedGridPolynomial bound machine).eval
        original.length := by
    simpa only [fiveFamilyFlatIndexedGridPolynomial_eval, Order.lt_add_one_iff] using position.isLt
  let rank : Fin
      ((fiveFamilyFlatIndexedGridPolynomial bound machine).eval
        original.length) := ⟨position.val, hbound⟩
  unfold fiveIndependentInitialGridPositions
  apply List.mem_map.mpr
  refine ⟨rank, by simp only [List.mem_finRange], ?_⟩
  apply Fin.ext
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentPhysicalInitialSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  (fiveIndependentInitialGridPositions
    bound machine original).map
      (initialClause
        (paddedAcceptancePhaseSpecification
          bound machine original).input)

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentPhysicalForbiddenSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  (fiveFamilyRowMajorWindowSymbols
    (completePhaseSymbolCount machine.tm)).flatMap fun symbols =>
      (fiveIndependentForbiddenGridWindows
        bound machine original).map fun window =>
          if paddedAcceptancePhaseSymbolAllowed machine symbols = false
          then transitionClause window symbols
          else atLeastOneClause window.1.1 window.1.2

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentPhysicalSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  fiveIndependentPhysicalAtLeastSourceClauses
      bound machine original ++
    (fiveIndependentPhysicalAtMostSourceClauses
      bound machine original ++
      (fiveIndependentPhysicalInitialSourceClauses
        bound machine original ++
        ((fiveFamilyRowMajorAcceptanceClauses
          (paddedAcceptancePhaseSpecification
            bound machine original) :
            List (Clause (rowWidth bound machine original)
              (completePhaseSymbolCount machine.tm))) ++
          fiveIndependentPhysicalForbiddenSourceClauses
            bound machine original)))

private theorem mem_fiveFamilyIndependentPhysicalAtLeastSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (clause : Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :
    clause ∈ fiveIndependentPhysicalAtLeastSourceClauses
        bound machine original ↔
      clause ∈ fiveFamilyRowMajorAtLeastClauses
        (rowWidth bound machine original)
        (completePhaseSymbolCount machine.tm) := by
  simp only [fiveIndependentPhysicalAtLeastSourceClauses,
    fiveFamilyRowMajorAtLeastClauses, List.mem_map]
  constructor
  · rintro ⟨position, _, hequality⟩
    exact ⟨position,
      mem_fiveFamilyRowMajorTimePositionSlots
        position.1 position.2,
      hequality⟩
  · rintro ⟨position, _, hequality⟩
    exact ⟨position,
      mem_fiveFamilyIndependentSquareGridSlots
        bound machine original position.1 position.2,
      hequality⟩

private theorem mem_fiveFamilyIndependentPhysicalAtMostSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (clause : Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :
    clause ∈ fiveIndependentPhysicalAtMostSourceClauses
        bound machine original ↔
      clause ∈ fiveIndependentAtMostSourceClauses
        (rowWidth bound machine original)
        (completePhaseSymbolCount machine.tm) := by
  simp only [fiveIndependentPhysicalAtMostSourceClauses,
    fiveIndependentAtMostSourceClauses,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨symbols, hsymbols, position, _, hequality⟩
    exact ⟨symbols, hsymbols, position,
      mem_fiveFamilyRowMajorTimePositionSlots
        position.1 position.2,
      hequality⟩
  · rintro ⟨symbols, hsymbols, position, _, hequality⟩
    exact ⟨symbols, hsymbols, position,
      mem_fiveFamilyIndependentSquareGridSlots
        bound machine original position.1 position.2,
      hequality⟩

private theorem mem_fiveFamilyIndependentPhysicalInitialSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (clause : Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :
    clause ∈ fiveIndependentPhysicalInitialSourceClauses
        bound machine original ↔
      clause ∈ fiveFamilyRowMajorInitialClauses
        (paddedAcceptancePhaseSpecification
          bound machine original) := by
  change
    clause ∈ (fiveIndependentInitialGridPositions
      bound machine original).map
        (initialClause
          (paddedAcceptancePhaseSpecification
            bound machine original).input) ↔
      clause ∈ (List.finRange
        (rowWidth bound machine original + 1)).map
          (initialClause
            (paddedAcceptancePhaseSpecification
              bound machine original).input)
  constructor
  · intro hmember
    obtain ⟨position, _, hequality⟩ := List.mem_map.mp hmember
    apply List.mem_map.mpr
    exact ⟨position, List.mem_finRange position, hequality⟩
  · intro hmember
    obtain ⟨position, _, hequality⟩ := List.mem_map.mp hmember
    apply List.mem_map.mpr
    exact ⟨position,
      mem_fiveFamilyIndependentInitialGridPositions
        bound machine original position,
      hequality⟩

private theorem mem_fiveFamilyIndependentPhysicalForbiddenSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (clause : Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :
    clause ∈ fiveIndependentPhysicalForbiddenSourceClauses
        bound machine original ↔
      clause ∈ fiveIndependentForbiddenSourceClauses
        (paddedAcceptancePhaseSpecification
          bound machine original) := by
  unfold fiveIndependentPhysicalForbiddenSourceClauses
    fiveIndependentForbiddenSourceClauses
  constructor
  · intro hmember
    obtain ⟨symbols, hsymbols, hwindow⟩ :=
      List.mem_flatMap.mp hmember
    obtain ⟨window, _, hequality⟩ := List.mem_map.mp hwindow
    apply List.mem_flatMap.mpr
    refine ⟨symbols, hsymbols, ?_⟩
    apply List.mem_map.mpr
    refine ⟨window, mem_fiveFamilyRowMajorWindows window, ?_⟩
    exact hequality
  · intro hmember
    obtain ⟨symbols, hsymbols, hwindow⟩ :=
      List.mem_flatMap.mp hmember
    obtain ⟨window, _, hequality⟩ := List.mem_map.mp hwindow
    apply List.mem_flatMap.mpr
    refine ⟨symbols, hsymbols, ?_⟩
    apply List.mem_map.mpr
    refine ⟨window,
      mem_fiveFamilyIndependentForbiddenGridWindows
        bound machine original window, ?_⟩
    exact hequality

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyIndependentPhysicalSourceClauses_toFinset
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    (fiveIndependentPhysicalSourceClauses
      bound machine original).toFinset =
      tableauFormula
        (paddedAcceptancePhaseSpecification
          bound machine original) := by
  rw [← fiveFamilyIndependentActualSourceClauses_toFinset
    (paddedAcceptancePhaseSpecification
      bound machine original)]
  ext clause
  constructor
  · intro hphysical
    have hmember : clause ∈
        fiveIndependentPhysicalSourceClauses
          bound machine original :=
      List.mem_toFinset.mp hphysical
    have hactual : clause ∈
        fiveIndependentActualSourceClauses
          (paddedAcceptancePhaseSpecification
            bound machine original) := by
      simp only [fiveIndependentPhysicalSourceClauses,
        List.mem_append] at hmember
      change
        (show Clause
          ((nondeterministicTableauDimensionPolynomial
            bound machine).eval original.length)
          (completePhaseSymbolCount machine.tm) from clause) ∈
        (fiveFamilyRowMajorAtLeastClauses
          ((nondeterministicTableauDimensionPolynomial
            bound machine).eval original.length)
          (completePhaseSymbolCount machine.tm) ++
          (fiveIndependentAtMostSourceClauses
            ((nondeterministicTableauDimensionPolynomial
              bound machine).eval original.length)
            (completePhaseSymbolCount machine.tm) ++
            (fiveFamilyRowMajorInitialClauses
              (paddedAcceptancePhaseSpecification
                bound machine original) ++
              (fiveFamilyRowMajorAcceptanceClauses
                (paddedAcceptancePhaseSpecification
                  bound machine original) ++
                fiveIndependentForbiddenSourceClauses
                  (paddedAcceptancePhaseSpecification
                    bound machine original)))))
      simp only [List.mem_append]
      rcases hmember with hleast | hmost | hinitial | haccept | hforbidden
      · exact Or.inl
          ((mem_fiveFamilyIndependentPhysicalAtLeastSourceClauses
            bound machine original clause).mp hleast)
      · exact Or.inr (Or.inl
          ((mem_fiveFamilyIndependentPhysicalAtMostSourceClauses
            bound machine original clause).mp hmost))
      · exact Or.inr (Or.inr (Or.inl
          ((mem_fiveFamilyIndependentPhysicalInitialSourceClauses
            bound machine original clause).mp hinitial)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl haccept)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ((mem_fiveFamilyIndependentPhysicalForbiddenSourceClauses
            bound machine original clause).mp hforbidden))))
    exact List.mem_toFinset.mpr hactual
  · intro hactual
    have hmember : clause ∈
        fiveIndependentActualSourceClauses
          (paddedAcceptancePhaseSpecification
            bound machine original) :=
      List.mem_toFinset.mp hactual
    change
      (show Clause
        ((nondeterministicTableauDimensionPolynomial
          bound machine).eval original.length)
        (completePhaseSymbolCount machine.tm) from clause) ∈
      (fiveFamilyRowMajorAtLeastClauses
        ((nondeterministicTableauDimensionPolynomial
          bound machine).eval original.length)
        (completePhaseSymbolCount machine.tm) ++
        (fiveIndependentAtMostSourceClauses
          ((nondeterministicTableauDimensionPolynomial
            bound machine).eval original.length)
          (completePhaseSymbolCount machine.tm) ++
          (fiveFamilyRowMajorInitialClauses
            (paddedAcceptancePhaseSpecification
              bound machine original) ++
            (fiveFamilyRowMajorAcceptanceClauses
              (paddedAcceptancePhaseSpecification
                bound machine original) ++
              fiveIndependentForbiddenSourceClauses
                (paddedAcceptancePhaseSpecification
                  bound machine original))))) at hmember
    have hphysical : clause ∈
        fiveIndependentPhysicalSourceClauses
          bound machine original := by
      simp only [List.mem_append] at hmember
      simp only [fiveIndependentPhysicalSourceClauses,
        List.mem_append]
      rcases hmember with hleast | hmost | hinitial | haccept | hforbidden
      · exact Or.inl
          ((mem_fiveFamilyIndependentPhysicalAtLeastSourceClauses
            bound machine original clause).mpr hleast)
      · exact Or.inr (Or.inl
          ((mem_fiveFamilyIndependentPhysicalAtMostSourceClauses
            bound machine original clause).mpr hmost))
      · exact Or.inr (Or.inr (Or.inl
          ((mem_fiveFamilyIndependentPhysicalInitialSourceClauses
            bound machine original clause).mpr hinitial)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl haccept)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ((mem_fiveFamilyIndependentPhysicalForbiddenSourceClauses
            bound machine original clause).mpr hforbidden))))
    exact List.mem_toFinset.mpr hphysical

end CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity

end GapCVP

end

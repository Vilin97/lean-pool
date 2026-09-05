/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07F

/-! # GapCVP proof, part 07, continuation 07 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation

open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding

open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter

open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

open GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM

open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM

open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM

open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM

open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM

open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM

/-- GapCVP reduction support. -/
def fiveIndependentFixedFamilyStreamWord
    {α : Type} (indices : List α)
    (stream : α → List Bool → List Bool)
    (original : List Bool) : List Bool :=
  indices.foldr (fun index output => stream index original ++ output) []

private noncomputable def fiveFamilyIndependentFixedFamilyStreamComputable
    {α : Type} (indices : List α)
    (stream : α → List Bool → List Bool)
    (computers : ∀ index ∈ indices,
      BitTM (stream index)) :
    BitTM
      (fiveIndependentFixedFamilyStreamWord indices stream) := by
  induction indices with
  | nil =>
      exact constantWordComputable []
  | cons index remaining ih =>
      have hfirst := computers index (by simp only [List.mem_cons, true_or])
      have hrest := ih (fun next hnext =>
        computers next (by simp only [List.mem_cons, hnext, or_true]))
      have physical := pointwiseAppendComputable hfirst hrest
      change BitTM
        (fun original => stream index original ++
          fiveIndependentFixedFamilyStreamWord
            remaining stream original)
      exact physical

/-- GapCVP reduction support. -/
def fiveIndependentAtLeastBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFlatRowMajorAtLeastClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1))

private noncomputable def fiveFamilyIndependentAtLeastBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAtLeastBundledStreamWord bound machine) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFamilyFlatRowMajorAtLeastClauseRecordComputable
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1))

/-- GapCVP reduction support. -/
def fiveIndependentAtMostFixedPairWorker
    (grid : Polynomial ℕ)
    (alphabet first second : ℕ) : List Bool → List Bool :=
  if first < second then
    fiveFlatRowMajorAtMostClauseRecordWord grid first second
  else
    fiveFlatRowMajorAtLeastClauseRecordWord grid alphabet

private noncomputable def fiveFamilyIndependentAtMostFixedPairWorkerComputable
    (grid : Polynomial ℕ)
    (alphabet first second : ℕ) :
    BitTM
      (fiveIndependentAtMostFixedPairWorker
        grid alphabet first second) := by
  by_cases hpair : first < second
  · simpa only [fiveIndependentAtMostFixedPairWorker, hpair,
      ↓reduceIte] using
      fiveFamilyFlatRowMajorAtMostClauseRecordComputable
        grid first second
  · simpa only [fiveIndependentAtMostFixedPairWorker, hpair,
      ↓reduceIte] using
      fiveFamilyFlatRowMajorAtLeastClauseRecordComputable
        grid alphabet

/-- GapCVP reduction support. -/
def fiveIndependentAtMostFixedPairBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm)) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveIndependentAtMostFixedPairWorker
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      pair.1.val pair.2.val)

private noncomputable def fiveFamilyIndependentAtMostFixedPairBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm)) :
    BitTM
      (fiveIndependentAtMostFixedPairBundledStreamWord
        bound machine pair) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFamilyIndependentAtMostFixedPairWorkerComputable
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      pair.1.val pair.2.val)

/-- GapCVP reduction support. -/
def fiveIndependentAtMostBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentFixedFamilyStreamWord
    (fiveFamilyRowMajorSymbolPairs
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentAtMostFixedPairBundledStreamWord
      bound machine)

private noncomputable def fiveFamilyIndependentAtMostBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAtMostBundledStreamWord bound machine) :=
  fiveFamilyIndependentFixedFamilyStreamComputable
    (fiveFamilyRowMajorSymbolPairs
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentAtMostFixedPairBundledStreamWord
      bound machine)
    (fun pair _ =>
      fiveFamilyIndependentAtMostFixedPairBundledStreamComputable
        bound machine pair)

/-- GapCVP reduction support. -/
def fiveIndependentInitialBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine (fiveFlatWholePackedInitialClauseRecordWord
      bound machine)

private noncomputable def fiveFamilyIndependentInitialBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentInitialBundledStreamWord bound machine) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine (fiveFamilyFlatWholePackedInitialClauseRecordComputable
      bound machine)

/-- GapCVP reduction support. -/
def fiveIndependentAcceptanceBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  lengthPrefixedWord
    (fiveFlatWholeAcceptanceClauseRecordWord
      bound machine original)

private noncomputable def fiveFamilyIndependentAcceptanceBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAcceptanceBundledStreamWord
        bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatWholeAcceptanceClauseRecordComputable
      bound machine)
    structuralPrefixWriterComputable
  change BitTM
    (fun original => lengthPrefixedWord
      (fiveFlatWholeAcceptanceClauseRecordWord
        bound machine original))
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveIndependentForbiddenFixedTupleWorker
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    List Bool → List Bool :=
  if paddedAcceptancePhaseSymbolAllowed machine symbols = false then
    fiveForbiddenExactWindowWholeClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
  else
    fiveFlatRowMajorAtLeastClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)

private noncomputable def fiveFamilyIndependentForbiddenFixedTupleWorkerComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    BitTM
      (fiveIndependentForbiddenFixedTupleWorker
        bound machine symbols) := by
  by_cases hforbidden :
      paddedAcceptancePhaseSymbolAllowed machine symbols = false
  · simpa only [fiveIndependentForbiddenFixedTupleWorker, hforbidden, ↓reduceIte] using
        fiveFamilyForbiddenExactWindowWholeClauseRecordComputable
            (fiveFamilyFlatIndexedGridPolynomial bound machine)
          symbols.1.val symbols.2.1.val symbols.2.2.1.val symbols.2.2.2.val
  · simpa only [fiveIndependentForbiddenFixedTupleWorker, hforbidden, Bool.true_eq_false,
      ↓reduceIte] using
        fiveFamilyFlatRowMajorAtLeastClauseRecordComputable (fiveFamilyFlatIndexedGridPolynomial
            bound machine)
          (completePhaseSymbolCount machine.tm + 1)

/-- GapCVP reduction support. -/
def fiveIndependentForbiddenFixedTupleBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound
    (nondeterministicTableauDimensionPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveIndependentForbiddenFixedTupleWorker
      bound machine symbols)

private noncomputable def fiveFamilyIndependentForbiddenFixedTupleBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    BitTM
      (fiveIndependentForbiddenFixedTupleBundledStreamWord
        bound machine symbols) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound
    (nondeterministicTableauDimensionPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFamilyIndependentForbiddenFixedTupleWorkerComputable
      bound machine symbols)

/-- GapCVP reduction support. -/
def fiveIndependentForbiddenBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentFixedFamilyStreamWord
    (fiveFamilyRowMajorWindowSymbols
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentForbiddenFixedTupleBundledStreamWord
      bound machine)

private noncomputable def fiveFamilyIndependentForbiddenBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentForbiddenBundledStreamWord
        bound machine) :=
  fiveFamilyIndependentFixedFamilyStreamComputable
    (fiveFamilyRowMajorWindowSymbols
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentForbiddenFixedTupleBundledStreamWord
      bound machine)
    (fun symbols _ =>
      fiveFamilyIndependentForbiddenFixedTupleBundledStreamComputable
        bound machine symbols)

/-- GapCVP reduction support. -/
def fiveIndependentActualBundledCatalogueWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveIndependentAtLeastBundledStreamWord
      bound machine original ++
    (fiveIndependentAtMostBundledStreamWord
      bound machine original ++
      (fiveIndependentInitialBundledStreamWord
        bound machine original ++
        (fiveIndependentAcceptanceBundledStreamWord
          bound machine original ++
          fiveIndependentForbiddenBundledStreamWord
            bound machine original)))

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyIndependentActualBundledCatalogueComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentActualBundledCatalogueWord
        bound machine) := by
  have hleast := fiveFamilyIndependentAtLeastBundledStreamComputable
    bound machine
  have hmost := fiveFamilyIndependentAtMostBundledStreamComputable
    bound machine
  have hinitial := fiveFamilyIndependentInitialBundledStreamComputable
    bound machine
  have haccept := fiveFamilyIndependentAcceptanceBundledStreamComputable
    bound machine
  have hforbidden := fiveFamilyIndependentForbiddenBundledStreamComputable
    bound machine
  have physical := pointwiseAppendComputable
    hleast (pointwiseAppendComputable
      hmost (pointwiseAppendComputable
        hinitial (pointwiseAppendComputable
          haccept hforbidden)))
  change BitTM
    (fun original =>
      fiveIndependentAtLeastBundledStreamWord
        bound machine original ++
      (fiveIndependentAtMostBundledStreamWord
        bound machine original ++
        (fiveIndependentInitialBundledStreamWord
          bound machine original ++
          (fiveIndependentAcceptanceBundledStreamWord
            bound machine original ++
            fiveIndependentForbiddenBundledStreamWord
              bound machine original))))
  exact physical

end CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM


end GapCVP

end

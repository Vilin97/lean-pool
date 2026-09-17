/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part01

/-! # GapCVP proof, part 02 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

private theorem ofClassicalDecide {proposition : Prop}
    (proof : @decide proposition (Classical.propDecidable proposition) = true) :
    proposition :=
  @of_decide_eq_true proposition (Classical.propDecidable proposition) proof

namespace CLPhaseSoundness

open Computability Turing GapCVP.CLLocalWindows

private def firstPhaseOffset (tm : Turing.FinTM2) : Fin (blockSize tm) :=
  ⟨0, blockSize_pos tm⟩

end CLPhaseSoundness

namespace CLPhaseSpecification

open Computability Turing GapCVP.CLBoundedStates GapCVP.CLLocalWindows
open GapCVP.CLCompleteVerifierSimulation

private noncomputable def CorrectedGuessingAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  window.2.2.2.mode = .guessing ∧
    window.2.2.2.range = window.2.1.range ∧
    window.2.2.2.rangeHead = window.2.1.rangeHead ∧
    window.2.2.2.budget = window.2.1.budget ∧
    (∀ offset : Fin (blockSize machine.tm),
      window.2.1.range offset = true →
        BroadcastWitnessGuessAllowed window.2.2.2.guessBit
          (completeWitnessWindow machine.tm window offset) ∧
        PairedInputGuessAllowed window.2.2.2.guessBit
          (completePayloadWindow machine.tm window offset) ∧
        (window.2.1.payload offset = .marker →
          window.2.1.budget offset = true))
  ) (Classical.propDecidable _)

end CLPhaseSpecification

namespace CLPhaseCompleteness

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation

/-- GapCVP reduction support. -/
def decodeCorrectedPhaseRow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {width : ℕ}
    (row : Position width →
      Symbol (completePhaseSymbolCount machine.tm)) :
    Position width → CompletePhaseCell machine.tm :=
  fun position => (completePhaseSymbolEquiv machine.tm).symm
    (row position)

end CLPhaseCompleteness

namespace CLPhaseTableauSimulation

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLBoundedStates
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification GapCVP.CLPhaseCompleteness

/-- GapCVP reduction support. -/
noncomputable def FirstBlockAnchored (tm : Turing.FinTM2)
    (cell : CompletePhaseCell tm) : Bool :=
  @decide (
  completeIsFirstBlock tm cell = true →
    completeMachineBlock tm cell =
      completeMachineHead tm cell ∧
      cell.payload = cell.payloadHead ∧
      cell.range = cell.rangeHead
  ) (Classical.propDecidable _)
private noncomputable def PhaseBoundaryPreserved
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm) : Bool :=
  @decide (
  completeIsFirstBlock tm window.2.2.2 =
    completeIsFirstBlock tm window.2.1
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def AnchoredGuessingAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  CorrectedGuessingAllowed machine window ∧
    PhaseBoundaryPreserved machine.tm window ∧
    FirstBlockAnchored machine.tm window.2.1 ∧
    FirstBlockAnchored machine.tm window.2.2.2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def AnchoredInitializationAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  CompleteInitializationAllowed machine window ∧
    FirstBlockAnchored machine.tm window.2.1 ∧
    FirstBlockAnchored machine.tm window.2.2.2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def AnchoredVerificationAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  CompleteVerificationAllowed machine window ∧
    FirstBlockAnchored machine.tm window.2.1 ∧
    FirstBlockAnchored machine.tm window.2.2.2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def AnchoredAcceptanceAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  CompleteAcceptanceAllowed machine window ∧
    FirstBlockAnchored machine.tm window.2.1
  ) (Classical.propDecidable _)
private noncomputable def AnchoredPhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  CompletePhaseCoherent machine.tm window ∧
    match window.2.1.mode with
    | .guessing =>
        AnchoredGuessingAllowed machine window ∨
          AnchoredInitializationAllowed machine window
    | .verifying =>
        AnchoredVerificationAllowed machine window ∨
          AnchoredAcceptanceAllowed machine window
    | .accepting =>
        window.2.2.2 = acceptingPhaseCell machine.tm
  ) (Classical.propDecidable _)
private def anchoredPhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool := by
  classical
  exact decide (AnchoredPhaseAllowed machine window)

private theorem anchoredPhaseAllowed_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) :
    anchoredPhaseAllowed machine window = true ↔
      AnchoredPhaseAllowed machine window := by
  classical
  simp only [anchoredPhaseAllowed, Bool.decide_eq_true]

private def anchoredPhaseSymbolAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    Bool :=
  anchoredPhaseAllowed machine
    ((completePhaseSymbolEquiv machine.tm).symm window.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.2)

private def anchoredPhaseSpecification
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    Specification
      ((nondeterministicTableauDimensionPolynomial bound machine).eval
        x.length)
      (completePhaseSymbolCount machine.tm) where
  input position :=
    completePhaseSymbolEquiv machine.tm
      (initialPhaseCell bound machine x position)
  accept :=
    completePhaseSymbolEquiv machine.tm
      (acceptingPhaseCell machine.tm)
  allowed := anchoredPhaseSymbolAllowed machine

private theorem anchoredTrace_window
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace :
      Time ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Position ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Symbol (completePhaseSymbolCount machine.tm))
    (htrace : ValidTrace
      (anchoredPhaseSpecification bound machine x) trace)
    (window : Window
      ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length)) :
    AnchoredPhaseAllowed machine
      (decodeCorrectedPhaseRow machine (trace window.1.1)
          (leftPosition window),
        decodeCorrectedPhaseRow machine (trace window.1.1)
          window.1.2,
        decodeCorrectedPhaseRow machine (trace window.1.1)
          (rightPosition window),
        decodeCorrectedPhaseRow machine
          (trace (nextTime window)) window.1.2) := by
  have htrace' := htrace
  simp only [ValidTrace, decide_eq_true_eq] at htrace'
  apply (anchoredPhaseAllowed_iff machine _).mp
  exact htrace'.2.2 window

private theorem anchoredTrace_initial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace :
      Time ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Position ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Symbol (completePhaseSymbolCount machine.tm))
    (htrace : ValidTrace
      (anchoredPhaseSpecification bound machine x) trace)
    (position : Position
      ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length)) :
    decodeCorrectedPhaseRow machine (trace 0) position =
      initialPhaseCell bound machine x position := by
  have htrace' := htrace
  simp only [ValidTrace, decide_eq_true_eq] at htrace'
  simp only [decodeCorrectedPhaseRow, htrace'.1 position, anchoredPhaseSpecification,
      Equiv.symm_apply_apply]

end CLPhaseTableauSimulation

namespace CLPhaseTraceInduction

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation

private def unpackPhaseMachineCell
    (tm : Turing.FinTM2)
    (width : ℕ)
    (row : Position width → CompletePhaseCell tm)
    (index : Position width) : LocalCellSymbol tm :=
  completeMachineBlock tm
    (row (coordinateBlock tm width index))
    (coordinateOffset tm width index)

private def unpackPhaseWitness
    (tm : Turing.FinTM2)
    (width : ℕ)
    (row : Position width → CompletePhaseCell tm)
    (index : Position width) : PhaseTag :=
  (unpackPhaseMachineCell tm width row index).1

private def unpackPhasePayload
    (tm : Turing.FinTM2)
    (width : ℕ)
    (row : Position width → CompletePhaseCell tm)
    (index : Position width) : PairedInputTag :=
  (row (coordinateBlock tm width index)).payload
    (coordinateOffset tm width index)

/-- GapCVP reduction support. -/
def canonicalAnchoredVerifyingRow
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration)
    (hint : FiniteVerifierHint machine.tm)
    (annotation : Bool) :
    Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm :=
  fun position => {
    mode := .verifying
    script := canonicalScriptBlockRow machine
      (rowWidth bound machine x) certificate
      configuration hsupported hint position
    payload := pairedInputBlockAt machine.tm
      (rowWidth bound machine x) x certificate position
    payloadHead := pairedInputBlockAt machine.tm
      (rowWidth bound machine x) x certificate 0
    range := phaseRangeBlockAt machine.tm
      (rowWidth bound machine x) position
    rangeHead := phaseRangeBlockAt machine.tm
      (rowWidth bound machine x) 0
    budget := phaseBudgetBlockAt bound machine x position
    guessBit := annotation
  }

private theorem canonicalAnchoredVerifyingRow_firstBlockAnchored
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration)
    (hint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    FirstBlockAnchored machine.tm
      (canonicalAnchoredVerifyingRow bound machine x certificate
        configuration hsupported hint annotation position) := by
  simp only [FirstBlockAnchored, decide_eq_true_eq]
  intro hfirst
  have hposition : position.val = 0 := by
    simpa only [Fin.val_eq_zero_iff, completeIsFirstBlock, canonicalAnchoredVerifyingRow,
        canonicalScriptBlockRow,
        decide_eq_true_eq] using hfirst
  have hzero : position = 0 := by
    apply Fin.ext
    exact hposition
  subst position
  exact ⟨rfl, rfl, rfl⟩

end CLPhaseTraceInduction

namespace CLPhaseGlobalSimulation

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRowBounds GapCVP.CLLocalWindows GapCVP.CLExactVerifierTransition
open GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction

/-- GapCVP reduction support. -/
def anchoredVerifierWindowAt
    (tm : Turing.FinTM2) (width : ℕ)
    (first next : Position width → CompletePhaseCell tm)
    (position : Position width) : CompletePhaseWindow tm :=
  (first (leftBlock width position),
    first position,
    first (rightBlock width position),
    next position)

private theorem canonicalAnchoredVerifierWindow_coherent
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    CompletePhaseCoherent machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          first hfirst firstHint annotation)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          next hnext nextHint annotation) position) := by
  simp only [CompletePhaseCoherent, anchoredVerifierWindowAt, canonicalAnchoredVerifyingRow,
      and_self,
      decide_true]

private theorem canonicalAnchoredVerifierWindow_static
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (firstAnnotation nextAnnotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    CompleteStaticTracksPreserved machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          first hfirst firstHint firstAnnotation)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          next hnext nextHint nextAnnotation) position) := by
  simp only [CompleteStaticTracksPreserved, anchoredVerifierWindowAt,
      canonicalAnchoredVerifyingRow,
      canonicalScriptBlockRow, Fin.val_eq_zero_iff, completeIsFirstBlock, and_self, decide_true]

private theorem canonicalAnchoredVerifierWindow_allowed_iff
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    AnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          first hfirst firstHint annotation)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          next hnext nextHint annotation) position) ↔
      scriptBlockAllowed machine
        (scriptBlockWindowAt machine.tm
          (rowWidth bound machine x)
          (canonicalScriptBlockRow machine
            (rowWidth bound machine x)
            certificate first hfirst firstHint)
          (canonicalScriptBlockRow machine
            (rowWidth bound machine x)
            certificate next hnext nextHint) position) = true := by
  let window := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x)
    (canonicalAnchoredVerifyingRow bound machine x certificate
      first hfirst firstHint annotation)
    (canonicalAnchoredVerifyingRow bound machine x certificate
      next hnext nextHint annotation) position
  have hfirstAnchor : FirstBlockAnchored machine.tm window.2.1 :=
    canonicalAnchoredVerifyingRow_firstBlockAnchored
      bound machine x certificate first hfirst
      firstHint annotation position
  have hnextAnchor : FirstBlockAnchored machine.tm window.2.2.2 :=
    canonicalAnchoredVerifyingRow_firstBlockAnchored
      bound machine x certificate next hnext
      nextHint annotation position
  have hmode : window.2.1.mode = .verifying := rfl
  have hnextMode : window.2.2.2.mode = .verifying := rfl
  have hscript : completeScriptWindow machine.tm window =
      scriptBlockWindowAt machine.tm (rowWidth bound machine x)
        (canonicalScriptBlockRow machine
          (rowWidth bound machine x)
          certificate first hfirst firstHint)
        (canonicalScriptBlockRow machine
          (rowWidth bound machine x)
          certificate next hnext nextHint) position := rfl
  constructor
  · intro hallowed
    change AnchoredPhaseAllowed machine window at hallowed
    have hallowed' := hallowed
    simp only [AnchoredPhaseAllowed, decide_eq_true_eq] at hallowed'
    have hbranch :
        AnchoredVerificationAllowed machine window ∨
          AnchoredAcceptanceAllowed machine window := by
      simpa only [hmode] using hallowed'.2
    rcases hbranch with hverification | hacceptance
    · have hverification' := hverification
      simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
        decide_eq_true_eq] at hverification'
      rw [← hscript]
      exact hverification'.1.2.2
    · have hacceptance' := hacceptance
      simp only [AnchoredAcceptanceAllowed, CompleteAcceptanceAllowed,
        decide_eq_true_eq] at hacceptance'
      have hacceptanceOuter := ofClassicalDecide hacceptance'
      have hacceptanceCore := ofClassicalDecide hacceptanceOuter.1
      have hfixed := hacceptanceCore.1
      have himpossible := congrArg CompletePhaseCell.mode hfixed
      simp only [hnextMode, acceptingPhaseCell, reduceCtorEq] at himpossible
  · intro hallowed
    change AnchoredPhaseAllowed machine window
    simp only [AnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨canonicalAnchoredVerifierWindow_coherent
      bound machine x certificate first next hfirst hnext
      firstHint nextHint annotation position, ?_⟩
    change AnchoredVerificationAllowed machine window ∨
      AnchoredAcceptanceAllowed machine window
    left
    simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
      decide_eq_true_eq]
    refine ⟨⟨hnextMode,
      canonicalAnchoredVerifierWindow_static
        bound machine x certificate first next hfirst hnext
        firstHint nextHint annotation annotation position,
      ?_⟩, hfirstAnchor, hnextAnchor⟩
    rw [hscript]
    exact hallowed

private theorem actualStep_iff_anchoredCanonicalVerifierWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstSpace : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ rowWidth bound machine x)
    (hnextSpace : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ rowWidth bound machine x) :
    machine.tm.step first = some next ↔
      ∃ (firstHint nextHint : FiniteVerifierHint machine.tm),
        ∀ position : Position (rowWidth bound machine x),
          AnchoredPhaseAllowed machine
            (anchoredVerifierWindowAt machine.tm
              (rowWidth bound machine x)
              (canonicalAnchoredVerifyingRow
                bound machine x certificate
                first hfirst firstHint false)
              (canonicalAnchoredVerifyingRow
                bound machine x certificate
                next hnext nextHint false) position) := by
  constructor
  · intro hstep
    obtain ⟨firstHint, nextHint, hwindows⟩ :=
      (actualStep_iff_canonical_block_windows
        machine (rowWidth bound machine x) certificate
        first next hfirst hnext hfirstSpace hnextSpace).mp hstep
    refine ⟨firstHint, nextHint, ?_⟩
    intro position
    exact (canonicalAnchoredVerifierWindow_allowed_iff
      bound machine x certificate first next hfirst hnext
      firstHint nextHint false position).mpr
      (hwindows position)
  · rintro ⟨firstHint, nextHint, hwindows⟩
    apply (actualStep_iff_canonical_block_windows
      machine (rowWidth bound machine x) certificate
      first next hfirst hnext hfirstSpace hnextSpace).mpr
    refine ⟨firstHint, nextHint, ?_⟩
    intro position
    exact (canonicalAnchoredVerifierWindow_allowed_iff
      bound machine x certificate first next hfirst hnext
      firstHint nextHint false position).mp
      (hwindows position)

end CLPhaseGlobalSimulation

namespace CLPhaseVerifierSimulation

open Computability Turing GapCVP.CL GapCVP.CLPushAlphabet GapCVP.CLCellRowBounds
open GapCVP.CLExactVerifierTransition GapCVP.CLGlobalTableauSimulation
open GapCVP.CLTableauSimulationCert GapCVP.CLFullTableauEmitter GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation

private noncomputable def AllCanonicalAnchoredVerifierTraceWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    {steps : ℕ}
    (configuration : Fin (steps + 1) → machine.tm.Cfg)
    (hsupported : ∀ time : Fin (steps + 1),
      StackAtomSupported machine (configuration time))
    (hint : Fin (steps + 1) → FiniteVerifierHint machine.tm) : Bool :=
  @decide (
  ∀ (time : Fin steps)
    (position : Position (rowWidth bound machine x)),
    AnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          (configuration (Fin.castSucc time))
          (hsupported (Fin.castSucc time))
          (hint (Fin.castSucc time)) false)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          (configuration time.succ)
          (hsupported time.succ)
          (hint time.succ) false) position)
  ) (Classical.propDecidable _)
private theorem canonicalAnchoredVerifierTraceWindows_iff_actualRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    {steps : ℕ}
    (configuration : Fin (steps + 1) → machine.tm.Cfg)
    (hsupported : ∀ time : Fin (steps + 1),
      StackAtomSupported machine (configuration time))
    (hspace : ∀ (time : Fin (steps + 1)) (stack : machine.tm.K),
      ((configuration time).stk stack).length ≤
        rowWidth bound machine x) :
    (∃ hint : Fin (steps + 1) → FiniteVerifierHint machine.tm,
      AllCanonicalAnchoredVerifierTraceWindows bound machine x
        certificate configuration hsupported hint) ↔
      ∀ time : Fin steps,
        machine.tm.step (configuration (Fin.castSucc time)) =
          some (configuration time.succ) := by
  constructor
  · rintro ⟨hint, hwindows⟩ time
    have hwindows' := hwindows
    simp only [AllCanonicalAnchoredVerifierTraceWindows,
      decide_eq_true_eq] at hwindows'
    apply (actualStep_iff_anchoredCanonicalVerifierWindows
      bound machine x certificate
      (configuration (Fin.castSucc time))
      (configuration time.succ)
      (hsupported (Fin.castSucc time))
      (hsupported time.succ)
      (hspace (Fin.castSucc time))
      (hspace time.succ)).mpr
    exact ⟨hint (Fin.castSucc time),
      hint time.succ, hwindows' time⟩
  · intro hrun
    have hlocal : ∀ time : Fin steps,
        ∃ firstHint : FiniteVerifierHint machine.tm,
          scriptVerifierAllowed machine
              (scriptVerifierQueryOf machine
                (configuration (Fin.castSucc time))
                (configuration time.succ)
                (hsupported (Fin.castSucc time))
                (hsupported time.succ) firstHint) = true ∧
            AllVerifierStackWindows machine
              (rowWidth bound machine x)
              (configuration (Fin.castSucc time))
              (configuration time.succ)
              (hsupported (Fin.castSucc time))
              (hsupported time.succ) firstHint := by
      intro time
      exact (actualStep_iff_finite_script_and_windows
        machine (rowWidth bound machine x)
        (configuration (Fin.castSucc time))
        (configuration time.succ)
        (hsupported (Fin.castSucc time))
        (hsupported time.succ)
        (hspace (Fin.castSucc time))
        (hspace time.succ)).mp (hrun time)
    choose selected hselectedScript hselectedWindows using hlocal
    let hint : Fin (steps + 1) → FiniteVerifierHint machine.tm :=
      fun time =>
        if htime : time.val < steps then
          selected ⟨time.val, htime⟩
        else
          defaultVerifierHint machine.tm
    refine ⟨hint, ?_⟩
    simp only [AllCanonicalAnchoredVerifierTraceWindows, decide_eq_true_eq]
    intro time position
    have hcurrent : hint (Fin.castSucc time) = selected time := by
      simp only [Fin.val_castSucc, time.isLt, ↓reduceDIte, Fin.eta, hint]
    rw [hcurrent]
    apply (canonicalAnchoredVerifierWindow_allowed_iff
      bound machine x certificate
      (configuration (Fin.castSucc time))
      (configuration time.succ)
      (hsupported (Fin.castSucc time))
      (hsupported time.succ)
      (selected time) (hint time.succ) false position).mpr
    exact (canonicalScriptBlockWindows_iff
      machine (rowWidth bound machine x) certificate
      (configuration (Fin.castSucc time))
      (configuration time.succ)
      (hsupported (Fin.castSucc time))
      (hsupported time.succ)
      (hspace (Fin.castSucc time))
      (hspace time.succ)
      (selected time) (hint time.succ)).mpr
      ⟨hselectedScript time,
        hselectedWindows time⟩ position

end CLPhaseVerifierSimulation

namespace CLValidTraceSoundness

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLTableauStitching GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation

private noncomputable def AllAnchoredPhaseWindows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm) : Bool :=
  @decide (
  ∀ position : Position width,
    AnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm width
        first next position)
  ) (Classical.propDecidable _)
private theorem allAnchoredWindows_mode_constant
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : AllAnchoredPhaseWindows machine width first next) :
    ∀ position : Position width,
      (first position).mode = (first 0).mode := by
  intro position
  induction position using Fin.induction with
  | zero => rfl
  | succ position ih =>
      have hlocal := hwindows
      simp only [AllAnchoredPhaseWindows, decide_eq_true_eq] at hlocal
      have hcoherent := hlocal position.succ
      simp only [AnchoredPhaseAllowed, CompletePhaseCoherent,
        decide_eq_true_eq] at hcoherent
      have hcoherentOuter := ofClassicalDecide hcoherent
      have hcoherentCore := ofClassicalDecide hcoherentOuter.1
      have hleft := hcoherentCore.1
      change (first (leftBlock width position.succ)).mode =
        (first position.succ).mode at hleft
      rw [leftBlock_succ] at hleft
      exact hleft.symm.trans ih

private theorem allAnchoredWindows_guessBit_constant
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : AllAnchoredPhaseWindows machine width first next) :
    ∀ position : Position width,
      (first position).guessBit = (first 0).guessBit := by
  intro position
  induction position using Fin.induction with
  | zero => rfl
  | succ position ih =>
      have hlocal := hwindows
      simp only [AllAnchoredPhaseWindows, decide_eq_true_eq] at hlocal
      have hcoherent := hlocal position.succ
      simp only [AnchoredPhaseAllowed, CompletePhaseCoherent,
        decide_eq_true_eq] at hcoherent
      have hcoherentOuter := ofClassicalDecide hcoherent
      have hcoherentCore := ofClassicalDecide hcoherentOuter.1
      have hleft := hcoherentCore.2.2.1
      change (first (leftBlock width position.succ)).guessBit =
        (first position.succ).guessBit at hleft
      rw [leftBlock_succ] at hleft
      exact hleft.symm.trans ih

private theorem anchoredGuessing_boundary
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hwindow : AnchoredGuessingAllowed machine window) :
    completeIsFirstBlock machine.tm window.2.2.2 =
      completeIsFirstBlock machine.tm window.2.1 := by
  have hwindow' := hwindow
  simp only [AnchoredGuessingAllowed, PhaseBoundaryPreserved,
    decide_eq_true_eq] at hwindow'
  exact hwindow'.2.1

private theorem anchoredVerification_boundary
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hwindow : AnchoredVerificationAllowed machine window) :
    completeIsFirstBlock machine.tm window.2.2.2 =
      completeIsFirstBlock machine.tm window.2.1 := by
  have hwindow' := hwindow
  simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
    CompleteStaticTracksPreserved, decide_eq_true_eq] at hwindow'
  exact hwindow'.1.2.1.2.2.2.2.2

private theorem anchoredValidTrace_allWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace :
      Time ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Position ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Symbol (completePhaseSymbolCount machine.tm))
    (htrace : ValidTrace
      (anchoredPhaseSpecification bound machine x) trace)
    (time : Fin ((nondeterministicTableauDimensionPolynomial
      bound machine).eval x.length)) :
    AllAnchoredPhaseWindows machine
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)))
      (decodeCorrectedPhaseRow machine (trace time.succ)) := by
  simp only [AllAnchoredPhaseWindows, decide_eq_true_eq]
  intro position
  exact anchoredTrace_window bound machine x trace htrace
    (windowAt time position)

private theorem anchoredValidTrace_mode_constant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace :
      Time ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Position ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Symbol (completePhaseSymbolCount machine.tm))
    (htrace : ValidTrace
      (anchoredPhaseSpecification bound machine x) trace)
    (time : Fin ((nondeterministicTableauDimensionPolynomial
      bound machine).eval x.length))
    (position : Position (rowWidth bound machine x)) :
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)) position).mode =
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)) 0).mode :=
  allAnchoredWindows_mode_constant machine
    (rowWidth bound machine x)
    (decodeCorrectedPhaseRow machine (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ))
    (anchoredValidTrace_allWindows bound machine x
      trace htrace time) position

private theorem anchoredValidTrace_guessBit_constant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace :
      Time ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Position ((nondeterministicTableauDimensionPolynomial
        bound machine).eval x.length) →
      Symbol (completePhaseSymbolCount machine.tm))
    (htrace : ValidTrace
      (anchoredPhaseSpecification bound machine x) trace)
    (time : Fin ((nondeterministicTableauDimensionPolynomial
      bound machine).eval x.length))
    (position : Position (rowWidth bound machine x)) :
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)) position).guessBit =
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)) 0).guessBit :=
  allAnchoredWindows_guessBit_constant machine
    (rowWidth bound machine x)
    (decodeCorrectedPhaseRow machine (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ))
    (anchoredValidTrace_allWindows bound machine x
      trace htrace time) position

end CLValidTraceSoundness

namespace CLWholeTraceSoundness

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLCellRowBounds
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLValidTraceSoundness

/-- GapCVP reduction support. -/
abbrev AnchoredPhaseTrace
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :=
  Time (rowWidth bound machine x) →
    Position (rowWidth bound machine x) →
      Symbol (completePhaseSymbolCount machine.tm)

/-- GapCVP reduction support. -/
noncomputable def AnchoredPhaseMasks
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (position : Position (rowWidth bound machine x))
    (cell : CompletePhaseCell machine.tm) : Bool :=
  @decide (
  cell.range =
      phaseRangeBlockAt machine.tm (rowWidth bound machine x) position ∧
    cell.rangeHead =
      phaseRangeBlockAt machine.tm (rowWidth bound machine x) 0 ∧
    cell.budget = phaseBudgetBlockAt bound machine x position ∧
    completeIsFirstBlock machine.tm cell = decide (position.val = 0)
  ) (Classical.propDecidable _)
private theorem anchoredPhase_old_not_accepting_of_next_not_accepting
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : AnchoredPhaseAllowed machine window)
    (hnext : window.2.2.2.mode ≠ .accepting) :
    window.2.1.mode ≠ .accepting := by
  have hallowed' := hallowed
  simp only [AnchoredPhaseAllowed, decide_eq_true_eq] at hallowed'
  intro hmode
  have hcleared : window.2.2.2 = acceptingPhaseCell machine.tm := by
    simpa only [hmode] using hallowed'.2
  apply hnext
  rw [hcleared]
  rfl

private theorem anchoredPhase_staticMasks_of_next_not_accepting
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : AnchoredPhaseAllowed machine window)
    (hnext : window.2.2.2.mode ≠ .accepting) :
    window.2.2.2.range = window.2.1.range ∧
      window.2.2.2.rangeHead = window.2.1.rangeHead ∧
      window.2.2.2.budget = window.2.1.budget ∧
      completeIsFirstBlock machine.tm window.2.2.2 =
        completeIsFirstBlock machine.tm window.2.1 := by
  have hallowed' := hallowed
  simp only [AnchoredPhaseAllowed, decide_eq_true_eq] at hallowed'
  cases hmode : window.2.1.mode with
  | guessing =>
      have hcases :
          AnchoredGuessingAllowed machine window ∨
            AnchoredInitializationAllowed machine window := by
        simpa only [hmode] using hallowed'.2
      rcases hcases with hguess | hinit
      · have hguess' := hguess
        simp only [AnchoredGuessingAllowed, CorrectedGuessingAllowed,
          decide_eq_true_eq] at hguess'
        exact ⟨hguess'.1.2.1,
          hguess'.1.2.2.1,
          hguess'.1.2.2.2.1,
          anchoredGuessing_boundary machine window hguess⟩
      · have hinit' := hinit
        simp only [AnchoredInitializationAllowed, CompleteInitializationAllowed,
          decide_eq_true_eq] at hinit'
        have hinitOuter := ofClassicalDecide hinit'
        have hinitCore := ofClassicalDecide hinitOuter.1
        have hstatic := hinitCore.2.1
        simp only [CompleteStaticTracksPreserved, decide_eq_true_eq] at hstatic
        exact ⟨hstatic.2.2.1,
          hstatic.2.2.2.1,
          hstatic.2.2.2.2.1,
          hstatic.2.2.2.2.2⟩
  | verifying =>
      have hcases :
          AnchoredVerificationAllowed machine window ∨
            AnchoredAcceptanceAllowed machine window := by
        simpa only [hmode] using hallowed'.2
      rcases hcases with hverify | haccept
      · have hverify' := hverify
        simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
          decide_eq_true_eq] at hverify'
        have hstatic := hverify'.1.2.1
        simp only [CompleteStaticTracksPreserved, decide_eq_true_eq] at hstatic
        exact ⟨hstatic.2.2.1,
          hstatic.2.2.2.1,
          hstatic.2.2.2.2.1,
          hstatic.2.2.2.2.2⟩
      · have haccept' := haccept
        simp only [AnchoredAcceptanceAllowed, CompleteAcceptanceAllowed,
          decide_eq_true_eq] at haccept'
        have hacceptOuter := ofClassicalDecide haccept'
        have hacceptCore := ofClassicalDecide hacceptOuter.1
        exact (hnext (by rw [hacceptCore.1]; rfl)).elim
  | accepting =>
      exact ((anchoredPhase_old_not_accepting_of_next_not_accepting
        machine window hallowed hnext) hmode).elim

private theorem anchoredValidTrace_masks_of_not_accepting
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x))
    (position : Position (rowWidth bound machine x)) :
    (decodeCorrectedPhaseRow machine (trace time) position).mode ≠
        .accepting →
      AnchoredPhaseMasks bound machine x position
        (decodeCorrectedPhaseRow machine (trace time) position) := by
  simp only [AnchoredPhaseMasks, decide_eq_true_eq]
  induction time using Fin.induction with
  | zero =>
      intro _
      have hinitial :
          decodeCorrectedPhaseRow machine (trace 0) position =
            initialPhaseCell bound machine x position := by
        exact anchoredTrace_initial bound machine x trace htrace position
      rw [hinitial]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | succ time ih =>
      intro hnext
      have hall :=
        anchoredValidTrace_allWindows bound machine x trace htrace time
      simp only [AllAnchoredPhaseWindows, decide_eq_true_eq] at hall
      have hwindow := hall position
      have hold := anchoredPhase_old_not_accepting_of_next_not_accepting
        machine _ hwindow hnext
      have hstatic := anchoredPhase_staticMasks_of_next_not_accepting
        machine _ hwindow hnext
      obtain ⟨hrange, hrangeHead, hbudget, hboundary⟩ := ih hold
      exact ⟨hstatic.1.trans hrange,
        hstatic.2.1.trans hrangeHead,
        hstatic.2.2.1.trans hbudget,
        hstatic.2.2.2.trans hboundary⟩

private theorem anchoredValidTrace_has_acceptingCell
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace) :
    ∃ position : Position (rowWidth bound machine x),
      decodeCorrectedPhaseRow machine
          (trace (Fin.last (rowWidth bound machine x))) position =
        acceptingPhaseCell machine.tm := by
  have htrace' := htrace
  simp only [ValidTrace, decide_eq_true_eq] at htrace'
  obtain ⟨position, haccept⟩ := htrace'.2.1
  refine ⟨position, ?_⟩
  change
    trace (Fin.last (rowWidth bound machine x)) position =
      completePhaseSymbolEquiv machine.tm
        (acceptingPhaseCell machine.tm) at haccept
  change
    (completePhaseSymbolEquiv machine.tm).symm
      (trace (Fin.last (rowWidth bound machine x)) position) =
      acceptingPhaseCell machine.tm
  rw [haccept]
  exact (completePhaseSymbolEquiv machine.tm).symm_apply_apply _

end CLWholeTraceSoundness

namespace CLFirstAcceptance

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLCellRowBounds
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness
open GapCVP.CLWholeTraceSoundness

private noncomputable def HasAcceptingModeAt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (index : ℕ) : Bool :=
  @decide (
  ∃ (time : Time (rowWidth bound machine x))
    (position : Position (rowWidth bound machine x)),
    time.val = index ∧
      (decodeCorrectedPhaseRow machine (trace time) position).mode =
        .accepting
  ) (Classical.propDecidable _)
private theorem anchoredValidTrace_hasAcceptingTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace) :
    ∃ index : ℕ, HasAcceptingModeAt bound machine x trace index := by
  simp only [HasAcceptingModeAt, decide_eq_true_eq]
  obtain ⟨position, haccept⟩ :=
    anchoredValidTrace_has_acceptingCell bound machine x trace htrace
  refine ⟨rowWidth bound machine x,
    Fin.last (rowWidth bound machine x), position, rfl, ?_⟩
  rw [haccept]
  rfl

private noncomputable def firstAcceptanceIndex
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace) :
    ℕ := by
  classical
  exact Nat.find (anchoredValidTrace_hasAcceptingTime
    bound machine x trace htrace)

private theorem firstAcceptanceIndex_spec
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace) :
    HasAcceptingModeAt bound machine x trace
      (firstAcceptanceIndex bound machine x trace htrace) := by
  classical
  exact Nat.find_spec (anchoredValidTrace_hasAcceptingTime
    bound machine x trace htrace)

private theorem firstAcceptanceIndex_min
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace)
    (index : ℕ)
    (hindex : index < firstAcceptanceIndex
      bound machine x trace htrace) :
    ¬ HasAcceptingModeAt bound machine x trace index := by
  classical
  exact Nat.find_min (anchoredValidTrace_hasAcceptingTime
    bound machine x trace htrace) hindex

private theorem anchoredPhase_first_acceptance_is_verifying
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : AnchoredPhaseAllowed machine window)
    (hnext : window.2.2.2.mode = .accepting)
    (hold : window.2.1.mode ≠ .accepting) :
    window.2.1.mode = .verifying ∧
      AnchoredAcceptanceAllowed machine window := by
  have hallowed' := hallowed
  simp only [AnchoredPhaseAllowed, decide_eq_true_eq] at hallowed'
  cases hmode : window.2.1.mode with
  | guessing =>
      have hcases :
          AnchoredGuessingAllowed machine window ∨
            AnchoredInitializationAllowed machine window := by
        simpa only [hmode] using hallowed'.2
      rcases hcases with hguess | hinit
      · have hguess' := hguess
        simp only [AnchoredGuessingAllowed, CorrectedGuessingAllowed,
          decide_eq_true_eq] at hguess'
        have hguessMode := hguess'.1.1
        rw [hnext] at hguessMode
        cases hguessMode
      · have hinit' := hinit
        simp only [AnchoredInitializationAllowed, CompleteInitializationAllowed,
          decide_eq_true_eq] at hinit'
        have hinitOuter := ofClassicalDecide hinit'
        have hinitCore := ofClassicalDecide hinitOuter.1
        have hinitMode := hinitCore.1
        rw [hnext] at hinitMode
        cases hinitMode
  | verifying =>
      have hcases :
          AnchoredVerificationAllowed machine window ∨
            AnchoredAcceptanceAllowed machine window := by
        simpa only [hmode] using hallowed'.2
      rcases hcases with hverify | haccept
      · have hverify' := hverify
        simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
          decide_eq_true_eq] at hverify'
        have hverifyMode := hverify'.1.1
        rw [hnext] at hverifyMode
        cases hverifyMode
      · exact ⟨rfl, haccept⟩
  | accepting =>
      exact (hold hmode).elim

private theorem anchoredValidTrace_has_first_checked_acceptance
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace (anchoredPhaseSpecification bound machine x) trace) :
    ∃ (time : Fin (rowWidth bound machine x))
      (position : Position (rowWidth bound machine x)),
      AnchoredAcceptanceAllowed machine
          (anchoredVerifierWindowAt machine.tm
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)))
            (decodeCorrectedPhaseRow machine (trace time.succ))
            position) ∧
        (∀ other : Position (rowWidth bound machine x),
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)) other).mode = .verifying) ∧
        (∀ other : Position (rowWidth bound machine x),
          AnchoredPhaseMasks bound machine x other
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)) other)) ∧
        (∀ (earlier : Time (rowWidth bound machine x)),
          earlier.val ≤ time.val →
          ∀ other : Position (rowWidth bound machine x),
            (decodeCorrectedPhaseRow machine
              (trace earlier) other).mode ≠ .accepting) := by
  have hfirst := firstAcceptanceIndex_spec bound machine x trace htrace
  simp only [HasAcceptingModeAt, decide_eq_true_eq] at hfirst
  obtain ⟨acceptTime, position, hindex, hmode⟩ := hfirst
  have hnonzero : acceptTime.val ≠ 0 := by
    intro hzero
    have htime : acceptTime = 0 := by
      apply Fin.ext
      exact hzero
    subst acceptTime
    have hinitial :
        decodeCorrectedPhaseRow machine (trace 0) position =
          initialPhaseCell bound machine x position := by
      exact anchoredTrace_initial bound machine x trace htrace position
    rw [hinitial] at hmode
    cases hmode
  have hpositive : 0 < acceptTime.val := Nat.pos_of_ne_zero hnonzero
  let previous : Fin (rowWidth bound machine x) :=
    ⟨acceptTime.val - 1, by
      have hbound := acceptTime.isLt
      omega⟩
  have hnext : previous.succ = acceptTime := by
    apply Fin.ext
    dsimp [previous]
    omega
  have hprefix :
      ∀ (earlier : Time (rowWidth bound machine x)),
        earlier.val < acceptTime.val →
          ∀ other : Position (rowWidth bound machine x),
            (decodeCorrectedPhaseRow machine
              (trace earlier) other).mode ≠ .accepting := by
    intro earlier hearlier other hearlyMode
    have hfirst :
        earlier.val < firstAcceptanceIndex
          bound machine x trace htrace := by
      omega
    have hearly : HasAcceptingModeAt bound machine x trace earlier.val := by
      simp only [HasAcceptingModeAt, decide_eq_true_eq]
      exact ⟨earlier, other, rfl, hearlyMode⟩
    exact (firstAcceptanceIndex_min bound machine x trace htrace
      earlier.val hfirst) hearly
  have hall :=
    anchoredValidTrace_allWindows bound machine x trace htrace previous
  simp only [AllAnchoredPhaseWindows, decide_eq_true_eq] at hall
  have hwindow := hall position
  have hnextMode :
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc previous)))
        (decodeCorrectedPhaseRow machine (trace previous.succ))
        position).2.2.2.mode = .accepting := by
    change
      (decodeCorrectedPhaseRow machine
        (trace previous.succ) position).mode = .accepting
    rw [hnext]
    exact hmode
  have hprevious :
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc previous)) position).mode ≠ .accepting := by
    apply hprefix (Fin.castSucc previous)
    dsimp [previous]
    omega
  obtain ⟨hverifying, haccept⟩ :=
    anchoredPhase_first_acceptance_is_verifying machine _
      hwindow hnextMode hprevious
  refine ⟨previous, position, haccept, ?_, ?_, ?_⟩
  · intro other
    have hother := anchoredValidTrace_mode_constant
      bound machine x trace htrace previous other
    have hselected := anchoredValidTrace_mode_constant
      bound machine x trace htrace previous position
    exact hother.trans (hselected.symm.trans hverifying)
  · intro other
    apply anchoredValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc previous) other
    apply hprefix (Fin.castSucc previous)
    dsimp [previous]
    omega
  · intro earlier hearlier other
    apply hprefix earlier
    have hprev : previous.val = acceptTime.val - 1 := rfl
    omega

end CLFirstAcceptance

namespace CLArbitraryVerifierSoundness

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLLocalWindows
open GapCVP.CLTableauStitching GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseGlobalSimulation

private noncomputable def AllAnchoredVerificationWindows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm) : Bool :=
  @decide (
  ∀ position : Position width,
    AnchoredVerificationAllowed machine
      (anchoredVerifierWindowAt machine.tm width
        first next position)
  ) (Classical.propDecidable _)
private theorem anchoredPhase_verification_of_verifying_modes
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : AnchoredPhaseAllowed machine window)
    (hfirst : window.2.1.mode = .verifying)
    (hnext : window.2.2.2.mode = .verifying) :
    AnchoredVerificationAllowed machine window := by
  have allowed := hallowed
  simp only [GapCVP.CLPhaseTableauSimulation.AnchoredPhaseAllowed, decide_eq_true_eq] at allowed
  have hcases :
      AnchoredVerificationAllowed machine window ∨
        AnchoredAcceptanceAllowed machine window := by
    simpa only [hfirst] using allowed.2
  rcases hcases with hverify | haccept
  · exact hverify
  · have acceptance := haccept
    simp only [GapCVP.CLPhaseTableauSimulation.AnchoredAcceptanceAllowed,
        GapCVP.CLCompleteVerifierSimulation.CompleteAcceptanceAllowed,
      decide_eq_true_eq] at acceptance
    have acceptanceOuter := ofClassicalDecide acceptance
    have acceptanceCore := ofClassicalDecide acceptanceOuter.1
    rw [acceptanceCore.1] at hnext
    cases hnext

private theorem allAnchoredVerificationWindows_script
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : AllAnchoredVerificationWindows
      machine width first next)
    (position : Position width) :
    scriptBlockAllowed machine
      (completeScriptWindow machine.tm
        (anchoredVerifierWindowAt machine.tm width
          first next position)) = true := by
  have windows := hwindows
  simp only [AllAnchoredVerificationWindows, decide_eq_true_eq] at windows
  have verification := windows position
  simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
    decide_eq_true_eq] at verification
  exact verification.1.2.2

private theorem allAnchoredVerificationWindows_scriptCoherent
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : AllAnchoredVerificationWindows
      machine width first next)
    (position : Position width) :
    ScriptBlockCoherent machine.tm
      (completeScriptWindow machine.tm
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :=
  ((scriptBlockAllowed_iff machine
    (completeScriptWindow machine.tm
      (anchoredVerifierWindowAt machine.tm width
        first next position))).mp
    (allAnchoredVerificationWindows_script machine width
      first next hwindows position)).1

private theorem allAnchoredVerificationWindows_hint_constant
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : AllAnchoredVerificationWindows
      machine width first next) :
    ∀ position : Position width,
      (first position).script.2.1 = (first 0).script.2.1 := by
  intro position
  induction position using Fin.induction with
  | zero => rfl
  | succ position ih =>
      have coherent :=
        allAnchoredVerificationWindows_scriptCoherent
          machine width first next hwindows position.succ
      simp only [GapCVP.CLTableauSimulationCert.ScriptBlockCoherent, decide_eq_true_eq] at coherent
      have hleft := coherent.2.2.1
      change
        (first (leftBlock width position.succ)).script.2.1 =
          (first position.succ).script.2.1 at hleft
      rw [leftBlock_succ] at hleft
      exact hleft.symm.trans ih

end CLArbitraryVerifierSoundness

namespace CLStackShiftSoundness

open Computability Turing GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLExactVerifierTransition

private noncomputable def OccupiedAtomTrack
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atoms : List (CellAtom machine.tm)) : Bool :=
  @decide (
  ∀ atom ∈ atoms,
    ∃ value : machine.tm.Γ stack,
      cellAtomValue machine stack atom = some value
  ) (Classical.propDecidable _)
private theorem occupiedAtomTrack_filterMap_drop
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atoms : List (CellAtom machine.tm))
    (hoccupied : OccupiedAtomTrack machine stack atoms)
    (count : ℕ) :
    (atoms.filterMap (cellAtomValue machine stack)).drop count =
      (atoms.drop count).filterMap (cellAtomValue machine stack) := by
  induction count generalizing atoms with
  | zero => simp only [List.drop_zero]
  | succ count induction =>
    cases atoms with
    | nil => simp only [List.filterMap_nil, List.drop_nil]
    | cons atom rest =>
      have hoccupied' := hoccupied
      simp only [OccupiedAtomTrack, decide_eq_true_eq] at hoccupied'
      obtain ⟨value, equation⟩ := hoccupied' atom (by simp only [List.mem_cons, true_or])
      have restOccupied : OccupiedAtomTrack machine stack rest := by
        simp only [OccupiedAtomTrack, decide_eq_true_eq]
        intro candidate membership
        exact hoccupied' candidate (by simp only [List.mem_cons, membership, or_true])
      simpa only [equation, Option.some.injEq, List.filterMap_cons_some, List.drop_succ_cons] using
          induction rest restOccupied

private theorem decodedCommonSuffix_of_occupied_atom_suffix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (first next : List (CellAtom machine.tm))
    (hfirst : OccupiedAtomTrack machine stack first)
    (hnext : OccupiedAtomTrack machine stack next)
    (firstDrop nextDrop : ℕ)
    (hcommon : first.drop firstDrop = next.drop nextDrop) :
    (first.filterMap (cellAtomValue machine stack)).drop firstDrop =
      (next.filterMap (cellAtomValue machine stack)).drop nextDrop := by
  calc
    (first.filterMap (cellAtomValue machine stack)).drop firstDrop =
        (first.drop firstDrop).filterMap
          (cellAtomValue machine stack) :=
      occupiedAtomTrack_filterMap_drop
        machine stack first hfirst firstDrop
    _ = (next.drop nextDrop).filterMap
          (cellAtomValue machine stack) := by rw [hcommon]
    _ = (next.filterMap
          (cellAtomValue machine stack)).drop nextDrop :=
      (occupiedAtomTrack_filterMap_drop
        machine stack next hnext nextDrop).symm

private noncomputable def OccupiedStackShiftAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (hint : SingleStackHint machine.tm)
    (window : StackShiftWindow machine.tm) : Bool :=
  @decide (
  StackShiftAllowed machine.tm hint window ∧
    ∀ offset : Fin (blockSize machine.tm),
      offset.val < hint.2.1.val →
        (cellAtomValue machine stack (hint.2.2 offset)).isSome = true
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def OccupiedVerifierPrefix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (hint : FiniteVerifierHint machine.tm) : Bool :=
  @decide (
  ∀ (stack : machine.tm.K)
    (offset : Fin (blockSize machine.tm)),
    offset.val < (hint stack).2.1.val →
      (cellAtomValue machine stack
        ((hint stack).2.2 offset)).isSome = true
  ) (Classical.propDecidable _)

end CLStackShiftSoundness

namespace CLStackVerifierSimulation

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows
open GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLExactVerifierTransition GapCVP.CLLocalTableauCompiler
open GapCVP.CLVerifierTableauEmission GapCVP.CLUnconditionalTableau
open GapCVP.CLGlobalTableauSimulation GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseTableauSimulation GapCVP.CLStackShiftSoundness

private theorem canonicalVerifierScriptHints_occupied
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hint : FiniteVerifierHint machine.tm)
    (hscript : scriptVerifierAllowed machine
      (scriptVerifierQueryOf machine first next
        hfirst hnext hint) = true)
    (hwindows : AllVerifierStackWindows machine width
      first next hfirst hnext hint) :
    OccupiedVerifierPrefix machine hint := by
  simp only [GapCVP.CLStackShiftSoundness.OccupiedVerifierPrefix, decide_eq_true_eq]
  have windows := hwindows
  simp only [GapCVP.CLExactVerifierTransition.AllVerifierStackWindows, decide_eq_true_eq]
      at windows
  obtain ⟨label, hlabel, hcontrol, hstate, hchecks⟩ :=
    (scriptVerifierAllowed_iff machine
      (scriptVerifierQueryOf machine first next
        hfirst hnext hint)).mp hscript
  intro stack offset hoffset
  let run := finiteHeadScriptRun machine label first.var
    (fun target => atomBlockAt machine.tm
      (canonicalStackAtoms machine target
        (first.stk target) (stackAtomSupported_supportedValues machine first hfirst target)) 0)
  have hcheck := hchecks stack
  change
    (hint stack).1.val = run.2.2.dropped stack ∧
      (hint stack).2.1.val =
        (run.2.2.pushed stack).length ∧
      (decodedAtomBlock machine stack
        (atomBlockAt machine.tm
          (canonicalStackAtoms machine stack
            (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
                0)).take
          (run.2.2.pushed stack).length =
        run.2.2.pushed stack at hcheck
  have hdecodedPrefix := hcheck.2.2
  rw [decodedAtomBlock_canonical] at hdecodedPrefix
  have hlength := congrArg List.length hdecodedPrefix
  simp only [List.length_take] at hlength
  have hvalueBound : offset.val < (next.stk stack).length := by
    have hcount := hcheck.2.1
    omega
  have hatom :=
    prefixHintCorrect_of_allStackShiftWindows machine.tm width
      (canonicalStackAtoms machine stack
        (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack))
      (canonicalStackAtoms machine stack
        (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
      (hint stack) (windows stack)
  simp only [GapCVP.CLFiniteShiftWindows.PrefixHintCorrect,
    decide_eq_true_eq] at hatom
  have hatom := hatom offset hoffset
  rw [hatom,
    paddedAtom_decode machine stack
      (canonicalStackAtoms_forall₂ machine stack
        (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))]
  simp only [hvalueBound, getElem?_pos, Option.isSome_some]

/-- GapCVP reduction support. -/
noncomputable def StackSoundAnchoredVerificationAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  AnchoredVerificationAllowed machine window ∧
    OccupiedVerifierPrefix machine window.2.1.script.2.1
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def StackSoundAnchoredPhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  CompletePhaseCoherent machine.tm window ∧
    match window.2.1.mode with
    | .guessing =>
        AnchoredGuessingAllowed machine window ∨
          AnchoredInitializationAllowed machine window
    | .verifying =>
        StackSoundAnchoredVerificationAllowed machine window ∨
          AnchoredAcceptanceAllowed machine window
    | .accepting =>
        window.2.2.2 = acceptingPhaseCell machine.tm
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def stackSoundAnchoredPhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool := by
  classical
  exact decide (StackSoundAnchoredPhaseAllowed machine window)

theorem stackSoundAnchoredPhaseAllowed_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) :
    stackSoundAnchoredPhaseAllowed machine window = true ↔
      StackSoundAnchoredPhaseAllowed machine window := by
  classical
  simp only [stackSoundAnchoredPhaseAllowed, Bool.decide_eq_true]

private theorem stackSoundAnchoredPhaseAllowed_implies_anchored
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : StackSoundAnchoredPhaseAllowed machine window) :
    AnchoredPhaseAllowed machine window := by
  simp only [GapCVP.CLPhaseTableauSimulation.AnchoredPhaseAllowed, decide_eq_true_eq]
  have hallowed' := hallowed
  simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq] at hallowed'
  refine ⟨hallowed'.1, ?_⟩
  cases mode : window.2.1.mode with
  | guessing =>
    simpa only [mode] using hallowed'.2
  | verifying =>
    have cases :
        StackSoundAnchoredVerificationAllowed machine window ∨
          AnchoredAcceptanceAllowed machine window := by
      simpa only [mode] using hallowed'.2
    rcases cases with verification | acceptance
    · have verification' := verification
      simp only [StackSoundAnchoredVerificationAllowed, decide_eq_true_eq] at verification'
      simpa only using Or.inl verification'.1
    · simpa only using Or.inr acceptance
  | accepting =>
    simpa only [mode] using hallowed'.2

/-- GapCVP reduction support. -/
def stackSoundAnchoredPhaseSymbolAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : WindowSymbols (completePhaseSymbolCount machine.tm)) : Bool :=
  stackSoundAnchoredPhaseAllowed machine
    ((completePhaseSymbolEquiv machine.tm).symm window.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.2)

/-- GapCVP reduction support. -/
def stackSoundAnchoredPhaseSpecification
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    Specification
      ((nondeterministicTableauDimensionPolynomial bound machine).eval
        x.length)
      (completePhaseSymbolCount machine.tm) where
  input position :=
    completePhaseSymbolEquiv machine.tm
      (initialPhaseCell bound machine x position)
  accept :=
    completePhaseSymbolEquiv machine.tm
      (acceptingPhaseCell machine.tm)
  allowed := stackSoundAnchoredPhaseSymbolAllowed machine

end CLStackVerifierSimulation

namespace CLAnchoredTraceSimulation

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRowBounds GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLFirstAcceptance GapCVP.CLArbitraryVerifierSoundness
open GapCVP.CLStackVerifierSimulation

private theorem stackSoundSymbolAllowed_implies_anchored
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : WindowSymbols (completePhaseSymbolCount machine.tm))
    (hallowed :
      stackSoundAnchoredPhaseSymbolAllowed machine window = true) :
    anchoredPhaseSymbolAllowed machine window = true := by
  let decoded : CompletePhaseWindow machine.tm :=
    ((completePhaseSymbolEquiv machine.tm).symm window.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.2)
  have hcorrected : StackSoundAnchoredPhaseAllowed machine decoded := by
    apply (stackSoundAnchoredPhaseAllowed_iff machine decoded).mp
    exact hallowed
  apply (anchoredPhaseAllowed_iff machine decoded).mpr
  exact stackSoundAnchoredPhaseAllowed_implies_anchored
    machine decoded hcorrected

private theorem stackSoundValidTrace_to_anchored
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace) :
    ValidTrace (anchoredPhaseSpecification bound machine x) trace := by
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq]
  have trace := htrace
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq] at trace
  refine ⟨trace.1, trace.2.1, ?_⟩
  intro window
  exact stackSoundSymbolAllowed_implies_anchored machine _
    (trace.2.2 window)

theorem stackSoundValidTrace_window
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (window : Window (rowWidth bound machine x)) :
    StackSoundAnchoredPhaseAllowed machine
      (decodeCorrectedPhaseRow machine (trace window.1.1)
          (leftPosition window),
        decodeCorrectedPhaseRow machine (trace window.1.1)
          window.1.2,
        decodeCorrectedPhaseRow machine (trace window.1.1)
          (rightPosition window),
        decodeCorrectedPhaseRow machine
          (trace (nextTime window)) window.1.2) := by
  have trace := htrace
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq] at trace
  apply (stackSoundAnchoredPhaseAllowed_iff machine _).mp
  exact trace.2.2 window

private theorem stackSoundValidTrace_masks_of_not_accepting
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x))
    (position : Position (rowWidth bound machine x))
    (hmode : (decodeCorrectedPhaseRow machine
      (trace time) position).mode ≠ .accepting) :
    AnchoredPhaseMasks bound machine x position
      (decodeCorrectedPhaseRow machine (trace time) position) :=
  anchoredValidTrace_masks_of_not_accepting
    bound machine x trace
    (stackSoundValidTrace_to_anchored
      bound machine x trace htrace)
    time position hmode

private theorem stackSoundValidTrace_has_first_checked_acceptance
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace) :
    ∃ (time : Fin (rowWidth bound machine x))
      (position : Position (rowWidth bound machine x)),
      AnchoredAcceptanceAllowed machine
          (anchoredVerifierWindowAt machine.tm
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)))
            (decodeCorrectedPhaseRow machine (trace time.succ))
            position) ∧
        (∀ other : Position (rowWidth bound machine x),
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)) other).mode = .verifying) ∧
        (∀ other : Position (rowWidth bound machine x),
          AnchoredPhaseMasks bound machine x other
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)) other)) ∧
        (∀ (earlier : Time (rowWidth bound machine x)),
          earlier.val ≤ time.val →
          ∀ other : Position (rowWidth bound machine x),
            (decodeCorrectedPhaseRow machine
              (trace earlier) other).mode ≠ .accepting) :=
  anchoredValidTrace_has_first_checked_acceptance
    bound machine x trace
    (stackSoundValidTrace_to_anchored
      bound machine x trace htrace)

private theorem stackSoundPhase_verification_of_verifying_modes
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : StackSoundAnchoredPhaseAllowed machine window)
    (hfirst : window.2.1.mode = .verifying)
    (hnext : window.2.2.2.mode = .verifying) :
    StackSoundAnchoredVerificationAllowed machine window := by
  have allowed := hallowed
  simp only [GapCVP.CLStackVerifierSimulation.StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
      at allowed
  have hcases :
      StackSoundAnchoredVerificationAllowed machine window ∨
        AnchoredAcceptanceAllowed machine window := by
    simpa only [hfirst] using allowed.2
  rcases hcases with hverify | haccept
  · exact hverify
  · have acceptance := haccept
    simp only [GapCVP.CLPhaseTableauSimulation.AnchoredAcceptanceAllowed,
        GapCVP.CLCompleteVerifierSimulation.CompleteAcceptanceAllowed,
      decide_eq_true_eq] at acceptance
    have acceptanceOuter := ofClassicalDecide acceptance
    have acceptanceCore := ofClassicalDecide acceptanceOuter.1
    rw [acceptanceCore.1] at hnext
    cases hnext

private theorem stackSoundValidTrace_occupied_verification_windows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    ∀ position : Position (rowWidth bound machine x),
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)))
          (decodeCorrectedPhaseRow machine (trace time.succ))
          position) := by
  intro position
  apply stackSoundPhase_verification_of_verifying_modes machine _
  · exact stackSoundValidTrace_window
      bound machine x trace htrace (windowAt time position)
  · exact hfirst position
  · exact hnext position

private theorem actualStep_iff_stackSoundCanonicalVerifierWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstSpace : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ rowWidth bound machine x)
    (hnextSpace : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ rowWidth bound machine x) :
    machine.tm.step first = some next ↔
      ∃ (firstHint nextHint : FiniteVerifierHint machine.tm),
        ∀ position : Position (rowWidth bound machine x),
          StackSoundAnchoredPhaseAllowed machine
            (anchoredVerifierWindowAt machine.tm
              (rowWidth bound machine x)
              (canonicalAnchoredVerifyingRow
                bound machine x certificate
                first hfirst firstHint false)
              (canonicalAnchoredVerifyingRow
                bound machine x certificate
                next hnext nextHint false) position) := by
  constructor
  · intro hstep
    obtain ⟨firstHint, nextHint, hanchored⟩ :=
      (actualStep_iff_anchoredCanonicalVerifierWindows
        bound machine x certificate first next
        hfirst hnext hfirstSpace hnextSpace).mp hstep
    have hscriptWindows :
        ∀ position : Position (rowWidth bound machine x),
          scriptBlockAllowed machine
            (scriptBlockWindowAt machine.tm
              (rowWidth bound machine x)
              (canonicalScriptBlockRow machine
                (rowWidth bound machine x)
                certificate first hfirst firstHint)
              (canonicalScriptBlockRow machine
                (rowWidth bound machine x)
                certificate next hnext nextHint)
              position) = true := by
      intro position
      exact (canonicalAnchoredVerifierWindow_allowed_iff
        bound machine x certificate first next hfirst hnext
        firstHint nextHint false position).mp
        (hanchored position)
    obtain ⟨hscript, hstackWindows⟩ :=
      (canonicalScriptBlockWindows_iff
        machine (rowWidth bound machine x)
        certificate first next hfirst hnext
        hfirstSpace hnextSpace firstHint nextHint).mp
        hscriptWindows
    have hoccupied := canonicalVerifierScriptHints_occupied
      machine (rowWidth bound machine x)
      first next hfirst hnext firstHint hscript hstackWindows
    refine ⟨firstHint, nextHint, ?_⟩
    intro position
    let window := anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x)
      (canonicalAnchoredVerifyingRow bound machine x certificate
        first hfirst firstHint false)
      (canonicalAnchoredVerifyingRow bound machine x certificate
        next hnext nextHint false) position
    have hold : AnchoredPhaseAllowed machine window :=
      hanchored position
    have hfirstMode : window.2.1.mode = .verifying := rfl
    have hnextMode : window.2.2.2.mode = .verifying := rfl
    have hverify := anchoredPhase_verification_of_verifying_modes
      machine window hold hfirstMode hnextMode
    change StackSoundAnchoredPhaseAllowed machine window
    simp only [GapCVP.CLStackVerifierSimulation.StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
    have hold' := hold
    simp only [GapCVP.CLPhaseTableauSimulation.AnchoredPhaseAllowed, decide_eq_true_eq] at hold'
    refine ⟨hold'.1, ?_⟩
    change StackSoundAnchoredVerificationAllowed machine window ∨
      AnchoredAcceptanceAllowed machine window
    left
    simp only [GapCVP.CLStackVerifierSimulation.StackSoundAnchoredVerificationAllowed,
        decide_eq_true_eq]
    exact ⟨hverify, hoccupied⟩
  · rintro ⟨firstHint, nextHint, hwindows⟩
    apply (actualStep_iff_anchoredCanonicalVerifierWindows
      bound machine x certificate first next
      hfirst hnext hfirstSpace hnextSpace).mpr
    refine ⟨firstHint, nextHint, ?_⟩
    intro position
    exact stackSoundAnchoredPhaseAllowed_implies_anchored machine _
      (hwindows position)

end CLAnchoredTraceSimulation

namespace CLArbitraryRowOccupancy

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLLocalWindows GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLStackVerifierSimulation

private noncomputable def DecodableOrBlank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atom : CellAtom machine.tm) : Bool :=
  @decide (
  atom = none ∨
    ∃ value : machine.tm.Γ stack,
      cellAtomValue machine stack atom = some value
  ) (Classical.propDecidable _)
private theorem decodableOrBlank_of_isSome
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atom : CellAtom machine.tm)
    (hoccupied : (cellAtomValue machine stack atom).isSome = true) :
    DecodableOrBlank machine stack atom := by
  simp only [DecodableOrBlank, decide_eq_true_eq]
  cases decoded : cellAtomValue machine stack atom with
  | none => simp only [decoded, Option.isSome_none, Bool.false_eq_true] at hoccupied
  | some value => exact Or.inr ⟨value, rfl⟩

private theorem initialPairedAtom_decodableOrBlank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (tag : PairedInputTag) :
    DecodableOrBlank machine stack
      (initialPairedAtom machine stack tag) := by
  simp only [DecodableOrBlank, decide_eq_true_eq]
  cases tag with
  | marker => exact Or.inl rfl
  | blank => exact Or.inl rfl
  | bit bit =>
    by_cases hstack : stack = machine.tm.k₀
    · subst stack
      right
      refine ⟨machine.inputAlphabet.invFun bit, ?_⟩
      simp only [initialPairedAtom, ↓reduceIte, Equiv.invFun_as_coe, canonicalCellAtom_decode]
    · left
      simp only [initialPairedAtom, hstack, ↓reduceIte]

private theorem initializedPhaseBlock_decodableOrBlank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (old : BlockCell machine.tm)
    (payload : PairedInputBlock machine.tm)
    (range : PhaseMaskBlock machine.tm)
    (stack : machine.tm.K)
    (offset : Fin (blockSize machine.tm)) :
    DecodableOrBlank machine stack
      ((initializedPhaseBlock machine old payload range
        offset).2.2.1 stack) := by
  by_cases hrange : range offset = true
  · have hrangeBool : range offset := by simpa only using hrange
    simp only [initializedPhaseBlock, hrangeBool, ↓reduceIte]
    exact initialPairedAtom_decodableOrBlank machine stack (payload offset)
  · have hfalse := Bool.eq_false_of_not_eq_true hrange
    simp only [DecodableOrBlank, initializedPhaseBlock, hfalse, Bool.false_eq_true, ↓reduceIte,
        blankCell,
        cellAtomValue_blank, reduceCtorEq, exists_false, or_false, decide_true]

/-- GapCVP reduction support. -/
noncomputable def PhaseRowAtomsWellTyped
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm) : Bool :=
  @decide (
  ∀ (position : Position width)
    (stack : machine.tm.K)
    (offset : Fin (blockSize machine.tm)),
    DecodableOrBlank machine stack
      ((completeMachineBlock machine.tm (row position)
        offset).2.2.1 stack)
  ) (Classical.propDecidable _)
private theorem occupiedShift_preserves_decodableOrBlank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (hint : SingleStackHint machine.tm)
    (window : StackShiftWindow machine.tm)
    (hshift : StackShiftAllowed machine.tm hint window)
    (hprefix : ∀ offset : Fin (blockSize machine.tm),
      offset.val < hint.2.1.val →
        (cellAtomValue machine stack
          (hint.2.2 offset)).isSome = true)
    (hleft : ∀ offset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack (window.1 offset))
    (hcenter : ∀ offset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack (window.2.1 offset))
    (hright : ∀ offset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack (window.2.2.1 offset)) :
    ∀ offset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack
        (window.2.2.2.1 offset) := by
  have hshift' := hshift
  simp only [StackShiftAllowed, decide_eq_true_eq] at hshift'
  intro offset
  rw [hshift' offset]
  unfold shiftedWindowAtom
  split
  next guard =>
    exact decodableOrBlank_of_isSome machine stack (hint.2.2 offset)
      (hprefix offset guard.2)
  next _ =>
    split
    next _ => exact hleft _
    next _ =>
      dsimp only
      split
      next _ => exact hcenter _
      next _ => exact hright _

private theorem allCorrectedVerifierWindows_preserve_wellTyped_rows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hfirst : PhaseRowAtomsWellTyped machine width first)
    (hwindows : ∀ position : Position width,
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    PhaseRowAtomsWellTyped machine width next := by
  simp only [GapCVP.CLArbitraryRowOccupancy.PhaseRowAtomsWellTyped, decide_eq_true_eq]
  have firstTyped := hfirst
  simp only [GapCVP.CLArbitraryRowOccupancy.PhaseRowAtomsWellTyped, decide_eq_true_eq]
      at firstTyped
  intro position stack offset
  let window := anchoredVerifierWindowAt machine.tm
    width first next position
  have hverification := hwindows position
  simp only [GapCVP.CLStackVerifierSimulation.StackSoundAnchoredVerificationAllowed,
      decide_eq_true_eq] at hverification
  have anchored := hverification.1
  simp only [GapCVP.CLPhaseTableauSimulation.AnchoredVerificationAllowed, decide_eq_true_eq]
      at anchored
  have complete := anchored.1
  simp only [GapCVP.CLCompleteVerifierSimulation.CompleteVerificationAllowed, decide_eq_true_eq]
      at complete
  have occupied := hverification.2
  simp only [GapCVP.CLStackShiftSoundness.OccupiedVerifierPrefix, decide_eq_true_eq] at occupied
  have hscript : scriptBlockAllowed machine
      (completeScriptWindow machine.tm window) = true :=
    complete.2.2
  obtain ⟨_, _, _, _, hstacks⟩ :=
    (scriptBlockAllowed_iff machine
      (completeScriptWindow machine.tm window)).mp hscript
  let stackWindow := stackWindowOfScriptBlock machine.tm
    (completeScriptWindow machine.tm window) stack
  have hshift : StackShiftAllowed machine.tm
      ((first position).script.2.1 stack) stackWindow :=
    (stackShiftAllowed_iff machine.tm
      ((first position).script.2.1 stack) stackWindow).mp
      (hstacks stack)
  have hprefix : ∀ innerOffset : Fin (blockSize machine.tm),
      innerOffset.val < ((first position).script.2.1 stack).2.1.val →
        (cellAtomValue machine stack
          (((first position).script.2.1 stack).2.2 innerOffset)).isSome =
            true :=
    occupied stack
  have hleft : ∀ innerOffset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack (stackWindow.1 innerOffset) := by
    intro innerOffset
    change DecodableOrBlank machine stack
      ((completeMachineBlock machine.tm
        (first (leftBlock width position)) innerOffset).2.2.1 stack)
    exact firstTyped (leftBlock width position) stack innerOffset
  have hcenter : ∀ innerOffset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack
        (stackWindow.2.1 innerOffset) := by
    intro innerOffset
    change DecodableOrBlank machine stack
      ((completeMachineBlock machine.tm
        (first position) innerOffset).2.2.1 stack)
    exact firstTyped position stack innerOffset
  have hright : ∀ innerOffset : Fin (blockSize machine.tm),
      DecodableOrBlank machine stack
        (stackWindow.2.2.1 innerOffset) := by
    intro innerOffset
    change DecodableOrBlank machine stack
      ((completeMachineBlock machine.tm
        (first (rightBlock width position)) innerOffset).2.2.1 stack)
    exact firstTyped (rightBlock width position) stack innerOffset
  exact occupiedShift_preserves_decodableOrBlank
    machine stack ((first position).script.2.1 stack)
    stackWindow hshift hprefix hleft hcenter hright offset

end CLArbitraryRowOccupancy

namespace CLWholeTimeOccupancy

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLArbitraryRowOccupancy

private theorem stackSoundPhase_initialization_of_modes
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : StackSoundAnchoredPhaseAllowed machine window)
    (hfirst : window.2.1.mode = .guessing)
    (hnext : window.2.2.2.mode = .verifying) :
    AnchoredInitializationAllowed machine window := by
  have allowed := hallowed
  simp only [GapCVP.CLStackVerifierSimulation.StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
      at allowed
  have hcases :
      AnchoredGuessingAllowed machine window ∨
        AnchoredInitializationAllowed machine window := by
    simpa only [hfirst] using allowed.2
  rcases hcases with hguess | hinit
  · have guess := hguess
    simp only [GapCVP.CLPhaseTableauSimulation.AnchoredGuessingAllowed,
        GapCVP.CLPhaseSpecification.CorrectedGuessingAllowed,
      decide_eq_true_eq] at guess
    have hguessMode := guess.1.1
    rw [hnext] at hguessMode
    cases hguessMode
  · exact hinit

private theorem initializationWindow_next_wellTyped
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hinit : AnchoredInitializationAllowed machine window)
    (stack : machine.tm.K)
    (offset : Fin (blockSize machine.tm)) :
    DecodableOrBlank machine stack
      ((completeMachineBlock machine.tm
        window.2.2.2 offset).2.2.1 stack) := by
  have initial := hinit
  simp only [GapCVP.CLPhaseTableauSimulation.AnchoredInitializationAllowed,
      GapCVP.CLCompleteVerifierSimulation.CompleteInitializationAllowed,
    decide_eq_true_eq] at initial
  have initialOuter := ofClassicalDecide initial
  have initialCore := ofClassicalDecide initialOuter.1
  have hblock := initialCore.2.2.1
  rw [hblock]
  exact initializedPhaseBlock_decodableOrBlank machine
    (completeMachineBlock machine.tm window.2.1)
    window.2.1.payload window.2.1.range stack offset

theorem stackSoundValidTrace_all_verifier_rows_wellTyped
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x)) :
    (∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time) position).mode = .verifying) →
    PhaseRowAtomsWellTyped machine (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine (trace time)) := by
  have hanchored := stackSoundValidTrace_to_anchored
    bound machine x trace htrace
  induction time using Fin.induction with
  | zero =>
      intro hmode
      have hzero := hmode 0
      have hinitial :
          decodeCorrectedPhaseRow machine (trace 0) 0 =
            initialPhaseCell bound machine x 0 := by
        exact anchoredTrace_initial
          bound machine x trace hanchored 0
      rw [hinitial] at hzero
      cases hzero
  | succ time ih =>
      intro hnextModes
      cases hsource :
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)) 0).mode with
      | guessing =>
          simp only [GapCVP.CLArbitraryRowOccupancy.PhaseRowAtomsWellTyped, decide_eq_true_eq]
          intro position stack offset
          let window := anchoredVerifierWindowAt machine.tm
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)))
            (decodeCorrectedPhaseRow machine (trace time.succ))
            position
          have hallowed :
              StackSoundAnchoredPhaseAllowed machine window :=
            stackSoundValidTrace_window
              bound machine x trace htrace (windowAt time position)
          have hfirstMode : window.2.1.mode = .guessing := by
            have hcoherent := anchoredValidTrace_mode_constant
              bound machine x trace hanchored time position
            exact hcoherent.trans hsource
          have hnextMode : window.2.2.2.mode = .verifying :=
            hnextModes position
          have hinit := stackSoundPhase_initialization_of_modes
            machine window hallowed hfirstMode hnextMode
          exact initializationWindow_next_wellTyped
            machine window hinit stack offset
      | verifying =>
          have hsourceModes :
              ∀ position : Position (rowWidth bound machine x),
                (decodeCorrectedPhaseRow machine
                  (trace (Fin.castSucc time)) position).mode =
                  .verifying := by
            intro position
            exact (anchoredValidTrace_mode_constant
              bound machine x trace hanchored time position).trans
              hsource
          have hsourceWellTyped := ih hsourceModes
          exact allCorrectedVerifierWindows_preserve_wellTyped_rows
            machine (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)))
            (decodeCorrectedPhaseRow machine (trace time.succ))
            hsourceWellTyped
            (stackSoundValidTrace_occupied_verification_windows
              bound machine x trace htrace time
              hsourceModes hnextModes)
      | accepting =>
          let window := anchoredVerifierWindowAt machine.tm
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)))
            (decodeCorrectedPhaseRow machine (trace time.succ)) 0
          have hallowed :
              StackSoundAnchoredPhaseAllowed machine window :=
            stackSoundValidTrace_window
              bound machine x trace htrace (windowAt time 0)
          have hsourceMode : window.2.1.mode = .accepting := by
            change
              (decodeCorrectedPhaseRow machine
                (trace (Fin.castSucc time)) 0).mode = .accepting
            exact hsource
          have allowed := hallowed
          simp only [GapCVP.CLStackVerifierSimulation.StackSoundAnchoredPhaseAllowed,
              decide_eq_true_eq] at allowed
          have hclear :
              window.2.2.2 = acceptingPhaseCell machine.tm := by
            simpa only [hsourceMode] using allowed.2
          have hnext := hnextModes 0
          change window.2.2.2.mode = .verifying at hnext
          rw [hclear] at hnext
          cases hnext

end CLWholeTimeOccupancy

namespace CLRawTrackSimulation

open Computability Turing GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLStackShiftSoundness

private theorem filterMap_ofFn_comp
    {α β : Type}
    (size : ℕ)
    (atoms : Fin size → α)
    (decode : α → Option β) :
    (List.ofFn (fun index : Fin size =>
      decode (atoms index))).filterMap id =
      (List.ofFn atoms).filterMap decode := by
  induction size with
  | zero => simp only [id_eq, List.ofFn_zero, List.filterMap_nil]
  | succ size ih =>
      cases hhead : decode (atoms 0) with
      | none =>
          simpa only [id_eq, List.ofFn_succ, hhead, List.filterMap_cons_none] using
              ih (fun index : Fin size => atoms index.succ)
      | some value =>
          simpa only [id_eq, List.ofFn_succ, hhead, Option.some.injEq, List.filterMap_cons_some,
              List.cons.injEq,
              true_and] using ih (fun index : Fin size => atoms index.succ)

private theorem filterMap_filter_isSome
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atoms : List (CellAtom machine.tm)) :
    (atoms.filter Option.isSome).filterMap
        (cellAtomValue machine stack) =
      atoms.filterMap (cellAtomValue machine stack) := by
  induction atoms with
  | nil => simp only [List.filter_nil, List.filterMap_nil]
  | cons atom rest ih =>
      cases atom with
      | none =>
          rw [List.filter_cons_of_neg (by simp only [Option.isSome_none,
            Bool.false_eq_true, not_false_eq_true]), ih]
          exact (List.filterMap_cons_none
            (cellAtomValue_blank machine stack)).symm
      | some value =>
          cases hdecode : cellAtomValue machine stack (some value) with
          | none => simp only [Option.isSome_some, List.filter_cons_of_pos, hdecode,
              List.filterMap_cons_none, ih]
          | some decoded => simp only [Option.isSome_some, List.filter_cons_of_pos, hdecode,
              Option.some.injEq, List.filterMap_cons_some,
                                ih]

private theorem occupiedAtomTrack_filterMap_length
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atoms : List (CellAtom machine.tm))
    (hoccupied : OccupiedAtomTrack machine stack atoms) :
    (atoms.filterMap (cellAtomValue machine stack)).length =
      atoms.length := by
  induction atoms with
  | nil => simp only [List.filterMap_nil, List.length_nil]
  | cons atom rest ih =>
      have occupied := hoccupied
      simp only [GapCVP.CLStackShiftSoundness.OccupiedAtomTrack, decide_eq_true_eq] at occupied
      obtain ⟨value, hvalue⟩ := occupied atom (by simp only [List.mem_cons, true_or])
      have hrest : OccupiedAtomTrack machine stack rest := by
        simp only [GapCVP.CLStackShiftSoundness.OccupiedAtomTrack, decide_eq_true_eq]
        intro candidate hcandidate
        exact occupied candidate (by simp only [List.mem_cons, hcandidate, or_true])
      simp only [hvalue, Option.some.injEq, List.filterMap_cons_some, List.length_cons, ih hrest]

end CLRawTrackSimulation

namespace CLCompactWindowSoundness

open Computability Turing GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLStackShiftSoundness2

/-- GapCVP reduction support. -/
noncomputable def NoInteriorPaddingHoles
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm)) : Bool :=
  @decide (
  ∃ (occupied : List (CellAtom tm)) (padding : ℕ),
    NoBlankAtoms tm occupied ∧
      atoms = occupied ++ List.replicate padding none
  ) (Classical.propDecidable _)
private theorem filter_isSome_eq_self_of_noBlank
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (hnoblank : NoBlankAtoms tm atoms) :
    atoms.filter Option.isSome = atoms := by
  induction atoms with
  | nil => simp only [List.filter_nil]
  | cons atom rest induction =>
    have hnoblank' := hnoblank
    simp only [NoBlankAtoms, decide_eq_true_eq] at hnoblank'
    have restNoBlank : NoBlankAtoms tm rest := by
      simp only [NoBlankAtoms, decide_eq_true_eq]
      intro candidate membership
      exact hnoblank' candidate (by simp only [List.mem_cons, membership, or_true])
    cases atom with
    | none => exact (hnoblank' none (by simp only [List.mem_cons, true_or]) rfl).elim
    | some value => simp only [Option.isSome_some, List.filter_cons_of_pos, induction restNoBlank]

private theorem paddedAtom_append_blank_padding
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (padding index : ℕ) :
    paddedAtom (atoms ++ List.replicate padding none) index =
      paddedAtom atoms index := by
  by_cases hindex : index < atoms.length
  · simp only [paddedAtom, List.getElem?_append, hindex, ↓reduceIte, getElem?_pos,
      Option.getD_some]
  · simp only [paddedAtom, List.getElem?_append, hindex, ↓reduceIte,
      List.getElem?_getD_replicate_default_eq,
        not_false_eq_true, getElem?_neg, Option.getD_none]

private theorem noHoles_padded_compact
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (hholes : NoInteriorPaddingHoles tm atoms)
    (index : ℕ) :
    paddedAtom atoms index =
      paddedAtom (atoms.filter Option.isSome) index := by
  have hholes' := hholes
  simp only [NoInteriorPaddingHoles, decide_eq_true_eq] at hholes'
  obtain ⟨occupied, padding, noBlank, equality⟩ := hholes'
  subst atoms
  have filtered :
      (occupied ++ List.replicate padding none).filter Option.isSome = occupied := by
    simp only [List.filter_append, filter_isSome_eq_self_of_noBlank tm occupied noBlank,
        Option.isSome_none,
        Bool.false_eq_true, not_false_eq_true, List.filter_replicate_of_neg, List.append_nil]
  rw [filtered]
  exact paddedAtom_append_blank_padding tm occupied padding index

private theorem noHoles_atomBlockAt_compact
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (hholes : NoInteriorPaddingHoles tm atoms)
    (position : ℕ) :
    atomBlockAt tm atoms position =
      atomBlockAt tm (atoms.filter Option.isSome) position := by
  funext offset
  exact noHoles_padded_compact tm atoms hholes
    (position * blockSize tm + offset.val)

end CLCompactWindowSoundness

namespace CLNoHoleTimeInduction

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRows GapCVP.CLLocalWindows GapCVP.CLCompleteLocalCompiler
open GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLStackShiftSoundness GapCVP.CLCompactWindowSoundness

private noncomputable def BlankPaddingMonotone
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm)) : Bool :=
  @decide (
  ∀ first next : ℕ,
    first ≤ next →
      paddedAtom atoms first = none →
        paddedAtom atoms next = none
  ) (Classical.propDecidable _)
private theorem paddedAtom_none_iff_length_le_of_noBlank
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (hoccupied : NoBlankAtoms tm atoms)
    (index : ℕ) :
    paddedAtom atoms index = none ↔ atoms.length ≤ index := by
  have hoccupied' := hoccupied
  simp only [NoBlankAtoms, decide_eq_true_eq] at hoccupied'
  constructor
  · intro blank
    by_contra bound
    have indexBound : index < atoms.length := by omega
    have equation : atoms[index] = none := by
      simpa only [paddedAtom, indexBound, getElem?_pos, Option.getD_some] using blank
    exact hoccupied' atoms[index] (List.getElem_mem indexBound) equation
  · exact paddedAtom_none_of_length_le tm atoms index

private theorem blankPaddingMonotone_of_noInteriorPaddingHoles
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (hholes : NoInteriorPaddingHoles tm atoms) :
    BlankPaddingMonotone tm atoms := by
  simp only [BlankPaddingMonotone, decide_eq_true_eq]
  have hholes' := hholes
  simp only [NoInteriorPaddingHoles, decide_eq_true_eq] at hholes'
  obtain ⟨occupied, padding, occupiedNoBlank, equality⟩ := hholes'
  subst atoms
  intro first next order firstBlank
  rw [paddedAtom_append_blank_padding tm occupied padding first] at firstBlank
  rw [paddedAtom_append_blank_padding tm occupied padding next]
  exact (paddedAtom_none_iff_length_le_of_noBlank tm occupied occupiedNoBlank next).mpr
    (le_trans
      ((paddedAtom_none_iff_length_le_of_noBlank tm occupied occupiedNoBlank first).mp
        firstBlank) order)

private theorem noInteriorPaddingHoles_of_blankPaddingMonotone
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (hmonotone : BlankPaddingMonotone tm atoms) :
    NoInteriorPaddingHoles tm atoms := by
  simp only [NoInteriorPaddingHoles, decide_eq_true_eq]
  have hmonotone' := hmonotone
  simp only [BlankPaddingMonotone, decide_eq_true_eq] at hmonotone'
  induction atoms with
  | nil =>
    refine ⟨[], 0, ?_, ?_⟩
    · simp only [NoBlankAtoms, List.not_mem_nil, ne_eq, IsEmpty.forall_iff, implies_true,
        decide_true]
    · simp only [List.replicate_zero, List.append_nil]
  | cons atom rest induction =>
    cases atom with
    | none =>
      have restBlank : ∀ candidate ∈ rest, candidate = none := by
        intro candidate membership
        obtain ⟨index, bound, value⟩ := List.getElem_of_mem membership
        have blank := hmonotone' 0 (index + 1) (Nat.zero_le _)
          (by simp only [paddedAtom, List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff,
              zero_le, getElem?_pos,
                  List.getElem_cons_zero, Option.getD_some])
        have entry : rest[index] = none := by
          simpa only [paddedAtom, List.length_cons, Order.lt_add_one_iff, Order.add_one_le_iff,
              bound, getElem?_pos,
              List.getElem_cons_succ, Option.getD_some] using blank
        exact value.symm.trans entry
      have replicated : rest = List.replicate rest.length none :=
        List.eq_replicate_of_mem restBlank
      refine ⟨[], rest.length + 1, ?_, ?_⟩
      · simp only [NoBlankAtoms, List.not_mem_nil, ne_eq, IsEmpty.forall_iff, implies_true,
          decide_true]
      · simpa only [List.nil_append, List.replicate_succ] using
          congrArg (List.cons none) replicated
    | some value =>
      have restMonotone : BlankPaddingMonotone tm rest := by
        simp only [BlankPaddingMonotone, decide_eq_true_eq]
        intro first next order blank
        have shifted := hmonotone' (first + 1) (next + 1) (by omega)
        apply shifted
        simpa only [paddedAtom, List.getElem?_cons_succ] using blank
      have restMonotone' := restMonotone
      simp only [BlankPaddingMonotone, decide_eq_true_eq] at restMonotone'
      obtain ⟨occupied, padding, noBlank, decomposition⟩ :=
        induction restMonotone restMonotone'
      refine ⟨some value :: occupied, padding, ?_, ?_⟩
      · simp only [NoBlankAtoms, decide_eq_true_eq] at noBlank ⊢
        intro candidate membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
        · exact noBlank candidate membership
      · simp only [decomposition, List.cons_append]

private theorem noHoles_stackShiftWindow_source_compact
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : List (CellAtom tm))
    (hfirst : NoInteriorPaddingHoles tm first)
    (position : Fin (width + 1)) :
    stackShiftWindowAt tm width first next position =
      stackShiftWindowAt tm width
        (first.filter Option.isSome) next position := by
  simp only [stackShiftWindowAt]
  rw [noHoles_atomBlockAt_compact tm first hfirst
    (leftBlock width position).val]
  rw [noHoles_atomBlockAt_compact tm first hfirst position.val]
  rw [noHoles_atomBlockAt_compact tm first hfirst
    (rightBlock width position).val]

private theorem occupiedRawWindows_prefix_nonblank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (stack : machine.tm.K)
    (first next : List (CellAtom machine.tm))
    (hint : SingleStackHint machine.tm)
    (hwindows : ∀ position : Fin (width + 1),
      OccupiedStackShiftAllowed machine stack hint
        (stackShiftWindowAt machine.tm width
          first next position))
    (index : ℕ)
    (hindex : index < hint.2.1.val) :
    paddedAtom next index ≠ none := by
  let position : Fin (width + 1) := 0
  let offset : Fin (blockSize machine.tm) :=
    ⟨index, Nat.lt_trans hindex hint.2.1.isLt⟩
  have allowed := hwindows position
  simp only [OccupiedStackShiftAllowed, decide_eq_true_eq] at allowed
  have shifted := allowed.1
  simp only [StackShiftAllowed, decide_eq_true_eq] at shifted
  have cell := shifted offset
  change paddedAtom next (position.val * blockSize machine.tm + offset.val) =
    shiftedWindowAtom machine.tm hint
      (stackShiftWindowAt machine.tm width first next position) offset at cell
  have guard :
      (stackShiftWindowAt machine.tm width first next position).2.2.2.2 = true ∧
        offset.val < hint.2.1.val := by
    simp [stackShiftWindowAt, position, offset, hindex]
  rw [shiftedWindowAtom, ite_eq_left guard] at cell
  have equation : paddedAtom next index = hint.2.2 offset := by
    simpa [position, offset] using cell
  intro blank
  have occupied := allowed.2 offset (by simpa [offset] using hindex)
  rw [← equation, blank] at occupied
  simp [cellAtomValue_blank] at occupied

private theorem occupiedRawWindows_suffix_paddedAtom
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (stack : machine.tm.K)
    (first next : List (CellAtom machine.tm))
    (hfirst : NoInteriorPaddingHoles machine.tm first)
    (hfirstLength : (first.filter Option.isSome).length ≤ width)
    (hint : SingleStackHint machine.tm)
    (hwindows : ∀ position : Fin (width + 1),
      OccupiedStackShiftAllowed machine stack hint
        (stackShiftWindowAt machine.tm width
          first next position))
    (index : ℕ)
    (hprefix : hint.2.1.val ≤ index)
    (hcovered : index < (width + 1) * blockSize machine.tm) :
    paddedAtom next index =
      paddedAtom (first.filter Option.isSome)
        (index - hint.2.1.val + hint.1.val) := by
  let position : Fin (width + 1) :=
    ⟨index / blockSize machine.tm,
      (Nat.div_lt_iff_lt_mul (blockSize_pos machine.tm)).mpr hcovered⟩
  let offset : Fin (blockSize machine.tm) :=
    ⟨index % blockSize machine.tm,
      Nat.mod_lt index (blockSize_pos machine.tm)⟩
  have coordinate : position.val * blockSize machine.tm + offset.val = index := by
    dsimp [position, offset]
    exact Nat.div_add_mod' index (blockSize machine.tm)
  have notPrefix : ¬ (position.val = 0 ∧ offset.val < hint.2.1.val) := by
    rintro ⟨zero, small⟩
    have coordinate' := coordinate
    rw [zero, Nat.zero_mul, Nat.zero_add] at coordinate'
    omega
  have shift : StackShiftAllowed machine.tm hint
      (stackShiftWindowAt machine.tm width
        (first.filter Option.isSome) next position) := by
    have allowed := hwindows position
    simp only [OccupiedStackShiftAllowed, decide_eq_true_eq] at allowed
    have raw := allowed.1
    rw [noHoles_stackShiftWindow_source_compact
      machine.tm width first next hfirst position] at raw
    exact raw
  have shift' := shift
  simp only [StackShiftAllowed, decide_eq_true_eq] at shift'
  have cell := shift' offset
  change paddedAtom next (position.val * blockSize machine.tm + offset.val) =
    shiftedWindowAtom machine.tm hint
      (stackShiftWindowAt machine.tm width
        (first.filter Option.isSome) next position) offset at cell
  rw [shiftedWindowAtom_eq_old machine.tm width
    (first.filter Option.isSome) next hfirstLength
    hint position offset notPrefix] at cell
  simpa only [coordinate] using cell

private theorem filter_isSome_noBlank
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm)) :
    NoBlankAtoms tm (atoms.filter Option.isSome) := by
  simp only [NoBlankAtoms, decide_eq_true_eq]
  intro atom membership blank
  have some := (List.mem_filter.mp membership).2
  simp only [blank, Option.isSome_none, Bool.false_eq_true] at some

private theorem occupiedRawWindows_preserve_noInteriorPaddingHoles
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (stack : machine.tm.K)
    (first next : List (CellAtom machine.tm))
    (hfirst : NoInteriorPaddingHoles machine.tm first)
    (hfirstLength : (first.filter Option.isSome).length ≤ width)
    (hnextCapacity :
      next.length ≤ (width + 1) * blockSize machine.tm)
    (hint : SingleStackHint machine.tm)
    (hwindows : ∀ position : Fin (width + 1),
      OccupiedStackShiftAllowed machine stack hint
        (stackShiftWindowAt machine.tm width
          first next position)) :
    NoInteriorPaddingHoles machine.tm next := by
  apply noInteriorPaddingHoles_of_blankPaddingMonotone
  simp only [BlankPaddingMonotone, decide_eq_true_eq]
  intro firstIndex nextIndex order blank
  by_cases nextBound : nextIndex < next.length
  · have nextCovered : nextIndex < (width + 1) * blockSize machine.tm :=
      Nat.lt_of_lt_of_le nextBound hnextCapacity
    have firstCovered : firstIndex < (width + 1) * blockSize machine.tm := by
      omega
    by_cases firstPrefix : firstIndex < hint.2.1.val
    · exact False.elim ((occupiedRawWindows_prefix_nonblank
        machine width stack first next hint hwindows firstIndex firstPrefix) blank)
    · have firstSuffix : hint.2.1.val ≤ firstIndex := by omega
      have nextSuffix : hint.2.1.val ≤ nextIndex := by omega
      have sourceBlank :
          paddedAtom (first.filter Option.isSome)
            (firstIndex - hint.2.1.val + hint.1.val) = none := by
        rw [← occupiedRawWindows_suffix_paddedAtom
          machine width stack first next hfirst hfirstLength
          hint hwindows firstIndex firstSuffix firstCovered]
        exact blank
      have sourceMonotone : BlankPaddingMonotone machine.tm
          (first.filter Option.isSome) := by
        apply blankPaddingMonotone_of_noInteriorPaddingHoles
        simp only [NoInteriorPaddingHoles, decide_eq_true_eq]
        exact ⟨first.filter Option.isSome, 0,
          filter_isSome_noBlank machine.tm first, by simp only [List.replicate_zero,
              List.append_nil]⟩
      have sourceMonotone' := sourceMonotone
      simp only [BlankPaddingMonotone, decide_eq_true_eq] at sourceMonotone'
      rw [occupiedRawWindows_suffix_paddedAtom
        machine width stack first next hfirst hfirstLength
        hint hwindows nextIndex nextSuffix nextCovered]
      apply sourceMonotone'
        (firstIndex - hint.2.1.val + hint.1.val)
        (nextIndex - hint.2.1.val + hint.1.val)
      · omega
      · exact sourceBlank
  · apply paddedAtom_none_of_length_le
    omega

private noncomputable def PhaseRowStackRangeFaithful
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm) : Bool :=
  @decide (
  ∀ (position : Position width)
    (stack : machine.tm.K)
    (offset : Fin (blockSize machine.tm)),
    width + 1 ≤ position.val * blockSize machine.tm + offset.val →
      ((completeMachineBlock machine.tm (row position)
        offset).2.2.1 stack) = none
  ) (Classical.propDecidable _)
private theorem allInitializationWindows_next_stackRangeFaithful
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hrange : ∀ position : Position width,
      (first position).range = phaseRangeBlockAt machine.tm width position)
    (hwindows : ∀ position : Position width,
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    PhaseRowStackRangeFaithful machine width next := by
  simp only [GapCVP.CLNoHoleTimeInduction.PhaseRowStackRangeFaithful, decide_eq_true_eq]
  intro position stack offset hout
  have initial := hwindows position
  simp only [GapCVP.CLPhaseTableauSimulation.AnchoredInitializationAllowed,
      GapCVP.CLCompleteVerifierSimulation.CompleteInitializationAllowed,
    decide_eq_true_eq] at initial
  have initialOuter := ofClassicalDecide initial
  have initialCore := ofClassicalDecide initialOuter.1
  have hblock := initialCore.2.2.1
  change
    completeMachineBlock machine.tm (next position) =
      initializedPhaseBlock machine
        (completeMachineBlock machine.tm (first position))
        (first position).payload (first position).range at hblock
  have hfalse : (first position).range offset = false := by
    rw [hrange position]
    simp only [phaseRangeBlockAt, Nat.not_lt.mpr hout, decide_false]
  rw [hblock]
  simp only [initializedPhaseBlock, hfalse, Bool.false_eq_true, ↓reduceIte, blankCell]

end CLNoHoleTimeInduction

namespace CLBoundedRowInduction

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation GapCVP.CLWholeTraceSoundness
open GapCVP.CLArbitraryVerifierSoundness GapCVP.CLStackShiftSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLAnchoredTraceSimulation
open GapCVP.CLArbitraryRowOccupancy GapCVP.CLRawTrackSimulation GapCVP.CLCompactWindowSoundness
open GapCVP.CLNoHoleTimeInduction

private def packedPhaseCapacity (tm : Turing.FinTM2) (width : ℕ) : ℕ :=
  (width + 1) * blockSize tm

/-- GapCVP reduction support. -/
def fullPackedPhaseStackAtoms
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (stack : machine.tm.K) : List (CellAtom machine.tm) :=
  List.ofFn fun index : Fin (packedPhaseCapacity machine.tm width) =>
    ((completeMachineBlock machine.tm
      (row ⟨index.val / blockSize machine.tm,
        (Nat.div_lt_iff_lt_mul
          (blockSize_pos machine.tm)).mpr index.isLt⟩)
      ⟨index.val % blockSize machine.tm,
        Nat.mod_lt index.val (blockSize_pos machine.tm)⟩).2.2.1 stack)

@[simp] private theorem fullPackedPhaseStackAtoms_length
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (stack : machine.tm.K) :
    (fullPackedPhaseStackAtoms machine width row stack).length =
      packedPhaseCapacity machine.tm width := by
  simp only [fullPackedPhaseStackAtoms, List.length_ofFn]

private theorem packedBlockOffset_lt_capacity
    (tm : Turing.FinTM2)
    (width : ℕ)
    (position : Position width)
    (offset : Fin (blockSize tm)) :
    position.val * blockSize tm + offset.val <
      packedPhaseCapacity tm width := by
  have hblock :
      (position.val + 1) * blockSize tm ≤
        (width + 1) * blockSize tm :=
    Nat.mul_le_mul_right (blockSize tm) (by
      have hpos := position.isLt
      omega)
  change position.val * blockSize tm + offset.val <
    (width + 1) * blockSize tm
  apply Nat.lt_of_lt_of_le _ hblock
  simpa only [Nat.add_mul, Nat.one_mul]
    using Nat.add_lt_add_left offset.isLt
      (position.val * blockSize tm)

private theorem atomBlockAt_fullPackedPhaseStackAtoms
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (stack : machine.tm.K)
    (position : Position width) :
    atomBlockAt machine.tm
      (fullPackedPhaseStackAtoms machine width row stack)
      position.val =
      stackAtomsOfBlock machine.tm
        (completeMachineBlock machine.tm (row position)) stack := by
  funext offset
  let global := position.val * blockSize machine.tm + offset.val
  have hglobal : global < packedPhaseCapacity machine.tm width := by
    exact packedBlockOffset_lt_capacity machine.tm width position offset
  have hblock :
      global / blockSize machine.tm = position.val := by
    dsimp [global]
    have hdivision := Nat.mul_add_div
      (blockSize_pos machine.tm) position.val offset.val
    simpa only [Nat.mul_comm, Nat.div_eq_of_lt offset.isLt, add_zero] using hdivision
  have hoffset : global % blockSize machine.tm = offset.val := by
    dsimp [global]
    exact Nat.mul_add_mod_of_lt offset.isLt
  change
    paddedAtom (fullPackedPhaseStackAtoms machine width row stack)
      global =
      ((completeMachineBlock machine.tm (row position)
        offset).2.2.1 stack)
  change
    ((List.ofFn fun index :
      Fin (packedPhaseCapacity machine.tm width) =>
        ((completeMachineBlock machine.tm
          (row ⟨index.val / blockSize machine.tm,
            (Nat.div_lt_iff_lt_mul
              (blockSize_pos machine.tm)).mpr index.isLt⟩)
          ⟨index.val % blockSize machine.tm,
            Nat.mod_lt index.val
              (blockSize_pos machine.tm)⟩).2.2.1 stack))[
                global]?).getD none =
      ((completeMachineBlock machine.tm (row position)
        offset).2.2.1 stack)
  rw [List.getElem?_ofFn]
  simp only [dite_eq_left hglobal, Option.getD_some]
  have hposition :
      (⟨global / blockSize machine.tm,
        (Nat.div_lt_iff_lt_mul
          (blockSize_pos machine.tm)).mpr hglobal⟩ : Position width) =
        position := by
    apply Fin.ext
    exact hblock
  have hlocal :
      (⟨global % blockSize machine.tm,
        Nat.mod_lt global (blockSize_pos machine.tm)⟩ :
          Fin (blockSize machine.tm)) = offset := by
    apply Fin.ext
    exact hoffset
  rw [hposition, hlocal]

private theorem phaseStackWindow_eq_fullPackedPhaseStackWindow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hboundary : ∀ position : Position width,
      completeIsFirstBlock machine.tm (first position) =
        decide (position.val = 0))
    (stack : machine.tm.K)
    (position : Position width) :
    stackWindowOfScriptBlock machine.tm
      (completeScriptWindow machine.tm
        (anchoredVerifierWindowAt machine.tm width
          first next position)) stack =
      stackShiftWindowAt machine.tm width
        (fullPackedPhaseStackAtoms machine width first stack)
        (fullPackedPhaseStackAtoms machine width next stack)
        position := by
  simp only [stackWindowOfScriptBlock, completeScriptWindow,
    anchoredVerifierWindowAt, stackShiftWindowAt]
  rw [atomBlockAt_fullPackedPhaseStackAtoms machine width
    first stack (leftBlock width position)]
  rw [atomBlockAt_fullPackedPhaseStackAtoms machine width
    first stack position]
  rw [atomBlockAt_fullPackedPhaseStackAtoms machine width
    first stack (rightBlock width position)]
  rw [atomBlockAt_fullPackedPhaseStackAtoms machine width
    next stack position]
  change
    (_, _, _, _, completeIsFirstBlock machine.tm (first position)) =
      (_, _, _, _, decide (position.val = 0))
  rw [hboundary position]
  simp only [completeMachineBlock]

private theorem allCorrectedVerifierWindows_occupied_fullPackedWindows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hboundary : ∀ position : Position width,
      completeIsFirstBlock machine.tm (first position) =
        decide (position.val = 0))
    (hwindows : ∀ position : Position width,
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    ∀ (stack : machine.tm.K) (position : Position width),
      OccupiedStackShiftAllowed machine stack
        ((first 0).script.2.1 stack)
        (stackShiftWindowAt machine.tm width
          (fullPackedPhaseStackAtoms machine width first stack)
          (fullPackedPhaseStackAtoms machine width next stack)
          position) := by
  have hanchored : AllAnchoredVerificationWindows
      machine width first next := by
    simp only [AllAnchoredVerificationWindows, decide_eq_true_eq]
    intro position
    have verification := hwindows position
    simp only [StackSoundAnchoredVerificationAllowed, decide_eq_true_eq] at verification
    exact verification.1
  intro stack position
  let window := anchoredVerifierWindowAt machine.tm
    width first next position
  have hverification := hwindows position
  simp only [StackSoundAnchoredVerificationAllowed, AnchoredVerificationAllowed,
    CompleteVerificationAllowed, decide_eq_true_eq] at hverification
  have hscript : scriptBlockAllowed machine
      (completeScriptWindow machine.tm window) = true :=
    hverification.1.1.2.2
  obtain ⟨_, _, _, _, hstacks⟩ :=
    (scriptBlockAllowed_iff machine
      (completeScriptWindow machine.tm window)).mp hscript
  have hshift :
      StackShiftAllowed machine.tm
        ((first position).script.2.1 stack)
        (stackWindowOfScriptBlock machine.tm
          (completeScriptWindow machine.tm window) stack) :=
    (stackShiftAllowed_iff machine.tm
      ((first position).script.2.1 stack)
      (stackWindowOfScriptBlock machine.tm
        (completeScriptWindow machine.tm window) stack)).mp
      (hstacks stack)
  have hhint := allAnchoredVerificationWindows_hint_constant
    machine width first next hanchored position
  have prefixEvidence := hverification.2
  simp only [OccupiedVerifierPrefix, decide_eq_true_eq] at prefixEvidence
  have hprefix := prefixEvidence stack
  simp only [OccupiedStackShiftAllowed, decide_eq_true_eq]
  change
    StackShiftAllowed machine.tm
      ((first 0).script.2.1 stack)
      (stackShiftWindowAt machine.tm width
        (fullPackedPhaseStackAtoms machine width first stack)
        (fullPackedPhaseStackAtoms machine width next stack) position) ∧
      ∀ offset : Fin (blockSize machine.tm),
        offset.val < ((first 0).script.2.1 stack).2.1.val →
          (cellAtomValue machine stack
            (((first 0).script.2.1 stack).2.2 offset)).isSome = true
  constructor
  · rw [← phaseStackWindow_eq_fullPackedPhaseStackWindow
      machine width first next hboundary stack position]
    change
      StackShiftAllowed machine.tm
        ((first 0).script.2.1 stack)
        (stackWindowOfScriptBlock machine.tm
          (completeScriptWindow machine.tm window) stack)
    rw [← hhint]
    exact hshift
  · rw [← hhint]
    exact hprefix

private theorem allCorrectedVerifierWindows_preserve_fullPacked_noHoles
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hboundary : ∀ position : Position width,
      completeIsFirstBlock machine.tm (first position) =
        decide (position.val = 0))
    (hfirstHoles : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine width first stack))
    (hfirstLength : ∀ stack : machine.tm.K,
      ((fullPackedPhaseStackAtoms machine width first stack).filter
        Option.isSome).length ≤ width)
    (hwindows : ∀ position : Position width,
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine width next stack) := by
  intro stack
  apply occupiedRawWindows_preserve_noInteriorPaddingHoles
    machine width stack
    (fullPackedPhaseStackAtoms machine width first stack)
    (fullPackedPhaseStackAtoms machine width next stack)
    (hfirstHoles stack)
  · exact hfirstLength stack
  · rw [fullPackedPhaseStackAtoms_length]
    exact le_rfl
  · exact allCorrectedVerifierWindows_occupied_fullPackedWindows
      machine width first next hboundary hwindows stack

private theorem fullPackedPhaseStackAtoms_occupied
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (hrow : PhaseRowAtomsWellTyped machine width row)
    (stack : machine.tm.K) :
    OccupiedAtomTrack machine stack
      ((fullPackedPhaseStackAtoms machine width row stack).filter
        Option.isSome) := by
  simp only [OccupiedAtomTrack, decide_eq_true_eq]
  have typedRow := hrow
  simp only [PhaseRowAtomsWellTyped, decide_eq_true_eq] at typedRow
  intro atom hmem
  have hfiltered := List.mem_filter.mp hmem
  obtain ⟨index, hindex⟩ := List.mem_ofFn.mp hfiltered.1
  let position : Position width :=
    ⟨index.val / blockSize machine.tm,
      (Nat.div_lt_iff_lt_mul
        (blockSize_pos machine.tm)).mpr index.isLt⟩
  let offset : Fin (blockSize machine.tm) :=
    ⟨index.val % blockSize machine.tm,
      Nat.mod_lt index.val (blockSize_pos machine.tm)⟩
  have htyped := typedRow position stack offset
  simp only [DecodableOrBlank, decide_eq_true_eq] at htyped
  change
    ((completeMachineBlock machine.tm (row position)
      offset).2.2.1 stack) = atom at hindex
  rw [hindex] at htyped
  rcases htyped with hblank | hoccupied
  · simp only [hblank, Option.isSome_none, Bool.false_eq_true, and_false] at hfiltered
  · exact hoccupied

private def decodedFullPackedPhaseStack
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (stack : machine.tm.K) : List (machine.tm.Γ stack) :=
  (fullPackedPhaseStackAtoms machine width row stack).filterMap
    (cellAtomValue machine stack)

private theorem fullPackedPhaseStackAtoms_filter_decode
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (stack : machine.tm.K) :
    ((fullPackedPhaseStackAtoms machine width row stack).filter
      Option.isSome).filterMap (cellAtomValue machine stack) =
      decodedFullPackedPhaseStack machine width row stack := by
  exact filterMap_filter_isSome machine stack
    (fullPackedPhaseStackAtoms machine width row stack)

private theorem fullPackedPhaseStackAtoms_compact_length
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (hrow : PhaseRowAtomsWellTyped machine width row)
    (stack : machine.tm.K) :
    ((fullPackedPhaseStackAtoms machine width row stack).filter
      Option.isSome).length =
        (decodedFullPackedPhaseStack machine width row stack).length := by
  calc
    ((fullPackedPhaseStackAtoms machine width row stack).filter
      Option.isSome).length =
        (((fullPackedPhaseStackAtoms machine width row stack).filter
          Option.isSome).filterMap
            (cellAtomValue machine stack)).length :=
      (occupiedAtomTrack_filterMap_length machine stack
        ((fullPackedPhaseStackAtoms machine width row stack).filter
          Option.isSome)
        (fullPackedPhaseStackAtoms_occupied
          machine width row hrow stack)).symm
    _ = (decodedFullPackedPhaseStack
        machine width row stack).length := by
      rw [fullPackedPhaseStackAtoms_filter_decode]

private theorem stackSoundValidTrace_occupied_fullPackedWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    ∀ (stack : machine.tm.K)
      (position : Position (rowWidth bound machine x)),
      OccupiedStackShiftAllowed machine stack
        (((decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time)) 0).script.2.1) stack)
        (stackShiftWindowAt machine.tm (rowWidth bound machine x)
          (fullPackedPhaseStackAtoms machine
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time))) stack)
          (fullPackedPhaseStackAtoms machine
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace time.succ)) stack)
          position) := by
  apply allCorrectedVerifierWindows_occupied_fullPackedWindows
    machine (rowWidth bound machine x)
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ))
  · intro position
    have hmask := stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time)
      position (by
        rw [hfirst position]
        exact PhaseTag.noConfusion)
    simp only [AnchoredPhaseMasks, decide_eq_true_eq] at hmask
    exact hmask.2.2.2
  · exact stackSoundValidTrace_occupied_verification_windows
      bound machine x trace htrace time hfirst hnext

private theorem stackSoundValidTrace_preserves_fullPacked_noHoles
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    (hfirstHoles : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))) stack))
    (hfirstLength : ∀ stack : machine.tm.K,
      ((fullPackedPhaseStackAtoms machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time))) stack).filter
            Option.isSome).length ≤ rowWidth bound machine x) :
    ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) stack) := by
  intro stack
  apply occupiedRawWindows_preserve_noInteriorPaddingHoles
    machine (rowWidth bound machine x) stack
    (fullPackedPhaseStackAtoms machine (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))) stack)
    (fullPackedPhaseStackAtoms machine (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine (trace time.succ)) stack)
    (hfirstHoles stack)
  · exact hfirstLength stack
  · rw [fullPackedPhaseStackAtoms_length]
    exact le_rfl
  · exact stackSoundValidTrace_occupied_fullPackedWindows
      bound machine x trace htrace time hfirst hnext stack

private theorem fullPacked_noHoles_and_bound_implies_stackRangeFaithful
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine width row stack))
    (hbound : ∀ stack : machine.tm.K,
      ((fullPackedPhaseStackAtoms machine width row stack).filter
        Option.isSome).length ≤ width) :
    PhaseRowStackRangeFaithful machine width row := by
  simp only [PhaseRowStackRangeFaithful, decide_eq_true_eq]
  intro position stack offset hout
  let global := position.val * blockSize machine.tm + offset.val
  have hpadded :
      paddedAtom (fullPackedPhaseStackAtoms
        machine width row stack) global = none := by
    rw [noHoles_padded_compact machine.tm
      (fullPackedPhaseStackAtoms machine width row stack)
      (hholes stack) global]
    apply paddedAtom_none_of_length_le machine.tm
      ((fullPackedPhaseStackAtoms machine width row stack).filter
        Option.isSome) global
    have hlength := hbound stack
    dsimp [global]
    omega
  have hblock := congrFun
    (atomBlockAt_fullPackedPhaseStackAtoms
      machine width row stack position) offset
  change
    paddedAtom (fullPackedPhaseStackAtoms machine width row stack)
      global =
      ((completeMachineBlock machine.tm (row position)
        offset).2.2.1 stack) at hblock
  exact hblock.symm.trans hpadded

end CLBoundedRowInduction

namespace CLFullStackStepSoundness

open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRows GapCVP.CLLocalWindows GapCVP.CLExactVerifierRules
open GapCVP.CLCompleteLocalCompiler GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows
open GapCVP.CLLocalTableauCompiler GapCVP.CLUnconditionalTableau
open GapCVP.CLGlobalTableauSimulation GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness GapCVP.CLStackShiftSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLArbitraryRowOccupancy GapCVP.CLRawTrackSimulation
open GapCVP.CLCompactWindowSoundness GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction

private theorem occupiedAtomTrack_forall₂_filterMap
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atoms : List (CellAtom machine.tm))
    (hoccupied : OccupiedAtomTrack machine stack atoms) :
    List.Forall₂
      (fun atom value =>
        cellAtomValue machine stack atom = some value)
      atoms (atoms.filterMap (cellAtomValue machine stack)) := by
  induction atoms with
  | nil => exact .nil
  | cons atom rest ih =>
      have occupied := hoccupied
      simp only [OccupiedAtomTrack, decide_eq_true_eq] at occupied
      obtain ⟨value, hvalue⟩ := occupied atom (by simp only [List.mem_cons, true_or])
      have hrest : OccupiedAtomTrack machine stack rest := by
        simp only [OccupiedAtomTrack, decide_eq_true_eq]
        intro candidate hcandidate
        exact occupied candidate (by simp only [List.mem_cons, hcandidate, or_true])
      rw [List.filterMap_cons_some hvalue]
      exact List.Forall₂.cons hvalue (ih hrest)

private theorem decodedAtomBlock_of_occupiedAtomTrack
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (atoms : List (CellAtom machine.tm))
    (hoccupied : OccupiedAtomTrack machine stack atoms) :
    decodedAtomBlock machine stack
      (atomBlockAt machine.tm atoms 0) =
        (atoms.filterMap (cellAtomValue machine stack)).take
          (blockSize machine.tm) := by
  have hforall := occupiedAtomTrack_forall₂_filterMap
    machine stack atoms hoccupied
  have hpointwise :
      (fun index : Fin (blockSize machine.tm) =>
        cellAtomValue machine stack
          ((atomBlockAt machine.tm atoms 0) index)) =
      (fun index : Fin (blockSize machine.tm) =>
        (atoms.filterMap
          (cellAtomValue machine stack))[index.val]?) := by
    funext index
    simpa only [atomBlockAt, zero_mul, zero_add] using paddedAtom_decode machine stack hforall
        index.val
  unfold decodedAtomBlock
  rw [hpointwise]
  exact filterMap_ofFn_getElem
    (atoms.filterMap (cellAtomValue machine stack))
    (blockSize machine.tm)

private theorem fullPackedPhaseStack_firstBlock_decode
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (hrow : PhaseRowAtomsWellTyped machine width row)
    (stack : machine.tm.K)
    (hholes : NoInteriorPaddingHoles machine.tm
      (fullPackedPhaseStackAtoms machine width row stack)) :
    decodedAtomBlock machine stack
      (stackAtomsOfBlock machine.tm
        (completeMachineBlock machine.tm (row 0)) stack) =
      (decodedFullPackedPhaseStack machine width row stack).take
        (blockSize machine.tm) := by
  rw [← atomBlockAt_fullPackedPhaseStackAtoms
    machine width row stack 0]
  change
    decodedAtomBlock machine stack
      (atomBlockAt machine.tm
        (fullPackedPhaseStackAtoms machine width row stack) 0) =
      (decodedFullPackedPhaseStack machine width row stack).take
        (blockSize machine.tm)
  rw [noHoles_atomBlockAt_compact machine.tm
    (fullPackedPhaseStackAtoms machine width row stack) hholes 0]
  rw [decodedAtomBlock_of_occupiedAtomTrack machine stack
    ((fullPackedPhaseStackAtoms machine width row stack).filter
      Option.isSome)
    (fullPackedPhaseStackAtoms_occupied
      machine width row hrow stack)]
  rw [fullPackedPhaseStackAtoms_filter_decode]

private theorem occupiedPackedWindows_compact_common_suffix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (stack : machine.tm.K)
    (first next : List (CellAtom machine.tm))
    (hfirstHoles : NoInteriorPaddingHoles machine.tm first)
    (hnextHoles : NoInteriorPaddingHoles machine.tm next)
    (hfirstLength : (first.filter Option.isSome).length ≤ width)
    (hnextCapacity :
      next.length ≤ (width + 1) * blockSize machine.tm)
    (hint : SingleStackHint machine.tm)
    (hwindows : ∀ position : Fin (width + 1),
      OccupiedStackShiftAllowed machine stack hint
        (stackShiftWindowAt machine.tm width
          first next position)) :
    (first.filter Option.isSome).drop hint.1.val =
      (next.filter Option.isSome).drop hint.2.1.val := by
  apply (atomSuffix_iff_paddedShift machine.tm
    (first.filter Option.isSome)
    (next.filter Option.isSome)
    (filter_isSome_noBlank machine.tm first)
    (filter_isSome_noBlank machine.tm next)
    hint.1.val hint.2.1.val).mpr
  intro index
  let global := hint.2.1.val + index
  by_cases hcovered :
      global < (width + 1) * blockSize machine.tm
  · have hprefix : hint.2.1.val ≤ global := by
      dsimp [global]
      omega
    have hshift := occupiedRawWindows_suffix_paddedAtom
      machine width stack first next hfirstHoles hfirstLength
      hint hwindows global hprefix hcovered
    have hnextPad := noHoles_padded_compact machine.tm
      next hnextHoles global
    have hcoordinate :
        global - hint.2.1.val + hint.1.val =
          hint.1.val + index := by
      dsimp [global]
      omega
    rw [hcoordinate] at hshift
    exact hshift.symm.trans hnextPad
  · have hbeyond :
        (width + 1) * blockSize machine.tm ≤ global := by
      omega
    have hblock :
        (width + 1) * blockSize machine.tm =
          width * blockSize machine.tm + blockSize machine.tm := by
      simp only [Nat.add_mul, one_mul]
    have hdrop := hint.2.1.isLt
    have hcapacity := width_le_block_capacity machine.tm width
    have hfirstBeyond :
        (first.filter Option.isSome).length ≤
          hint.1.val + index := by
      dsimp [global] at hbeyond
      rw [hblock] at hbeyond
      omega
    have hnextCompactLength :
        (next.filter Option.isSome).length ≤ next.length :=
      List.length_filter_le Option.isSome next
    have hnextBeyond :
        (next.filter Option.isSome).length ≤
          hint.2.1.val + index := by
      dsimp [global] at hbeyond
      omega
    rw [paddedAtom_none_of_length_le machine.tm
      (first.filter Option.isSome)
      (hint.1.val + index) hfirstBeyond,
      paddedAtom_none_of_length_le machine.tm
        (next.filter Option.isSome)
        (hint.2.1.val + index) hnextBeyond]

private theorem occupiedPackedWindows_decoded_common_suffix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (stack : machine.tm.K)
    (first next : List (CellAtom machine.tm))
    (hfirstHoles : NoInteriorPaddingHoles machine.tm first)
    (hnextHoles : NoInteriorPaddingHoles machine.tm next)
    (hfirstLength : (first.filter Option.isSome).length ≤ width)
    (hnextCapacity :
      next.length ≤ (width + 1) * blockSize machine.tm)
    (hfirstOccupied : OccupiedAtomTrack machine stack
      (first.filter Option.isSome))
    (hnextOccupied : OccupiedAtomTrack machine stack
      (next.filter Option.isSome))
    (hint : SingleStackHint machine.tm)
    (hwindows : ∀ position : Fin (width + 1),
      OccupiedStackShiftAllowed machine stack hint
        (stackShiftWindowAt machine.tm width
          first next position)) :
    (first.filterMap (cellAtomValue machine stack)).drop hint.1.val =
      (next.filterMap (cellAtomValue machine stack)).drop
        hint.2.1.val := by
  have hcompact := decodedCommonSuffix_of_occupied_atom_suffix
    machine stack
    (first.filter Option.isSome)
    (next.filter Option.isSome)
    hfirstOccupied hnextOccupied
    hint.1.val hint.2.1.val
    (occupiedPackedWindows_compact_common_suffix
      machine width stack first next hfirstHoles hnextHoles
      hfirstLength hnextCapacity hint hwindows)
  rw [filterMap_filter_isSome machine stack,
    filterMap_filter_isSome machine stack] at hcompact
  exact hcompact

/-- GapCVP reduction support. -/
def decodedFullPackedPhaseConfiguration
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm) :
    machine.tm.Cfg :=
  match machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (row 0)) with
  | none => Turing.initList machine.tm []
  | some control => {
      l := control.1
      var := control.2
      stk := fun stack => decodedFullPackedPhaseStack
        machine width row stack
    }

private theorem finiteHeadScriptRun_eq_fullPacked
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (hrow : PhaseRowAtomsWellTyped machine width row)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine width row stack))
    (label : machine.tm.Λ)
    (state : machine.tm.σ) :
    finiteHeadScriptRun machine label state
      (fun stack => stackAtomsOfBlock machine.tm
        (completeMachineBlock machine.tm (row 0)) stack) =
      executePrefixScript (machine.tm.m label) state
        (fun stack => decodedFullPackedPhaseStack
          machine width row stack)
        (emptyPrefixScript machine.tm.Γ) := by
  let heads : machine.tm.K → AtomBlock machine.tm :=
    fun stack => stackAtomsOfBlock machine.tm
      (completeMachineBlock machine.tm (row 0)) stack
  let finite := finiteHeadConfiguration
    machine (some label, state) heads
  have hagreement : StackPrefixAgreement (blockSize machine.tm)
      (fun stack => decodedFullPackedPhaseStack
        machine width row stack) finite.stk := by
    simp only [StackPrefixAgreement, decide_eq_true_eq]
    intro stack
    change
      (decodedFullPackedPhaseStack machine width row stack).take
        (blockSize machine.tm) =
        (decodedAtomBlock machine stack (heads stack)).take
          (blockSize machine.tm)
    rw [fullPackedPhaseStack_firstBlock_decode
      machine width row hrow stack (hholes stack)]
    simp only [List.take_self_eq_iff, List.length_take, inf_le_left]
  have hlookahead : StackPrefixAgreement
      (statementStackActions (machine.tm.m label) + 1)
      (fun stack => decodedFullPackedPhaseStack
        machine width row stack) finite.stk :=
    stackPrefixAgreement_mono
      (statementLookahead_le_blockSize machine.tm label)
      hagreement
  have hscript := executePrefixScript_of_prefix
    (machine.tm.m label) state
    (fun stack => decodedFullPackedPhaseStack
      machine width row stack)
    finite.stk (emptyPrefixScript machine.tm.Γ)
    (by simpa only [scriptStacks_empty] using hlookahead)
  change
    executePrefixScript (machine.tm.m label) state finite.stk
      (emptyPrefixScript machine.tm.Γ) =
      executePrefixScript (machine.tm.m label) state
        (fun stack => decodedFullPackedPhaseStack
          machine width row stack)
        (emptyPrefixScript machine.tm.Γ)
  exact hscript.symm

private theorem allCorrectedVerifierWindows_fullPacked_decoded_suffix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hfirstTyped : PhaseRowAtomsWellTyped machine width first)
    (hnextTyped : PhaseRowAtomsWellTyped machine width next)
    (hboundary : ∀ position : Position width,
      completeIsFirstBlock machine.tm (first position) =
        decide (position.val = 0))
    (hfirstHoles : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine width first stack))
    (hfirstLength : ∀ stack : machine.tm.K,
      ((fullPackedPhaseStackAtoms machine width first stack).filter
        Option.isSome).length ≤ width)
    (hwindows : ∀ position : Position width,
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    ∀ stack : machine.tm.K,
      (decodedFullPackedPhaseStack machine width first stack).drop
          ((first 0).script.2.1 stack).1.val =
        (decodedFullPackedPhaseStack machine width next stack).drop
          ((first 0).script.2.1 stack).2.1.val := by
  have hnextHoles :=
    allCorrectedVerifierWindows_preserve_fullPacked_noHoles
      machine width first next hboundary hfirstHoles
      hfirstLength hwindows
  intro stack
  exact occupiedPackedWindows_decoded_common_suffix
    machine width stack
    (fullPackedPhaseStackAtoms machine width first stack)
    (fullPackedPhaseStackAtoms machine width next stack)
    (hfirstHoles stack) (hnextHoles stack)
    (hfirstLength stack)
    (by rw [fullPackedPhaseStackAtoms_length]; exact le_rfl)
    (fullPackedPhaseStackAtoms_occupied
      machine width first hfirstTyped stack)
    (fullPackedPhaseStackAtoms_occupied
      machine width next hnextTyped stack)
    ((first 0).script.2.1 stack)
    (allCorrectedVerifierWindows_occupied_fullPackedWindows
      machine width first next hboundary hwindows stack)

private theorem allCorrectedVerifierWindows_actual_fullPackedStep
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hfirstTyped : PhaseRowAtomsWellTyped machine width first)
    (hnextTyped : PhaseRowAtomsWellTyped machine width next)
    (hboundary : ∀ position : Position width,
      completeIsFirstBlock machine.tm (first position) =
        decide (position.val = 0))
    (hfirstHoles : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine width first stack))
    (hfirstLength : ∀ stack : machine.tm.K,
      ((fullPackedPhaseStackAtoms machine width first stack).filter
        Option.isSome).length ≤ width)
    (hwindows : ∀ position : Position width,
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    machine.tm.step
        (decodedFullPackedPhaseConfiguration machine width first) =
      some (decodedFullPackedPhaseConfiguration
        machine width next) := by
  let window := anchoredVerifierWindowAt machine.tm width first next 0
  have hverification := hwindows 0
  simp only [StackSoundAnchoredVerificationAllowed, decide_eq_true_eq] at hverification
  have anchored := hverification.1
  have fields := anchored
  simp only [AnchoredVerificationAllowed, CompleteVerificationAllowed,
    FirstBlockAnchored, decide_eq_true_eq] at fields
  have fieldsOuter := ofClassicalDecide fields
  have verificationFields := ofClassicalDecide fieldsOuter.1
  have sourceAnchorFields := ofClassicalDecide fieldsOuter.2.1
  have nextAnchorFields := ofClassicalDecide fieldsOuter.2.2
  have hmarked :
      completeIsFirstBlock machine.tm (first 0) = true := by
    simpa only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, decide_true] using hboundary 0
  have hsourceAnchor :
      completeMachineBlock machine.tm (first 0) =
        completeMachineHead machine.tm (first 0) :=
    (sourceAnchorFields hmarked).1
  have hnextMarked :
      completeIsFirstBlock machine.tm (next 0) = true := by
    have hkeep := anchoredVerification_boundary machine window anchored
    exact hkeep.trans hmarked
  have hnextAnchor :
      completeMachineBlock machine.tm (next 0) =
        completeMachineHead machine.tm (next 0) :=
    (nextAnchorFields hnextMarked).1
  have hscriptBlock : scriptBlockAllowed machine
      (completeScriptWindow machine.tm window) = true :=
    verificationFields.2.2
  obtain ⟨_, query, hquery, hscript, _⟩ :=
    (scriptBlockAllowed_iff machine
      (completeScriptWindow machine.tm window)).mp hscriptBlock
  cases hfirstControl : machineControlOfBlock machine.tm
      (first 0).script.1.2 with
  | none =>
      simp only [scriptQueryOfBlockWindow, completeScriptWindow, anchoredVerifierWindowAt,
          leftBlock_zero,
          hfirstControl, reduceCtorEq, window] at hquery
  | some firstControl =>
      cases hnextControl : machineControlOfBlock machine.tm
          (next 0).script.1.2 with
      | none =>
          simp only [scriptQueryOfBlockWindow, completeScriptWindow, anchoredVerifierWindowAt,
              leftBlock_zero,
              hfirstControl, hnextControl, reduceCtorEq, window] at hquery
      | some nextControl =>
          have hfirstControl' :
              machineControlOfBlock machine.tm
                (completeMachineHead machine.tm (first 0)) =
                  some firstControl := by
            simpa only [completeMachineHead] using hfirstControl
          have hnextControl' :
              machineControlOfBlock machine.tm
                (completeMachineHead machine.tm (next 0)) =
                  some nextControl := by
            simpa only [completeMachineHead] using hnextControl
          have hqueryValue :
              query =
                ((firstControl,
                  (fun stack => stackAtomsOfBlock machine.tm
                    (completeMachineHead machine.tm (first 0)) stack),
                  nextControl),
                  (fun stack => stackAtomsOfBlock machine.tm
                    (completeMachineHead machine.tm (next 0)) stack),
                  (first 0).script.2.1) := by
            have heq := hquery
            simp only [scriptQueryOfBlockWindow, completeScriptWindow, anchoredVerifierWindowAt,
                leftBlock_zero,
                hfirstControl, hnextControl, Option.some.injEq, window] at heq
            simpa only [completeMachineHead] using heq.symm
          subst query
          rw [← hsourceAnchor, ← hnextAnchor] at hscript
          obtain ⟨label, hlabel, hcontrol, hstate, hchecks⟩ :=
            (scriptVerifierAllowed_iff machine _).mp hscript
          let heads : machine.tm.K → AtomBlock machine.tm :=
            fun stack => stackAtomsOfBlock machine.tm
              (completeMachineBlock machine.tm (first 0)) stack
          let run := finiteHeadScriptRun machine label firstControl.2 heads
          have hsourceLabel : firstControl.1 = some label := by exact hlabel
          have hnextLabel : run.1 = nextControl.1 := by exact hcontrol
          have hnextState : run.2.1 = nextControl.2 := by exact hstate
          have hnextHoles :=
            allCorrectedVerifierWindows_preserve_fullPacked_noHoles
              machine width first next hboundary
              hfirstHoles hfirstLength hwindows
          have hsuffix :=
            allCorrectedVerifierWindows_fullPacked_decoded_suffix
              machine width first next hfirstTyped hnextTyped
              hboundary hfirstHoles hfirstLength hwindows
          have hstacks :
              scriptStacks
                  (fun stack => decodedFullPackedPhaseStack
                    machine width first stack) run.2.2 =
                (fun stack => decodedFullPackedPhaseStack
                  machine width next stack) := by
            funext stack
            have hcheck := hchecks stack
            change
              ((first 0).script.2.1 stack).1.val =
                    run.2.2.dropped stack ∧
                ((first 0).script.2.1 stack).2.1.val =
                    (run.2.2.pushed stack).length ∧
                  (decodedAtomBlock machine stack
                    (stackAtomsOfBlock machine.tm
                      (completeMachineBlock machine.tm (next 0))
                      stack)).take
                        (run.2.2.pushed stack).length =
                      run.2.2.pushed stack at hcheck
            have hprefix := hcheck.2.2
            rw [fullPackedPhaseStack_firstBlock_decode
              machine width next hnextTyped stack
              (hnextHoles stack)] at hprefix
            have hpushBound :
                (run.2.2.pushed stack).length ≤
                  blockSize machine.tm := by
              have hfin := ((first 0).script.2.1 stack).2.1.isLt
              omega
            simp only [List.take_take,
              Nat.min_eq_left hpushBound] at hprefix
            have hcommon := hsuffix stack
            rw [hcheck.1, hcheck.2.1] at hcommon
            have hnextStack :
                decodedFullPackedPhaseStack machine width next stack =
                  scriptStacks
                    (fun target => decodedFullPackedPhaseStack
                      machine width first target)
                    run.2.2 stack := by
              calc
                decodedFullPackedPhaseStack machine width next stack =
                    (decodedFullPackedPhaseStack
                      machine width next stack).take
                        (run.2.2.pushed stack).length ++
                      (decodedFullPackedPhaseStack
                        machine width next stack).drop
                          (run.2.2.pushed stack).length :=
                    (List.take_append_drop
                      (run.2.2.pushed stack).length
                      (decodedFullPackedPhaseStack
                        machine width next stack)).symm
                _ = run.2.2.pushed stack ++
                    (decodedFullPackedPhaseStack
                      machine width first stack).drop
                        (run.2.2.dropped stack) := by
                    rw [hprefix, ← hcommon]
                _ = scriptStacks
                    (fun target => decodedFullPackedPhaseStack
                      machine width first target)
                    run.2.2 stack := rfl
            exact hnextStack.symm
          have hrun := finiteHeadScriptRun_eq_fullPacked
            machine width first hfirstTyped hfirstHoles
            label firstControl.2
          change
            run = executePrefixScript (machine.tm.m label)
              firstControl.2
              (fun stack => decodedFullPackedPhaseStack
                machine width first stack)
              (emptyPrefixScript machine.tm.Γ) at hrun
          have hexecution := executePrefixScript_correct
            (machine.tm.m label) firstControl.2
            (fun stack => decodedFullPackedPhaseStack
              machine width first stack)
            (emptyPrefixScript machine.tm.Γ)
          simp only [scriptStacks_empty] at hexecution
          rw [← hrun] at hexecution
          have htarget :
              ({ l := run.1
                 var := run.2.1
                 stk := scriptStacks
                   (fun stack => decodedFullPackedPhaseStack
                     machine width first stack)
                   run.2.2 } : machine.tm.Cfg) =
                decodedFullPackedPhaseConfiguration
                  machine width next := by
            unfold decodedFullPackedPhaseConfiguration
            rw [hnextControl']
            apply configuration_eq_of_components machine.tm
            · exact hnextLabel
            · exact hnextState
            · exact hstacks
          apply actualStep_of_stepAux machine.tm
            (decodedFullPackedPhaseConfiguration
              machine width first)
            (decodedFullPackedPhaseConfiguration
              machine width next) label
          · simp only [decodedFullPackedPhaseConfiguration, hfirstControl', hsourceLabel]
          · unfold decodedFullPackedPhaseConfiguration
            rw [hfirstControl']
            exact hexecution.trans htarget

end CLFullStackStepSoundness

namespace CLFullTraceReachability

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLBoundedStates
open GapCVP.CLCellRowBounds GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLArbitraryRowOccupancy GapCVP.CLWholeTimeOccupancy
open GapCVP.CLCompactWindowSoundness GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness

private theorem allCorrectedVerifierWindows_controls
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : ∀ position : Position width,
      StackSoundAnchoredVerificationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position)) :
    ∃ (firstControl nextControl :
      Option machine.tm.Λ × machine.tm.σ),
      machineControlOfBlock machine.tm
        (completeMachineHead machine.tm (first 0)) =
          some firstControl ∧
        machineControlOfBlock machine.tm
          (completeMachineHead machine.tm (next 0)) =
            some nextControl := by
  let window := anchoredVerifierWindowAt machine.tm
    width first next 0
  have verification := hwindows 0
  simp only [StackSoundAnchoredVerificationAllowed, AnchoredVerificationAllowed,
    CompleteVerificationAllowed, decide_eq_true_eq] at verification
  have hscript : scriptBlockAllowed machine
      (completeScriptWindow machine.tm window) = true :=
    verification.1.1.2.2
  obtain ⟨_, query, hquery, _, _⟩ :=
    (scriptBlockAllowed_iff machine
      (completeScriptWindow machine.tm window)).mp hscript
  cases hfirst : machineControlOfBlock machine.tm
      (first 0).script.1.2 with
  | none =>
      simp only [scriptQueryOfBlockWindow, completeScriptWindow, anchoredVerifierWindowAt,
          CLLocalWindows.leftBlock_zero, hfirst, reduceCtorEq, window] at hquery
  | some firstControl =>
      cases hnext : machineControlOfBlock machine.tm
          (next 0).script.1.2 with
      | none =>
          simp only [scriptQueryOfBlockWindow, completeScriptWindow, anchoredVerifierWindowAt,
              CLLocalWindows.leftBlock_zero, hfirst, hnext, reduceCtorEq, window] at hquery
      | some nextControl =>
          refine ⟨firstControl, nextControl, ?_, ?_⟩
          · simpa only [completeMachineHead] using hfirst
          · simpa only [completeMachineHead] using hnext

private theorem decodedFullPackedPhaseConfiguration_stack
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (row : Position width → CompletePhaseCell machine.tm)
    (control : Option machine.tm.Λ × machine.tm.σ)
    (hcontrol : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (row 0)) = some control)
    (stack : machine.tm.K) :
    (decodedFullPackedPhaseConfiguration
      machine width row).stk stack =
      decodedFullPackedPhaseStack machine width row stack := by
  simp only [decodedFullPackedPhaseConfiguration, hcontrol]

private theorem fullPackedStack_space_of_actualTimedRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (row : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (control : Option machine.tm.Λ × machine.tm.σ)
    (hcontrol : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (row 0)) = some control)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x) row)) elapsed)
    (hruntime : elapsed ≤
      (guessTimePolynomial bound machine).eval x.length)
    (stack : machine.tm.K) :
    (decodedFullPackedPhaseStack machine
      (rowWidth bound machine x) row stack).length ≤
      rowWidth bound machine x := by
  have hstack := verifying_stack_length_le
    bound machine x certificate
    (decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x) row)
    run hruntime stack
  rw [decodedFullPackedPhaseConfiguration_stack
    machine (rowWidth bound machine x) row
    control hcontrol stack] at hstack
  exact hstack

private theorem fullPackedCompact_space_of_actualTimedRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (row : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hrow : PhaseRowAtomsWellTyped machine
      (rowWidth bound machine x) row)
    (control : Option machine.tm.Λ × machine.tm.σ)
    (hcontrol : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (row 0)) = some control)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x) row)) elapsed)
    (hruntime : elapsed ≤
      (guessTimePolynomial bound machine).eval x.length)
    (stack : machine.tm.K) :
    ((fullPackedPhaseStackAtoms machine
      (rowWidth bound machine x) row stack).filter
        Option.isSome).length ≤ rowWidth bound machine x := by
  rw [fullPackedPhaseStackAtoms_compact_length
    machine (rowWidth bound machine x) row hrow stack]
  exact fullPackedStack_space_of_actualTimedRun
    bound machine x certificate row control hcontrol
    run hruntime stack

private theorem stackSoundValidTrace_actualFullPackedStep_of_actualTimedRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))) stack))
    (certificate : List Bool)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))))) elapsed)
    (hruntime : elapsed ≤
      (guessTimePolynomial bound machine).eval x.length) :
    machine.tm.step
      (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time)))) =
      some (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace time.succ))) := by
  let first := decodeCorrectedPhaseRow machine
    (trace (Fin.castSucc time))
  let next := decodeCorrectedPhaseRow machine
    (trace time.succ)
  have hfirstTyped := stackSoundValidTrace_all_verifier_rows_wellTyped
    bound machine x trace htrace (Fin.castSucc time) hfirst
  have hnextTyped := stackSoundValidTrace_all_verifier_rows_wellTyped
    bound machine x trace htrace time.succ hnext
  have hwindows := stackSoundValidTrace_occupied_verification_windows
    bound machine x trace htrace time hfirst hnext
  obtain ⟨control, _, hcontrol, _⟩ :=
    allCorrectedVerifierWindows_controls machine
      (rowWidth bound machine x) first next hwindows
  apply allCorrectedVerifierWindows_actual_fullPackedStep
    machine (rowWidth bound machine x) first next
    hfirstTyped hnextTyped
  · intro position
    have mask := stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time)
      position (by rw [hfirst position]; exact PhaseTag.noConfusion)
    simp only [AnchoredPhaseMasks, decide_eq_true_eq] at mask
    exact mask.2.2.2
  · exact hholes
  · intro stack
    exact fullPackedCompact_space_of_actualTimedRun
      bound machine x certificate first hfirstTyped
      control hcontrol run hruntime stack
  · exact hwindows

private theorem stackSoundValidTrace_allInitializationWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .guessing)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)))
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) position) := by
  intro position
  apply stackSoundPhase_initialization_of_modes machine
    (anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)))
      (decodeCorrectedPhaseRow machine (trace time.succ)) position)
  · exact stackSoundValidTrace_window
      bound machine x trace htrace (windowAt time position)
  · exact hfirst position
  · exact hnext position

private theorem stackSoundValidTrace_initialization_rangeFaithful
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .guessing)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    PhaseRowStackRangeFaithful machine
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine (trace time.succ)) := by
  apply allInitializationWindows_next_stackRangeFaithful
    machine (rowWidth bound machine x)
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ))
  · intro position
    have mask := stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time)
      position (by rw [hfirst position]; exact PhaseTag.noConfusion)
    simp only [AnchoredPhaseMasks, decide_eq_true_eq] at mask
    exact mask.1
  · exact stackSoundValidTrace_allInitializationWindows
      bound machine x trace htrace time hfirst hnext

private noncomputable def stackSoundValidTrace_verifierSuccessor_reachable_space_padding
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))) stack))
    (certificate : List Bool)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))))) elapsed)
    (hruntime : elapsed + 1 ≤
      (guessTimePolynomial bound machine).eval x.length) :
    { _nextRun : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace time.succ)))) (elapsed + 1) //
      (∀ stack : machine.tm.K,
        (decodedFullPackedPhaseStack machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) stack).length ≤
          rowWidth bound machine x) ∧
      PhaseRowStackRangeFaithful machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine (trace time.succ)) ∧
      (∀ stack : machine.tm.K,
        NoInteriorPaddingHoles machine.tm
          (fullPackedPhaseStackAtoms machine
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace time.succ)) stack))  } := by
  let first := decodeCorrectedPhaseRow machine
    (trace (Fin.castSucc time))
  let next := decodeCorrectedPhaseRow machine
    (trace time.succ)
  have hsourceTime : elapsed ≤
      (guessTimePolynomial bound machine).eval x.length := by
    omega
  have hstep :=
    stackSoundValidTrace_actualFullPackedStep_of_actualTimedRun
      bound machine x trace htrace time hfirst hnext
      hholes certificate run hsourceTime
  let nextRun : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x) next)) (elapsed + 1) :=
    FiniteRun.tail run
      (GuessStep.execute certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x) first)
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x) next) hstep)
  have hfirstTyped := stackSoundValidTrace_all_verifier_rows_wellTyped
    bound machine x trace htrace (Fin.castSucc time) hfirst
  have hnextTyped := stackSoundValidTrace_all_verifier_rows_wellTyped
    bound machine x trace htrace time.succ hnext
  have hwindows := stackSoundValidTrace_occupied_verification_windows
    bound machine x trace htrace time hfirst hnext
  have hcontrolsExists := allCorrectedVerifierWindows_controls machine
    (rowWidth bound machine x) first next hwindows
  let firstControl := Classical.choose hcontrolsExists
  let nextControl := Classical.choose (Classical.choose_spec hcontrolsExists)
  have hcontrols := Classical.choose_spec (Classical.choose_spec hcontrolsExists)
  have hfirstControl : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (first 0)) = some firstControl :=
    hcontrols.1
  have hnextControl : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (next 0)) = some nextControl :=
    hcontrols.2
  have hsourceCompact : ∀ stack : machine.tm.K,
      ((fullPackedPhaseStackAtoms machine
        (rowWidth bound machine x) first stack).filter
          Option.isSome).length ≤ rowWidth bound machine x := by
    intro stack
    exact fullPackedCompact_space_of_actualTimedRun
      bound machine x certificate first hfirstTyped firstControl
      hfirstControl run hsourceTime stack
  have hnextHoles : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x) next stack) := by
    exact stackSoundValidTrace_preserves_fullPacked_noHoles
      bound machine x trace htrace time hfirst hnext
      hholes hsourceCompact
  have hnextSpace : ∀ stack : machine.tm.K,
      (decodedFullPackedPhaseStack machine
        (rowWidth bound machine x) next stack).length ≤
          rowWidth bound machine x := by
    intro stack
    exact fullPackedStack_space_of_actualTimedRun
      bound machine x certificate next nextControl
      hnextControl nextRun hruntime stack
  have hnextRange : PhaseRowStackRangeFaithful machine
      (rowWidth bound machine x) next := by
    apply fullPacked_noHoles_and_bound_implies_stackRangeFaithful
      machine (rowWidth bound machine x) next hnextHoles
    intro stack
    rw [fullPackedPhaseStackAtoms_compact_length
      machine (rowWidth bound machine x) next hnextTyped stack]
    exact hnextSpace stack
  exact ⟨nextRun, hnextSpace, hnextRange, hnextHoles⟩

end CLFullTraceReachability

namespace CLGuessPayloadReachability

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactLocalRules GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness GapCVP.CLWholeTraceSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLAnchoredTraceSimulation

private theorem pairedInputTagAt_append_before
    (x certificate : List Bool) (bit : Bool) (index : ℕ)
    (hindex : index < x.length + certificate.length) :
    pairedInputTagAt x (certificate ++ [bit]) index =
      pairedInputTagAt x certificate index := by
  have hword : index < (pairBitEncoding (x, certificate)).length := by
    simpa only [pairBitEncoding_apply, List.length_append, List.length_map] using hindex
  unfold pairedInputTagAt
  rw [pairBitEncoding_append_guess,
    List.getElem?_append_left hword]
  split <;> rename_i hentry
  · rfl
  · have houtside := List.getElem?_eq_none_iff.mp hentry
    omega

private theorem pairedInputTagAt_append_old_marker
    (x certificate : List Bool) (bit : Bool) :
    pairedInputTagAt x (certificate ++ [bit])
      (x.length + certificate.length) = .bit (.inr bit) := by
  unfold pairedInputTagAt
  rw [pairBitEncoding_append_guess]
  have hindex :
      (pairBitEncoding (x, certificate)).length ≤
        x.length + certificate.length := by
    simp only [pairBitEncoding_apply, List.length_append, List.length_map, Std.le_refl]
  rw [List.getElem?_append_right hindex]
  simp only [pairBitEncoding_apply, List.length_append, List.length_map, tsub_self,
      List.length_cons,
      List.length_nil, zero_add, Order.lt_one_iff, getElem?_pos, List.getElem_cons_zero]

private theorem pairedInputTagAt_append_new_marker
    (x certificate : List Bool) (bit : Bool) :
    pairedInputTagAt x (certificate ++ [bit])
      (x.length + certificate.length + 1) = .marker := by
  simpa only [Nat.add_assoc, List.length_append, List.length_cons, List.length_nil, zero_add] using
      pairedInputTagAt_marker x (certificate ++ [bit])

private theorem pairedInputTagAt_append_after
    (x certificate : List Bool) (bit : Bool) (index : ℕ)
    (hindex : x.length + certificate.length + 1 < index) :
    pairedInputTagAt x (certificate ++ [bit]) index =
      pairedInputTagAt x certificate index := by
  have hold : (pairBitEncoding (x, certificate)).length < index := by
    simp only [pairBitEncoding_length]
    omega
  have hnew :
      (pairBitEncoding (x, certificate ++ [bit])).length < index := by
    simp only [pairBitEncoding_length, List.length_append,
      List.length_singleton]
    omega
  unfold pairedInputTagAt
  rw [List.getElem?_eq_none (Nat.le_of_lt hnew),
    List.getElem?_eq_none (Nat.le_of_lt hold)]
  have hneOld : index ≠ x.length + certificate.length := by
    omega
  have hneNew : index ≠ x.length + (certificate.length + 1) := by
    omega
  simp only [pairBitEncoding_apply, List.map_append, List.map_cons, List.map_nil,
      List.length_append,
      List.length_map, List.length_cons, List.length_nil, zero_add, hneNew, ↓reduceIte, hneOld]

private theorem pairedInputTagAt_marker_iff
    (x certificate : List Bool) (index : ℕ) :
    pairedInputTagAt x certificate index = .marker ↔
      index = x.length + certificate.length := by
  unfold pairedInputTagAt
  split <;> rename_i hentry
  · obtain ⟨hinside, _⟩ := List.getElem?_eq_some_iff.mp hentry
    have hlength :
        (pairBitEncoding (x, certificate)).length =
          x.length + certificate.length := by
      simp only [pairBitEncoding_apply, List.length_append, List.length_map]
    simp only [reduceCtorEq, false_iff, ne_eq]
    omega
  · simp only [pairBitEncoding_apply, List.length_append, List.length_map, ite_eq_left_iff,
      reduceCtorEq,
        imp_false, Decidable.not_not]

private theorem pairedInputTagAt_blank_after
    (x certificate : List Bool) (index : ℕ)
    (hindex : x.length + certificate.length < index) :
    pairedInputTagAt x certificate index = .blank := by
  have houtside :
      (pairBitEncoding (x, certificate)).length ≤ index := by
    simpa only [pairBitEncoding_apply, List.length_append, List.length_map] using (Nat.le_of_lt
        hindex)
  unfold pairedInputTagAt
  rw [List.getElem?_eq_none houtside]
  have hne : index ≠ x.length + certificate.length := by
    omega
  simp only [pairBitEncoding_apply, List.length_append, List.length_map, hne, ↓reduceIte]

private theorem pairedInputGuessAllowed_canonical_next
    (x certificate : List Bool) (bit : Bool) (index : ℕ)
    (left right next : PairedInputTag)
    (hleft : left = pairedInputTagAt x certificate (index - 1))
    (hallowed : PairedInputGuessAllowed bit
      (left, pairedInputTagAt x certificate index, right, next)) :
    next = pairedInputTagAt x (certificate ++ [bit]) index := by
  simp only [PairedInputGuessAllowed, decide_eq_true_eq] at hallowed
  rcases hallowed with hwrite | hmarker | hunchanged
  · have hindex : index = x.length + certificate.length :=
      (pairedInputTagAt_marker_iff x certificate index).mp hwrite.1
    subst index
    exact hwrite.2.2.trans
      (pairedInputTagAt_append_old_marker x certificate bit).symm
  · have hleftMarker :
        pairedInputTagAt x certificate (index - 1) = .marker := by
      rw [← hleft]
      exact hmarker.2.1
    have hpredecessor :
        index - 1 = x.length + certificate.length :=
      (pairedInputTagAt_marker_iff
        x certificate (index - 1)).mp hleftMarker
    have hnotMarker : index ≠ x.length + certificate.length := by
      intro heq
      exact hmarker.1
        ((pairedInputTagAt_marker_iff
          x certificate index).mpr heq)
    have hindex : index = x.length + certificate.length + 1 := by
      omega
    subst index
    exact hmarker.2.2.trans
      (pairedInputTagAt_append_new_marker x certificate bit).symm
  · have hnotMarker : index ≠ x.length + certificate.length := by
      intro heq
      exact hunchanged.1
        ((pairedInputTagAt_marker_iff
          x certificate index).mpr heq)
    have hnotPrevious :
        index - 1 ≠ x.length + certificate.length := by
      intro heq
      apply hunchanged.2.1
      rw [hleft]
      exact (pairedInputTagAt_marker_iff
        x certificate (index - 1)).mpr heq
    by_cases hbefore : index < x.length + certificate.length
    · exact hunchanged.2.2.trans
        (pairedInputTagAt_append_before
          x certificate bit index hbefore).symm
    · have hafter : x.length + certificate.length + 1 < index := by
        omega
      exact hunchanged.2.2.trans
        (pairedInputTagAt_append_after
          x certificate bit index hafter).symm

private theorem broadcastWitnessGuessAllowed_canonical_next
    (certificate : List Bool) (bit : Bool) (index : ℕ)
    (left right next : PhaseTag)
    (hleft : left = certificatePhase certificate (index - 1))
    (hallowed : BroadcastWitnessGuessAllowed bit
      (left, certificatePhase certificate index, right, next)) :
    next = certificatePhase (certificate ++ [bit]) index := by
  simp only [BroadcastWitnessGuessAllowed, GuessPhaseAllowed, decide_eq_true_eq]
    at hallowed
  rcases hallowed.1 with hwrite | hmarker | hunchanged
  · have hindex : index = certificate.length :=
      (certificatePhase_accepting_iff certificate index).mp hwrite.1
    have hnext :
        next = if bit then PhaseTag.verifying else PhaseTag.guessing :=
      hallowed.2 hwrite.1
    subst index
    exact hnext.trans
      (certificatePhase_append_old_marker certificate bit).symm
  · have hleftMarker :
        certificatePhase certificate (index - 1) = .accepting := by
      rw [← hleft]
      exact hmarker.2.1
    have hpredecessor : index - 1 = certificate.length :=
      (certificatePhase_accepting_iff
        certificate (index - 1)).mp hleftMarker
    have hnotMarker : index ≠ certificate.length := by
      intro heq
      exact hmarker.1
        ((certificatePhase_accepting_iff certificate index).mpr heq)
    have hindex : index = certificate.length + 1 := by
      omega
    subst index
    exact hmarker.2.2.trans
      (certificatePhase_append_new_marker certificate bit).symm
  · have hnotMarker : index ≠ certificate.length := by
      intro heq
      exact hunchanged.1
        ((certificatePhase_accepting_iff certificate index).mpr heq)
    have hnotPrevious : index - 1 ≠ certificate.length := by
      intro heq
      apply hunchanged.2.1
      rw [hleft]
      exact (certificatePhase_accepting_iff
        certificate (index - 1)).mpr heq
    by_cases hbefore : index < certificate.length
    · exact hunchanged.2.2.trans
        (certificatePhase_append_before
          certificate bit index hbefore).symm
    · have hafter : certificate.length + 1 < index := by
        omega
      exact hunchanged.2.2.trans
        (certificatePhase_append_after
          certificate bit index hafter).symm

private theorem pairedInputGuessAllowed_of_append
    (x certificate : List Bool) (bit : Bool) (index : ℕ) :
    PairedInputGuessAllowed bit
      (pairedInputTagAt x certificate (index - 1),
       pairedInputTagAt x certificate index,
       pairedInputTagAt x certificate (index + 1),
       pairedInputTagAt x (certificate ++ [bit]) index) := by
  simp only [PairedInputGuessAllowed, decide_eq_true_eq]
  by_cases hmarker : index = x.length + certificate.length
  · subst index
    refine Or.inl ⟨pairedInputTagAt_marker x certificate, ?_,
      pairedInputTagAt_append_old_marker x certificate bit⟩
    exact pairedInputTagAt_blank_after x certificate _ (by omega)
  · by_cases hnextMarker : index = x.length + certificate.length + 1
    · subst index
      refine Or.inr (Or.inl ⟨?_, ?_,
        pairedInputTagAt_append_new_marker x certificate bit⟩)
      · intro hfalse
        have heq := (pairedInputTagAt_marker_iff
          x certificate (x.length + certificate.length + 1)).mp hfalse
        omega
      · have hpred :
            x.length + certificate.length + 1 - 1 =
              x.length + certificate.length := by
          omega
        rw [hpred]
        exact pairedInputTagAt_marker x certificate
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · intro hfalse
        exact hmarker
          ((pairedInputTagAt_marker_iff
            x certificate index).mp hfalse)
      · intro hfalse
        have hpred := (pairedInputTagAt_marker_iff
          x certificate (index - 1)).mp hfalse
        omega
      · by_cases hbefore : index < x.length + certificate.length
        · exact pairedInputTagAt_append_before
            x certificate bit index hbefore
        · have hafter : x.length + certificate.length + 1 < index := by
            omega
          exact pairedInputTagAt_append_after
            x certificate bit index hafter

private theorem pairedCertificateBound_le_rowWidth
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    x.length + bound.eval x.length ≤ rowWidth bound machine x := by
  simp only [rowWidth, nondeterministicTableauDimensionPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  omega

private theorem phaseLeftOffset_coordinate
    {α : Type}
    (tm : Turing.FinTM2)
    (width : ℕ)
    (track : Position width → Fin (blockSize tm) → α)
    (index : Position width) :
    phaseLeftOffset tm
      (decide ((coordinateBlock tm width index).val = 0))
      (track (leftBlock width (coordinateBlock tm width index)))
      (track (coordinateBlock tm width index))
      (coordinateOffset tm width index) =
      track (coordinateBlock tm width (leftBlock width index))
        (coordinateOffset tm width (leftBlock width index)) := by
  have hpositive := blockSize_pos tm
  by_cases hzero : index.val = 0
  · have hindex : index = 0 := Fin.ext hzero
    subst index
    simp only [phaseLeftOffset, coordinateOffset, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceDIte,
        coordinateBlock, Nat.zero_div, Fin.zero_eta, decide_true, ↓reduceIte, leftBlock, zero_tsub]
  · have hprevious : index.val - 1 + 1 = index.val := by
      omega
    by_cases hseam : index.val % blockSize tm = 0
    · have hdivision :
          index.val / blockSize tm =
            (index.val - 1) / blockSize tm + 1 := by
        have hz :
            (index.val - 1 + 1) % blockSize tm = 0 := by
          simpa only [hprevious] using hseam
        simpa only [hprevious] using (Nat.succ_div_of_mod_eq_zero hz)
      have hblockPositive : 0 < index.val / blockSize tm := by
        rw [hdivision]
        exact Nat.zero_lt_succ _
      have hdivisible :
          blockSize tm ∣ index.val - 1 + 1 :=
        Nat.dvd_of_mod_eq_zero (by
          simpa only [hprevious] using hseam)
      have hpreviousMod :
          (index.val - 1) % blockSize tm = blockSize tm - 1 := by
        apply (Nat.mod_eq_sub_iff Nat.zero_lt_one (by omega)).mpr
        exact hdivisible
      have hleftBlock :
          leftBlock width (coordinateBlock tm width index) =
            coordinateBlock tm width (leftBlock width index) := by
        apply Fin.ext
        change index.val / blockSize tm - 1 =
          (index.val - 1) / blockSize tm
        omega
      have hleftOffset :
          lastPhaseOffset tm =
            coordinateOffset tm width (leftBlock width index) := by
        apply Fin.ext
        change blockSize tm - 1 =
          (index.val - 1) % blockSize tm
        omega
      have hoffset :
          (coordinateOffset tm width index).val = 0 := hseam
      have hfirst :
          decide ((coordinateBlock tm width index).val = 0) = false := by
        simp only [coordinateBlock, Nat.ne_of_gt hblockPositive, decide_false]
      have hleft :
          phaseLeftOffset tm
            (decide ((coordinateBlock tm width index).val = 0))
            (track (leftBlock width (coordinateBlock tm width index)))
            (track (coordinateBlock tm width index))
            (coordinateOffset tm width index) =
          track (leftBlock width (coordinateBlock tm width index))
            (lastPhaseOffset tm) := by
        rw [hfirst]
        simp only [phaseLeftOffset, hoffset, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      rw [hleft, hleftBlock, hleftOffset]
    · have hdivision :
          index.val / blockSize tm =
            (index.val - 1) / blockSize tm := by
        have hnonzero :
            (index.val - 1 + 1) % blockSize tm ≠ 0 := by
          simpa only [hprevious, ne_eq] using hseam
        simpa only [hprevious] using (Nat.succ_div_of_mod_ne_zero hnonzero)
      have hpreviousMod :
          (index.val - 1) % blockSize tm =
            index.val % blockSize tm - 1 := by
        rw [Nat.mod_eq_sub_div_mul, Nat.mod_eq_sub_div_mul,
          ← hdivision]
        omega
      have hsameBlock :
          coordinateBlock tm width index =
            coordinateBlock tm width (leftBlock width index) := by
        apply Fin.ext
        exact hdivision
      let predecessorOffset : Fin (blockSize tm) :=
        ⟨(coordinateOffset tm width index).val - 1, by
          have hlt := (coordinateOffset tm width index).isLt
          omega⟩
      have hsameOffset :
          predecessorOffset =
            coordinateOffset tm width (leftBlock width index) := by
        apply Fin.ext
        change index.val % blockSize tm - 1 =
          (index.val - 1) % blockSize tm
        omega
      have hoffset :
          (coordinateOffset tm width index).val ≠ 0 := hseam
      have hleft :
          phaseLeftOffset tm
            (decide ((coordinateBlock tm width index).val = 0))
            (track (leftBlock width (coordinateBlock tm width index)))
            (track (coordinateBlock tm width index))
            (coordinateOffset tm width index) =
            track (coordinateBlock tm width index)
              predecessorOffset := by
        simp only [phaseLeftOffset, hoffset, ↓reduceDIte, predecessorOffset]
      rw [hleft, hsameBlock, hsameOffset]

private theorem phaseRangeBlockAt_coordinate
    (tm : Turing.FinTM2)
    (width : ℕ)
    (index : Position width) :
    phaseRangeBlockAt tm width
      (coordinateBlock tm width index)
      (coordinateOffset tm width index) = true := by
  change decide
    (index.val / blockSize tm * blockSize tm +
      index.val % blockSize tm < width + 1) = true
  rw [Nat.div_add_mod']
  exact decide_eq_true index.isLt

private theorem phaseBudgetBlockAt_coordinate
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (index : Position (rowWidth bound machine x)) :
    phaseBudgetBlockAt bound machine x
      (coordinateBlock machine.tm (rowWidth bound machine x) index)
      (coordinateOffset machine.tm (rowWidth bound machine x) index) =
      decide (index.val < x.length + bound.eval x.length) := by
  change decide
    (index.val / blockSize machine.tm * blockSize machine.tm +
      index.val % blockSize machine.tm <
        x.length + bound.eval x.length) = _
  rw [Nat.div_add_mod']

private theorem completeWitnessWindow_left_unpacked
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell tm)
    (index : Position width)
    (hboundary : completeIsFirstBlock tm
      (first (coordinateBlock tm width index)) =
        decide ((coordinateBlock tm width index).val = 0)) :
    (completeWitnessWindow tm
      (anchoredVerifierWindowAt tm width first next
        (coordinateBlock tm width index))
      (coordinateOffset tm width index)).1 =
      unpackPhaseWitness tm width first (leftBlock width index) := by
  change
    phaseLeftOffset tm
      (completeIsFirstBlock tm
        (first (coordinateBlock tm width index)))
      (fun offset =>
        (completeMachineBlock tm
          (first (leftBlock width
            (coordinateBlock tm width index))) offset).1)
      (fun offset =>
        (completeMachineBlock tm
          (first (coordinateBlock tm width index)) offset).1)
      (coordinateOffset tm width index) =
      (completeMachineBlock tm
        (first (coordinateBlock tm width (leftBlock width index)))
        (coordinateOffset tm width (leftBlock width index))).1
  rw [hboundary]
  exact phaseLeftOffset_coordinate tm width
    (fun position offset =>
      (completeMachineBlock tm (first position) offset).1) index

private theorem completePayloadWindow_left_unpacked
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell tm)
    (index : Position width)
    (hboundary : completeIsFirstBlock tm
      (first (coordinateBlock tm width index)) =
        decide ((coordinateBlock tm width index).val = 0)) :
    (completePayloadWindow tm
      (anchoredVerifierWindowAt tm width first next
        (coordinateBlock tm width index))
      (coordinateOffset tm width index)).1 =
      unpackPhasePayload tm width first (leftBlock width index) := by
  change
    phaseLeftOffset tm
      (completeIsFirstBlock tm
        (first (coordinateBlock tm width index)))
      (first (leftBlock width
        (coordinateBlock tm width index))).payload
      (first (coordinateBlock tm width index)).payload
      (coordinateOffset tm width index) =
      (first (coordinateBlock tm width (leftBlock width index))).payload
        (coordinateOffset tm width (leftBlock width index))
  rw [hboundary]
  exact phaseLeftOffset_coordinate tm width
    (fun position => (first position).payload) index

private structure CanonicalGuessingTracks
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (row : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm) where
  certificate : List Bool
  certificate_le : certificate.length ≤ bound.eval x.length
  mode : ∀ position : Position (rowWidth bound machine x),
    (row position).mode = .guessing
  witness : ∀ index : Position (rowWidth bound machine x),
    unpackPhaseWitness machine.tm (rowWidth bound machine x) row index =
      certificatePhase certificate index.val
  payload : ∀ index : Position (rowWidth bound machine x),
    unpackPhasePayload machine.tm (rowWidth bound machine x) row index =
      pairedInputTagAt x certificate index.val

private theorem unpackPhaseWitness_initialPhaseCell
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (index : Position (rowWidth bound machine x)) :
    unpackPhaseWitness machine.tm (rowWidth bound machine x)
      (initialPhaseCell bound machine x) index =
        certificatePhase [] index.val := by
  change
    (packRow machine.tm (rowWidth bound machine x)
      (guessingRow machine.tm (rowWidth bound machine x) [])
      (coordinateBlock machine.tm (rowWidth bound machine x) index)
      (coordinateOffset machine.tm (rowWidth bound machine x) index)).1 =
      certificatePhase [] index.val
  rw [packRow_cell]
  rfl

private theorem unpackPhasePayload_initialPhaseCell
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (index : Position (rowWidth bound machine x)) :
    unpackPhasePayload machine.tm (rowWidth bound machine x)
      (initialPhaseCell bound machine x) index =
        pairedInputTagAt x [] index.val := by
  have hcoordinate :
      index.val / blockSize machine.tm * blockSize machine.tm +
        index.val % blockSize machine.tm = index.val :=
    Nat.div_add_mod' index.val (blockSize machine.tm)
  simp only [unpackPhasePayload, initialPhaseCell, coordinateBlock, coordinateOffset,
      pairedInputBlockAt,
      hcoordinate, Order.lt_add_one_iff, ite_eq_left_iff, not_le]
  omega

private def initialCanonicalGuessingTracks
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    CanonicalGuessingTracks bound machine x
      (initialPhaseCell bound machine x) where
  certificate := []
  certificate_le := Nat.zero_le _
  mode := fun _ => rfl
  witness := unpackPhaseWitness_initialPhaseCell bound machine x
  payload := unpackPhasePayload_initialPhaseCell bound machine x

private theorem correctedGuessingWindows_certificate_lt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      CorrectedGuessingAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    hfirst.certificate.length < bound.eval x.length := by
  have hmarkerWidth :
      x.length + hfirst.certificate.length ≤ rowWidth bound machine x :=
    (Nat.add_le_add_left hfirst.certificate_le x.length).trans
      (pairedCertificateBound_le_rowWidth bound machine x)
  let marker : Position (rowWidth bound machine x) :=
    ⟨x.length + hfirst.certificate.length,
      Nat.lt_succ_of_le hmarkerWidth⟩
  let block := coordinateBlock machine.tm
    (rowWidth bound machine x) marker
  let offset := coordinateOffset machine.tm
    (rowWidth bound machine x) marker
  have mask := hmasks block
  simp only [AnchoredPhaseMasks, decide_eq_true_eq] at mask
  have guess := hwindows block
  simp only [CorrectedGuessingAllowed, decide_eq_true_eq] at guess
  have hrange : (first block).range offset = true := by
    rw [mask.1]
    exact phaseRangeBlockAt_coordinate machine.tm
      (rowWidth bound machine x) marker
  have hmarker : (first block).payload offset = .marker := by
    change unpackPhasePayload machine.tm
      (rowWidth bound machine x) first marker = .marker
    rw [hfirst.payload marker]
    exact pairedInputTagAt_marker x hfirst.certificate
  have hbudget : (first block).budget offset = true :=
    (guess.2.2.2.2 offset hrange).2.2 hmarker
  rw [mask.2.2.1] at hbudget
  change phaseBudgetBlockAt bound machine x
    (coordinateBlock machine.tm (rowWidth bound machine x) marker)
    (coordinateOffset machine.tm (rowWidth bound machine x) marker) =
      true at hbudget
  rw [phaseBudgetBlockAt_coordinate] at hbudget
  have hbudgetLt : marker.val < x.length + bound.eval x.length :=
    of_decide_eq_true hbudget
  change x.length + hfirst.certificate.length <
    x.length + bound.eval x.length at hbudgetLt
  omega

private def correctedGuessingWindows_nextCanonical
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (bit : Bool)
    (hbit : ∀ position : Position (rowWidth bound machine x),
      (next position).guessBit = bit)
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      CorrectedGuessingAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    CanonicalGuessingTracks bound machine x next := by
  let certificate := hfirst.certificate
  have hcertificate : certificate.length < bound.eval x.length :=
    correctedGuessingWindows_certificate_lt
      bound machine x first next hfirst hmasks hwindows
  refine {
    certificate := certificate ++ [bit]
    certificate_le := ?_
    mode := ?_
    witness := ?_
    payload := ?_
  }
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro position
    have guess := hwindows position
    simp only [CorrectedGuessingAllowed, decide_eq_true_eq] at guess
    exact guess.1
  · intro index
    let block := coordinateBlock machine.tm
      (rowWidth bound machine x) index
    let offset := coordinateOffset machine.tm
      (rowWidth bound machine x) index
    let window := anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x) first next block
    have mask := hmasks block
    simp only [AnchoredPhaseMasks, decide_eq_true_eq] at mask
    have guess := hwindows block
    simp only [CorrectedGuessingAllowed, decide_eq_true_eq] at guess
    have hrange : (first block).range offset = true := by
      rw [mask.1]
      exact phaseRangeBlockAt_coordinate machine.tm
        (rowWidth bound machine x) index
    have hallowed : BroadcastWitnessGuessAllowed
        ((next block).guessBit)
        (completeWitnessWindow machine.tm window offset) :=
      (guess.2.2.2.2 offset hrange).1
    rw [hbit block] at hallowed
    have hleft :
        (completeWitnessWindow machine.tm window offset).1 =
          certificatePhase certificate (index.val - 1) := by
      calc
        (completeWitnessWindow machine.tm window offset).1 =
            unpackPhaseWitness machine.tm
              (rowWidth bound machine x) first
              (leftBlock (rowWidth bound machine x) index) :=
          completeWitnessWindow_left_unpacked machine.tm
            (rowWidth bound machine x) first next index
            mask.2.2.2
        _ = certificatePhase hfirst.certificate
              (leftBlock (rowWidth bound machine x) index).val :=
          hfirst.witness _
        _ = certificatePhase certificate (index.val - 1) := rfl
    have hcenter :
        (completeWitnessWindow machine.tm window offset).2.1 =
          certificatePhase certificate index.val := by
      exact hfirst.witness index
    change BroadcastWitnessGuessAllowed bit
      ((completeWitnessWindow machine.tm window offset).1,
       (completeWitnessWindow machine.tm window offset).2.1,
       (completeWitnessWindow machine.tm window offset).2.2.1,
       (completeWitnessWindow machine.tm window offset).2.2.2)
      at hallowed
    rw [hcenter] at hallowed
    exact broadcastWitnessGuessAllowed_canonical_next
      certificate bit index.val
      (completeWitnessWindow machine.tm window offset).1
      (completeWitnessWindow machine.tm window offset).2.2.1
      (completeWitnessWindow machine.tm window offset).2.2.2
      hleft hallowed
  · intro index
    let block := coordinateBlock machine.tm
      (rowWidth bound machine x) index
    let offset := coordinateOffset machine.tm
      (rowWidth bound machine x) index
    let window := anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x) first next block
    have mask := hmasks block
    simp only [AnchoredPhaseMasks, decide_eq_true_eq] at mask
    have guess := hwindows block
    simp only [CorrectedGuessingAllowed, decide_eq_true_eq] at guess
    have hrange : (first block).range offset = true := by
      rw [mask.1]
      exact phaseRangeBlockAt_coordinate machine.tm
        (rowWidth bound machine x) index
    have hallowed : PairedInputGuessAllowed
        ((next block).guessBit)
        (completePayloadWindow machine.tm window offset) :=
      (guess.2.2.2.2 offset hrange).2.1
    rw [hbit block] at hallowed
    have hleft :
        (completePayloadWindow machine.tm window offset).1 =
          pairedInputTagAt x certificate (index.val - 1) := by
      calc
        (completePayloadWindow machine.tm window offset).1 =
            unpackPhasePayload machine.tm
              (rowWidth bound machine x) first
              (leftBlock (rowWidth bound machine x) index) :=
          completePayloadWindow_left_unpacked machine.tm
            (rowWidth bound machine x) first next index
            mask.2.2.2
        _ = pairedInputTagAt x hfirst.certificate
              (leftBlock (rowWidth bound machine x) index).val :=
          hfirst.payload _
        _ = pairedInputTagAt x certificate (index.val - 1) := rfl
    have hcenter :
        (completePayloadWindow machine.tm window offset).2.1 =
          pairedInputTagAt x certificate index.val := by
      exact hfirst.payload index
    change PairedInputGuessAllowed bit
      ((completePayloadWindow machine.tm window offset).1,
       (completePayloadWindow machine.tm window offset).2.1,
       (completePayloadWindow machine.tm window offset).2.2.1,
       (completePayloadWindow machine.tm window offset).2.2.2)
      at hallowed
    rw [hcenter] at hallowed
    exact pairedInputGuessAllowed_canonical_next
      x certificate bit index.val
      (completePayloadWindow machine.tm window offset).1
      (completePayloadWindow machine.tm window offset).2.2.1
      (completePayloadWindow machine.tm window offset).2.2.2
      hleft hallowed

private theorem stackSoundValidTrace_guessingTime_lt_width
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x))
    (hguess : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time) position).mode = .guessing) :
    time.val < rowWidth bound machine x := by
  have hanchored := stackSoundValidTrace_to_anchored
    bound machine x trace htrace
  obtain ⟨position, haccept⟩ :=
    anchoredValidTrace_has_acceptingCell
      bound machine x trace hanchored
  by_contra hnot
  have hlastVal : time.val = rowWidth bound machine x := by
    have hlt := time.isLt
    omega
  have hlast : time = Fin.last (rowWidth bound machine x) := by
    apply Fin.ext
    exact hlastVal
  have himpossible := hguess position
  rw [hlast, haccept] at himpossible
  cases himpossible

private theorem stackSoundValidTrace_guessingSuccessor_bit_constant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .guessing) :
    ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).guessBit =
      (decodeCorrectedPhaseRow machine
        (trace time.succ) 0).guessBit := by
  have hnextTime := stackSoundValidTrace_guessingTime_lt_width
    bound machine x trace htrace time.succ hnext
  let following : Fin (rowWidth bound machine x) :=
    ⟨time.succ.val, hnextTime⟩
  have hrow : trace (Fin.castSucc following) = trace time.succ := by
    apply congrArg trace
    apply Fin.ext
    rfl
  intro position
  have hconstant := anchoredValidTrace_guessBit_constant
    bound machine x trace
    (stackSoundValidTrace_to_anchored bound machine x trace htrace)
    following position
  calc
    (decodeCorrectedPhaseRow machine
      (trace time.succ) position).guessBit =
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc following)) position).guessBit :=
      (congrArg (fun row =>
        (decodeCorrectedPhaseRow machine row position).guessBit)
        hrow).symm
    _ = (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc following)) 0).guessBit := hconstant
    _ = (decodeCorrectedPhaseRow machine
          (trace time.succ) 0).guessBit :=
      congrArg (fun row =>
        (decodeCorrectedPhaseRow machine row 0).guessBit) hrow

private theorem stackSoundValidTrace_allGuessingWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .guessing)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .guessing) :
    ∀ position : Position (rowWidth bound machine x),
      CorrectedGuessingAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)))
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) position) := by
  intro position
  let window := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x)
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine
      (trace time.succ)) position
  have hallowed := stackSoundValidTrace_window
    bound machine x trace htrace (windowAt time position)
  change StackSoundAnchoredPhaseAllowed machine window at hallowed
  simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq] at hallowed
  have hbranches :
      AnchoredGuessingAllowed machine window ∨
        AnchoredInitializationAllowed machine window := by
    have hbranch := hallowed.2
    change
      match (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode with
      | .guessing =>
          AnchoredGuessingAllowed machine window ∨
            AnchoredInitializationAllowed machine window
      | .verifying =>
          StackSoundAnchoredVerificationAllowed machine window ∨
            AnchoredAcceptanceAllowed machine window
      | .accepting =>
          window.2.2.2 = acceptingPhaseCell machine.tm
      at hbranch
    simpa only [hfirst position] using hbranch
  rcases hbranches with hguess | hinitial
  · simp only [AnchoredGuessingAllowed, decide_eq_true_eq] at hguess
    exact hguess.1
  · simp only [AnchoredInitializationAllowed, CompleteInitializationAllowed,
      decide_eq_true_eq] at hinitial
    have hinitialOuter := ofClassicalDecide hinitial
    have hinitialCore := ofClassicalDecide hinitialOuter.1
    have himpossible := hinitialCore.1
    change
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying at himpossible
    rw [hnext position] at himpossible
    cases himpossible

private def stackSoundValidTrace_guessingSuccessorCanonical
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .guessing) :
    CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine (trace time.succ)) := by
  apply correctedGuessingWindows_nextCanonical
    bound machine x
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ))
    hfirst
    (fun position => stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time) position
      (by rw [hfirst.mode position]; exact PhaseTag.noConfusion))
    ((decodeCorrectedPhaseRow machine
      (trace time.succ) 0).guessBit)
  · exact stackSoundValidTrace_guessingSuccessor_bit_constant
      bound machine x trace htrace time hnext
  · exact stackSoundValidTrace_allGuessingWindows
      bound machine x trace htrace time hfirst.mode hnext

private noncomputable def stackSoundValidTrace_guessingSuccessor_actualStep
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .guessing) :
    GuessStep bound machine x
      (.guessing hfirst.certificate)
      (.guessing
        (stackSoundValidTrace_guessingSuccessorCanonical
          bound machine x trace htrace time hfirst hnext).certificate) := by
  have hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time)) position) := by
    intro position
    exact stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time) position
      (by rw [hfirst.mode position]; exact PhaseTag.noConfusion)
  have hwindows := stackSoundValidTrace_allGuessingWindows
    bound machine x trace htrace time hfirst.mode hnext
  have hbound := correctedGuessingWindows_certificate_lt
    bound machine x
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ))
    hfirst hmasks hwindows
  exact GuessStep.guess hfirst.certificate
    ((decodeCorrectedPhaseRow machine
      (trace time.succ) 0).guessBit) hbound

end CLGuessPayloadReachability

namespace CLReachableTableauCompiler

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLExactStackRules GapCVP.CLFiniteShiftWindows
open GapCVP.CLLocalTableauCompiler GapCVP.CLGlobalTableauSimulation
open GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSoundness
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLRawTrackSimulation
open GapCVP.CLCompactWindowSoundness GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness GapCVP.CLFullTraceReachability
open GapCVP.CLGuessPayloadReachability

private theorem initialPairedAtom_input_decode
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (bit : Bool ⊕ Bool) :
    cellAtomValue machine machine.tm.k₀
      (initialPairedAtom machine machine.tm.k₀ (.bit bit)) =
      some (machine.inputAlphabet.invFun bit) := by
  simp only [initialPairedAtom, ↓reduceIte, Equiv.invFun_as_coe, canonicalCellAtom_decode]

private theorem initialPairedAtom_private_blank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (hstack : stack ≠ machine.tm.k₀)
    (tag : PairedInputTag) :
    initialPairedAtom machine stack tag = none := by
  cases tag <;> simp [initialPairedAtom, hstack]

private theorem initialPairedAtom_pairedInput_decode
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (index : ℕ) :
    cellAtomValue machine machine.tm.k₀
      (initialPairedAtom machine machine.tm.k₀
        (pairedInputTagAt x certificate index)) =
      (verifierInput machine x certificate)[index]? := by
  change
    cellAtomValue machine machine.tm.k₀
      (initialPairedAtom machine machine.tm.k₀
        (pairedInputTagAt x certificate index)) =
      ((pairBitEncoding (x, certificate)).map
        machine.inputAlphabet.invFun)[index]?
  rw [List.getElem?_map]
  cases hentry : (pairBitEncoding (x, certificate))[index]? with
  | none =>
      simp only [Option.map_none]
      have htag : pairedInputTagAt x certificate index =
          if index = (pairBitEncoding (x, certificate)).length then
            .marker
          else
            .blank := by
        unfold pairedInputTagAt
        rw [hentry]
      rw [htag]
      split <;> rfl
  | some bit =>
      simp only [Option.map_some]
      have htag : pairedInputTagAt x certificate index = .bit bit := by
        unfold pairedInputTagAt
        rw [hentry]
      rw [htag]
      exact initialPairedAtom_input_decode machine bit

private theorem allInitializationWindows_stackAtom
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : Position width → CompletePhaseCell machine.tm)
    (hwindows : ∀ position : Position width,
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm width
          first next position))
    (position : Position width)
    (stack : machine.tm.K)
    (offset : Fin (blockSize machine.tm)) :
    ((completeMachineBlock machine.tm (next position)
      offset).2.2.1 stack) =
      if (first position).range offset then
        initialPairedAtom machine stack
          ((first position).payload offset)
      else
        none := by
  have hwindow := hwindows position
  simp only [AnchoredInitializationAllowed,
    CompleteInitializationAllowed, decide_eq_true_eq] at hwindow
  have hwindowOuter := ofClassicalDecide hwindow
  have hwindowCore := ofClassicalDecide hwindowOuter.1
  have hblock := hwindowCore.2.2.1
  change
    completeMachineBlock machine.tm (next position) =
      initializedPhaseBlock machine
        (completeMachineBlock machine.tm (first position))
        (first position).payload (first position).range at hblock
  rw [hblock]
  cases hrange : (first position).range offset <;>
    simp [initializedPhaseBlock, hrange, blankCell]

private theorem allInitializationWindows_fullPackedStackAtoms
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position))
    (stack : machine.tm.K) :
    fullPackedPhaseStackAtoms machine
      (rowWidth bound machine x) next stack =
      List.ofFn (fun index : Fin
        (packedPhaseCapacity machine.tm (rowWidth bound machine x)) =>
        initialPairedAtom machine stack
          (pairedInputTagAt x hfirst.certificate index.val)) := by
  unfold fullPackedPhaseStackAtoms
  congr 1
  funext index
  let position : Position (rowWidth bound machine x) :=
    ⟨index.val / blockSize machine.tm,
      (Nat.div_lt_iff_lt_mul
        (blockSize_pos machine.tm)).mpr index.isLt⟩
  let offset : Fin (blockSize machine.tm) :=
    ⟨index.val % blockSize machine.tm,
      Nat.mod_lt index.val (blockSize_pos machine.tm)⟩
  have hatom := allInitializationWindows_stackAtom
    machine (rowWidth bound machine x)
    first next hwindows position stack offset
  have hmaskView := hmasks position
  simp only [AnchoredPhaseMasks, decide_eq_true_eq] at hmaskView
  by_cases hrange : index.val < rowWidth bound machine x + 1
  · let original : Position (rowWidth bound machine x) :=
      ⟨index.val, hrange⟩
    have hposition :
        position = coordinateBlock machine.tm
          (rowWidth bound machine x) original := by
      apply Fin.ext
      rfl
    have hoffset :
        offset = coordinateOffset machine.tm
          (rowWidth bound machine x) original := by
      apply Fin.ext
      rfl
    have hmask : (first position).range offset = true := by
      rw [hmaskView.1]
      change decide
        (index.val / blockSize machine.tm * blockSize machine.tm +
          index.val % blockSize machine.tm <
            rowWidth bound machine x + 1) = true
      rw [Nat.div_add_mod']
      exact decide_eq_true hrange
    have hpayload :
        (first position).payload offset =
          pairedInputTagAt x hfirst.certificate index.val := by
      rw [hposition, hoffset]
      exact hfirst.payload original
    change
      ((completeMachineBlock machine.tm (next position)
        offset).2.2.1 stack) =
        initialPairedAtom machine stack
          (pairedInputTagAt x hfirst.certificate index.val)
    rw [hatom, hmask, hpayload]
    rfl
  · have hmask : (first position).range offset = false := by
      rw [hmaskView.1]
      change decide
        (index.val / blockSize machine.tm * blockSize machine.tm +
          index.val % blockSize machine.tm <
            rowWidth bound machine x + 1) = false
      rw [Nat.div_add_mod']
      exact decide_eq_false hrange
    have hcertificateWidth :
        x.length + hfirst.certificate.length ≤
          rowWidth bound machine x :=
      (Nat.add_le_add_left hfirst.certificate_le x.length).trans
        (pairedCertificateBound_le_rowWidth bound machine x)
    have hblank :
        pairedInputTagAt x hfirst.certificate index.val = .blank := by
      apply pairedInputTagAt_blank_after
      omega
    change
      ((completeMachineBlock machine.tm (next position)
        offset).2.2.1 stack) =
        initialPairedAtom machine stack
          (pairedInputTagAt x hfirst.certificate index.val)
    rw [hatom, hmask, hblank]
    rfl

private theorem allInitializationWindows_decodedFullPackedInputStack
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    decodedFullPackedPhaseStack machine
      (rowWidth bound machine x) next machine.tm.k₀ =
      verifierInput machine x hfirst.certificate := by
  unfold decodedFullPackedPhaseStack
  rw [allInitializationWindows_fullPackedStackAtoms
    bound machine x first next hfirst hmasks hwindows machine.tm.k₀]
  rw [← filterMap_ofFn_comp
    (packedPhaseCapacity machine.tm (rowWidth bound machine x))
    (fun index : Fin
      (packedPhaseCapacity machine.tm (rowWidth bound machine x)) =>
      initialPairedAtom machine machine.tm.k₀
        (pairedInputTagAt x hfirst.certificate index.val))
    (cellAtomValue machine machine.tm.k₀)]
  have hpointwise :
      (fun index : Fin
        (packedPhaseCapacity machine.tm (rowWidth bound machine x)) =>
        cellAtomValue machine machine.tm.k₀
          (initialPairedAtom machine machine.tm.k₀
            (pairedInputTagAt x hfirst.certificate index.val))) =
      (fun index : Fin
        (packedPhaseCapacity machine.tm (rowWidth bound machine x)) =>
        (verifierInput machine x hfirst.certificate)[index.val]?) := by
    funext index
    exact initialPairedAtom_pairedInput_decode
      machine x hfirst.certificate index.val
  rw [hpointwise, filterMap_ofFn_getElem]
  apply List.take_of_length_le
  have hcertificateWidth :
      x.length + hfirst.certificate.length ≤
        rowWidth bound machine x :=
    (Nat.add_le_add_left hfirst.certificate_le x.length).trans
      (pairedCertificateBound_le_rowWidth bound machine x)
  have hblock : 1 ≤ blockSize machine.tm := by
    have hpositive := blockSize_pos machine.tm
    omega
  have hcapacity :
      rowWidth bound machine x + 1 ≤
        packedPhaseCapacity machine.tm
          (rowWidth bound machine x) := by
    unfold packedPhaseCapacity
    simpa only [Order.lt_add_one_iff, zero_le, le_mul_iff_one_le_right, mul_one] using
        Nat.mul_le_mul_left (rowWidth bound machine x + 1) hblock
  simp only [verifierInput, List.length_map,
    pairBitEncoding_length]
  omega

private theorem allInitializationWindows_decodedFullPackedPrivateStack
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position))
    (stack : machine.tm.K)
    (hstack : stack ≠ machine.tm.k₀) :
    decodedFullPackedPhaseStack machine
      (rowWidth bound machine x) next stack = [] := by
  unfold decodedFullPackedPhaseStack
  rw [allInitializationWindows_fullPackedStackAtoms
    bound machine x first next hfirst hmasks hwindows stack]
  have hblank :
      (fun index : Fin
        (packedPhaseCapacity machine.tm
          (rowWidth bound machine x)) =>
        initialPairedAtom machine stack
          (pairedInputTagAt x hfirst.certificate index.val)) =
      (fun _ : Fin
        (packedPhaseCapacity machine.tm
          (rowWidth bound machine x)) =>
        (none : CellAtom machine.tm)) := by
    funext index
    exact initialPairedAtom_private_blank
      machine stack hstack
      (pairedInputTagAt x hfirst.certificate index.val)
  rw [hblank]
  rw [List.ofFn_const]
  exact List.filterMap_replicate_of_none
    (cellAtomValue_blank machine stack)

private theorem allInitializationWindows_decodedFullPackedStack
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position))
    (stack : machine.tm.K) :
    decodedFullPackedPhaseStack machine
      (rowWidth bound machine x) next stack =
      (Turing.initList machine.tm
        (verifierInput machine x hfirst.certificate)).stk stack := by
  classical
  by_cases hstack : stack = machine.tm.k₀
  · subst stack
    simpa only [initList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq] using
        allInitializationWindows_decodedFullPackedInputStack bound machine x first next hfirst
            hmasks hwindows
  · rw [allInitializationWindows_decodedFullPackedPrivateStack
      bound machine x first next hfirst hmasks hwindows stack hstack]
    simp only [initList, eq_mpr_eq_cast, hstack, ↓reduceDIte]

private theorem allInitializationWindows_initialControl
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (next 0)) =
      some
        ((Turing.initList machine.tm
            (verifierInput machine x hfirst.certificate)).l,
         (Turing.initList machine.tm
            (verifierInput machine x hfirst.certificate)).var) := by
  have hwindow := hwindows 0
  simp only [AnchoredInitializationAllowed,
    CompleteInitializationAllowed, decide_eq_true_eq] at hwindow
  have hwindowOuter := ofClassicalDecide hwindow
  have hwindowCore := ofClassicalDecide hwindowOuter.1
  have hhead := hwindowCore.2.2.2
  have hmask := hmasks 0
  simp only [AnchoredPhaseMasks, decide_eq_true_eq] at hmask
  change
    completeMachineHead machine.tm (next 0) =
      initializedPhaseBlock machine
        (completeMachineHead machine.tm (first 0))
        (first 0).payloadHead (first 0).rangeHead at hhead
  have hrange :
      (first 0).rangeHead (firstPhaseOffset machine.tm) = true := by
    rw [hmask.2.1]
    simp only [phaseRangeBlockAt, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul, firstPhaseOffset,
        add_zero,
        Order.lt_add_one_iff, zero_le, decide_true]
  have hrangeZero :
      (first 0).rangeHead
        (⟨0, blockSize_pos machine.tm⟩ :
          Fin (blockSize machine.tm)) = true := by
    simpa only [firstPhaseOffset] using hrange
  have hlabel :
      (initializedPhaseBlock machine
        (completeMachineHead machine.tm (first 0))
        (first 0).payloadHead (first 0).rangeHead
          (⟨0, blockSize_pos machine.tm⟩ :
            Fin (blockSize machine.tm))).2.1 =
        some (configurationControl machine.tm
          (Turing.initList machine.tm [])) := by
    simp only [initializedPhaseBlock, hrangeZero, ↓reduceIte]
  have hnonhalt :
      (initializedPhaseBlock machine
        (completeMachineHead machine.tm (first 0))
        (first 0).payloadHead (first 0).rangeHead
          (⟨0, blockSize_pos machine.tm⟩ :
            Fin (blockSize machine.tm))).2.2.2 =
        true := by
    simp only [initializedPhaseBlock, hrangeZero, ↓reduceIte, initList, eq_mpr_eq_cast,
        Option.isSome_some]
  rw [hhead]
  unfold machineControlOfBlock
  rw [hlabel, hnonhalt]
  simp only [↓reduceIte, configurationControl, initList, eq_mpr_eq_cast, Option.getD_some]

private theorem allInitializationWindows_actualFullPackedConfiguration
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x) next =
      Turing.initList machine.tm
        (verifierInput machine x hfirst.certificate) := by
  have hcontrol := allInitializationWindows_initialControl
    bound machine x first next hfirst hmasks hwindows
  unfold decodedFullPackedPhaseConfiguration
  rw [hcontrol]
  apply configuration_eq_of_components machine.tm
  · rfl
  · rfl
  · funext stack
    exact allInitializationWindows_decodedFullPackedStack
      bound machine x first next hfirst hmasks hwindows stack

private theorem initialPairedAtom_input_ne_blank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (bit : Bool ⊕ Bool) :
    initialPairedAtom machine machine.tm.k₀ (.bit bit) ≠ none := by
  intro hblank
  have hdecode := initialPairedAtom_input_decode machine bit
  rw [hblank, cellAtomValue_blank] at hdecode
  cases hdecode

private theorem initialPairedAtom_pairedInput_blank_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (index : ℕ) :
    initialPairedAtom machine machine.tm.k₀
      (pairedInputTagAt x certificate index) = none ↔
      (pairBitEncoding (x, certificate)).length ≤ index := by
  constructor
  · intro hblank
    by_contra hnot
    have hinside : index <
        (pairBitEncoding (x, certificate)).length := by
      omega
    have hentry :
        (pairBitEncoding (x, certificate))[index]? =
          some ((pairBitEncoding (x, certificate))[index]) :=
      List.getElem?_eq_getElem hinside
    have htag :
        pairedInputTagAt x certificate index =
          .bit ((pairBitEncoding (x, certificate))[index]) := by
      unfold pairedInputTagAt
      rw [hentry]
    rw [htag] at hblank
    exact initialPairedAtom_input_ne_blank machine _ hblank
  · intro houtside
    have hentry := List.getElem?_eq_none houtside
    have htag :
        pairedInputTagAt x certificate index =
          if index = (pairBitEncoding (x, certificate)).length then
            .marker
          else
            .blank := by
      unfold pairedInputTagAt
      rw [hentry]
    rw [htag]
    split <;> rfl

private theorem pairedInputAtomTrack_noInteriorPaddingHoles
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (capacity : ℕ)
    (stack : machine.tm.K) :
    NoInteriorPaddingHoles machine.tm
      (List.ofFn (fun index : Fin capacity =>
        initialPairedAtom machine stack
          (pairedInputTagAt x certificate index.val))) := by
  apply noInteriorPaddingHoles_of_blankPaddingMonotone
  simp only [BlankPaddingMonotone, decide_eq_true_eq]
  intro first next hle hblank
  by_cases hnext : next < capacity
  · have hfirst : first < capacity := by omega
    let firstIndex : Fin capacity := ⟨first, hfirst⟩
    let nextIndex : Fin capacity := ⟨next, hnext⟩
    have hfirstAtom :
        paddedAtom
          (List.ofFn (fun index : Fin capacity =>
            initialPairedAtom machine stack
              (pairedInputTagAt x certificate index.val))) first =
        initialPairedAtom machine stack
          (pairedInputTagAt x certificate first) := by
      simp only [paddedAtom, List.length_ofFn, hfirst, getElem?_pos, List.getElem_ofFn,
          Option.getD_some]
    have hnextAtom :
        paddedAtom
          (List.ofFn (fun index : Fin capacity =>
            initialPairedAtom machine stack
              (pairedInputTagAt x certificate index.val))) next =
        initialPairedAtom machine stack
          (pairedInputTagAt x certificate next) := by
      simp only [paddedAtom, List.length_ofFn, hnext, getElem?_pos, List.getElem_ofFn,
          Option.getD_some]
    rw [hfirstAtom] at hblank
    rw [hnextAtom]
    by_cases hstack : stack = machine.tm.k₀
    · subst stack
      apply (initialPairedAtom_pairedInput_blank_iff
        machine x certificate next).mpr
      have hword := (initialPairedAtom_pairedInput_blank_iff
        machine x certificate first).mp hblank
      omega
    · exact initialPairedAtom_private_blank
        machine stack hstack
        (pairedInputTagAt x certificate next)
  · apply paddedAtom_none_of_length_le
      machine.tm
      (List.ofFn (fun index : Fin capacity =>
        initialPairedAtom machine stack
          (pairedInputTagAt x certificate index.val))) next
    simp only [List.length_ofFn]
    omega

private theorem allInitializationWindows_fullPacked_noInteriorPaddingHoles
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x) next stack) := by
  intro stack
  rw [allInitializationWindows_fullPackedStackAtoms
    bound machine x first next hfirst hmasks hwindows stack]
  exact pairedInputAtomTrack_noInteriorPaddingHoles
    machine x hfirst.certificate
    (packedPhaseCapacity machine.tm (rowWidth bound machine x)) stack

private theorem allInitializationWindows_fullPackedStack_length_le
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (first next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hfirst : CanonicalGuessingTracks bound machine x first)
    (hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position))
    (hwindows : ∀ position : Position (rowWidth bound machine x),
      AnchoredInitializationAllowed machine
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x) first next position)) :
    ∀ stack : machine.tm.K,
      (decodedFullPackedPhaseStack machine
        (rowWidth bound machine x) next stack).length ≤
          rowWidth bound machine x := by
  intro stack
  classical
  by_cases hstack : stack = machine.tm.k₀
  · subst stack
    rw [allInitializationWindows_decodedFullPackedInputStack
      bound machine x first next hfirst hmasks hwindows]
    simp only [verifierInput, List.length_map,
      pairBitEncoding_length]
    exact (Nat.add_le_add_left hfirst.certificate_le x.length).trans
      (pairedCertificateBound_le_rowWidth bound machine x)
  · rw [allInitializationWindows_decodedFullPackedPrivateStack
      bound machine x first next hfirst hmasks hwindows stack hstack]
    exact Nat.zero_le _

private theorem stackSoundValidTrace_initialization_actualConfiguration
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine (trace time.succ)) =
      Turing.initList machine.tm
        (verifierInput machine x hfirst.certificate) := by
  apply allInitializationWindows_actualFullPackedConfiguration
    bound machine x
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ)) hfirst
  · intro position
    exact stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time) position
      (by rw [hfirst.mode position]; exact PhaseTag.noConfusion)
  · exact stackSoundValidTrace_allInitializationWindows
      bound machine x trace htrace time hfirst.mode hnext

private noncomputable def stackSoundValidTrace_initialization_actualBegin
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    GuessStep bound machine x
      (.guessing hfirst.certificate)
      (.verifying hfirst.certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine (trace time.succ)))) := by
  rw [stackSoundValidTrace_initialization_actualConfiguration
    bound machine x trace htrace time hfirst hnext]
  exact GuessStep.begin hfirst.certificate hfirst.certificate_le

private noncomputable def stackSoundValidTrace_initialization_reachable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing []) (.guessing hfirst.certificate) elapsed) :
    FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying hfirst.certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine (trace time.succ))))
      (elapsed + 1) :=
  FiniteRun.tail run
    (stackSoundValidTrace_initialization_actualBegin
      bound machine x trace htrace time hfirst hnext)

private theorem stackSoundValidTrace_initialization_space_padding_noHoles
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying) :
    (∀ stack : machine.tm.K,
      (decodedFullPackedPhaseStack machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace time.succ)) stack).length ≤
          rowWidth bound machine x) ∧
    PhaseRowStackRangeFaithful machine
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine (trace time.succ)) ∧
    (∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) stack)) := by
  let first := decodeCorrectedPhaseRow machine
    (trace (Fin.castSucc time))
  let next := decodeCorrectedPhaseRow machine
    (trace time.succ)
  have hmasks : ∀ position : Position (rowWidth bound machine x),
      AnchoredPhaseMasks bound machine x position (first position) := by
    intro position
    exact stackSoundValidTrace_masks_of_not_accepting
      bound machine x trace htrace (Fin.castSucc time) position
      (by rw [hfirst.mode position]; exact PhaseTag.noConfusion)
  have hwindows := stackSoundValidTrace_allInitializationWindows
    bound machine x trace htrace time hfirst.mode hnext
  refine ⟨?_, ?_, ?_⟩
  · exact allInitializationWindows_fullPackedStack_length_le
      bound machine x first next hfirst hmasks hwindows
  · exact stackSoundValidTrace_initialization_rangeFaithful
      bound machine x trace htrace time hfirst.mode hnext
  · exact allInitializationWindows_fullPacked_noInteriorPaddingHoles
      bound machine x first next hfirst hmasks hwindows

private noncomputable def stackSoundValidTrace_initialization_reachable_space_padding
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : CanonicalGuessingTracks bound machine x
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing []) (.guessing hfirst.certificate) elapsed) :
    { _nextRun : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying hfirst.certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine (trace time.succ))))
      (elapsed + 1) //
      (∀ stack : machine.tm.K,
        (decodedFullPackedPhaseStack machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) stack).length ≤
            rowWidth bound machine x) ∧
      PhaseRowStackRangeFaithful machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine (trace time.succ)) ∧
      (∀ stack : machine.tm.K,
        NoInteriorPaddingHoles machine.tm
          (fullPackedPhaseStackAtoms machine
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace time.succ)) stack))  } := by
  exact ⟨stackSoundValidTrace_initialization_reachable
    bound machine x trace htrace time hfirst hnext run,
    stackSoundValidTrace_initialization_space_padding_noHoles
      bound machine x trace htrace time hfirst hnext⟩

end CLReachableTableauCompiler

namespace CLNaturalTimeCompiler

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLCellRowBounds GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLValidTraceSoundness GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLCompactWindowSoundness
open GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction GapCVP.CLFullStackStepSoundness
open GapCVP.CLFullTraceReachability GapCVP.CLGuessPayloadReachability
open GapCVP.CLReachableTableauCompiler

private theorem evalsTo_prefix_steps_le_terminal
    {α : Type}
    (step : α → Option α)
    (initial configuration terminal : α)
    (partialRun : StateTransition.EvalsTo step initial (some configuration))
    (halting : StateTransition.EvalsTo step initial (some terminal))
    (hterminal : step terminal = none) :
    partialRun.steps ≤ halting.steps := by
  by_contra hnot
  have hstrict : halting.steps < partialRun.steps := by
    omega
  let advance : Option α → Option α := flip bind step
  let extra : ℕ := partialRun.steps - halting.steps
  have hextra : 0 < extra := by
    dsimp [extra]
    omega
  have hsplit : partialRun.steps = extra + halting.steps := by
    dsimp [extra]
    omega
  have hhaltRun :
      (advance^[halting.steps]) (some initial) = some terminal := by
    simpa only [advance] using halting.evals_in_steps
  have hprefixRun :
      (advance^[partialRun.steps]) (some initial) =
        some configuration := by
    simpa only [advance] using partialRun.evals_in_steps
  have hremaining :
      (advance^[extra]) (some terminal) = some configuration := by
    calc
      (advance^[extra]) (some terminal) =
          (advance^[extra])
            ((advance^[halting.steps]) (some initial)) := by
          rw [hhaltRun]
      _ = (advance^[extra + halting.steps]) (some initial) :=
          (Function.iterate_add_apply advance extra halting.steps
            (some initial)).symm
      _ = some configuration := by
          rw [← hsplit]
          exact hprefixRun
  obtain ⟨count, hcount⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hextra)
  have hnone : (advance^[extra]) (some terminal) = none := by
    rw [hcount, Function.iterate_succ_apply]
    change (advance^[count]) ((some terminal).bind step) = none
    rw [Option.bind_some, hterminal]
    exact Function.iterate_fixed (by rfl) count
  rw [hnone] at hremaining
  cases hremaining

private theorem evalsTo_prefix_steps_lt_terminal_of_step
    {α : Type}
    (step : α → Option α)
    (initial configuration successor terminal : α)
    (partialRun : StateTransition.EvalsTo step initial (some configuration))
    (halting : StateTransition.EvalsTo step initial (some terminal))
    (hterminal : step terminal = none)
    (hstep : step configuration = some successor) :
    partialRun.steps < halting.steps := by
  have hle := evalsTo_prefix_steps_le_terminal
    step initial configuration terminal partialRun halting hterminal
  by_contra hnot
  have heq : partialRun.steps = halting.steps := by
    omega
  have hsame : terminal = configuration :=
    evalsTo_terminal_unique_of_steps_le
      step initial terminal configuration
      halting partialRun hterminal (by omega)
  rw [← hsame, hterminal] at hstep
  cases hstep

private theorem verifierPrefix_steps_le_witnessTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hcertificate : certificate.length ≤ bound.eval x.length)
    (configuration : machine.tm.Cfg)
    (partialRun : StateTransition.EvalsTo machine.tm.step
      (Turing.initList machine.tm
        (verifierInput machine x certificate))
      (some configuration)) :
    partialRun.steps ≤
      (witnessTimePolynomial bound machine).eval x.length := by
  let halting := boundedVerifierRun
    bound machine x certificate hcertificate
  have hprefix := evalsTo_prefix_steps_le_terminal
    machine.tm.step
    (Turing.initList machine.tm
      (verifierInput machine x certificate))
    configuration
    (Turing.haltList machine.tm
      (verifierOutput machine (verifier (x, certificate))))
    partialRun halting.toEvalsTo
    (haltList_step machine.tm
      (verifierOutput machine (verifier (x, certificate))))
  exact hprefix.trans halting.steps_le_m

private theorem verifierPrefix_successor_steps_le_witnessTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hcertificate : certificate.length ≤ bound.eval x.length)
    (configuration successor : machine.tm.Cfg)
    (partialRun : StateTransition.EvalsTo machine.tm.step
      (Turing.initList machine.tm
        (verifierInput machine x certificate))
      (some configuration))
    (hstep : machine.tm.step configuration = some successor) :
    partialRun.steps + 1 ≤
      (witnessTimePolynomial bound machine).eval x.length := by
  let halting := boundedVerifierRun
    bound machine x certificate hcertificate
  have hprefix := evalsTo_prefix_steps_lt_terminal_of_step
    machine.tm.step
    (Turing.initList machine.tm
      (verifierInput machine x certificate))
    configuration successor
    (Turing.haltList machine.tm
      (verifierOutput machine (verifier (x, certificate))))
    partialRun halting.toEvalsTo
    (haltList_step machine.tm
      (verifierOutput machine (verifier (x, certificate)))) hstep
  have hbound := halting.steps_le_m
  omega

private noncomputable def ExactNaturalGuessInvariant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (elapsed : ℕ) : GuessState machine.tm → Bool
  | .guessing certificate =>
    @decide (
      certificate.length ≤ bound.eval x.length ∧
        elapsed = certificate.length
    ) (Classical.propDecidable _)
  | .verifying certificate configuration =>
    @decide (
      certificate.length ≤ bound.eval x.length ∧
        ∃ run : StateTransition.EvalsTo machine.tm.step
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          (some configuration),
          elapsed = certificate.length + 1 + run.steps
    ) (Classical.propDecidable _)
private theorem exactNaturalGuessInvariant_step
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    {elapsed : ℕ}
    {first next : GuessState machine.tm}
    (hfirst : ExactNaturalGuessInvariant
      bound machine x elapsed first)
    (hstep : GuessStep bound machine x first next) :
    ExactNaturalGuessInvariant bound machine x (elapsed + 1) next := by
  cases hstep with
  | guess certificate bit hbound =>
      simp only [ExactNaturalGuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨_, helapsed⟩
      simp only [List.length_append, List.length_singleton]
      constructor <;> omega
  | begin certificate hbound =>
      simp only [ExactNaturalGuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨_, helapsed⟩
      refine ⟨hbound, StateTransition.EvalsTo.refl machine.tm.step
        (Turing.initList machine.tm
          (verifierInput machine x certificate)), ?_⟩
      change elapsed + 1 = certificate.length + 1 + 0
      omega
  | execute certificate configuration successor hstep =>
      simp only [ExactNaturalGuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨hcertificate, run, helapsed⟩
      let successorRun := StateTransition.EvalsTo.trans machine.tm.step
        (Turing.initList machine.tm
          (verifierInput machine x certificate))
        configuration (some successor) run
        (oneStepEvalsTo machine.tm configuration successor hstep)
      refine ⟨hcertificate, successorRun, ?_⟩
      change elapsed + 1 =
        certificate.length + 1 + (1 + run.steps)
      omega

private theorem exactNaturalGuessInvariant_run
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    {state : GuessState machine.tm}
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing []) state elapsed) :
    ExactNaturalGuessInvariant bound machine x elapsed state := by
  have hinitial : ExactNaturalGuessInvariant
      bound machine x 0 (.guessing []) := by
    simp only [ExactNaturalGuessInvariant, decide_eq_true_eq,
      List.length_nil, Nat.zero_le, and_self]
  induction run with
  | refl => exact hinitial
  | tail prior hstep ih =>
      exact exactNaturalGuessInvariant_step
        bound machine x ih hstep

private theorem finiteRun_verifying_elapsed_le_guessTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (configuration : machine.tm.Cfg)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate configuration) elapsed) :
    elapsed ≤ (guessTimePolynomial bound machine).eval x.length := by
  have hinvariant := exactNaturalGuessInvariant_run bound machine x run
  simp only [ExactNaturalGuessInvariant, decide_eq_true_eq] at hinvariant
  obtain ⟨hcertificate, machineRun, helapsed⟩ := hinvariant
  have hmachine := verifierPrefix_steps_le_witnessTime
    bound machine x certificate hcertificate
    configuration machineRun
  simp only [guessTimePolynomial, Polynomial.eval_add,
    Polynomial.eval_one]
  omega

private theorem finiteRun_verifierSuccessor_elapsed_le_guessTime
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (configuration successor : machine.tm.Cfg)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate configuration) elapsed)
    (hstep : machine.tm.step configuration = some successor) :
    elapsed + 1 ≤
      (guessTimePolynomial bound machine).eval x.length := by
  have hinvariant := exactNaturalGuessInvariant_run bound machine x run
  simp only [ExactNaturalGuessInvariant, decide_eq_true_eq] at hinvariant
  obtain ⟨hcertificate, machineRun, helapsed⟩ := hinvariant
  have hmachine := verifierPrefix_successor_steps_le_witnessTime
    bound machine x certificate hcertificate
    configuration successor machineRun hstep
  simp only [guessTimePolynomial, Polynomial.eval_add,
    Polynomial.eval_one]
  omega

private theorem stackSoundValidTrace_actualFullPackedStep_of_run
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))) stack))
    (certificate : List Bool)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))))) elapsed) :
    machine.tm.step
      (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time)))) =
      some
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine (trace time.succ))) := by
  exact stackSoundValidTrace_actualFullPackedStep_of_actualTimedRun
    bound machine x trace htrace time hfirst hnext hholes
    certificate run
    (finiteRun_verifying_elapsed_le_guessTime
      bound machine x certificate
      (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time)))) run)

private noncomputable def stackSoundValidTrace_verifierSuccessor_reachable_of_run
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnext : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))) stack))
    (certificate : List Bool)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time))))) elapsed) :
    { _nextRun : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine (trace time.succ))))
      (elapsed + 1) //
      (∀ stack : machine.tm.K,
        (decodedFullPackedPhaseStack machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace time.succ)) stack).length ≤
              rowWidth bound machine x) ∧
      PhaseRowStackRangeFaithful machine
        (rowWidth bound machine x)
        (decodeCorrectedPhaseRow machine (trace time.succ)) ∧
      (∀ stack : machine.tm.K,
        NoInteriorPaddingHoles machine.tm
          (fullPackedPhaseStackAtoms machine
            (rowWidth bound machine x)
            (decodeCorrectedPhaseRow machine
              (trace time.succ)) stack))  } := by
  have hstep := stackSoundValidTrace_actualFullPackedStep_of_run
    bound machine x trace htrace time hfirst hnext hholes
    certificate run
  have hruntime := finiteRun_verifierSuccessor_elapsed_le_guessTime
    bound machine x certificate
    (decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))))
    (decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine (trace time.succ)))
    run hstep
  exact stackSoundValidTrace_verifierSuccessor_reachable_space_padding
    bound machine x trace htrace time hfirst hnext hholes
    certificate run hruntime

private theorem stackSoundValidTrace_nonacceptingTime_lt_width
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x))
    (hnonaccept : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time) position).mode ≠ .accepting) :
    time.val < rowWidth bound machine x := by
  obtain ⟨position, haccept⟩ :=
    anchoredValidTrace_has_acceptingCell
      bound machine x trace
      (stackSoundValidTrace_to_anchored
        bound machine x trace htrace)
  by_contra hnot
  have hlastVal : time.val = rowWidth bound machine x := by
    have hlt := time.isLt
    omega
  have hlast : time = Fin.last (rowWidth bound machine x) := by
    apply Fin.ext
    exact hlastVal
  apply hnonaccept position
  rw [hlast, haccept]
  rfl

private theorem stackSoundValidTrace_nonaccepting_mode_constant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x))
    (hnonaccept : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time) position).mode ≠ .accepting) :
    ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time) position).mode =
      (decodeCorrectedPhaseRow machine
        (trace time) 0).mode := by
  have hlt := stackSoundValidTrace_nonacceptingTime_lt_width
    bound machine x trace htrace time hnonaccept
  let outgoing : Fin (rowWidth bound machine x) :=
    ⟨time.val, hlt⟩
  have hrow : trace (Fin.castSucc outgoing) = trace time := by
    apply congrArg trace
    apply Fin.ext
    rfl
  intro position
  have hconstant := anchoredValidTrace_mode_constant
    bound machine x trace
    (stackSoundValidTrace_to_anchored
      bound machine x trace htrace)
    outgoing position
  calc
    (decodeCorrectedPhaseRow machine
      (trace time) position).mode =
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc outgoing)) position).mode :=
      (congrArg (fun row =>
        (decodeCorrectedPhaseRow machine row position).mode)
        hrow).symm
    _ = (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc outgoing)) 0).mode := hconstant
    _ = (decodeCorrectedPhaseRow machine
          (trace time) 0).mode :=
      congrArg (fun row =>
        (decodeCorrectedPhaseRow machine row 0).mode) hrow

private inductive CorrectedReachablePhase
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (row : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (elapsed : ℕ) : Type where
  | guessing
      (tracks : CanonicalGuessingTracks bound machine x row)
      (run : FiniteRun (GuessStep bound machine x)
        (.guessing []) (.guessing tracks.certificate) elapsed) :
      CorrectedReachablePhase bound machine x row elapsed
  | verifying
      (certificate : List Bool)
      (mode : ∀ position : Position (rowWidth bound machine x),
        (row position).mode = .verifying)
      (holes : ∀ stack : machine.tm.K,
        NoInteriorPaddingHoles machine.tm
          (fullPackedPhaseStackAtoms machine
            (rowWidth bound machine x) row stack))
      (run : FiniteRun (GuessStep bound machine x)
        (.guessing [])
        (.verifying certificate
          (decodedFullPackedPhaseConfiguration machine
            (rowWidth bound machine x) row)) elapsed) :
      CorrectedReachablePhase bound machine x row elapsed

private theorem stackSoundValidTrace_predecessor_nonaccepting
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hnonaccept : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode ≠ .accepting) :
    ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode ≠ .accepting := by
  intro position
  apply anchoredPhase_old_not_accepting_of_next_not_accepting
    machine
    (anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x)
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)))
      (decodeCorrectedPhaseRow machine (trace time.succ)) position)
  · exact stackSoundAnchoredPhaseAllowed_implies_anchored
      machine _
      (stackSoundValidTrace_window
        bound machine x trace htrace (windowAt time position))
  · exact hnonaccept position

private theorem stackSoundValidTrace_verifyingSuccessor_modes
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x))
    (hfirst : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) position).mode = .verifying)
    (hnonaccept : ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode ≠ .accepting) :
    ∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .verifying := by
  let window := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x)
    (decodeCorrectedPhaseRow machine
      (trace (Fin.castSucc time)))
    (decodeCorrectedPhaseRow machine (trace time.succ)) 0
  have hallowed := stackSoundValidTrace_window
    bound machine x trace htrace (windowAt time 0)
  change StackSoundAnchoredPhaseAllowed machine window at hallowed
  have hallowed' := hallowed
  simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
    at hallowed'
  have hbranches :
      StackSoundAnchoredVerificationAllowed machine window ∨
        AnchoredAcceptanceAllowed machine window := by
    have hbranch := hallowed'.2
    change
      match (decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time)) 0).mode with
      | .guessing =>
          AnchoredGuessingAllowed machine window ∨
            AnchoredInitializationAllowed machine window
      | .verifying =>
          StackSoundAnchoredVerificationAllowed machine window ∨
            AnchoredAcceptanceAllowed machine window
      | .accepting =>
          window.2.2.2 = acceptingPhaseCell machine.tm
      at hbranch
    simpa only [hfirst 0] using hbranch
  have hzero :
      (decodeCorrectedPhaseRow machine
        (trace time.succ) 0).mode = .verifying := by
    rcases hbranches with hverify | haccept
    · have hverify' := hverify
      simp only [StackSoundAnchoredVerificationAllowed,
        AnchoredVerificationAllowed, CompleteVerificationAllowed,
        decide_eq_true_eq] at hverify'
      exact hverify'.1.1.1
    · have hbad :
          (decodeCorrectedPhaseRow machine
            (trace time.succ) 0).mode = .accepting := by
        change window.2.2.2.mode = .accepting
        have haccept' := haccept
        simp only [AnchoredAcceptanceAllowed, CompleteAcceptanceAllowed,
          decide_eq_true_eq] at haccept'
        have hacceptOuter := ofClassicalDecide haccept'
        have hacceptCore := ofClassicalDecide hacceptOuter.1
        rw [hacceptCore.1]
        rfl
      exact (hnonaccept 0 hbad).elim
  intro position
  exact (stackSoundValidTrace_nonaccepting_mode_constant
    bound machine x trace htrace time.succ hnonaccept position).trans hzero

private noncomputable def stackSoundValidTrace_nonaccepting_reachablePhase
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace)
    (time : Time (rowWidth bound machine x)) :
    (∀ position : Position (rowWidth bound machine x),
      (decodeCorrectedPhaseRow machine
        (trace time) position).mode ≠ .accepting) →
    CorrectedReachablePhase bound machine x
      (decodeCorrectedPhaseRow machine (trace time)) time.val := by
  induction time using Fin.induction with
  | zero =>
      intro _
      have hrow :
          decodeCorrectedPhaseRow machine (trace 0) =
            initialPhaseCell bound machine x := by
        funext position
        exact anchoredTrace_initial bound machine x trace
          (stackSoundValidTrace_to_anchored
            bound machine x trace htrace) position
      rw [hrow]
      exact CorrectedReachablePhase.guessing
        (initialCanonicalGuessingTracks bound machine x)
        (FiniteRun.refl (GuessState.guessing []))
  | succ time ih =>
      intro hnonaccept
      have hsourceNot := stackSoundValidTrace_predecessor_nonaccepting
        bound machine x trace htrace time hnonaccept
      have hsource := ih hsourceNot
      cases hsource with
      | guessing tracks run =>
          have hconstant := stackSoundValidTrace_nonaccepting_mode_constant
            bound machine x trace htrace time.succ hnonaccept
          cases hmode :
              (decodeCorrectedPhaseRow machine
                (trace time.succ) 0).mode with
          | guessing =>
              have hnext : ∀ position : Position
                  (rowWidth bound machine x),
                  (decodeCorrectedPhaseRow machine
                    (trace time.succ) position).mode = .guessing := by
                intro position
                exact (hconstant position).trans hmode
              let nextTracks :=
                stackSoundValidTrace_guessingSuccessorCanonical
                  bound machine x trace htrace time tracks hnext
              refine CorrectedReachablePhase.guessing nextTracks ?_
              exact FiniteRun.tail run
                (stackSoundValidTrace_guessingSuccessor_actualStep
                  bound machine x trace htrace time tracks hnext)
          | verifying =>
              have hnext : ∀ position : Position
                  (rowWidth bound machine x),
                  (decodeCorrectedPhaseRow machine
                    (trace time.succ) position).mode = .verifying := by
                intro position
                exact (hconstant position).trans hmode
              obtain ⟨nextRun, _, _, holes⟩ :=
                stackSoundValidTrace_initialization_reachable_space_padding
                  bound machine x trace htrace time tracks hnext run
              exact CorrectedReachablePhase.verifying
                tracks.certificate hnext holes nextRun
          | accepting =>
              exact (hnonaccept 0 hmode).elim
      | verifying certificate modes holes run =>
          have hnext := stackSoundValidTrace_verifyingSuccessor_modes
            bound machine x trace htrace time modes hnonaccept
          obtain ⟨nextRun, _, _, nextHoles⟩ :=
            stackSoundValidTrace_verifierSuccessor_reachable_of_run
              bound machine x trace htrace time modes hnext holes
              certificate run
          exact CorrectedReachablePhase.verifying
            certificate hnext nextHoles nextRun

theorem stackSoundValidTrace_firstAcceptance_actualReachable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace) :
    ∃ (time : Fin (rowWidth bound machine x))
      (position : Position (rowWidth bound machine x))
      (certificate : List Bool),
      let first := decodeCorrectedPhaseRow machine
        (trace (Fin.castSucc time))
      let next := decodeCorrectedPhaseRow machine
        (trace time.succ)
      AnchoredAcceptanceAllowed machine
          (anchoredVerifierWindowAt machine.tm
            (rowWidth bound machine x) first next position) ∧
        (∀ other : Position (rowWidth bound machine x),
          (first other).mode = .verifying) ∧
        (∀ other : Position (rowWidth bound machine x),
          AnchoredPhaseMasks bound machine x other (first other)) ∧
        (∀ stack : machine.tm.K,
          NoInteriorPaddingHoles machine.tm
            (fullPackedPhaseStackAtoms machine
              (rowWidth bound machine x) first stack)) ∧
        certificate.length ≤ bound.eval x.length ∧
        Nonempty (FiniteRun (GuessStep bound machine x)
          (.guessing [])
          (.verifying certificate
            (decodedFullPackedPhaseConfiguration machine
              (rowWidth bound machine x) first)) time.val) ∧
        (∃ verifierRun : StateTransition.EvalsTo machine.tm.step
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          (some (decodedFullPackedPhaseConfiguration machine
            (rowWidth bound machine x) first)),
          time.val = certificate.length + 1 + verifierRun.steps) ∧
        time.val ≤
          (guessTimePolynomial bound machine).eval x.length ∧
        (∀ (earlier : Time (rowWidth bound machine x)),
          earlier.val ≤ time.val →
          ∀ other : Position (rowWidth bound machine x),
            (decodeCorrectedPhaseRow machine
              (trace earlier) other).mode ≠ .accepting) := by
  obtain ⟨time, position, haccept, hmode, hmasks, hprefix⟩ :=
    stackSoundValidTrace_has_first_checked_acceptance
      bound machine x trace htrace
  have hnonaccept :
      ∀ other : Position (rowWidth bound machine x),
        (decodeCorrectedPhaseRow machine
          (trace (Fin.castSucc time)) other).mode ≠ .accepting :=
    hprefix (Fin.castSucc time) (by simp only [Fin.val_castSucc, Std.le_refl])
  have hreachable := stackSoundValidTrace_nonaccepting_reachablePhase
    bound machine x trace htrace (Fin.castSucc time) hnonaccept
  cases hreachable with
  | guessing tracks run =>
      have hguess := tracks.mode 0
      rw [hmode 0] at hguess
      cases hguess
  | verifying certificate modes holes run =>
      have hinvariant := exactNaturalGuessInvariant_run bound machine x run
      simp only [ExactNaturalGuessInvariant, decide_eq_true_eq] at hinvariant
      obtain ⟨hcertificate, verifierRun, helapsed⟩ := hinvariant
      have hruntime := finiteRun_verifying_elapsed_le_guessTime
        bound machine x certificate
        (decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x)
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)))) run
      refine ⟨time, position, certificate, ?_⟩
      dsimp
      exact ⟨haccept, hmode, hmasks, holes, hcertificate, ⟨run⟩,
        ⟨verifierRun, helapsed⟩, hruntime, hprefix⟩

end CLNaturalTimeCompiler

namespace CLAcceptanceAnchor

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler GapCVP.CLExactVerifierTransition
open GapCVP.CLLocalTableauCompiler GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLStackVerifierSimulation GapCVP.CLArbitraryRowOccupancy
open GapCVP.CLCompactWindowSoundness GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness GapCVP.CLFullTraceReachability GapCVP.CLNaturalTimeCompiler

/-- GapCVP reduction support. -/
noncomputable def ReplicatedMachineHeadCoherent
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm) : Bool :=
  @decide (
  completeMachineHead tm window.1 =
      completeMachineHead tm window.2.1 ∧
    completeMachineHead tm window.2.2.1 =
      completeMachineHead tm window.2.1
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def TrueOutputMachineHead
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (cell : CompletePhaseCell machine.tm) : Bool :=
  @decide (
  ∀ (offset : Fin (blockSize machine.tm))
    (stack : machine.tm.K),
    cellAtomValue machine stack
        ((completeMachineHead machine.tm cell offset).2.2.1 stack) =
      if offset.val = 0 then
        ((Turing.haltList machine.tm
          (verifierOutput machine true)).stk stack)[0]?
      else
        none
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def AcceptanceAnchoredPhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  StackSoundAnchoredPhaseAllowed machine window ∧
    ReplicatedMachineHeadCoherent machine.tm window ∧
    (window.2.2.2.mode = .accepting →
      TrueOutputMachineHead machine window.2.1)
  ) (Classical.propDecidable _)
private theorem verifierHalt_stack_length_le_one
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (value : Bool)
    (stack : machine.tm.K) :
    ((Turing.haltList machine.tm
      (verifierOutput machine value)).stk stack).length ≤ 1 := by
  classical
  by_cases hstack : stack = machine.tm.k₁
  · subst stack
    rw [GapCVP.TMComposition.haltList_stk_self]
    exact (verifierOutput_length machine value).le
  · simp only [haltList, eq_mpr_eq_cast, hstack, ↓reduceDIte, List.length_nil, zero_le]

private theorem canonicalAnchoredVerifyingRow_blockAtom_decode
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration)
    (hspace : ∀ stack : machine.tm.K,
      (configuration.stk stack).length ≤ rowWidth bound machine x)
    (hint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (stack : machine.tm.K) :
    cellAtomValue machine stack
        ((completeMachineBlock machine.tm
          (canonicalAnchoredVerifyingRow bound machine x certificate
            configuration hsupported hint annotation position)
          offset).2.2.1 stack) =
      (configuration.stk stack)[
        position.val * blockSize machine.tm + offset.val]? := by
  change
    cellAtomValue machine stack
        ((stackAtomsOfBlock machine.tm
          (packRow machine.tm (rowWidth bound machine x)
            (canonicalVerifyingRow machine
              (rowWidth bound machine x)
              certificate configuration hsupported) position)
          stack) offset) = _
  rw [stackAtomsOfBlock_pack_canonical machine
    (rowWidth bound machine x) certificate configuration
    hsupported hspace position stack]
  simpa only [atomBlockAt] using
      paddedAtom_decode machine stack
        (canonicalStackAtoms_forall₂ machine stack (configuration.stk stack)
          (stackAtomSupported_supportedValues machine configuration hsupported stack))
        (position.val * blockSize machine.tm + offset.val)

private theorem canonicalAnchoredVerifyingWindow_replicatedMachineHeadCoherent
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (firstAnnotation nextAnnotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    ReplicatedMachineHeadCoherent machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          first hfirst firstHint firstAnnotation)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          next hnext nextHint nextAnnotation)
        position) := by
  simp only [ReplicatedMachineHeadCoherent, completeMachineHead, anchoredVerifierWindowAt,
      canonicalAnchoredVerifyingRow, canonicalScriptBlockRow, Fin.val_eq_zero_iff, and_self,
          decide_true]

private theorem canonicalTrueHalt_trueOutputMachineHead
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.haltList machine.tm
        (verifierOutput machine true)))
    (hint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (hwidth : 1 ≤ rowWidth bound machine x)
    (position : Position (rowWidth bound machine x)) :
    TrueOutputMachineHead machine
      (canonicalAnchoredVerifyingRow bound machine x certificate
        (Turing.haltList machine.tm
          (verifierOutput machine true))
        hsupported hint annotation position) := by
  simp only [TrueOutputMachineHead, decide_eq_true_eq]
  let configuration := Turing.haltList machine.tm
    (verifierOutput machine true)
  have hspace : ∀ stack : machine.tm.K,
      (configuration.stk stack).length ≤ rowWidth bound machine x := by
    intro stack
    exact (verifierHalt_stack_length_le_one
      machine true stack).trans hwidth
  intro offset stack
  have hatom := canonicalAnchoredVerifyingRow_blockAtom_decode
    bound machine x certificate configuration hsupported hspace
    hint annotation 0 offset stack
  change
    cellAtomValue machine stack
      ((packRow machine.tm (rowWidth bound machine x)
        (canonicalVerifyingRow machine
          (rowWidth bound machine x)
          certificate configuration hsupported) 0
        offset).2.2.1 stack) = _
  change
    cellAtomValue machine stack
      ((packRow machine.tm (rowWidth bound machine x)
        (canonicalVerifyingRow machine
          (rowWidth bound machine x)
          certificate configuration hsupported) 0
        offset).2.2.1 stack) = _
    at hatom
  rw [hatom]
  by_cases hzero : offset.val = 0
  · simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul, hzero, add_zero, ↓reduceIte,
      configuration]
  · have hlength := verifierHalt_stack_length_le_one
      machine true stack
    have hindex :
        (configuration.stk stack).length ≤ offset.val := by
      change
        ((Turing.haltList machine.tm
          (verifierOutput machine true)).stk stack).length ≤ _
      omega
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul, zero_add, not_lt, hindex,
        getElem?_neg, hzero,
        ↓reduceIte]

private theorem trueOutputMachineHead_decodedAtomBlock
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (cell : CompletePhaseCell machine.tm)
    (hfirst : completeIsFirstBlock machine.tm cell = true)
    (hanchor : FirstBlockAnchored machine.tm cell)
    (htrue : TrueOutputMachineHead machine cell)
    (stack : machine.tm.K) :
    decodedAtomBlock machine stack
        (stackAtomsOfBlock machine.tm
          (completeMachineBlock machine.tm cell) stack) =
      (Turing.haltList machine.tm
        (verifierOutput machine true)).stk stack := by
  have htrue' := htrue
  simp only [TrueOutputMachineHead, decide_eq_true_eq] at htrue'
  have hanchor' := hanchor
  simp only [FirstBlockAnchored, decide_eq_true_eq] at hanchor'
  let output := (Turing.haltList machine.tm
    (verifierOutput machine true)).stk stack
  have hlength : output.length ≤ 1 :=
    verifierHalt_stack_length_le_one machine true stack
  have hblock := (hanchor' hfirst).1
  have hpointwise :
      (fun offset : Fin (blockSize machine.tm) =>
        cellAtomValue machine stack
          ((completeMachineBlock machine.tm cell offset).2.2.1 stack)) =
      (fun offset : Fin (blockSize machine.tm) =>
        output[offset.val]?) := by
    funext offset
    rw [hblock, htrue' offset stack]
    by_cases hzero : offset.val = 0
    · simp only [hzero, ↓reduceIte, output]
    · have hout : output.length ≤ offset.val := by
        omega
      simp only [hzero, ↓reduceIte, not_lt, hout, getElem?_neg]
  change
    (List.ofFn (fun offset : Fin (blockSize machine.tm) =>
      cellAtomValue machine stack
        ((completeMachineBlock machine.tm cell offset).2.2.1 stack))).filterMap
        id = output
  rw [hpointwise, filterMap_ofFn_getElem]
  exact List.take_of_length_le (by
    have hpositive := blockSize_pos machine.tm
    omega)

private theorem finiteTM2_step_none_of_none_label
    (tm : Turing.FinTM2)
    (configuration : tm.Cfg)
    (hlabel : configuration.l = none) :
    tm.step configuration = none := by
  rcases configuration with ⟨label, machineState, machineStacks⟩
  cases label with
  | none => rfl
  | some label => simp only [reduceCtorEq] at hlabel

private theorem reachableHaltedPackedConfiguration_eq_actualVerifierHalt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (row : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hcertificate : certificate.length ≤ bound.eval x.length)
    (verifierRun : StateTransition.EvalsTo machine.tm.step
      (Turing.initList machine.tm
        (verifierInput machine x certificate))
      (some (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x) row)))
    (hcontrol : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (row 0)) =
        some
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).l,
            (Turing.haltList machine.tm
              (verifierOutput machine true)).var)) :
    decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x) row =
      Turing.haltList machine.tm
        (verifierOutput machine (verifier (x, certificate))) := by
  let actualHalt := boundedVerifierRun
    bound machine x certificate hcertificate
  have hlabel :
      (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x) row).l = none := by
    simp only [decodedFullPackedPhaseConfiguration, hcontrol, haltList, eq_mpr_eq_cast]
  have hterminal := finiteTM2_step_none_of_none_label machine.tm
    (decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x) row) hlabel
  have hsteps := evalsTo_prefix_steps_le_terminal
    machine.tm.step
    (Turing.initList machine.tm
      (verifierInput machine x certificate))
    (decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x) row)
    (Turing.haltList machine.tm
      (verifierOutput machine (verifier (x, certificate))))
    verifierRun actualHalt.toEvalsTo
    (haltList_step machine.tm
      (verifierOutput machine (verifier (x, certificate))))
  exact evalsTo_terminal_unique_of_steps_le machine.tm.step
    (Turing.initList machine.tm
      (verifierInput machine x certificate))
    (decodedFullPackedPhaseConfiguration machine
      (rowWidth bound machine x) row)
    (Turing.haltList machine.tm
      (verifierOutput machine (verifier (x, certificate))))
    verifierRun actualHalt.toEvalsTo hterminal hsteps

theorem trueOutputMachineHead_actualVerifierHalt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (row : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (hcertificate : certificate.length ≤ bound.eval x.length)
    (verifierRun : StateTransition.EvalsTo machine.tm.step
      (Turing.initList machine.tm
        (verifierInput machine x certificate))
      (some (decodedFullPackedPhaseConfiguration machine
        (rowWidth bound machine x) row)))
    (hrow : PhaseRowAtomsWellTyped machine
      (rowWidth bound machine x) row)
    (hholes : ∀ stack : machine.tm.K,
      NoInteriorPaddingHoles machine.tm
        (fullPackedPhaseStackAtoms machine
          (rowWidth bound machine x) row stack))
    (hfirst : completeIsFirstBlock machine.tm (row 0) = true)
    (hanchor : FirstBlockAnchored machine.tm (row 0))
    (htrue : TrueOutputMachineHead machine (row 0))
    (hcontrol : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (row 0)) =
        some
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).l,
            (Turing.haltList machine.tm
              (verifierOutput machine true)).var)) :
    verifier (x, certificate) = true ∧
      decodedFullPackedPhaseConfiguration machine
          (rowWidth bound machine x) row =
        Turing.haltList machine.tm
          (verifierOutput machine true) := by
  have hconfiguration :=
    reachableHaltedPackedConfiguration_eq_actualVerifierHalt
      bound machine x certificate row hcertificate verifierRun hcontrol
  have hheadBlock := trueOutputMachineHead_decodedAtomBlock
    machine (row 0) hfirst hanchor htrue machine.tm.k₁
  have hfullBlock := fullPackedPhaseStack_firstBlock_decode
    machine (rowWidth bound machine x) row hrow machine.tm.k₁
    (hholes machine.tm.k₁)
  have hactualStack :
      decodedFullPackedPhaseStack machine
          (rowWidth bound machine x) row machine.tm.k₁ =
        verifierOutput machine (verifier (x, certificate)) := by
    calc
      decodedFullPackedPhaseStack machine
          (rowWidth bound machine x) row machine.tm.k₁ =
          (decodedFullPackedPhaseConfiguration machine
            (rowWidth bound machine x) row).stk machine.tm.k₁ :=
        (decodedFullPackedPhaseConfiguration_stack machine
          (rowWidth bound machine x) row
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).l,
            (Turing.haltList machine.tm
              (verifierOutput machine true)).var)
          hcontrol machine.tm.k₁).symm
      _ = (Turing.haltList machine.tm
          (verifierOutput machine
            (verifier (x, certificate)))).stk machine.tm.k₁ :=
        congrArg (fun configuration : machine.tm.Cfg =>
          configuration.stk machine.tm.k₁) hconfiguration
      _ = verifierOutput machine (verifier (x, certificate)) :=
        GapCVP.TMComposition.haltList_stk_self
          machine.tm (verifierOutput machine
            (verifier (x, certificate)))
  have htake :
      (verifierOutput machine (verifier (x, certificate))).take
          (blockSize machine.tm) =
        verifierOutput machine true := by
    calc
      (verifierOutput machine (verifier (x, certificate))).take
          (blockSize machine.tm) =
          (decodedFullPackedPhaseStack machine
            (rowWidth bound machine x) row machine.tm.k₁).take
            (blockSize machine.tm) := by
        rw [hactualStack]
      _ = decodedAtomBlock machine machine.tm.k₁
          (stackAtomsOfBlock machine.tm
            (completeMachineBlock machine.tm (row 0))
            machine.tm.k₁) := hfullBlock.symm
      _ = (Turing.haltList machine.tm
            (verifierOutput machine true)).stk machine.tm.k₁ :=
        hheadBlock
      _ = verifierOutput machine true :=
        GapCVP.TMComposition.haltList_stk_self
          machine.tm (verifierOutput machine true)
  have hlength :
      (verifierOutput machine (verifier (x, certificate))).length ≤
        blockSize machine.tm := by
    rw [verifierOutput_length]
    exact blockSize_pos machine.tm
  have houtput :
      verifierOutput machine (verifier (x, certificate)) =
        verifierOutput machine true := by
    calc
      verifierOutput machine (verifier (x, certificate)) =
          (verifierOutput machine (verifier (x, certificate))).take
            (blockSize machine.tm) :=
        (List.take_of_length_le hlength).symm
      _ = verifierOutput machine true := htake
  have hverifier : verifier (x, certificate) = true :=
    verifierOutput_injective machine houtput
  exact ⟨hverifier, by simpa only [hverifier] using hconfiguration⟩

end CLAcceptanceAnchor

namespace CLVerifiedLocalTableauCompiler

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLFullTableauEmitter GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLPhaseVerifierSimulation GapCVP.CLArbitraryVerifierSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLAnchoredTraceSimulation
open GapCVP.CLGuessPayloadReachability GapCVP.CLAcceptanceAnchor

/-- GapCVP reduction support. -/
def canonicalAnchoredGuessingRow
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool) :
    Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm :=
  fun position => {
    mode := .guessing
    script := canonicalGuessingScriptRow machine
      (rowWidth bound machine x) certificate
      (defaultVerifierHint machine.tm) position
    payload := pairedInputBlockAt machine.tm
      (rowWidth bound machine x) x certificate position
    payloadHead := pairedInputBlockAt machine.tm
      (rowWidth bound machine x) x certificate 0
    range := phaseRangeBlockAt machine.tm
      (rowWidth bound machine x) position
    rangeHead := phaseRangeBlockAt machine.tm
      (rowWidth bound machine x) 0
    budget := phaseBudgetBlockAt bound machine x position
    guessBit := annotation
  }

@[simp] theorem canonicalAnchoredGuessingRow_initial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    canonicalAnchoredGuessingRow bound machine x [] false =
      initialPhaseCell bound machine x := by
  rfl

private theorem canonicalAnchoredGuessingRow_boundary
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    completeIsFirstBlock machine.tm
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation position) =
      decide (position.val = 0) := by
  rfl

private theorem canonicalAnchoredGuessingRow_firstBlockAnchored
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    FirstBlockAnchored machine.tm
      (canonicalAnchoredGuessingRow
        bound machine x certificate annotation position) := by
  simp only [FirstBlockAnchored, decide_eq_true_eq]
  intro hfirst
  have hposition : position.val = 0 := by
    simpa only [Fin.val_eq_zero_iff, completeIsFirstBlock, canonicalAnchoredGuessingRow,
        canonicalGuessingScriptRow, decide_eq_true_eq] using hfirst
  have hzero : position = 0 := Fin.ext hposition
  subst position
  exact ⟨rfl, rfl, rfl⟩

private theorem canonicalAnchoredGuessingWindow_replicatedMachineHeadCoherent
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (position : Position (rowWidth bound machine x)) :
    ReplicatedMachineHeadCoherent machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next position) := by
  simp only [ReplicatedMachineHeadCoherent, completeMachineHead, anchoredVerifierWindowAt,
      canonicalAnchoredGuessingRow, canonicalGuessingScriptRow, Fin.val_eq_zero_iff, and_self,
          decide_true]

@[simp] private theorem canonicalAnchoredGuessingRow_unpackWitness
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (index : Position (rowWidth bound machine x)) :
    unpackPhaseWitness machine.tm (rowWidth bound machine x)
      (canonicalAnchoredGuessingRow
        bound machine x certificate annotation) index =
      certificatePhase certificate index.val := by
  change
    (packRow machine.tm (rowWidth bound machine x)
      (guessingRow machine.tm
        (rowWidth bound machine x) certificate)
      (coordinateBlock machine.tm
        (rowWidth bound machine x) index)
      (coordinateOffset machine.tm
        (rowWidth bound machine x) index)).1 = _
  rw [packRow_cell]
  rfl

@[simp] private theorem canonicalAnchoredGuessingRow_unpackPayload
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (index : Position (rowWidth bound machine x)) :
    unpackPhasePayload machine.tm (rowWidth bound machine x)
      (canonicalAnchoredGuessingRow
        bound machine x certificate annotation) index =
      pairedInputTagAt x certificate index.val := by
  have hcoordinate :
      index.val / blockSize machine.tm * blockSize machine.tm +
        index.val % blockSize machine.tm = index.val :=
    Nat.div_add_mod' index.val (blockSize machine.tm)
  simp only [unpackPhasePayload, canonicalAnchoredGuessingRow, coordinateBlock, coordinateOffset,
      pairedInputBlockAt, hcoordinate, index.isLt, ↓reduceIte]

private theorem canonicalGuessingWitnessWindow_left
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (index : Position (rowWidth bound machine x)) :
    (completeWitnessWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next (coordinateBlock machine.tm
          (rowWidth bound machine x) index))
      (coordinateOffset machine.tm
        (rowWidth bound machine x) index)).1 =
      certificatePhase certificate
        (leftBlock (rowWidth bound machine x) index).val := by
  have hboundary := canonicalAnchoredGuessingRow_boundary
    bound machine x certificate annotation
    (coordinateBlock machine.tm
      (rowWidth bound machine x) index)
  rw [completeWitnessWindow_left_unpacked machine.tm
    (rowWidth bound machine x)
    (canonicalAnchoredGuessingRow
      bound machine x certificate annotation)
    next index hboundary]
  exact canonicalAnchoredGuessingRow_unpackWitness
    bound machine x certificate annotation
    (leftBlock (rowWidth bound machine x) index)

private theorem canonicalGuessingPayloadWindow_left
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (index : Position (rowWidth bound machine x)) :
    (completePayloadWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next (coordinateBlock machine.tm
          (rowWidth bound machine x) index))
      (coordinateOffset machine.tm
        (rowWidth bound machine x) index)).1 =
      pairedInputTagAt x certificate
        (leftBlock (rowWidth bound machine x) index).val := by
  have hboundary := canonicalAnchoredGuessingRow_boundary
    bound machine x certificate annotation
    (coordinateBlock machine.tm
      (rowWidth bound machine x) index)
  rw [completePayloadWindow_left_unpacked machine.tm
    (rowWidth bound machine x)
    (canonicalAnchoredGuessingRow
      bound machine x certificate annotation)
    next index hboundary]
  exact canonicalAnchoredGuessingRow_unpackPayload
    bound machine x certificate annotation
    (leftBlock (rowWidth bound machine x) index)

private theorem coordinateBlock_of_packed
    (tm : Turing.FinTM2)
    (width : ℕ)
    (position : Position width)
    (offset : Fin (blockSize tm))
    (hinrange : position.val * blockSize tm + offset.val < width + 1) :
    coordinateBlock tm width
        (⟨position.val * blockSize tm + offset.val, hinrange⟩ :
          Position width) = position := by
  apply Fin.ext
  change
    (position.val * blockSize tm + offset.val) /
      blockSize tm = position.val
  have hdivision := Nat.mul_add_div
    (blockSize_pos tm) position.val offset.val
  simpa only [Nat.mul_comm, Nat.div_eq_of_lt offset.isLt, add_zero] using hdivision

private theorem coordinateOffset_of_packed
    (tm : Turing.FinTM2)
    (width : ℕ)
    (position : Position width)
    (offset : Fin (blockSize tm))
    (hinrange : position.val * blockSize tm + offset.val < width + 1) :
    coordinateOffset tm width
        (⟨position.val * blockSize tm + offset.val, hinrange⟩ :
          Position width) = offset := by
  apply Fin.ext
  exact Nat.mul_add_mod_of_lt offset.isLt

private theorem nondeterministicRowWidth_pos
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    1 ≤ rowWidth bound machine x := by
  simp only [rowWidth, nondeterministicTableauDimensionPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  omega

private theorem actualStep_iff_acceptanceAnchoredCanonicalVerifierWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstSpace : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ rowWidth bound machine x)
    (hnextSpace : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ rowWidth bound machine x) :
    machine.tm.step first = some next ↔
      ∃ (firstHint nextHint : FiniteVerifierHint machine.tm),
        ∀ position : Position (rowWidth bound machine x),
          AcceptanceAnchoredPhaseAllowed machine
            (anchoredVerifierWindowAt machine.tm
              (rowWidth bound machine x)
              (canonicalAnchoredVerifyingRow
                bound machine x certificate
                first hfirst firstHint false)
              (canonicalAnchoredVerifyingRow
                bound machine x certificate
                next hnext nextHint false) position) := by
  constructor
  · intro hstep
    obtain ⟨firstHint, nextHint, hwindows⟩ :=
      (actualStep_iff_stackSoundCanonicalVerifierWindows
        bound machine x certificate first next hfirst hnext
        hfirstSpace hnextSpace).mp hstep
    refine ⟨firstHint, nextHint, ?_⟩
    intro position
    simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨hwindows position,
      canonicalAnchoredVerifyingWindow_replicatedMachineHeadCoherent
        bound machine x certificate first next hfirst hnext
        firstHint nextHint false false position, ?_⟩
    intro himpossible
    change PhaseTag.verifying = PhaseTag.accepting at himpossible
    cases himpossible
  · rintro ⟨firstHint, nextHint, hwindows⟩
    apply (actualStep_iff_stackSoundCanonicalVerifierWindows
      bound machine x certificate first next hfirst hnext
      hfirstSpace hnextSpace).mpr
    refine ⟨firstHint, nextHint, ?_⟩
    intro position
    have hwindow := hwindows position
    simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq] at hwindow
    exact hwindow.1

/-- GapCVP reduction support. -/
noncomputable def AllCanonicalAcceptanceAnchoredVerifierTraceWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    {steps : ℕ}
    (configuration : Fin (steps + 1) → machine.tm.Cfg)
    (hsupported : ∀ time : Fin (steps + 1),
      StackAtomSupported machine (configuration time))
    (hint : Fin (steps + 1) → FiniteVerifierHint machine.tm) : Bool :=
  @decide (
  ∀ (time : Fin steps)
    (position : Position (rowWidth bound machine x)),
    AcceptanceAnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          (configuration (Fin.castSucc time))
          (hsupported (Fin.castSucc time))
          (hint (Fin.castSucc time)) false)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          (configuration time.succ)
          (hsupported time.succ)
          (hint time.succ) false)
        position)
  ) (Classical.propDecidable _)
theorem canonicalAcceptanceAnchoredVerifierTraceWindows_iff_actualRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    {steps : ℕ}
    (configuration : Fin (steps + 1) → machine.tm.Cfg)
    (hsupported : ∀ time : Fin (steps + 1),
      StackAtomSupported machine (configuration time))
    (hspace : ∀ (time : Fin (steps + 1)) (stack : machine.tm.K),
      ((configuration time).stk stack).length ≤
        rowWidth bound machine x) :
    (∃ hint : Fin (steps + 1) → FiniteVerifierHint machine.tm,
      AllCanonicalAcceptanceAnchoredVerifierTraceWindows
        bound machine x certificate
        configuration hsupported hint) ↔
      ∀ time : Fin steps,
        machine.tm.step (configuration (Fin.castSucc time)) =
          some (configuration time.succ) := by
  constructor
  · rintro ⟨hint, hwindows⟩ time
    have hwindows' := hwindows
    simp only [AllCanonicalAcceptanceAnchoredVerifierTraceWindows,
      decide_eq_true_eq] at hwindows'
    apply (actualStep_iff_acceptanceAnchoredCanonicalVerifierWindows
      bound machine x certificate
      (configuration (Fin.castSucc time))
      (configuration time.succ)
      (hsupported (Fin.castSucc time))
      (hsupported time.succ)
      (hspace (Fin.castSucc time))
      (hspace time.succ)).mpr
    exact ⟨hint (Fin.castSucc time),
      hint time.succ, hwindows' time⟩
  · intro hrun
    obtain ⟨hint, hanchored⟩ :=
      (canonicalAnchoredVerifierTraceWindows_iff_actualRun
        bound machine x certificate
        configuration hsupported hspace).mpr hrun
    have hanchored' := hanchored
    simp only [AllCanonicalAnchoredVerifierTraceWindows,
      decide_eq_true_eq] at hanchored'
    refine ⟨hint, ?_⟩
    simp only [AllCanonicalAcceptanceAnchoredVerifierTraceWindows,
      decide_eq_true_eq]
    intro time position
    let first := configuration (Fin.castSucc time)
    let next := configuration time.succ
    let firstSupport := hsupported (Fin.castSucc time)
    let nextSupport := hsupported time.succ
    let firstHint := hint (Fin.castSucc time)
    let nextHint := hint time.succ
    let window := anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x)
      (canonicalAnchoredVerifyingRow
        bound machine x certificate
        first firstSupport firstHint false)
      (canonicalAnchoredVerifyingRow
        bound machine x certificate
        next nextSupport nextHint false)
      position
    have hscriptWindows :
        ∀ other : Position (rowWidth bound machine x),
          scriptBlockAllowed machine
            (scriptBlockWindowAt machine.tm
              (rowWidth bound machine x)
              (canonicalScriptBlockRow machine
                (rowWidth bound machine x)
                certificate first firstSupport firstHint)
              (canonicalScriptBlockRow machine
                (rowWidth bound machine x)
                certificate next nextSupport nextHint)
              other) = true := by
      intro other
      exact (canonicalAnchoredVerifierWindow_allowed_iff
        bound machine x certificate first next
        firstSupport nextSupport firstHint nextHint
        false other).mp (hanchored' time other)
    obtain ⟨hscript, hstackWindows⟩ :=
      (canonicalScriptBlockWindows_iff
        machine (rowWidth bound machine x)
        certificate first next firstSupport nextSupport
        (hspace (Fin.castSucc time))
        (hspace time.succ)
        firstHint nextHint).mp hscriptWindows
    have hoccupied := canonicalVerifierScriptHints_occupied
      machine (rowWidth bound machine x)
      first next firstSupport nextSupport
      firstHint hscript hstackWindows
    have hold : AnchoredPhaseAllowed machine window :=
      hanchored' time position
    have hold' := hold
    simp only [AnchoredPhaseAllowed, decide_eq_true_eq] at hold'
    have hverify := anchoredPhase_verification_of_verifying_modes
      machine window hold rfl rfl
    have hstack : StackSoundAnchoredPhaseAllowed machine window := by
      simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
      refine ⟨hold'.1, ?_⟩
      change
        StackSoundAnchoredVerificationAllowed machine window ∨
          AnchoredAcceptanceAllowed machine window
      apply Or.inl
      simp only [StackSoundAnchoredVerificationAllowed,
        decide_eq_true_eq]
      exact ⟨hverify, hoccupied⟩
    simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨hstack,
      canonicalAnchoredVerifyingWindow_replicatedMachineHeadCoherent
        bound machine x certificate first next
        firstSupport nextSupport firstHint nextHint
        false false position, ?_⟩
    intro himpossible
    change PhaseTag.verifying = PhaseTag.accepting at himpossible
    cases himpossible

private theorem canonicalTrueHalt_acceptingPhaseBlock
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.haltList machine.tm
        (verifierOutput machine true)))
    (hint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (position : Position (rowWidth bound machine x)) :
    AcceptingPhaseBlock machine
      (canonicalAnchoredVerifyingRow bound machine x certificate
        (Turing.haltList machine.tm
          (verifierOutput machine true))
        hsupported hint annotation position) := by
  simp only [AcceptingPhaseBlock, decide_eq_true_eq]
  let configuration := Turing.haltList machine.tm
    (verifierOutput machine true)
  have hwidth := nondeterministicRowWidth_pos bound machine x
  have hspace : ∀ stack : machine.tm.K,
      (configuration.stk stack).length ≤ rowWidth bound machine x := by
    intro stack
    exact (verifierHalt_stack_length_le_one
      machine true stack).trans hwidth
  constructor
  · change
      machineControlOfBlock machine.tm
        (packRow machine.tm (rowWidth bound machine x)
          (canonicalVerifyingRow machine
            (rowWidth bound machine x)
            certificate configuration hsupported) 0) = _
    exact machineControlOfBlock_pack_canonical machine
      (rowWidth bound machine x)
      certificate configuration hsupported
  · intro offset stack
    rw [canonicalAnchoredVerifyingRow_blockAtom_decode
      bound machine x certificate configuration hsupported hspace
      hint annotation position offset stack]
    change
      (configuration.stk stack)[
        position.val * blockSize machine.tm + offset.val]? =
        if decide (position.val = 0) = true ∧
          offset.val = 0 then
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).stk stack)[0]?
        else none
    by_cases hposition : position.val = 0
    · have hzero : position = 0 := Fin.ext hposition
      subst position
      by_cases hoffset : offset.val = 0
      · simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul, hoffset, add_zero, decide_true,
          and_self, ↓reduceIte,
            configuration]
      · have hlength := verifierHalt_stack_length_le_one
          machine true stack
        have hout :
            (configuration.stk stack).length ≤ offset.val := by
          change
            ((Turing.haltList machine.tm
              (verifierOutput machine true)).stk stack).length ≤ _
          omega
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul, zero_add, not_lt, hout,
            getElem?_neg, decide_true,
            hoffset, and_false, ↓reduceIte]
    · have hproduct :
          0 < position.val * blockSize machine.tm :=
        Nat.mul_pos (Nat.pos_of_ne_zero hposition)
          (blockSize_pos machine.tm)
      have hlength := verifierHalt_stack_length_le_one
        machine true stack
      have hout :
          (configuration.stk stack).length ≤
            position.val * blockSize machine.tm + offset.val := by
        change
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).stk stack).length ≤ _
        omega
      simp only [not_lt, hout, getElem?_neg, hposition, decide_false, Bool.false_eq_true,
          false_and, ↓reduceIte]

theorem canonicalTrueHalt_acceptanceAnchoredWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.haltList machine.tm
        (verifierOutput machine true)))
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    AcceptanceAnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          (Turing.haltList machine.tm
            (verifierOutput machine true))
          hsupported hint false)
        (fun _ => acceptingPhaseCell machine.tm)
        position) := by
  let first := canonicalAnchoredVerifyingRow
    bound machine x certificate
    (Turing.haltList machine.tm
      (verifierOutput machine true))
    hsupported hint false
  let next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm :=
    fun _ => acceptingPhaseCell machine.tm
  let window := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x) first next position
  have hcoherent : CompletePhaseCoherent machine.tm window := by
    simp only [CompletePhaseCoherent, anchoredVerifierWindowAt, canonicalAnchoredVerifyingRow,
        and_self,
        decide_true, window, first]
  have hhead : ReplicatedMachineHeadCoherent machine.tm window := by
    simp only [ReplicatedMachineHeadCoherent, completeMachineHead, anchoredVerifierWindowAt,
        canonicalAnchoredVerifyingRow, canonicalScriptBlockRow, Fin.val_eq_zero_iff, and_self,
            decide_true, window, first]
  have haccept : AnchoredAcceptanceAllowed machine window := by
    apply @decide_eq_true _ (Classical.propDecidable _)
    refine ⟨?_, canonicalAnchoredVerifyingRow_firstBlockAnchored
      bound machine x certificate
      (Turing.haltList machine.tm
        (verifierOutput machine true))
      hsupported hint false position⟩
    apply @decide_eq_true _ (Classical.propDecidable _)
    exact ⟨rfl, canonicalTrueHalt_acceptingPhaseBlock
      bound machine x certificate hsupported hint false position⟩
  have hstack : StackSoundAnchoredPhaseAllowed machine window := by
    simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨hcoherent, ?_⟩
    change
      StackSoundAnchoredVerificationAllowed machine window ∨
        AnchoredAcceptanceAllowed machine window
    exact Or.inr haccept
  simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq]
  refine ⟨hstack, hhead, ?_⟩
  intro _
  exact canonicalTrueHalt_trueOutputMachineHead
    bound machine x certificate hsupported hint false
    (nondeterministicRowWidth_pos bound machine x) position

end CLVerifiedLocalTableauCompiler

namespace CLFinalTableauAssembly

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactLocalRules GapCVP.CLExactStackRules GapCVP.CLFiniteShiftWindows
open GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLStackVerifierSimulation GapCVP.CLGuessPayloadReachability
open GapCVP.CLReachableTableauCompiler GapCVP.CLAcceptanceAnchor
open GapCVP.CLVerifiedLocalTableauCompiler

private theorem canonicalGuessingWitnessWindow_center
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) :
    (completeWitnessWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next position) offset).2.1 =
      certificatePhase certificate
        (position.val * blockSize machine.tm + offset.val) := by
  simp only [completeWitnessWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
      canonicalGuessingScriptRow, Fin.val_eq_zero_iff, completeMachineBlock, packRow,
          Order.lt_add_one_iff, guessingRow,
      dite_eq_ite, hinrange, ↓reduceDIte]

private theorem canonicalGuessingWitnessWindow_next
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) :
    (completeWitnessWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredGuessingRow
          bound machine x (certificate ++ [bit]) bit)
        position) offset).2.2.2 =
      certificatePhase (certificate ++ [bit])
        (position.val * blockSize machine.tm + offset.val) := by
  simp only [completeWitnessWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
      canonicalGuessingScriptRow, Fin.val_eq_zero_iff, completeMachineBlock, packRow,
          Order.lt_add_one_iff, guessingRow,
      dite_eq_ite, hinrange, ↓reduceDIte]

private theorem canonicalGuessingPayloadWindow_center
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) :
    (completePayloadWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next position) offset).2.1 =
      pairedInputTagAt x certificate
        (position.val * blockSize machine.tm + offset.val) := by
  simp only [completePayloadWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
      pairedInputBlockAt,
      hinrange, ↓reduceIte]

private theorem canonicalGuessingPayloadWindow_next
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) :
    (completePayloadWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredGuessingRow
          bound machine x (certificate ++ [bit]) bit)
        position) offset).2.2.2 =
      pairedInputTagAt x (certificate ++ [bit])
        (position.val * blockSize machine.tm + offset.val) := by
  simp only [completePayloadWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
      pairedInputBlockAt,
      hinrange, ↓reduceIte]

private theorem canonicalGuessingWitnessWindow_right
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hnext : position.val * blockSize machine.tm + offset.val + 1 <
      rowWidth bound machine x + 1) :
    (completeWitnessWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next position) offset).2.2.1 =
      certificatePhase certificate
        (position.val * blockSize machine.tm + offset.val + 1) := by
  by_cases hoffset : offset.val + 1 < blockSize machine.tm
  · have hinrange :
        position.val * blockSize machine.tm + (offset.val + 1) <
          rowWidth bound machine x + 1 := by
      omega
    simp only [completeWitnessWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
        canonicalGuessingScriptRow, Fin.val_eq_zero_iff, completeMachineBlock, packRow,
            Order.lt_add_one_iff, guessingRow,
        dite_eq_ite, phaseRightOffset, hoffset, ↓reduceDIte, hinrange, Nat.add_assoc]
  · have hoffsetLast : offset.val + 1 = blockSize machine.tm := by
      have hlt := offset.isLt
      omega
    have hmul : position.val ≤
        position.val * blockSize machine.tm :=
      Nat.le_mul_of_pos_right position.val
        (blockSize_pos machine.tm)
    have hright : position.val + 1 ≤
        rowWidth bound machine x := by
      omega
    have hrightVal :
        (rightBlock (rowWidth bound machine x) position).val =
          position.val + 1 := by
      exact Nat.min_eq_left hright
    have hpacked :
        position.val * blockSize machine.tm +
          blockSize machine.tm ≤ rowWidth bound machine x := by
      omega
    simp only [completeWitnessWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
        canonicalGuessingScriptRow, Fin.val_eq_zero_iff, hrightVal, Nat.add_eq_zero_iff,
            one_ne_zero, and_false,
        decide_false, completeMachineBlock, packRow, Order.lt_add_one_iff, guessingRow,
            dite_eq_ite, phaseRightOffset,
        hoffsetLast, lt_self_iff_false, ↓reduceDIte, Nat.add_mul, one_mul, add_zero, hpacked,
            Nat.add_assoc]

private theorem canonicalGuessingPayloadWindow_right
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (annotation : Bool)
    (next : Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hnext : position.val * blockSize machine.tm + offset.val + 1 <
      rowWidth bound machine x + 1) :
    (completePayloadWindow machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate annotation)
        next position) offset).2.2.1 =
      pairedInputTagAt x certificate
        (position.val * blockSize machine.tm + offset.val + 1) := by
  by_cases hoffset : offset.val + 1 < blockSize machine.tm
  · have hinrange :
        position.val * blockSize machine.tm + (offset.val + 1) <
          rowWidth bound machine x + 1 := by
      omega
    simp only [completePayloadWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
        pairedInputBlockAt,
        Order.lt_add_one_iff, phaseRightOffset, hoffset, ↓reduceDIte, hinrange, ↓reduceIte,
            Nat.add_assoc]
  · have hoffsetLast : offset.val + 1 = blockSize machine.tm := by
      have hlt := offset.isLt
      omega
    have hmul : position.val ≤
        position.val * blockSize machine.tm :=
      Nat.le_mul_of_pos_right position.val
        (blockSize_pos machine.tm)
    have hright : position.val + 1 ≤
        rowWidth bound machine x := by
      omega
    have hrightVal :
        (rightBlock (rowWidth bound machine x) position).val =
          position.val + 1 := by
      exact Nat.min_eq_left hright
    have hpacked :
        position.val * blockSize machine.tm +
          blockSize machine.tm ≤ rowWidth bound machine x := by
      omega
    simp only [completePayloadWindow, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
        pairedInputBlockAt,
        Order.lt_add_one_iff, phaseRightOffset, hoffsetLast, lt_self_iff_false, ↓reduceDIte,
            hrightVal, Nat.add_mul,
        one_mul, add_zero, hpacked, ↓reduceIte, Nat.add_assoc]

private theorem canonicalGuessingWitnessWindow_broadcast
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (hbound : certificate.length < bound.eval x.length)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) :
    BroadcastWitnessGuessAllowed bit
      (completeWitnessWindow machine.tm
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x)
          (canonicalAnchoredGuessingRow
            bound machine x certificate oldAnnotation)
          (canonicalAnchoredGuessingRow
            bound machine x (certificate ++ [bit]) bit)
          position) offset) := by
  let width := rowWidth bound machine x
  let first := canonicalAnchoredGuessingRow
    bound machine x certificate oldAnnotation
  let next := canonicalAnchoredGuessingRow
    bound machine x (certificate ++ [bit]) bit
  let index : Position width :=
    ⟨position.val * blockSize machine.tm + offset.val, hinrange⟩
  let window := completeWitnessWindow machine.tm
    (anchoredVerifierWindowAt machine.tm width first next position)
    offset
  have hblock := coordinateBlock_of_packed machine.tm width
    position offset hinrange
  have hoffset := coordinateOffset_of_packed machine.tm width
    position offset hinrange
  have hleft := canonicalGuessingWitnessWindow_left
    bound machine x certificate oldAnnotation next index
  rw [hblock, hoffset] at hleft
  have hcenter := canonicalGuessingWitnessWindow_center
    bound machine x certificate oldAnnotation next
    position offset hinrange
  have hnext := canonicalGuessingWitnessWindow_next
    bound machine x certificate oldAnnotation bit
    position offset hinrange
  have hspace : certificate.length < width :=
    hbound.trans_le (certificateBound_le_rowWidth
      bound machine x)
  have hcanonical := guessPhaseWindow_of_append
    width certificate bit hspace index
  simp only [GuessPhaseAllowed, decide_eq_true_eq] at hcanonical
  have hphase : GuessPhaseAllowed window := by
    simp only [GuessPhaseAllowed, decide_eq_true_eq]
    rcases hcanonical with hwrite | hrest
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact hcenter.trans hwrite.1
      · have hmarker : index.val = certificate.length :=
          (certificatePhase_accepting_iff
            certificate index.val).mp hwrite.1
        have hrightInRange :
            position.val * blockSize machine.tm +
              offset.val + 1 < width + 1 := by
          change position.val * blockSize machine.tm +
            offset.val = certificate.length at hmarker
          omega
        rw [canonicalGuessingWitnessWindow_right
          bound machine x certificate oldAnnotation next
          position offset hrightInRange]
        change
          certificatePhase certificate
            (position.val * blockSize machine.tm +
              offset.val + 1) = .guessing
        apply certificatePhase_after
        change position.val * blockSize machine.tm +
          offset.val = certificate.length at hmarker
        omega
      · rcases hwrite.2.2 with hguessing | hverifying
        · exact Or.inl (hnext.trans hguessing)
        · exact Or.inr (hnext.trans hverifying)
    · rcases hrest with hmarker | hunchanged
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · intro himpossible
          exact hmarker.1 (hcenter.symm.trans himpossible)
        · exact hleft.trans hmarker.2.1
        · exact hnext.trans hmarker.2.2
      · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
        · intro himpossible
          exact hunchanged.1 (hcenter.symm.trans himpossible)
        · intro himpossible
          exact hunchanged.2.1 (hleft.symm.trans himpossible)
        · exact hnext.trans
            (hunchanged.2.2.trans hcenter.symm)
  simp only [BroadcastWitnessGuessAllowed, decide_eq_true_eq]
  refine ⟨hphase, ?_⟩
  intro hmarker
  have hindex : index.val = certificate.length :=
    (certificatePhase_accepting_iff
      certificate index.val).mp (hcenter.symm.trans hmarker)
  rw [hnext]
  change
    certificatePhase (certificate ++ [bit]) index.val =
      if bit then PhaseTag.verifying else PhaseTag.guessing
  rw [hindex, certificatePhase_append_old_marker]

private theorem canonicalGuessingPayloadWindow_append
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (hbound : certificate.length < bound.eval x.length)
    (position : Position (rowWidth bound machine x))
    (offset : Fin (blockSize machine.tm))
    (hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) :
    PairedInputGuessAllowed bit
      (completePayloadWindow machine.tm
        (anchoredVerifierWindowAt machine.tm
          (rowWidth bound machine x)
          (canonicalAnchoredGuessingRow
            bound machine x certificate oldAnnotation)
          (canonicalAnchoredGuessingRow
            bound machine x (certificate ++ [bit]) bit)
          position) offset) := by
  let width := rowWidth bound machine x
  let first := canonicalAnchoredGuessingRow
    bound machine x certificate oldAnnotation
  let next := canonicalAnchoredGuessingRow
    bound machine x (certificate ++ [bit]) bit
  let index : Position width :=
    ⟨position.val * blockSize machine.tm + offset.val, hinrange⟩
  let window := completePayloadWindow machine.tm
    (anchoredVerifierWindowAt machine.tm width first next position)
    offset
  have hblock := coordinateBlock_of_packed machine.tm width
    position offset hinrange
  have hoffset := coordinateOffset_of_packed machine.tm width
    position offset hinrange
  have hleft := canonicalGuessingPayloadWindow_left
    bound machine x certificate oldAnnotation next index
  rw [hblock, hoffset] at hleft
  have hcenter := canonicalGuessingPayloadWindow_center
    bound machine x certificate oldAnnotation next
    position offset hinrange
  have hnext := canonicalGuessingPayloadWindow_next
    bound machine x certificate oldAnnotation bit
    position offset hinrange
  have hcanonical := pairedInputGuessAllowed_of_append
    x certificate bit index.val
  simp only [PairedInputGuessAllowed, decide_eq_true_eq] at hcanonical ⊢
  rcases hcanonical with hwrite | hrest
  · refine Or.inl ⟨hcenter.trans hwrite.1, ?_,
      hnext.trans hwrite.2.2⟩
    have hmarker : index.val = x.length + certificate.length :=
      (pairedInputTagAt_marker_iff
        x certificate index.val).mp hwrite.1
    have hbudget := pairedCertificateBound_le_rowWidth
      bound machine x
    have hrightInRange :
        position.val * blockSize machine.tm +
          offset.val + 1 < width + 1 := by
      change position.val * blockSize machine.tm +
        offset.val = x.length + certificate.length at hmarker
      omega
    rw [canonicalGuessingPayloadWindow_right
      bound machine x certificate oldAnnotation next
      position offset hrightInRange]
    exact hwrite.2.1
  · rcases hrest with hmarker | hunchanged
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · intro himpossible
        exact hmarker.1 (hcenter.symm.trans himpossible)
      · exact hleft.trans hmarker.2.1
      · exact hnext.trans hmarker.2.2
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · intro himpossible
        exact hunchanged.1 (hcenter.symm.trans himpossible)
      · intro himpossible
        exact hunchanged.2.1 (hleft.symm.trans himpossible)
      · exact hnext.trans
          (hunchanged.2.2.trans hcenter.symm)

private theorem canonicalGuessingStep_correctedWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (hbound : certificate.length < bound.eval x.length)
    (position : Position (rowWidth bound machine x)) :
    CorrectedGuessingAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredGuessingRow
          bound machine x (certificate ++ [bit]) bit)
        position) := by
  simp only [CorrectedGuessingAllowed, decide_eq_true_eq]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro offset hrange
  have hinrange :
      position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1 := by
    change
      decide (position.val * blockSize machine.tm + offset.val <
        rowWidth bound machine x + 1) = true at hrange
    exact of_decide_eq_true hrange
  refine ⟨canonicalGuessingWitnessWindow_broadcast
      bound machine x certificate oldAnnotation bit hbound
      position offset hinrange,
    canonicalGuessingPayloadWindow_append
      bound machine x certificate oldAnnotation bit hbound
      position offset hinrange, ?_⟩
  intro hmarker
  have hcenter := canonicalGuessingPayloadWindow_center
    bound machine x certificate oldAnnotation
    (canonicalAnchoredGuessingRow
      bound machine x (certificate ++ [bit]) bit)
    position offset hinrange
  have hindex :
      position.val * blockSize machine.tm + offset.val =
        x.length + certificate.length :=
    (pairedInputTagAt_marker_iff x certificate _).mp
      (hcenter.symm.trans hmarker)
  change
    decide (position.val * blockSize machine.tm + offset.val <
      x.length + bound.eval x.length) = true
  apply decide_eq_true
  omega

theorem canonicalGuessingStep_acceptanceAnchoredWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (hbound : certificate.length < bound.eval x.length)
    (position : Position (rowWidth bound machine x)) :
    AcceptanceAnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredGuessingRow
          bound machine x (certificate ++ [bit]) bit)
        position) := by
  let first := canonicalAnchoredGuessingRow
    bound machine x certificate oldAnnotation
  let next := canonicalAnchoredGuessingRow
    bound machine x (certificate ++ [bit]) bit
  let window := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x) first next position
  have hcoherent : CompletePhaseCoherent machine.tm window := by
    simp only [CompletePhaseCoherent, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
        and_self,
        decide_true, window, first]
  have hboundary : PhaseBoundaryPreserved machine.tm window := by
    simp only [PhaseBoundaryPreserved, completeIsFirstBlock, anchoredVerifierWindowAt,
        canonicalAnchoredGuessingRow, canonicalGuessingScriptRow, Fin.val_eq_zero_iff, decide_true,
            window, first, next]
  have hguess : AnchoredGuessingAllowed machine window := by
    simp only [AnchoredGuessingAllowed, decide_eq_true_eq]
    refine ⟨canonicalGuessingStep_correctedWindows
      bound machine x certificate oldAnnotation bit hbound position,
      hboundary, ?_, ?_⟩
    · exact canonicalAnchoredGuessingRow_firstBlockAnchored
        bound machine x certificate oldAnnotation position
    · exact canonicalAnchoredGuessingRow_firstBlockAnchored
        bound machine x (certificate ++ [bit]) bit position
  have hstack : StackSoundAnchoredPhaseAllowed machine window := by
    simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨hcoherent, ?_⟩
    change
      AnchoredGuessingAllowed machine window ∨
        AnchoredInitializationAllowed machine window
    exact Or.inl hguess
  simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq]
  refine ⟨hstack,
    canonicalAnchoredGuessingWindow_replicatedMachineHeadCoherent
      bound machine x certificate oldAnnotation next position, ?_⟩
  intro himpossible
  change PhaseTag.guessing = PhaseTag.accepting at himpossible
  cases himpossible

private theorem canonicalCellAtom_eq_of_value_eq
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (first next : machine.tm.Γ stack)
    (hfirst : SupportedStackValue machine stack first)
    (hnext : SupportedStackValue machine stack next)
    (hvalue : first = next) :
    canonicalCellAtom machine stack first hfirst =
      canonicalCellAtom machine stack next hnext := by
  subst next
  rfl

private theorem paddedCanonicalStackAtoms_get
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value)
    (index : Fin values.length) :
    paddedAtom
        (canonicalStackAtoms machine stack values hsupported)
        index.val =
      canonicalCellAtom machine stack (values.get index)
        (hsupported (values.get index) (List.get_mem values index)) := by
  simp only [paddedAtom, canonicalStackAtoms, List.length_pmap, Fin.is_lt, getElem?_pos,
      List.getElem_pmap,
      Option.getD_some, List.get_eq_getElem]

private theorem canonicalInitialStackAtom_eq_initialPairedAtom
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)))
    (stack : machine.tm.K)
    (index : ℕ) :
    paddedAtom
        (canonicalStackAtoms machine stack
          ((Turing.initList machine.tm
            (verifierInput machine x certificate)).stk stack)
          (stackAtomSupported_supportedValues machine _ hsupported stack)) index =
      initialPairedAtom machine stack
        (pairedInputTagAt x certificate index) := by
  classical
  by_cases hstack : stack = machine.tm.k₀
  · subst stack
    by_cases hinside : index <
        (verifierInput machine x certificate).length
    · have hstackInside :
          index <
            ((Turing.initList machine.tm
              (verifierInput machine x certificate)).stk
              machine.tm.k₀).length := by
        simpa only [initList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq, verifierInput_length]
            using hinside
      let entryIndex : Fin
          ((Turing.initList machine.tm
            (verifierInput machine x certificate)).stk
            machine.tm.k₀).length := ⟨index, hstackInside⟩
      have hatom := paddedCanonicalStackAtoms_get
        machine machine.tm.k₀
        ((Turing.initList machine.tm
          (verifierInput machine x certificate)).stk
          machine.tm.k₀)
        (stackAtomSupported_supportedValues machine _ hsupported
          machine.tm.k₀) entryIndex
      have hpairInside : index <
          (pairBitEncoding (x, certificate)).length := by
        simpa only [pairBitEncoding_apply, List.length_append, List.length_map, verifierInput,
            Equiv.invFun_as_coe,
            List.map_append, List.map_map] using hinside
      have htag :
          pairedInputTagAt x certificate index =
            .bit ((pairBitEncoding (x, certificate))[index]) := by
        unfold pairedInputTagAt
        rw [List.getElem?_eq_getElem hpairInside]
      have hvalueOptional :
          ((Turing.initList machine.tm
            (verifierInput machine x certificate)).stk
            machine.tm.k₀)[index]? =
          some (machine.inputAlphabet.invFun
            ((pairBitEncoding (x, certificate))[index])) := by
        rw [show (Turing.initList machine.tm
            (verifierInput machine x certificate)).stk
              machine.tm.k₀ =
            verifierInput machine x certificate by
              simp only [initList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq]]
        unfold verifierInput
        rw [List.getElem?_map,
          List.getElem?_eq_getElem hpairInside]
        rfl
      have hvalue :
          ((Turing.initList machine.tm
            (verifierInput machine x certificate)).stk
            machine.tm.k₀).get entryIndex =
          machine.inputAlphabet.invFun
            ((pairBitEncoding (x, certificate))[index]) := by
        apply Option.some.inj
        calc
          some (((Turing.initList machine.tm
              (verifierInput machine x certificate)).stk
              machine.tm.k₀).get entryIndex) =
              ((Turing.initList machine.tm
                (verifierInput machine x certificate)).stk
                machine.tm.k₀)[index]? := by
            simp only [List.get_eq_getElem, hstackInside, getElem?_pos, entryIndex]
          _ = some (machine.inputAlphabet.invFun
                ((pairBitEncoding (x, certificate))[index])) :=
            hvalueOptional
      have hcanonical :
          paddedAtom
              (canonicalStackAtoms machine machine.tm.k₀
                ((Turing.initList machine.tm
                  (verifierInput machine x certificate)).stk
                  machine.tm.k₀)
                (stackAtomSupported_supportedValues machine _ hsupported
          machine.tm.k₀)) index =
            canonicalCellAtom machine machine.tm.k₀
              (((Turing.initList machine.tm
                (verifierInput machine x certificate)).stk
                machine.tm.k₀).get entryIndex)
              (stackAtomSupported_supportedValues machine _ hsupported
                machine.tm.k₀ _
                (List.get_mem _ entryIndex)) := by
        simpa only [List.get_eq_getElem] using hatom
      rw [htag]
      rw [hcanonical]
      simp only [initialPairedAtom]
      exact canonicalCellAtom_eq_of_value_eq
        machine machine.tm.k₀ _ _ _
        (hvalue ▸ stackAtomSupported_supportedValues machine _ hsupported
          machine.tm.k₀ _ (List.get_mem _ entryIndex)) hvalue
    · have hlength :
          (canonicalStackAtoms machine machine.tm.k₀
            ((Turing.initList machine.tm
              (verifierInput machine x certificate)).stk
              machine.tm.k₀)
            (stackAtomSupported_supportedValues machine _ hsupported
          machine.tm.k₀)).length ≤ index := by
        rw [canonicalStackAtoms_length]
        simpa only [initList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq, verifierInput_length] using
            (Nat.le_of_not_gt hinside)
      rw [paddedAtom_none_of_length_le
        machine.tm _ index hlength]
      symm
      apply (initialPairedAtom_pairedInput_blank_iff
        machine x certificate index).mpr
      simpa only [pairBitEncoding_apply, List.length_append, List.length_map, verifierInput,
          Equiv.invFun_as_coe,
          List.map_append, List.map_map] using (Nat.le_of_not_gt hinside)
  · have hblank :
        ((Turing.initList machine.tm
          (verifierInput machine x certificate)).stk stack).length =
          0 := by
      simp only [initList, eq_mpr_eq_cast, hstack, ↓reduceDIte, List.length_nil]
    have hlength :
        (canonicalStackAtoms machine stack
          ((Turing.initList machine.tm
            (verifierInput machine x certificate)).stk stack)
          (stackAtomSupported_supportedValues machine _ hsupported stack)).length ≤ index := by
      rw [canonicalStackAtoms_length, hblank]
      exact Nat.zero_le index
    rw [paddedAtom_none_of_length_le
      machine.tm _ index hlength]
    exact (initialPairedAtom_private_blank
      machine stack hstack
      (pairedInputTagAt x certificate index)).symm

private theorem canonicalInitialMachineBlock_eq_initializedPhaseBlock
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)))
    (oldAnnotation : Bool)
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    completeMachineBlock machine.tm
        (canonicalAnchoredVerifyingRow
          bound machine x certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          hsupported hint false position) =
      initializedPhaseBlock machine
        (completeMachineBlock machine.tm
          (canonicalAnchoredGuessingRow
            bound machine x certificate oldAnnotation position))
        ((canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation position).payload)
        ((canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation position).range) := by
  funext offset
  let index := position.val * blockSize machine.tm + offset.val
  by_cases hinrange : index < rowWidth bound machine x + 1
  · have hatoms :
        (fun stack : machine.tm.K =>
          paddedAtom
            (canonicalStackAtoms machine stack
              ((Turing.initList machine.tm
                (verifierInput machine x certificate)).stk stack)
              (stackAtomSupported_supportedValues machine _ hsupported stack)) index) =
        (fun stack : machine.tm.K =>
          initialPairedAtom machine stack
            (pairedInputTagAt x certificate index)) := by
      funext stack
      exact canonicalInitialStackAtom_eq_initialPairedAtom
        machine x certificate hsupported stack index
    have hcontrol :
        configurationControl machine.tm
          (Turing.initList machine.tm
            (verifierInput machine x certificate)) =
          configurationControl machine.tm
            (Turing.initList machine.tm []) := by
      simp only [configurationControl, initList, eq_mpr_eq_cast, Option.getD_some]
    have hlabel :
        (Turing.initList machine.tm
          (verifierInput machine x certificate)).l.isSome =
          (Turing.initList machine.tm []).l.isSome := by
      simp only [initList, eq_mpr_eq_cast, Option.isSome_some]
    simp only [completeMachineBlock, canonicalAnchoredVerifyingRow, canonicalScriptBlockRow,
        Fin.val_eq_zero_iff,
        packRow, hinrange, ↓reduceDIte, canonicalVerifyingRow, hcontrol, hatoms, hlabel,
            initializedPhaseBlock,
        canonicalAnchoredGuessingRow, canonicalGuessingScriptRow, phaseRangeBlockAt, decide_true,
            ↓reduceIte, guessingRow,
        pairedInputBlockAt, index]
  · simp only [completeMachineBlock, canonicalAnchoredVerifyingRow, canonicalScriptBlockRow,
      Fin.val_eq_zero_iff,
        packRow, hinrange, ↓reduceDIte, initializedPhaseBlock, canonicalAnchoredGuessingRow,
            canonicalGuessingScriptRow,
        phaseRangeBlockAt, decide_false, Bool.false_eq_true, ↓reduceIte, index]

private theorem canonicalInitialMachineHead_eq_initializedPhaseBlock
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)))
    (oldAnnotation : Bool)
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    completeMachineHead machine.tm
        (canonicalAnchoredVerifyingRow
          bound machine x certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          hsupported hint false position) =
      initializedPhaseBlock machine
        (completeMachineHead machine.tm
          (canonicalAnchoredGuessingRow
            bound machine x certificate oldAnnotation position))
        ((canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation position).payloadHead)
        ((canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation position).rangeHead) := by
  have hzero := canonicalInitialMachineBlock_eq_initializedPhaseBlock
    bound machine x certificate hsupported oldAnnotation hint 0
  simpa only [completeMachineHead, canonicalAnchoredVerifyingRow, canonicalScriptBlockRow,
      Fin.val_eq_zero_iff,
      canonicalAnchoredGuessingRow, canonicalGuessingScriptRow, completeMachineBlock,
          Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      decide_true] using hzero

private theorem canonicalInitialization_staticTracks
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)))
    (oldAnnotation : Bool)
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    CompleteStaticTracksPreserved machine.tm
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredVerifyingRow
          bound machine x certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          hsupported hint false)
        position) := by
  simp only [CompleteStaticTracksPreserved, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
      canonicalGuessingScriptRow, Fin.val_eq_zero_iff, canonicalAnchoredVerifyingRow,
          canonicalScriptBlockRow,
      completeIsFirstBlock, and_self, decide_true]

private theorem canonicalInitialization_anchoredWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)))
    (oldAnnotation : Bool)
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    AnchoredInitializationAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredVerifyingRow
          bound machine x certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          hsupported hint false)
        position) := by
  apply @decide_eq_true _ (Classical.propDecidable _)
  refine ⟨?_, canonicalAnchoredGuessingRow_firstBlockAnchored
    bound machine x certificate oldAnnotation position,
    canonicalAnchoredVerifyingRow_firstBlockAnchored
      bound machine x certificate
      (Turing.initList machine.tm
        (verifierInput machine x certificate))
      hsupported hint false position⟩
  apply @decide_eq_true _ (Classical.propDecidable _)
  exact ⟨rfl,
    canonicalInitialization_staticTracks
      bound machine x certificate hsupported
      oldAnnotation hint position,
    canonicalInitialMachineBlock_eq_initializedPhaseBlock
      bound machine x certificate hsupported
      oldAnnotation hint position,
    canonicalInitialMachineHead_eq_initializedPhaseBlock
      bound machine x certificate hsupported
      oldAnnotation hint position⟩

theorem canonicalInitialization_acceptanceAnchoredWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)))
    (oldAnnotation : Bool)
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    AcceptanceAnchoredPhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredVerifyingRow
          bound machine x certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          hsupported hint false)
        position) := by
  let first := canonicalAnchoredGuessingRow
    bound machine x certificate oldAnnotation
  let next := canonicalAnchoredVerifyingRow
    bound machine x certificate
    (Turing.initList machine.tm
      (verifierInput machine x certificate))
    hsupported hint false
  let window := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x) first next position
  have hcoherent : CompletePhaseCoherent machine.tm window := by
    simp only [CompletePhaseCoherent, anchoredVerifierWindowAt, canonicalAnchoredGuessingRow,
        and_self,
        decide_true, window, first]
  have hinitial : AnchoredInitializationAllowed machine window :=
    canonicalInitialization_anchoredWindows
      bound machine x certificate hsupported
      oldAnnotation hint position
  have hstack : StackSoundAnchoredPhaseAllowed machine window := by
    simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨hcoherent, ?_⟩
    change
      AnchoredGuessingAllowed machine window ∨
        AnchoredInitializationAllowed machine window
    exact Or.inr hinitial
  simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq]
  refine ⟨hstack,
    canonicalAnchoredGuessingWindow_replicatedMachineHeadCoherent
      bound machine x certificate oldAnnotation next position, ?_⟩
  intro himpossible
  change PhaseTag.verifying = PhaseTag.accepting at himpossible
  cases himpossible

end CLFinalTableauAssembly


end GapCVP

end

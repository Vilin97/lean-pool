/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part02

/-! # GapCVP proof, part 03 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

private theorem ofClassicalDecide03 {proposition : Prop}
    (proof : @decide proposition (Classical.propDecidable proposition) = true) :
    proposition :=
  @of_decide_eq_true proposition (Classical.propDecidable proposition) proof

namespace CLPaddedAcceptanceCompiler

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLTableauStitching GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLVerifierPhaseCert GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLWholeTimeOccupancy
open GapCVP.CLCompactWindowSoundness GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness GapCVP.CLNaturalTimeCompiler GapCVP.CLAcceptanceAnchor
open GapCVP.CLVerifiedLocalTableauCompiler GapCVP.CLFinalTableauAssembly

private noncomputable def PaddedAcceptancePhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  StackSoundAnchoredPhaseAllowed machine window ∧
    ReplicatedMachineHeadCoherent machine.tm window ∧
    (window.2.1.mode = .verifying →
      window.2.2.2.mode = .accepting →
        TrueOutputMachineHead machine window.2.1)
  ) (Classical.propDecidable _)
private def paddedAcceptancePhaseAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool := by
  classical
  exact decide (PaddedAcceptancePhaseAllowed machine window)

private theorem paddedAcceptancePhaseAllowed_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) :
    paddedAcceptancePhaseAllowed machine window = true ↔
      PaddedAcceptancePhaseAllowed machine window := by
  classical
  simp only [paddedAcceptancePhaseAllowed, Bool.decide_eq_true]

private theorem acceptanceAnchoredPhaseAllowed_implies_padded
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm)
    (hallowed : AcceptanceAnchoredPhaseAllowed machine window) :
    PaddedAcceptancePhaseAllowed machine window := by
  simp only [PaddedAcceptancePhaseAllowed, decide_eq_true_eq]
  have hallowed' := hallowed
  simp only [AcceptanceAnchoredPhaseAllowed, decide_eq_true_eq] at hallowed'
  exact ⟨hallowed'.1, hallowed'.2.1,
    fun _ haccept => hallowed'.2.2 haccept⟩

/-- GapCVP reduction support. -/
def paddedAcceptancePhaseSymbolAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    Bool :=
  paddedAcceptancePhaseAllowed machine
    ((completePhaseSymbolEquiv machine.tm).symm window.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.2)

/-- GapCVP reduction support. -/
def paddedAcceptancePhaseSpecification
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
  allowed := paddedAcceptancePhaseSymbolAllowed machine

private theorem paddedAcceptance_acceptingSelfWindow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (position : Position width) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm width
        (fun _ => acceptingPhaseCell machine.tm)
        (fun _ => acceptingPhaseCell machine.tm)
        position) := by
  let window := anchoredVerifierWindowAt machine.tm width
    (fun _ => acceptingPhaseCell machine.tm)
    (fun _ => acceptingPhaseCell machine.tm)
    position
  have hcoherent : CompletePhaseCoherent machine.tm window := by
    simp only [CompletePhaseCoherent, anchoredVerifierWindowAt, and_self, decide_true, window]
  have hstack : StackSoundAnchoredPhaseAllowed machine window := by
    simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq]
    refine ⟨hcoherent, ?_⟩
    change acceptingPhaseCell machine.tm = acceptingPhaseCell machine.tm
    rfl
  simp only [PaddedAcceptancePhaseAllowed, decide_eq_true_eq]
  refine ⟨hstack, ?_, ?_⟩
  · simp only [ReplicatedMachineHeadCoherent, anchoredVerifierWindowAt, and_self, decide_true]
  · intro himpossible
    change PhaseTag.accepting = PhaseTag.verifying at himpossible
    cases himpossible

private theorem canonicalGuessingStep_paddedAcceptanceWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (oldAnnotation bit : Bool)
    (hbound : certificate.length < bound.eval x.length)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredGuessingRow
          bound machine x (certificate ++ [bit]) bit)
        position) :=
  acceptanceAnchoredPhaseAllowed_implies_padded machine _
    (canonicalGuessingStep_acceptanceAnchoredWindows
      bound machine x certificate oldAnnotation bit hbound position)

private theorem canonicalInitialization_paddedAcceptanceWindows
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
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredGuessingRow
          bound machine x certificate oldAnnotation)
        (canonicalAnchoredVerifyingRow
          bound machine x certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          hsupported hint false)
        position) :=
  acceptanceAnchoredPhaseAllowed_implies_padded machine _
    (canonicalInitialization_acceptanceAnchoredWindows
      bound machine x certificate hsupported oldAnnotation hint position)

private theorem canonicalTrueHalt_paddedAcceptanceWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hsupported : StackAtomSupported machine
      (Turing.haltList machine.tm
        (verifierOutput machine true)))
    (hint : FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (canonicalAnchoredVerifyingRow bound machine x certificate
          (Turing.haltList machine.tm
            (verifierOutput machine true))
          hsupported hint false)
        (fun _ => acceptingPhaseCell machine.tm)
        position) :=
  acceptanceAnchoredPhaseAllowed_implies_padded machine _
    (canonicalTrueHalt_acceptanceAnchoredWindows
      bound machine x certificate hsupported hint position)

private theorem paddedAcceptanceSymbolAllowed_implies_stackSound
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : WindowSymbols (completePhaseSymbolCount machine.tm))
    (hallowed :
      paddedAcceptancePhaseSymbolAllowed machine window = true) :
    stackSoundAnchoredPhaseSymbolAllowed machine window = true := by
  let decoded : CompletePhaseWindow machine.tm :=
    ((completePhaseSymbolEquiv machine.tm).symm window.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.1,
      (completePhaseSymbolEquiv machine.tm).symm window.2.2.2)
  have hcorrected : PaddedAcceptancePhaseAllowed machine decoded := by
    apply (paddedAcceptancePhaseAllowed_iff machine decoded).mp
    exact hallowed
  have hcorrected' := hcorrected
  simp only [PaddedAcceptancePhaseAllowed, decide_eq_true_eq] at hcorrected'
  apply (stackSoundAnchoredPhaseAllowed_iff machine decoded).mpr
  exact hcorrected'.1

private theorem paddedAcceptanceValidTrace_to_stackSound
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (paddedAcceptancePhaseSpecification bound machine x) trace) :
    ValidTrace
      (stackSoundAnchoredPhaseSpecification bound machine x) trace := by
  have htrace' := htrace
  simp only [ValidTrace, decide_eq_true_eq] at htrace' ⊢
  refine ⟨htrace'.1, htrace'.2.1, ?_⟩
  intro window
  exact paddedAcceptanceSymbolAllowed_implies_stackSound
    machine _ (htrace'.2.2 window)

private theorem paddedAcceptanceValidTrace_window
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (paddedAcceptancePhaseSpecification bound machine x) trace)
    (window : Window (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
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
  apply (paddedAcceptancePhaseAllowed_iff machine _).mp
  exact htrace'.2.2 window

private theorem paddedAcceptanceValidTrace_machineHead_constant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (paddedAcceptancePhaseSpecification bound machine x) trace)
    (time : Fin (rowWidth bound machine x)) :
    ∀ position : Position (rowWidth bound machine x),
      completeMachineHead machine.tm
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)) position) =
        completeMachineHead machine.tm
          (decodeCorrectedPhaseRow machine
            (trace (Fin.castSucc time)) 0) := by
  intro position
  induction position using Fin.induction with
  | zero => rfl
  | succ position ih =>
      have hwindow := paddedAcceptanceValidTrace_window
        bound machine x trace htrace (windowAt time position.succ)
      simp only [PaddedAcceptancePhaseAllowed,
        ReplicatedMachineHeadCoherent, decide_eq_true_eq] at hwindow
      have hwindowOuter := ofClassicalDecide03 hwindow
      have hreplicated := ofClassicalDecide03 hwindowOuter.2.1
      have hleft := hreplicated.1
      change
        completeMachineHead machine.tm
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time))
              (leftBlock (rowWidth bound machine x)
                position.succ)) =
          completeMachineHead machine.tm
            (decodeCorrectedPhaseRow machine
              (trace (Fin.castSucc time)) position.succ)
        at hleft
      rw [leftBlock_succ] at hleft
      exact hleft.symm.trans ih

private theorem paddedAcceptanceValidTrace_firstAcceptance_trueHalt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (paddedAcceptancePhaseSpecification bound machine x) trace) :
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
        TrueOutputMachineHead machine (first 0) ∧
        verifier (x, certificate) = true ∧
        decodedFullPackedPhaseConfiguration machine
            (rowWidth bound machine x) first =
          Turing.haltList machine.tm
            (verifierOutput machine true) ∧
        Nonempty (FiniteRun (GuessStep bound machine x)
          (.guessing [])
          (.verifying certificate
            (Turing.haltList machine.tm
              (verifierOutput machine true))) time.val) ∧
        time.val ≤
          (guessTimePolynomial bound machine).eval x.length ∧
        (∀ (earlier : Time (rowWidth bound machine x)),
          earlier.val ≤ time.val →
          ∀ other : Position (rowWidth bound machine x),
            (decodeCorrectedPhaseRow machine
              (trace earlier) other).mode ≠ .accepting) := by
  have hstack := paddedAcceptanceValidTrace_to_stackSound
    bound machine x trace htrace
  obtain ⟨time, position, certificate,
      haccept, hmode, hmasks, hholes, hcertificate,
      ⟨run⟩, ⟨verifierRun, _⟩, hruntime, hprefix⟩ :=
    stackSoundValidTrace_firstAcceptance_actualReachable
      bound machine x trace hstack
  have haccept' := haccept
  simp only [AnchoredAcceptanceAllowed, CompleteAcceptanceAllowed,
    AcceptingPhaseBlock, decide_eq_true_eq] at haccept'
  have hacceptOuter := ofClassicalDecide03 haccept'
  have hacceptComplete := ofClassicalDecide03 hacceptOuter.1
  have hacceptBlock := ofClassicalDecide03 hacceptComplete.2
  let first := decodeCorrectedPhaseRow machine
    (trace (Fin.castSucc time))
  let next := decodeCorrectedPhaseRow machine
    (trace time.succ)
  have hselected := paddedAcceptanceValidTrace_window
    bound machine x trace htrace (windowAt time position)
  change PaddedAcceptancePhaseAllowed machine
    (anchoredVerifierWindowAt machine.tm
      (rowWidth bound machine x) first next position) at hselected
  simp only [PaddedAcceptancePhaseAllowed, decide_eq_true_eq] at hselected
  have hnextAccept : (next position).mode = .accepting := by
    change
      (decodeCorrectedPhaseRow machine
        (trace time.succ) position).mode = .accepting
    simpa only [anchoredVerifierWindowAt, acceptingPhaseCell] using
      congrArg CompletePhaseCell.mode hacceptComplete.1
  have htrueSelected :
      TrueOutputMachineHead machine (first position) :=
    hselected.2.2 (hmode position) hnextAccept
  have hhead := paddedAcceptanceValidTrace_machineHead_constant
    bound machine x trace htrace time position
  have htrueFirst : TrueOutputMachineHead machine (first 0) := by
    simp only [TrueOutputMachineHead, decide_eq_true_eq]
    have htrueSelected' := htrueSelected
    simp only [TrueOutputMachineHead, decide_eq_true_eq] at htrueSelected'
    intro offset stack
    rw [← hhead]
    exact htrueSelected' offset stack
  have hcontrol : machineControlOfBlock machine.tm
      (completeMachineHead machine.tm (first 0)) =
        some
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).l,
            (Turing.haltList machine.tm
              (verifierOutput machine true)).var) := by
    rw [← hhead]
    exact hacceptBlock.1
  have hmarked :
      completeIsFirstBlock machine.tm (first 0) = true := by
    have hmask := hmasks 0
    simp only [AnchoredPhaseMasks, decide_eq_true_eq] at hmask
    have hboundary := hmask.2.2.2
    simpa only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, decide_true] using hboundary
  let zeroWindow := anchoredVerifierWindowAt machine.tm
    (rowWidth bound machine x) first next 0
  have hzero := stackSoundValidTrace_window
    bound machine x trace hstack (windowAt time 0)
  change StackSoundAnchoredPhaseAllowed machine zeroWindow at hzero
  have hzero' := hzero
  simp only [StackSoundAnchoredPhaseAllowed, decide_eq_true_eq] at hzero'
  have hsourceZero : (first 0).mode = .verifying := hmode 0
  have hbranches :
      StackSoundAnchoredVerificationAllowed machine zeroWindow ∨
        AnchoredAcceptanceAllowed machine zeroWindow := by
    have hbranch := hzero'.2
    change
      match (first 0).mode with
      | .guessing =>
          AnchoredGuessingAllowed machine zeroWindow ∨
            AnchoredInitializationAllowed machine zeroWindow
      | .verifying =>
          StackSoundAnchoredVerificationAllowed machine zeroWindow ∨
            AnchoredAcceptanceAllowed machine zeroWindow
      | .accepting =>
          zeroWindow.2.2.2 = acceptingPhaseCell machine.tm
      at hbranch
    simpa only [hsourceZero] using hbranch
  have hanchor : FirstBlockAnchored machine.tm (first 0) := by
    rcases hbranches with hverify | hacceptZero
    · have hverify' := hverify
      simp only [StackSoundAnchoredVerificationAllowed,
        AnchoredVerificationAllowed, decide_eq_true_eq] at hverify'
      exact hverify'.1.2.1
    · have hacceptZero' := hacceptZero
      simp only [AnchoredAcceptanceAllowed, decide_eq_true_eq]
        at hacceptZero'
      exact hacceptZero'.2
  have htyped := stackSoundValidTrace_all_verifier_rows_wellTyped
    bound machine x trace hstack (Fin.castSucc time) hmode
  have htrueHalt := trueOutputMachineHead_actualVerifierHalt
    bound machine x certificate first hcertificate verifierRun
    htyped hholes hmarked hanchor htrueFirst hcontrol
  have htrueRun : FiniteRun (GuessStep bound machine x)
      (.guessing [])
      (.verifying certificate
        (Turing.haltList machine.tm
          (verifierOutput machine true))) time.val := by
    rw [← htrueHalt.2]
    exact run
  refine ⟨time, position, certificate, ?_⟩
  dsimp
  exact ⟨haccept, hmode, hmasks, hholes, hcertificate,
    htrueFirst, htrueHalt.1, htrueHalt.2,
    ⟨htrueRun⟩, hruntime, hprefix⟩

private def paddedAcceptanceValidTrace_guessingExecution
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (trace : AnchoredPhaseTrace bound machine x)
    (htrace : ValidTrace
      (paddedAcceptancePhaseSpecification bound machine x) trace) :
    GuessingExecution bound machine x := by
  classical
  apply Classical.choice
  obtain ⟨time, _, certificate, _, _, _, _, _, _, _, _,
      ⟨run⟩, hruntime, _⟩ :=
    paddedAcceptanceValidTrace_firstAcceptance_trueHalt
      bound machine x trace htrace
  exact ⟨{
    certificate := certificate
    steps := time.val
    steps_le := hruntime
    run := run
  }⟩

private def paddedWitnessAnnotation (certificate : List Bool)
    (elapsed : ℕ) : Bool :=
  if elapsed = 0 then false else
    (certificate[elapsed - 1]?).getD false

@[simp] private theorem paddedWitnessAnnotation_zero
    (certificate : List Bool) :
    paddedWitnessAnnotation certificate 0 = false := by
  simp only [paddedWitnessAnnotation, ↓reduceIte]

private theorem paddedWitnessAnnotation_succ
    (certificate : List Bool)
    (index : Fin certificate.length) :
    paddedWitnessAnnotation certificate (index.val + 1) =
      certificate.get index := by
  simp only [paddedWitnessAnnotation, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      add_tsub_cancel_right, Fin.is_lt, getElem?_pos, Option.getD_some, List.get_eq_getElem]

private theorem acceptedExecution_acceptanceTransition_le_rowWidth
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x) :
    execution.certificate.length + 1 + execution.steps + 1 ≤
      rowWidth bound machine x := by
  have hcertificate := execution.certificate_le
  have hsteps := execution.steps_le
  simp only [rowWidth, nondeterministicTableauDimensionPolynomial,
    guessTimePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  omega

private def paddedAcceptedExecutionNaturalRow
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (elapsed : ℕ) :
    Position (rowWidth bound machine x) →
      CompletePhaseCell machine.tm :=
  if hguess : elapsed ≤ execution.certificate.length then
    canonicalAnchoredGuessingRow bound machine x
      (execution.certificate.take elapsed)
      (paddedWitnessAnnotation execution.certificate elapsed)
  else if hverify :
      elapsed ≤ execution.certificate.length + 1 + execution.steps then
    let index : Fin (execution.steps + 1) :=
      ⟨elapsed - (execution.certificate.length + 1), by omega⟩
    canonicalAnchoredVerifyingRow bound machine x
      execution.certificate (execution.trace.configuration index)
      (supported index) (hint index) false
  else
    fun _ => acceptingPhaseCell machine.tm

private theorem paddedAcceptedExecutionNaturalRow_guessing
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (elapsed : ℕ)
    (hguess : elapsed ≤ execution.certificate.length) :
    paddedAcceptedExecutionNaturalRow
      bound machine execution supported hint elapsed =
      canonicalAnchoredGuessingRow bound machine x
        (execution.certificate.take elapsed)
        (paddedWitnessAnnotation execution.certificate elapsed) := by
  simp only [paddedAcceptedExecutionNaturalRow, hguess, ↓reduceDIte]

private theorem paddedAcceptedExecutionNaturalRow_verifying
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (index : Fin (execution.steps + 1)) :
    paddedAcceptedExecutionNaturalRow
      bound machine execution supported hint
      (execution.certificate.length + 1 + index.val) =
      canonicalAnchoredVerifyingRow bound machine x
        execution.certificate
        (execution.trace.configuration index)
        (supported index) (hint index) false := by
  have hguess :
      ¬ execution.certificate.length + 1 + index.val ≤
        execution.certificate.length := by
    omega
  have hverify :
      execution.certificate.length + 1 + index.val ≤
        execution.certificate.length + 1 + execution.steps := by
    have hindex := index.isLt
    omega
  have hdifference :
      execution.certificate.length + 1 + index.val -
        (execution.certificate.length + 1) = index.val := by
    omega
  have hindex :
      (⟨execution.certificate.length + 1 + index.val -
          (execution.certificate.length + 1), by omega⟩ :
        Fin (execution.steps + 1)) = index := by
    apply Fin.ext
    exact hdifference
  simp only [paddedAcceptedExecutionNaturalRow,
    dite_eq_right hguess, dite_eq_left hverify]
  rw [hindex]

private theorem paddedAcceptedExecutionNaturalRow_accepting
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (elapsed : ℕ)
    (haccept :
      execution.certificate.length + 1 + execution.steps < elapsed) :
    paddedAcceptedExecutionNaturalRow
      bound machine execution supported hint elapsed =
      fun _ => acceptingPhaseCell machine.tm := by
  have hguess : ¬ elapsed ≤ execution.certificate.length := by
    omega
  have hverify :
      ¬ elapsed ≤
        execution.certificate.length + 1 + execution.steps := by
    omega
  simp only [paddedAcceptedExecutionNaturalRow, hguess, ↓reduceDIte, hverify]

private theorem canonicalAnchoredVerifyingRow_eq_of_configuration_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hint : FiniteVerifierHint machine.tm)
    (annotation : Bool)
    (hconfiguration : first = next) :
    canonicalAnchoredVerifyingRow bound machine x certificate
        first hfirst hint annotation =
      canonicalAnchoredVerifyingRow bound machine x certificate
        next hnext hint annotation := by
  subst next
  rfl

private theorem acceptedExecution_has_paddedVerifierHints
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time)) :
    ∃ hint : Fin (execution.steps + 1) →
        FiniteVerifierHint machine.tm,
      AllCanonicalAcceptanceAnchoredVerifierTraceWindows
        bound machine x execution.certificate
        execution.trace.configuration supported hint := by
  apply (canonicalAcceptanceAnchoredVerifierTraceWindows_iff_actualRun
    bound machine x execution.certificate
    execution.trace.configuration supported
    (acceptedExecution_stack_length_le_rowWidth
      bound machine execution)).mpr
  exact execution.trace.transition

private theorem paddedAcceptedExecutionNaturalRow_guessingWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (time : Fin execution.certificate.length)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint time.val)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint (time.val + 1))
        position) := by
  have hfirst : time.val ≤ execution.certificate.length :=
    Nat.le_of_lt time.isLt
  have hnext : time.val + 1 ≤ execution.certificate.length := by
    have htime := time.isLt
    omega
  rw [paddedAcceptedExecutionNaturalRow_guessing
      bound machine execution supported hint time.val hfirst,
    paddedAcceptedExecutionNaturalRow_guessing
      bound machine execution supported hint
      (time.val + 1) hnext,
    paddedWitnessAnnotation_succ execution.certificate time]
  have htake :
      execution.certificate.take (time.val + 1) =
        execution.certificate.take time.val ++
          [execution.certificate.get time] := by
    exact List.take_succ_eq_append_getElem time.isLt
  rw [htake]
  have hlength :
      (execution.certificate.take time.val).length = time.val := by
    simp only [List.length_take, Fin.is_le', inf_of_le_left]
  have hbound :
      (execution.certificate.take time.val).length <
        bound.eval x.length := by
    rw [hlength]
    exact time.isLt.trans_le execution.certificate_le
  exact canonicalGuessingStep_paddedAcceptanceWindows
    bound machine x (execution.certificate.take time.val)
    (paddedWitnessAnnotation execution.certificate time.val)
    (execution.certificate.get time) hbound position

private theorem paddedAcceptedExecutionNaturalRow_initializationWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint
          execution.certificate.length)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint
          (execution.certificate.length + 1))
        position) := by
  have hsource := paddedAcceptedExecutionNaturalRow_guessing
    bound machine execution supported hint
    execution.certificate.length (le_refl _)
  have htarget :
      paddedAcceptedExecutionNaturalRow
        bound machine execution supported hint
        (execution.certificate.length + 1) =
      canonicalAnchoredVerifyingRow bound machine x
        execution.certificate
        (execution.trace.configuration 0)
        (supported 0) (hint 0) false := by
    simpa only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero] using
        paddedAcceptedExecutionNaturalRow_verifying bound machine execution supported hint 0
  rw [hsource, htarget]
  simp only [List.take_length]
  have hinitialSupport : StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x execution.certificate)) :=
    initialConfiguration_stackAtomSupported machine x
      execution.certificate
  have hwindows := canonicalInitialization_paddedAcceptanceWindows
    bound machine x execution.certificate hinitialSupport
    (paddedWitnessAnnotation execution.certificate
      execution.certificate.length)
    (hint 0) position
  have hrow := canonicalAnchoredVerifyingRow_eq_of_configuration_eq
    bound machine x execution.certificate
    (execution.trace.configuration 0)
    (Turing.initList machine.tm
      (verifierInput machine x execution.certificate))
    (supported 0) hinitialSupport (hint 0) false
    execution.trace.initial
  rw [hrow]
  exact hwindows

private theorem paddedAcceptedExecutionNaturalRow_verifierWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (hwindows :
      AllCanonicalAcceptanceAnchoredVerifierTraceWindows
        bound machine x execution.certificate
        execution.trace.configuration supported hint)
    (time : Fin execution.steps)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint
          (execution.certificate.length + 1 + time.val))
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint
          (execution.certificate.length + 1 + time.val + 1))
        position) := by
  have hwindows' := hwindows
  simp only [AllCanonicalAcceptanceAnchoredVerifierTraceWindows,
    decide_eq_true_eq] at hwindows'
  have hsource :
      paddedAcceptedExecutionNaturalRow
        bound machine execution supported hint
        (execution.certificate.length + 1 + time.val) =
      canonicalAnchoredVerifyingRow bound machine x
        execution.certificate
        (execution.trace.configuration (Fin.castSucc time))
        (supported (Fin.castSucc time))
        (hint (Fin.castSucc time)) false := by
    simpa only [Fin.val_castSucc] using
      paddedAcceptedExecutionNaturalRow_verifying
        bound machine execution supported hint (Fin.castSucc time)
  have htarget :
      paddedAcceptedExecutionNaturalRow
        bound machine execution supported hint
        (execution.certificate.length + 1 + time.val + 1) =
      canonicalAnchoredVerifyingRow bound machine x
        execution.certificate
        (execution.trace.configuration time.succ)
        (supported time.succ) (hint time.succ) false := by
    simpa only [Nat.add_assoc, Fin.val_succ] using
        paddedAcceptedExecutionNaturalRow_verifying bound machine execution supported hint
            time.succ
  rw [hsource, htarget]
  exact acceptanceAnchoredPhaseAllowed_implies_padded machine _
    (hwindows' time position)

private theorem paddedAcceptedExecutionNaturalRow_trueHaltWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint
          (execution.certificate.length + 1 + execution.steps))
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint
          (execution.certificate.length + 1 + execution.steps + 1))
        position) := by
  have hsource :
      paddedAcceptedExecutionNaturalRow
        bound machine execution supported hint
        (execution.certificate.length + 1 + execution.steps) =
      canonicalAnchoredVerifyingRow bound machine x
        execution.certificate
        (execution.trace.configuration
          (Fin.last execution.steps))
        (supported (Fin.last execution.steps))
        (hint (Fin.last execution.steps)) false := by
    simpa only [Fin.val_last] using
        paddedAcceptedExecutionNaturalRow_verifying bound machine execution supported hint
            (Fin.last execution.steps)
  have htarget :
      paddedAcceptedExecutionNaturalRow
        bound machine execution supported hint
        (execution.certificate.length + 1 + execution.steps + 1) =
      (fun _ => acceptingPhaseCell machine.tm) := by
    apply paddedAcceptedExecutionNaturalRow_accepting
      bound machine execution supported hint
    omega
  rw [hsource, htarget]
  have hhaltSupported : StackAtomSupported machine
      (Turing.haltList machine.tm
        (verifierOutput machine true)) := by
    rw [← execution.trace.final]
    exact supported (Fin.last execution.steps)
  have hwindows := canonicalTrueHalt_paddedAcceptanceWindows
    bound machine x execution.certificate hhaltSupported
    (hint (Fin.last execution.steps)) position
  have hrow := canonicalAnchoredVerifyingRow_eq_of_configuration_eq
    bound machine x execution.certificate
    (execution.trace.configuration (Fin.last execution.steps))
    (Turing.haltList machine.tm
      (verifierOutput machine true))
    (supported (Fin.last execution.steps))
    hhaltSupported (hint (Fin.last execution.steps)) false
    execution.trace.final
  rw [hrow]
  exact hwindows

private theorem paddedAcceptedExecutionNaturalRow_paddingWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (elapsed : ℕ)
    (haccept :
      execution.certificate.length + 1 + execution.steps < elapsed)
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint elapsed)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint (elapsed + 1))
        position) := by
  rw [paddedAcceptedExecutionNaturalRow_accepting
      bound machine execution supported hint elapsed haccept,
    paddedAcceptedExecutionNaturalRow_accepting
      bound machine execution supported hint (elapsed + 1)
      (by omega)]
  exact paddedAcceptance_acceptingSelfWindow
    machine (rowWidth bound machine x) position

private theorem paddedAcceptedExecutionNaturalRow_allWindows
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (hwindows :
      AllCanonicalAcceptanceAnchoredVerifierTraceWindows
        bound machine x execution.certificate
        execution.trace.configuration supported hint)
    (time : Fin (rowWidth bound machine x))
    (position : Position (rowWidth bound machine x)) :
    PaddedAcceptancePhaseAllowed machine
      (anchoredVerifierWindowAt machine.tm
        (rowWidth bound machine x)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint time.val)
        (paddedAcceptedExecutionNaturalRow
          bound machine execution supported hint (time.val + 1))
        position) := by
  by_cases hguess : time.val < execution.certificate.length
  · exact paddedAcceptedExecutionNaturalRow_guessingWindows
      bound machine execution supported hint
      ⟨time.val, hguess⟩ position
  by_cases hinitial : time.val = execution.certificate.length
  · simpa only [hinitial] using
      paddedAcceptedExecutionNaturalRow_initializationWindows
        bound machine execution supported hint position
  have hafter : execution.certificate.length + 1 ≤ time.val := by
    omega
  by_cases hverifier :
      time.val < execution.certificate.length + 1 + execution.steps
  · let index : Fin execution.steps :=
      ⟨time.val - (execution.certificate.length + 1), by omega⟩
    have htime :
        time.val =
          execution.certificate.length + 1 + index.val := by
      dsimp [index]
      omega
    simpa only [htime] using
      paddedAcceptedExecutionNaturalRow_verifierWindows
        bound machine execution supported hint hwindows index position
  by_cases hhalt :
      time.val = execution.certificate.length + 1 + execution.steps
  · simpa only [hhalt] using
      paddedAcceptedExecutionNaturalRow_trueHaltWindows
        bound machine execution supported hint position
  have hpadding :
      execution.certificate.length + 1 + execution.steps <
        time.val := by
    omega
  exact paddedAcceptedExecutionNaturalRow_paddingWindows
    bound machine execution supported hint time.val hpadding position

private def paddedAcceptedExecutionTrace
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm) :
    AnchoredPhaseTrace bound machine x :=
  fun time position =>
    completePhaseSymbolEquiv machine.tm
      (paddedAcceptedExecutionNaturalRow
        bound machine execution supported hint time.val position)

private theorem paddedAcceptedExecutionTrace_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (supported : ∀ time : Fin (execution.steps + 1),
      StackAtomSupported machine
        (execution.trace.configuration time))
    (hint : Fin (execution.steps + 1) →
      FiniteVerifierHint machine.tm)
    (hwindows :
      AllCanonicalAcceptanceAnchoredVerifierTraceWindows
        bound machine x execution.certificate
        execution.trace.configuration supported hint) :
    ValidTrace (paddedAcceptancePhaseSpecification bound machine x)
      (paddedAcceptedExecutionTrace
        bound machine execution supported hint) := by
  simp only [ValidTrace, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro position
    change
      completePhaseSymbolEquiv machine.tm
          (paddedAcceptedExecutionNaturalRow
            bound machine execution supported hint 0 position) =
        completePhaseSymbolEquiv machine.tm
          (initialPhaseCell bound machine x position)
    rw [paddedAcceptedExecutionNaturalRow_guessing
      bound machine execution supported hint 0 (Nat.zero_le _)]
    simp only [List.take_zero, paddedWitnessAnnotation_zero, canonicalAnchoredGuessingRow_initial]
  · refine ⟨0, ?_⟩
    have hbudget := acceptedExecution_acceptanceTransition_le_rowWidth
      bound machine execution
    have hpadding :
        execution.certificate.length + 1 + execution.steps <
          rowWidth bound machine x := by
      omega
    change
      completePhaseSymbolEquiv machine.tm
          (paddedAcceptedExecutionNaturalRow
            bound machine execution supported hint
            (rowWidth bound machine x) 0) =
        completePhaseSymbolEquiv machine.tm
          (acceptingPhaseCell machine.tm)
    rw [paddedAcceptedExecutionNaturalRow_accepting
      bound machine execution supported hint
      (rowWidth bound machine x) hpadding]
  · intro window
    change
      paddedAcceptancePhaseAllowed machine
        ((completePhaseSymbolEquiv machine.tm).symm
            (paddedAcceptedExecutionTrace
              bound machine execution supported hint
              window.1.1 (leftPosition window)),
          (completePhaseSymbolEquiv machine.tm).symm
            (paddedAcceptedExecutionTrace
              bound machine execution supported hint
              window.1.1 window.1.2),
          (completePhaseSymbolEquiv machine.tm).symm
            (paddedAcceptedExecutionTrace
              bound machine execution supported hint
              window.1.1 (rightPosition window)),
          (completePhaseSymbolEquiv machine.tm).symm
            (paddedAcceptedExecutionTrace
              bound machine execution supported hint
              (nextTime window) window.1.2)) = true
    simp only [paddedAcceptedExecutionTrace,
      Equiv.symm_apply_apply]
    apply (paddedAcceptancePhaseAllowed_iff machine _).mpr
    let time : Fin (rowWidth bound machine x) :=
      ⟨window.1.1.val, by
        have htime := window.2
        change
          window.1.1.val + 1 < rowWidth bound machine x + 1
          at htime
        omega⟩
    exact paddedAcceptedExecutionNaturalRow_allWindows
      bound machine execution supported hint hwindows
      time window.1.2

private theorem acceptedExecution_paddedAcceptance_validTrace
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x) :
    ∃ trace : AnchoredPhaseTrace bound machine x,
      ValidTrace
        (paddedAcceptancePhaseSpecification bound machine x) trace := by
  let supported := configurationTrace_stackAtomSupported
    machine x execution.certificate execution.trace
  obtain ⟨hint, hwindows⟩ :=
    acceptedExecution_has_paddedVerifierHints
      bound machine execution supported
  exact ⟨paddedAcceptedExecutionTrace
      bound machine execution supported hint,
    paddedAcceptedExecutionTrace_valid
      bound machine execution supported hint hwindows⟩

/-- Internal support shared across GapCVP continuation modules. -/
def paddedAcceptanceLocalTableauCompiler
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    GapCVP.CLNondeterminism.LocalTableauCompiler
      bound machine where
  symbols := completePhaseSymbolCount machine.tm
  specification := paddedAcceptancePhaseSpecification bound machine
  encode x execution := by
    obtain ⟨accepted⟩ :=
      guessingExecution_accepted bound machine execution
    exact acceptedExecution_paddedAcceptance_validTrace
      bound machine accepted
  decode x trace htrace :=
    paddedAcceptanceValidTrace_guessingExecution
      bound machine x trace htrace

end CLPaddedAcceptanceCompiler

namespace CLStructuralCNFVariableBounds

open GapCVP.CL GapCVP.ThreeCNFReduction

/-- GapCVP reduction support. -/
def tableauFiniteVariableCodeBound (T S : ℕ) : ℕ :=
  ((T + S + 2) ^ 2 + 1) ^ 2

theorem tableauVariable_encode_lt
    {T S : ℕ} (v : Variable T S) :
    Encodable.encode v < tableauFiniteVariableCodeBound T S := by
  rcases v with ⟨time, position, symbol⟩
  change Nat.pair time.val (Nat.pair position.val symbol.val) <
    ((T + S + 2) ^ 2 + 1) ^ 2
  have hinner : Nat.pair position.val symbol.val < (T + S + 2) ^ 2 := by
    calc
      Nat.pair position.val symbol.val <
          (max position.val symbol.val + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq position.val symbol.val
      _ ≤ (T + S + 2) ^ 2 := by
        apply Nat.pow_le_pow_left
        have hposition := position.isLt
        have hsymbol := symbol.isLt
        omega
  have htime : time.val ≤ (T + S + 2) ^ 2 := by
    have hfirst : time.val ≤ T + S + 2 := by
      have hactual := time.isLt
      omega
    calc
      time.val ≤ T + S + 2 := hfirst
      _ ≤ (T + S + 2) ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_self (T + S + 2)
  calc
    Nat.pair time.val (Nat.pair position.val symbol.val) <
        (max time.val (Nat.pair position.val symbol.val) + 1) ^ 2 :=
      Nat.pair_lt_max_add_one_sq time.val
        (Nat.pair position.val symbol.val)
    _ ≤ ((T + S + 2) ^ 2 + 1) ^ 2 := by
      apply Nat.pow_le_pow_left
      omega

theorem sourceVariable_lt_tableauFiniteBound
    {T S : ℕ} (v : Variable T S) :
    sourceVariable v < 4 * tableauFiniteVariableCodeBound T S := by
  have hcode := tableauVariable_encode_lt v
  unfold sourceVariable
  omega

end CLStructuralCNFVariableBounds

namespace CLStructuralPrefixWriter

open Turing GapCVP.BinaryEncoding

private def prefixWriterPeek (stack : Fin 4)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def prefixWriterPop (stack : Fin 4)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  .pop stack (fun symbol _ => symbol) continuation

private def prefixWriterPushBit (stack : Fin 4)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  .push stack (fun symbol => symbol.getD false) continuation

private def prefixWriterPushMarker (stack : Fin 4)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  .push stack (fun _ => true) continuation

private def prefixWriterGoto (phase : Fin 3) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private def prefixWriterScanStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  prefixWriterPeek 0
    (prefixWriterPop 0
      (prefixWriterPushBit 1
        (prefixWriterPushMarker 2 (prefixWriterGoto 0))))
    (prefixWriterGoto 1)

private def prefixWriterRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  prefixWriterPeek 1
    (prefixWriterPop 1
      (prefixWriterPushBit 3 (prefixWriterGoto 1)))
    (.push 3 (fun _ => false) (prefixWriterGoto 2))

private def prefixWriterMarkerStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool) :=
  prefixWriterPeek 2
    (prefixWriterPop 2
      (prefixWriterPushMarker 3 (prefixWriterGoto 2)))
    .halt

private abbrev structuralPrefixWriter : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 3) then
      prefixWriterScanStatement
    else if phase = (1 : Fin 3) then
      prefixWriterRestoreStatement
    else
      prefixWriterMarkerStatement

private def prefixWriterConfiguration (phase : Fin 3)
    (input scratch markers output : List Bool) :
    structuralPrefixWriter.Cfg where
  l := some phase
  var := none
  stk := ![input, scratch, markers, output]

private theorem structuralPrefixWriter_init (input : List Bool) :
    Turing.initList structuralPrefixWriter input =
      prefixWriterConfiguration 0 input [] [] [] := by
  simp only [structuralPrefixWriter, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      prefixWriterConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `prefixWriterStepTac` machine-step simplifier. -/
macro "prefixWriterStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [structuralPrefixWriter, prefixWriterConfiguration,
          prefixWriterPeek, prefixWriterPop, prefixWriterPushBit,
          prefixWriterPushMarker, prefixWriterGoto,
          prefixWriterScanStatement, prefixWriterRestoreStatement,
          prefixWriterMarkerStatement, Turing.haltList,
          Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

private theorem prefixWriter_scan_step (bit : Bool)
    (input scratch markers output : List Bool) :
    structuralPrefixWriter.step
      (prefixWriterConfiguration 0
        (bit :: input) scratch markers output) =
      some (prefixWriterConfiguration 0
        input (bit :: scratch) (true :: markers) output) := by
  cases bit <;> prefixWriterStepTac

private theorem prefixWriter_scan_finish
    (scratch markers output : List Bool) :
    structuralPrefixWriter.step
      (prefixWriterConfiguration 0 [] scratch markers output) =
      some (prefixWriterConfiguration 1 [] scratch markers output) := by
  prefixWriterStepTac

private theorem prefixWriter_restore_step (bit : Bool)
    (scratch markers output : List Bool) :
    structuralPrefixWriter.step
      (prefixWriterConfiguration 1 []
        (bit :: scratch) markers output) =
      some (prefixWriterConfiguration 1 []
        scratch markers (bit :: output)) := by
  cases bit <;> prefixWriterStepTac

private theorem prefixWriter_restore_finish
    (markers output : List Bool) :
    structuralPrefixWriter.step
      (prefixWriterConfiguration 1 [] [] markers output) =
      some (prefixWriterConfiguration 2 [] [] markers
        (false :: output)) := by
  prefixWriterStepTac

private theorem prefixWriter_marker_step (bit : Bool)
    (markers output : List Bool) :
    structuralPrefixWriter.step
      (prefixWriterConfiguration 2 [] [] (bit :: markers) output) =
      some (prefixWriterConfiguration 2 [] [] markers
        (true :: output)) := by
  cases bit <;> prefixWriterStepTac

private theorem prefixWriter_finish (output : List Bool) :
    structuralPrefixWriter.step
      (prefixWriterConfiguration 2 [] [] [] output) =
      some (Turing.haltList structuralPrefixWriter output) := by
  prefixWriterStepTac

private def prefixWriter_scanTrace
    (input scratch markers output : List Bool) :
    EvalsToInTime structuralPrefixWriter.step
      (prefixWriterConfiguration 0 input scratch markers output)
      (some (prefixWriterConfiguration 1 []
        (input.reverse ++ scratch)
        (List.replicate input.length true ++ markers) output))
      (input.length + 1) := by
  induction input generalizing scratch markers with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          List.replicate_zero,
          zero_add] using oneStep _ _ (prefixWriter_scan_finish scratch markers output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ (prefixWriter_scan_step bit input scratch markers output)
      have hrest := ih (bit :: scratch) (true :: markers)
      have hfull := EvalsToInTime.trans structuralPrefixWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, List.replicate_succ', Nat.add_assoc, Nat.reduceAdd] using hfull

private def prefixWriter_restoreTrace
    (scratch markers output : List Bool) :
    EvalsToInTime structuralPrefixWriter.step
      (prefixWriterConfiguration 1 [] scratch markers output)
      (some (prefixWriterConfiguration 2 [] [] markers
        (false :: (scratch.reverse ++ output))))
      (scratch.length + 1) := by
  induction scratch generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (prefixWriter_restore_finish markers output)
  | cons bit scratch ih =>
      have hfirst := oneStep _ _ (prefixWriter_restore_step bit scratch markers output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans structuralPrefixWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def prefixWriter_markerTrace (markers output : List Bool) :
    EvalsToInTime structuralPrefixWriter.step (prefixWriterConfiguration 2 [] [] markers output)
      (some (Turing.haltList structuralPrefixWriter
        (List.replicate markers.length true ++ output)))
      (markers.length + 1) := by
  induction markers generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.replicate_zero, List.nil_append,
          zero_add] using
          oneStep _ _ (prefixWriter_finish output)
  | cons bit markers ih =>
      have hfirst := oneStep _ _ (prefixWriter_marker_step bit markers output)
      have hrest := ih (true :: output)
      have hfull := EvalsToInTime.trans structuralPrefixWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, List.replicate_succ',
          List.append_assoc,
          List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using hfull

private def prefixWriter_totalTrace (input : List Bool) :
    EvalsToInTime structuralPrefixWriter.step (prefixWriterConfiguration 0 input [] [] [])
      (some (Turing.haltList structuralPrefixWriter
        (lengthPrefixedWord input)))
      (3 * input.length + 3) := by
  have hscan := prefixWriter_scanTrace input [] [] []
  simp only [List.append_nil] at hscan
  have hrestore := prefixWriter_restoreTrace
    input.reverse (List.replicate input.length true) []
  simp only [List.reverse_reverse, List.append_nil] at hrestore
  have hmarkers := prefixWriter_markerTrace
    (List.replicate input.length true) (false :: input)
  simp only [List.length_replicate] at hmarkers
  have hfirst := EvalsToInTime.trans structuralPrefixWriter.step _ _ _ _ _ hscan hrestore
  have hfull := EvalsToInTime.trans structuralPrefixWriter.step _ _ _ _ _ hfirst hmarkers
  have hbounded := rebound (newBudget := 3 * input.length + 3) hfull (by
      simp only [List.length_reverse]
      omega)
  simpa only [FinTM2.step, Fin.isValue, lengthPrefixedWord] using hbounded

/-- GapCVP reduction support. -/
noncomputable def structuralPrefixWriterComputable :
    Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
      GapCVP.bitEncoding
      (fun input : List Bool => lengthPrefixedWord input) where
  tm := structuralPrefixWriter
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 3
  outputsFun input := {
    steps := (prefixWriter_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, structuralPrefixWriter_init,
              Option.map_some] using
          (prefixWriter_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (prefixWriter_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

end CLStructuralPrefixWriter

namespace SourceMachineCert

open Turing

private def prependBitMachine (bit : Bool) : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => bit) .halt

/-- GapCVP reduction support. -/
noncomputable def prependBitComputable (bit : Bool) :
    BitTM
      (fun input : List Bool => bit :: input) where
  tm := prependBitMachine bit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun input := {
    steps := 1
    evals_in_steps := by
      simp only [prependBitMachine, Option.bind_eq_bind, FinTM2.step, initList, ↓reduceDIte,
          Equiv.invFun_as_coe,
          Equiv.refl_symm, Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, eq_mpr_eq_cast,
              cast_eq, Function.iterate_one,
          flip, List.map_cons, Option.map_some, haltList]
      congr 2
    steps_le_m := by simp only [id_eq, Polynomial.eval_one, Std.le_refl]
  }

/-- GapCVP reduction support. -/
noncomputable def prependWordComputable (word : List Bool) :
    BitTM
      (fun input : List Bool => word ++ input) := by
  induction word with
  | nil =>
      exact Turing.idComputableInPolyTime bitEncoding
  | cons bit rest ih =>
      change BitTM
        ((fun input : List Bool => bit :: input) ∘
          (fun input : List Bool => rest ++ input))
      exact TMComposition.computableInPolyTime ih
        (prependBitComputable bit)

/-- GapCVP reduction support. -/
def formulaVariables (formula : ThreeCNF) : List ℕ :=
  formula.flatMap fun clause =>
    [(clause 0).1, (clause 1).1, (clause 2).1]

@[simp] theorem formulaVariables_length (formula : ThreeCNF) :
    (formulaVariables formula).length = 3 * formula.length := by
  induction formula with
  | nil => simp only [formulaVariables, Fin.isValue, List.flatMap_nil, List.length_nil, mul_zero]
  | cons clause rest ih =>
      simp only [formulaVariables, Fin.isValue, List.flatMap_cons, List.cons_append,
          List.nil_append,
          List.length_cons, List.length_flatMap, List.length_nil, zero_add, Nat.reduceAdd,
              List.map_const',
          List.sum_replicate, smul_eq_mul]
      omega

theorem mem_formulaVariables
    (formula : ThreeCNF) (clause : ThreeClause)
    (hclause : clause ∈ formula) (i : Fin 3) :
    (clause i).1 ∈ formulaVariables formula := by
  unfold formulaVariables
  apply List.mem_flatMap.mpr
  refine ⟨clause, hclause, ?_⟩
  fin_cases i <;> simp

/-- GapCVP reduction support. -/
def variableRank (formula : ThreeCNF) (index : ℕ) : ℕ :=
  (formulaVariables formula).idxOf index

end SourceMachineCert

namespace SourceMachineRouting

open SourceMachineCert

/-- GapCVP reduction support. -/
def canonicalYesInstance : GapCVPInstance where
  dimension := 1
  basis := Matrix.of fun _ _ => 1
  target _ := 0
  radius := 1

theorem canonicalYesInstance_wellFormed :
    gapCVPWellFormed canonicalYesInstance := by
  simp only [GapCVP.gapCVPWellFormed, decide_eq_true_eq]
  refine ⟨by decide, ?_, by norm_num [canonicalYesInstance]⟩
  unfold canonicalYesInstance
  change (Matrix.of (fun _ _ : Fin 1 => (1 : ℤ))).det ≠ 0
  rw [Matrix.det_fin_one]
  norm_num

theorem canonicalYesInstance_gapYES : gapYES canonicalYesInstance := by
  simp only [GapCVP.gapYES, decide_eq_true_eq]
  refine ⟨canonicalYesInstance_wellFormed, ?_⟩
  refine ⟨fun _ => 0, ?_⟩
  have hdistance :
      distanceSquared canonicalYesInstance (fun _ => 0) = 0 := by
    simp only [distanceSquared, canonicalYesInstance,
        Int.cast_zero, mul_zero, Finset.sum_const_zero, Rat.cast_zero, sub_self,
            ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  rw [hdistance]
  norm_num [canonicalYesInstance]

/-- GapCVP reduction support. -/
def canonicalYesWord : List Bool :=
  BinaryEncoding.encodeGapCVPInstance canonicalYesInstance

end SourceMachineRouting

namespace SourceUniformTuringTM

open Turing

private abbrev eraseMachine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ :=
    .peek () (fun _ symbol => symbol.isSome)
      (.branch (fun hasSymbol => hasSymbol)
        (.pop () (fun _ _ => false) (.goto (fun _ => ())))
        .halt)

private theorem eraseMachine_step_cons
    (bit : Bool) (rest : List Bool) :
    eraseMachine.step (Turing.initList eraseMachine (bit :: rest)) =
      some (Turing.initList eraseMachine rest) := by
  compactMachineStepTac [eraseMachine, Turing.initList]

private theorem eraseMachine_step_nil :
    eraseMachine.step (Turing.initList eraseMachine []) =
      some (Turing.haltList eraseMachine []) := by
  compactMachineStepTac [eraseMachine, Turing.initList]

private theorem eraseMachine_iterate (input : List Bool) :
    ((flip Option.bind eraseMachine.step)^[input.length + 1])
        (some (Turing.initList eraseMachine input)) =
      some (Turing.haltList eraseMachine []) := by
  induction input with
  | nil =>
      change eraseMachine.step (Turing.initList eraseMachine []) =
        some (Turing.haltList eraseMachine [])
      exact eraseMachine_step_nil
  | cons bit rest ih =>
      change
        ((flip Option.bind eraseMachine.step)^[rest.length + 1 + 1])
            (some (Turing.initList eraseMachine (bit :: rest))) =
          some (Turing.haltList eraseMachine [])
      rw [Function.iterate_succ_apply]
      change
        ((flip Option.bind eraseMachine.step)^[rest.length + 1])
            (eraseMachine.step
              (Turing.initList eraseMachine (bit :: rest))) =
          some (Turing.haltList eraseMachine [])
      rw [eraseMachine_step_cons]
      exact ih

private noncomputable def eraseComputable :
    BitTM
      (fun _ : List Bool => []) where
  tm := eraseMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := {
    steps := input.length + 1
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Equiv.invFun_as_coe, Equiv.refl_symm,
          Equiv.coe_refl,
          bitEncoding, id_eq, List.map_id_fun, Function.iterate_succ, Function.comp_apply,
              List.map_nil,
          Option.map_some] using eraseMachine_iterate input
    steps_le_m := by
      simp only [bitEncoding, id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
          Std.le_refl]
  }

/-- GapCVP reduction support. -/
noncomputable def constantWordComputable (word : List Bool) :
    BitTM
      (fun _ : List Bool => word) := by
  have machine := TMComposition.computableInPolyTime eraseComputable
    (SourceMachineCert.prependWordComputable word)
  have hmap :
      ((fun input : List Bool => word ++ input) ∘
        (fun _ : List Bool => [])) =
        (fun _ : List Bool => word) := by
    funext input
    simp only [Function.comp_apply, List.append_nil]
  rw [hmap] at machine
  exact machine

end SourceUniformTuringTM

namespace SourceStructuralTuringTM

open Turing

private abbrev unaryPrefixMachine : Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Bool
  main := true
  σ := Option Bool
  initialState := none
  m phase :=
    if phase then
      .peek false (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.pop false (fun _ _ => none)
            (.push true (fun _ => true)
              (.goto (fun _ => true))))
          (.branch (fun symbol => symbol.isSome)
            (.pop false (fun _ _ => none)
              (.goto (fun _ => false)))
            (.push true (fun _ => false) .halt)))
    else
      .peek false (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop false (fun _ _ => none)
            (.goto (fun _ => false)))
          (.push true (fun _ => true) .halt))

private def unaryConfiguration
    (phase : Bool) (input : List Bool) (count : ℕ) :
    unaryPrefixMachine.Cfg where
  l := some phase
  var := none
  stk
    | false => input
    | true => List.replicate count true

private theorem unaryPrefixMachine_step_true
    (input : List Bool) (count : ℕ) :
    unaryPrefixMachine.step
        (unaryConfiguration true (true :: input) count) =
      some (unaryConfiguration true input (count + 1)) := by
  simp only [unaryPrefixMachine, FinTM2.step, TM2.step, unaryConfiguration, ↓reduceIte,
      TM2.stepAux,
      List.head?_cons, BEq.rfl, List.tail_cons, ne_eq, Bool.true_eq_false, not_false_eq_true,
          Function.update_of_ne,
      Option.isSome_some, Bool.cond_true]
  congr 2
  funext stack
  cases stack <;> simp [Function.update, List.replicate_succ]

private theorem unaryPrefixMachine_step_false
    (input : List Bool) (count : ℕ) :
    unaryPrefixMachine.step
        (unaryConfiguration true (false :: input) count) =
      some (unaryConfiguration false input count) := by
  simp only [unaryPrefixMachine, FinTM2.step, TM2.step, unaryConfiguration, ↓reduceIte,
      TM2.stepAux,
      List.head?_cons, Option.some_beq_some, beq_true, List.tail_cons, ne_eq, Bool.true_eq_false,
          not_false_eq_true,
      Function.update_of_ne, Option.isSome_some, Bool.cond_true, Bool.cond_false]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

private theorem unaryPrefixMachine_drain_step
    (bit : Bool) (input : List Bool) (count : ℕ) :
    unaryPrefixMachine.step
        (unaryConfiguration false (bit :: input) count) =
      some (unaryConfiguration false input count) := by
  cases bit <;>
    compactMachineStepTac [unaryPrefixMachine, unaryConfiguration]

private theorem unaryPrefixMachine_finish_prefix (count : ℕ) :
    unaryPrefixMachine.step (unaryConfiguration true [] count) =
      some (Turing.haltList unaryPrefixMachine
        (false :: List.replicate count true)) := by
  simp only [unaryPrefixMachine, FinTM2.step, TM2.step, unaryConfiguration, ↓reduceIte,
      TM2.stepAux,
      List.head?_nil, Option.none_beq_some, List.tail_nil, Function.update_eq_self, ne_eq,
          Bool.true_eq_false,
      not_false_eq_true, Function.update_of_ne, Option.isSome_none, Bool.cond_false, haltList,
          eq_mpr_eq_cast, cast_eq,
      dite_eq_ite]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

private theorem unaryPrefixMachine_finish_drain (count : ℕ) :
    unaryPrefixMachine.step (unaryConfiguration false [] count) =
      some (Turing.haltList unaryPrefixMachine
        (true :: List.replicate count true)) := by
  simp only [unaryPrefixMachine, FinTM2.step, TM2.step, unaryConfiguration, Bool.false_eq_true,
      ↓reduceIte,
      TM2.stepAux, List.head?_nil, Option.isSome_none, List.tail_nil, Function.update_eq_self,
          Bool.cond_false, haltList,
      eq_mpr_eq_cast, cast_eq, dite_eq_ite]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

/-- GapCVP reduction support. -/
def unaryPrefixLength : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: rest => unaryPrefixLength rest + 1

/-- GapCVP reduction support. -/
def unaryPrefixHasDelimiter : List Bool → Bool
  | [] => false
  | false :: _ => true
  | true :: rest => unaryPrefixHasDelimiter rest

/-- GapCVP reduction support. -/
def unaryPrefixOutput (input : List Bool) : List Bool :=
  unaryPrefixHasDelimiter input ::
    List.replicate (unaryPrefixLength input) true

private theorem unaryPrefixMachine_drain_iterate
    (input : List Bool) (count : ℕ) :
    ((flip Option.bind unaryPrefixMachine.step)^[input.length + 1])
        (some (unaryConfiguration false input count)) =
      some (Turing.haltList unaryPrefixMachine
        (true :: List.replicate count true)) := by
  induction input with
  | nil =>
      change unaryPrefixMachine.step
        (unaryConfiguration false [] count) = _
      exact unaryPrefixMachine_finish_drain count
  | cons bit rest ih =>
      change
        ((flip Option.bind unaryPrefixMachine.step)^[rest.length + 1 + 1])
            (some (unaryConfiguration false (bit :: rest) count)) = _
      rw [Function.iterate_succ_apply]
      change
        ((flip Option.bind unaryPrefixMachine.step)^[rest.length + 1])
            (unaryPrefixMachine.step
              (unaryConfiguration false (bit :: rest) count)) = _
      rw [unaryPrefixMachine_drain_step]
      exact ih

private theorem unaryPrefixMachine_prefix_iterate
    (input : List Bool) (count : ℕ) :
    ((flip Option.bind unaryPrefixMachine.step)^[input.length + 1])
        (some (unaryConfiguration true input count)) =
      some (Turing.haltList unaryPrefixMachine
        (unaryPrefixHasDelimiter input ::
          List.replicate (unaryPrefixLength input + count) true)) := by
  induction input generalizing count with
  | nil =>
      change unaryPrefixMachine.step
        (unaryConfiguration true [] count) = _
      simpa only [FinTM2.step, unaryPrefixHasDelimiter, unaryPrefixLength, zero_add] using
          unaryPrefixMachine_finish_prefix count
  | cons bit rest ih =>
      cases bit with
      | false =>
          change
            ((flip Option.bind unaryPrefixMachine.step)^[rest.length + 1 + 1])
                (some (unaryConfiguration true (false :: rest) count)) = _
          rw [Function.iterate_succ_apply]
          change
            ((flip Option.bind unaryPrefixMachine.step)^[rest.length + 1])
                (unaryPrefixMachine.step
                  (unaryConfiguration true (false :: rest) count)) = _
          rw [unaryPrefixMachine_step_false]
          simpa only [FinTM2.step, Function.iterate_succ, Function.comp_apply,
              unaryPrefixHasDelimiter,
              unaryPrefixLength, zero_add] using unaryPrefixMachine_drain_iterate rest count
      | true =>
          change
            ((flip Option.bind unaryPrefixMachine.step)^[rest.length + 1 + 1])
                (some (unaryConfiguration true (true :: rest) count)) = _
          rw [Function.iterate_succ_apply]
          change
            ((flip Option.bind unaryPrefixMachine.step)^[rest.length + 1])
                (unaryPrefixMachine.step
                  (unaryConfiguration true (true :: rest) count)) = _
          rw [unaryPrefixMachine_step_true]
          simpa only [FinTM2.step, Function.iterate_succ, Function.comp_apply,
              unaryPrefixHasDelimiter,
              unaryPrefixLength, Nat.add_comm, Nat.add_assoc] using ih (count + 1)

private theorem unaryPrefixMachine_init (input : List Bool) :
    Turing.initList unaryPrefixMachine input =
      unaryConfiguration true input 0 := by
  simp only [unaryPrefixMachine, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      unaryConfiguration,
      List.replicate_zero]
  congr 1
  funext stack
  cases stack <;> simp

/-- GapCVP reduction support. -/
noncomputable def unaryPrefixComputable :
    BitTM
      unaryPrefixOutput where
  tm := unaryPrefixMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := {
    steps := input.length + 1
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Equiv.invFun_as_coe, Equiv.refl_symm,
          Equiv.coe_refl,
          bitEncoding, id_eq, List.map_id_fun, unaryPrefixMachine_init, Function.iterate_succ,
              Function.comp_apply,
          unaryPrefixOutput, List.map_cons, List.map_replicate, Option.map_some, add_zero] using
          unaryPrefixMachine_prefix_iterate input 0
    steps_le_m := by
      simp only [bitEncoding, id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
          Std.le_refl]
  }

@[simp] private theorem unaryPrefixLength_replicate_delimiter
    (count : ℕ) (suffix : List Bool) :
    unaryPrefixLength
        (List.replicate count true ++ false :: suffix) = count := by
  induction count with
  | zero => simp only [List.replicate_zero, List.nil_append, unaryPrefixLength]
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, unaryPrefixLength, ih]

@[simp] private theorem unaryPrefixHasDelimiter_replicate_delimiter
    (count : ℕ) (suffix : List Bool) :
    unaryPrefixHasDelimiter
        (List.replicate count true ++ false :: suffix) = true := by
  induction count with
  | zero => simp only [List.replicate_zero, List.nil_append, unaryPrefixHasDelimiter]
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, unaryPrefixHasDelimiter, ih]

@[simp] theorem unaryPrefixOutput_replicate_delimiter
    (count : ℕ) (suffix : List Bool) :
    unaryPrefixOutput
        (List.replicate count true ++ false :: suffix) =
      true :: List.replicate count true := by
  simp only [unaryPrefixOutput, unaryPrefixHasDelimiter_replicate_delimiter,
      unaryPrefixLength_replicate_delimiter]

end SourceStructuralTuringTM

namespace SourceStructuralDecoder

open Turing

/-- Internal support shared across GapCVP continuation modules. -/
abbrev payloadDecoderMachine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 5) then
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.pop 0 (fun _ _ => none)
            (.push 1 (fun _ => true)
              (.goto (fun _ => 0))))
          (.branch (fun symbol => symbol.isSome)
            (.pop 0 (fun _ _ => none)
              (.goto (fun _ => 1)))
            (.goto (fun _ => 4))))
    else if phase = (1 : Fin 5) then
      .peek 1 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.peek 0 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun state _ => state)
                (.pop 0 (fun state _ => state)
                  (.push 2 (fun state => state.getD false)
                    (.load (fun _ => none) (.goto (fun _ => 1))))))
              (.goto (fun _ => 4))))
          (.goto (fun _ => 2)))
    else if phase = (2 : Fin 5) then
      .peek 2 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 2 (fun state _ => state)
            (.push 3 (fun state => state.getD false)
              (.load (fun _ => none) (.goto (fun _ => 2)))))
          (.goto (fun _ => 3)))
    else if phase = (3 : Fin 5) then
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun _ _ => none) (.goto (fun _ => 3)))
          (.push 3 (fun _ => true) .halt))
    else
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun _ _ => none) (.goto (fun _ => 4)))
          (.peek 1 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun _ _ => none) (.goto (fun _ => 4)))
              (.peek 2 (fun _ symbol => symbol)
                (.branch (fun symbol => symbol.isSome)
                  (.pop 2 (fun _ _ => none) (.goto (fun _ => 4)))
                  (.push 3 (fun _ => false) .halt))))))

/-- Internal support shared across GapCVP continuation modules. -/
def payloadConfiguration
    (phase : Fin 5)
    (input counter reversed output : List Bool) :
    payloadDecoderMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, reversed, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_prefix_true
    (input counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 0 (true :: input) counter reversed output) =
      some (payloadConfiguration 0 input (true :: counter)
        reversed output) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

private theorem payload_prefix_delimiter
    (input counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 0 (false :: input) counter reversed output) =
      some (payloadConfiguration 1 input counter reversed output) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_prefix_missing_delimiter
    (counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 0 [] counter reversed output) =
      some (payloadConfiguration 4 [] counter reversed output) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_copy_step
    (bit : Bool) (input counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 1 (bit :: input)
        (true :: counter) reversed output) =
      some (payloadConfiguration 1 input counter
        (bit :: reversed) output) := by
  cases bit <;> compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_insufficient
    (counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 1 [] (true :: counter) reversed output) =
      some (payloadConfiguration 4 []
        (true :: counter) reversed output) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_counter_complete
    (input reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 1 input [] reversed output) =
      some (payloadConfiguration 2 input [] reversed output) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

private theorem payload_reverse_step
    (bit : Bool) (input reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 2 input [] (bit :: reversed) output) =
      some (payloadConfiguration 2 input [] reversed (bit :: output)) := by
  cases bit <;> compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_reverse_complete
    (input output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 2 input [] [] output) =
      some (payloadConfiguration 3 input [] [] output) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

private theorem payload_drain_step
    (bit : Bool) (input output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 3 (bit :: input) [] [] output) =
      some (payloadConfiguration 3 input [] [] output) := by
  cases bit <;> compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

private theorem payload_drain_finish
    (output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 3 [] [] [] output) =
      some (Turing.haltList payloadDecoderMachine (true :: output)) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_failure_drop_input
    (bit : Bool) (input counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 4 (bit :: input) counter reversed output) =
      some (payloadConfiguration 4 input counter reversed output) := by
  cases bit <;> compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_failure_drop_counter
    (bit : Bool) (counter reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 4 [] (bit :: counter) reversed output) =
      some (payloadConfiguration 4 [] counter reversed output) := by
  cases bit <;> compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_failure_drop_reversed
    (bit : Bool) (reversed output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 4 [] [] (bit :: reversed) output) =
      some (payloadConfiguration 4 [] [] reversed output) := by
  cases bit <;> compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem payload_failure_finish
    (output : List Bool) :
    payloadDecoderMachine.step
      (payloadConfiguration 4 [] [] [] output) =
      some (Turing.haltList payloadDecoderMachine (false :: output)) := by
  compactMachineStepTac [payloadDecoderMachine, payloadConfiguration]

@[simp] theorem replicate_true_append_cons
    (count : ℕ) (tail : List Bool) :
    List.replicate count true ++ true :: tail =
      true :: (List.replicate count true ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

/-- Internal support shared across GapCVP continuation modules. -/
def payloadPrefixTrace
    (count : ℕ) (tail counter reversed output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0
        (List.replicate count true ++ false :: tail)
        counter reversed output)
      (some (payloadConfiguration 1 tail
        (List.replicate count true ++ counter) reversed output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (payload_prefix_delimiter tail counter reversed output)
  | succ count ih =>
      have hfirst := oneStep _ _ (payload_prefix_true
          (List.replicate count true ++ false :: tail)
          counter reversed output)
      have hrest := ih (true :: counter)
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 (count + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_true_append_cons] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def payloadCopyTrace
    (payload suffix reversed output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 1 (payload ++ suffix)
        (List.replicate payload.length true) reversed output)
      (some (payloadConfiguration 1 suffix []
        (payload.reverse ++ reversed) output))
      payload.length := by
  induction payload generalizing reversed with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil] using
          EvalsToInTime.refl payloadDecoderMachine.step (payloadConfiguration 1 suffix [] reversed
              output)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (payload_copy_step bit (payload ++ suffix)
          (List.replicate payload.length true) reversed output)
      have hrest := ih (bit :: reversed)
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 payload.length
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def payloadReverseTrace
    (input reversed output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 2 input [] reversed output)
      (some (payloadConfiguration 2 input [] []
        (reversed.reverse ++ output)))
      reversed.length := by
  induction reversed generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil]
          using
          EvalsToInTime.refl payloadDecoderMachine.step (payloadConfiguration 2 input [] [] output)
  | cons bit reversed ih =>
      have hfirst := oneStep _ _ (payload_reverse_step bit input reversed output)
      have hrest := ih (bit :: output)
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 reversed.length
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def payloadDrainTrace
    (suffix output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 3 suffix [] [] output)
      (some (Turing.haltList payloadDecoderMachine (true :: output)))
      (suffix.length + 1) := by
  induction suffix with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (payload_drain_finish output)
  | cons bit suffix ih =>
      have hfirst := oneStep _ _ (payload_drain_step bit suffix output)
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 (suffix.length + 1)
        _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using hboth

/-- Internal support shared across GapCVP continuation modules. -/
theorem payloadDecoderMachine_init (input : List Bool) :
    Turing.initList payloadDecoderMachine input =
      payloadConfiguration 0 input [] [] [] := by
  simp only [payloadDecoderMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      payloadConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

end SourceStructuralDecoder

end GapCVP

end

/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineFPBasics
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Containment

/-!
# From logarithmic-cost RAM deciders to one-bit `FP` functions

Complexitylib's RAM simulator is stated for languages.  The executable
permanent approximation will use it as a bit graph: a RAM program answers one
requested output bit, and an outer bounded `FP` loop assembles those answers.
This file proves the first, generic bridge without introducing a machine-time
assumption.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

namespace MachineRAMBridge

open RAM.RegisterStore.Machine

/-- The clean verdict tape emitted by the RAM simulator contains exactly one
Boolean output symbol and then a blank. -/
theorem registerVerdictOutput_hasOutput (value : ℕ) :
    (registerVerdictOutput value).HasOutput [decide (value ≠ 0)] := by
  by_cases h : value = 0 <;>
    simp [h, Tape.HasOutput, registerVerdictOutput, registerVerdictSymbol,
      TM.idleDir, Tape.writeAndMove, Tape.move, Tape.write, Tape.read,
      Tape.init]
  all_goals rfl

/-- The ordinary one-bit characteristic string of a decidable language. -/
def languageFlag (L : Language)
    [DecidablePred (fun word => word ∈ L)] (word : List Bool) : List Bool :=
  [decide (word ∈ L)]

/-- A logarithmic-cost RAM decider computes the corresponding one-bit string
on the verified sparse simulator, with the simulator's explicit envelope. -/
theorem programDecision_computesLanguageFlagInTime
    {L : Language} {T : ℕ → ℕ}
    [DecidablePred (fun word => word ∈ L)]
    (program : RAM.Program) (hdecides : program.DecidesInTime L T) :
    (programDecisionTM standardControlInstructionTapes program).ComputesInTime
      (languageFlag L)
      (fun inputLength =>
        programDecisionEnvelope program inputLength (T inputLength)) := by
  intro input
  obtain ⟨fuel, hhalted, hcost, hyes, hno⟩ := hdecides input
  let haltWitness : ∃ candidate,
      RAM.Halted program
        (RAM.run program candidate (RAM.initCfg input)) := ⟨fuel, hhalted⟩
  let firstFuel := Nat.find haltWitness
  have hfirstHalted : RAM.Halted program
      (RAM.run program firstFuel (RAM.initCfg input)) :=
    Nat.find_spec haltWitness
  have hfirstLe : firstFuel ≤ fuel := Nat.find_min' haltWitness hhalted
  have hnotHalted : ∀ candidate < firstFuel,
      ¬ RAM.Halted program
        (RAM.run program candidate (RAM.initCfg input)) := by
    intro candidate hcandidate
    exact Nat.find_min haltWitness hcandidate
  have hunit : RAM.unitTimeUpto program firstFuel (RAM.initCfg input) =
      firstFuel :=
    RAM.unitTimeUpto_eq_of_not_halted program (RAM.initCfg input) firstFuel
      hnotHalted
  have hfuelCost : firstFuel ≤
      RAM.logTimeUpto program firstFuel (RAM.initCfg input) := by
    calc
      firstFuel = RAM.unitTimeUpto program firstFuel (RAM.initCfg input) :=
        hunit.symm
      _ ≤ RAM.logTimeUpto program firstFuel (RAM.initCfg input) :=
        RAM.unitTimeUpto_le_logTimeUpto program firstFuel (RAM.initCfg input)
  have hcostMono := RAM.logTimeUpto_mono program
    (c := RAM.initCfg input) hfirstLe
  have hfirstCost : RAM.logTimeUpto program firstFuel (RAM.initCfg input) ≤
      T input.length := le_trans hcostMono hcost
  have hrunEq : RAM.run program fuel (RAM.initCfg input) =
      RAM.run program firstFuel (RAM.initCfg input) :=
    RAM.run_eq_of_halted_le program hfirstLe hfirstHalted
  have hmachine := programDecisionTM_hoareTime_ramRun
    standardControlInstructionTapes program input firstFuel hfirstHalted
  obtain ⟨final, time, htime, hreach, hfinalHalted, houtput⟩ :=
    hmachine (Tape.init (input.map Γ.ofBool))
      (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  have hresource := programDecisionTime_le_envelope
    standardControlInstructionTapes program input firstFuel hfirstHalted
      hfuelCost
  have henvelope := programDecisionEnvelope_mono_cost program input.length
    (RAM.logTimeUpto program firstFuel (RAM.initCfg input))
      (T input.length) hfirstCost
  refine ⟨final, time, le_trans htime (le_trans hresource henvelope),
    hreach, hfinalHalted, ?_⟩
  by_cases hmember : input ∈ L
  · have hverdict :
        (RAM.run program firstFuel (RAM.initCfg input)).verdict = 1 := by
      rw [← hrunEq]
      exact hyes hmember
    rw [houtput, hverdict]
    simpa [languageFlag, hmember] using! registerVerdictOutput_hasOutput 1
  · have hverdict :
        (RAM.run program firstFuel (RAM.initCfg input)).verdict = 0 := by
      rw [← hrunEq]
      exact hno hmember
    rw [houtput, hverdict]
    simpa [languageFlag, hmember] using! registerVerdictOutput_hasOutput 0

/-- If the RAM time bound is a polynomial evaluation, its one-bit answer is a
genuine deterministic Turing-machine `FP` function. -/
theorem languageFlag_mem_FP_of_ramProgram
    {L : Language} [DecidablePred (fun word => word ∈ L)]
    (program : RAM.Program) (p : Polynomial ℕ)
    (hdecides : program.DecidesInTime L p.eval) :
    languageFlag L ∈ Complexity.FP := by
  apply mem_FP_iff_computesInTime_polynomial.mpr
  refine ⟨20, programDecisionTM standardControlInstructionTapes program,
    programDecisionPolynomial program p, ?_⟩
  simpa only [programDecisionPolynomial_eval] using!
    programDecision_computesLanguageFlagInTime program hdecides

/-- Reserve a fixed prefix of zero input registers for a RAM program's direct
scratch registers.  The semantic payload begins immediately after it. -/
def prefixZeroRegisters (count : ℕ) (word : List Bool) : List Bool :=
  List.replicate count false ++ word

theorem prefixZeroRegisters_mem_FP (count : ℕ) :
    prefixZeroRegisters count ∈ Complexity.FP := by
  simpa only [prefixZeroRegisters] using!
    machineAppend_mem_FP (machineConst_mem_FP (List.replicate count false))
      id_mem_FP

/-- Language seen through a fixed zero-register prefix. -/
def paddedLanguage (count : ℕ) (L : Language) : Language :=
  {word | word.drop count ∈ L}

instance paddedLanguage_decidable (count : ℕ) (L : Language)
    [DecidablePred (fun word => word ∈ L)] :
    DecidablePred (fun word => word ∈ paddedLanguage count L) := by
  intro word
  change Decidable (word.drop count ∈ L)
  infer_instance

theorem languageFlag_padded_prefix (count : ℕ) (L : Language)
    [DecidablePred (fun word => word ∈ L)] (word : List Bool) :
    languageFlag (paddedLanguage count L) (prefixZeroRegisters count word) =
      languageFlag L word := by
  simp [languageFlag, paddedLanguage, prefixZeroRegisters]

/-- A RAM decider may safely use a fixed direct-register prefix: preprocessing
that prefix and composing the verified one-bit simulator remains in `FP`. -/
theorem languageFlag_mem_FP_of_paddedRamProgram
    (count : ℕ) {L : Language}
    [DecidablePred (fun word => word ∈ L)]
    (program : RAM.Program) (p : Polynomial ℕ)
    (hdecides : program.DecidesInTime (paddedLanguage count L) p.eval) :
    languageFlag L ∈ Complexity.FP := by
  have hpadded : languageFlag (paddedLanguage count L) ∈ Complexity.FP :=
    languageFlag_mem_FP_of_ramProgram program p hdecides
  have hcomposed :
      (fun word => languageFlag (paddedLanguage count L)
        (prefixZeroRegisters count word)) ∈ Complexity.FP :=
    machineCompose_mem_FP (prefixZeroRegisters_mem_FP count) hpadded
  have heq : (fun word => languageFlag (paddedLanguage count L)
      (prefixZeroRegisters count word)) = languageFlag L := by
    funext word
    exact languageFlag_padded_prefix count L word
  rwa [heq] at hcomposed

end MachineRAMBridge

end BeyondBethe

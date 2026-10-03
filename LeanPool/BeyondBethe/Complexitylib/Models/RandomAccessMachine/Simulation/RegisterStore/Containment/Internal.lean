/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.NormalForm
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Classes
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Containment.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBounds
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecision
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Decision
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.SetNotationForOrder

/-!
# RAM-to-TM time-class containment -- proof internals

The concrete sparse simulator is applied at the first halting fuel. Minimality
makes that fuel equal to unit-cost time, hence no larger than logarithmic RAM
time. This discharges the quantitative side condition of the checked runtime
envelope and lifts the simulation to deterministic polynomial time.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

theorem programDecisionPolynomial_eval_internal (program : Program)
    (p : Polynomial ℕ) (inputLength : ℕ) :
    (programDecisionPolynomial program p).eval inputLength =
      programDecisionEnvelope program inputLength (p.eval inputLength) := by
  simp [programDecisionPolynomial, programDecisionEnvelope,
    programDecisionScale, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]
  ring_nf
  exact Or.inl trivial

theorem programDecision_decidesInTime_internal
    {L : Language} {T : ℕ → ℕ} (program : Program)
    (hdecides : program.DecidesInTime L T) :
    (programDecisionTM standardControlInstructionTapes program).DecidesInTime L
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
    standardControlInstructionTapes program input firstFuel hfirstHalted hfuelCost
  have henvelope := programDecisionEnvelope_mono_cost program input.length
    (RAM.logTimeUpto program firstFuel (RAM.initCfg input)) (T input.length)
    hfirstCost
  refine ⟨final, time, le_trans htime (le_trans hresource henvelope),
    hreach, hfinalHalted, ?_, ?_⟩
  · intro hmember
    rw [houtput, registerVerdictOutput_cell_one]
    have hverdict :
        (RAM.run program firstFuel (RAM.initCfg input)).verdict = 1 := by
      rw [← hrunEq]
      exact hyes hmember
    rw [hverdict]
    decide
  · intro hnotMember
    rw [houtput, registerVerdictOutput_cell_one]
    have hverdict :
        (RAM.run program firstFuel (RAM.initCfg input)).verdict = 0 := by
      rw [← hrunEq]
      exact hno hnotMember
    rw [hverdict]
    decide

theorem denseProgramDecision_decidesInTime_internal
    {L : Language} {T : ℕ → ℕ} (program : Program)
    (hdecides : program.DecidesInTime L T) :
    (denseProgramDecisionTM standardControlInstructionTapes program).DecidesInTime L
      (fun inputLength =>
        denseProgramDecisionEnvelope program inputLength (T inputLength)) := by
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
  have hmachine := denseProgramDecisionTM_hoareTime_ramRun
    standardControlInstructionTapes program input firstFuel hfirstHalted
  obtain ⟨final, time, htime, hreach, hfinalHalted, houtput⟩ :=
    hmachine (Tape.init (input.map Γ.ofBool))
      (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  have hresource := denseProgramDecisionTime_le_envelope
    standardControlInstructionTapes program input firstFuel hfirstHalted hfuelCost
  have henvelope := denseProgramDecisionEnvelope_mono_cost program input.length
    (RAM.logTimeUpto program firstFuel (RAM.initCfg input)) (T input.length)
    hfirstCost
  refine ⟨final, time, le_trans htime (le_trans hresource henvelope),
    hreach, hfinalHalted, ?_, ?_⟩
  · intro hmember
    rw [houtput, registerVerdictOutput_cell_one]
    have hverdict :
        (RAM.run program firstFuel (RAM.initCfg input)).verdict = 1 := by
      rw [← hrunEq]
      exact hyes hmember
    rw [hverdict]
    decide
  · intro hnotMember
    rw [houtput, registerVerdictOutput_cell_one]
    have hverdict :
        (RAM.run program firstFuel (RAM.initCfg input)).verdict = 0 := by
      rw [← hrunEq]
      exact hno hnotMember
    rw [hverdict]
    decide

theorem DTIME_subset_DTIME_sq_internal (T : ℕ → ℕ)
    (hinput : (fun inputLength => inputLength + 1) =O T) :
    RAM.DTIME T ⊆ Complexity.DTIME (fun inputLength => (T inputLength) ^ 2) := by
  intro L hL
  obtain ⟨program, timeBound, hdecides, htimeBound⟩ := hL
  have htm := denseProgramDecision_decidesInTime_internal program hdecides
  refine ⟨20, denseProgramDecisionTM standardControlInstructionTapes program,
    (fun inputLength => denseProgramDecisionEnvelope program inputLength
      (timeBound inputLength)), htm, ?_⟩
  have hsumRaw := BigO.add hinput htimeBound
  have hsum : (fun inputLength => inputLength + timeBound inputLength + 1) =O T := by
    convert hsumRaw using 1
    ext inputLength
    omega
  have hsquare := BigO.pow hsum 2
  have hconstant := BigO.const_mul_left
    (500000000000 * (programResourceMagnitude program + 1) ^ 4) hsquare
  simpa only [denseProgramDecisionEnvelope, Nat.mul_assoc] using hconstant

theorem P_subset_internal : RAM.P ⊆ Complexity.P := by
  intro L hL
  obtain ⟨degree, program, timeBound, hdecides, hbigO⟩ :=
    Set.mem_iUnion.mp hL
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hbigO
  have hramPolynomial := RAM.Program.DecidesInTime.mono hp hdecides
  have htm := programDecision_decidesInTime_internal program hramPolynomial
  apply mem_P_iff_decidesInTime_polynomial.mpr
  refine ⟨20, programDecisionTM standardControlInstructionTapes program,
    programDecisionPolynomial program p, ?_⟩
  simpa only [programDecisionPolynomial_eval_internal] using htm

end Machine

end RegisterStore

end RAM

end Complexity

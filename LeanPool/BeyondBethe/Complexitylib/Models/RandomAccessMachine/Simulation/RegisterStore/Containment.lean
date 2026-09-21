/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Containment.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Containment

/-!
# RAM-to-TM time-class containment

The fixed twenty-work-tape simulators transfer logarithmic-cost RAM deciders to
deterministic Turing deciders. The sparse fallback gives the original quartic
polynomial envelope; the dense-input overlay gives the sharp quadratic
parametric containment. Together with the sparse TM-to-RAM compiler, these
establish machine-model robustness of polynomial time.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Evaluating the packaged simulator polynomial gives its concrete runtime
envelope with the supplied polynomial RAM-time bound. -/
theorem programDecisionPolynomial_eval (program : Program)
    (p : Polynomial ℕ) (inputLength : ℕ) :
    (programDecisionPolynomial program p).eval inputLength =
      programDecisionEnvelope program inputLength (p.eval inputLength) :=
  programDecisionPolynomial_eval_internal program p inputLength

/-- Every RAM decider transfers to the fixed sparse Turing simulator with the
explicit fourth-degree envelope around its logarithmic-time bound. -/
theorem programDecision_decidesInTime
    {L : Language} {T : ℕ → ℕ} (program : Program)
    (hdecides : program.DecidesInTime L T) :
    (programDecisionTM standardControlInstructionTapes program).DecidesInTime L
      (fun inputLength =>
        programDecisionEnvelope program inputLength (T inputLength)) :=
  programDecision_decidesInTime_internal program hdecides

/-- Every RAM decider transfers to the optimized fixed dense-input simulator
with an explicit quadratic envelope in input length plus RAM time. -/
theorem denseProgramDecision_decidesInTime
    {L : Language} {T : ℕ → ℕ} (program : Program)
    (hdecides : program.DecidesInTime L T) :
    (denseProgramDecisionTM standardControlInstructionTapes program).DecidesInTime L
      (fun inputLength =>
        denseProgramDecisionEnvelope program inputLength (T inputLength)) :=
  denseProgramDecision_decidesInTime_internal program hdecides

/-- Under the standard assumption that the RAM time bound dominates reading
the input, logarithmic-cost RAM time `T` is contained in deterministic Turing
time `T²`. -/
theorem RAM_DTIME_subset_DTIME_sq (T : ℕ → ℕ)
    (hinput : (fun inputLength => inputLength + 1) =O T) :
    RAM.DTIME T ⊆ Complexity.DTIME (fun inputLength => (T inputLength) ^ 2) :=
  DTIME_subset_DTIME_sq_internal T hinput

/-- Every polynomial logarithmic-cost RAM language is in deterministic
polynomial Turing time. -/
theorem RAM_P_subset_P : RAM.P ⊆ Complexity.P :=
  P_subset_internal

/-- Polynomial time is invariant between the concrete multitape TM and
logarithmic-cost RAM models formalized in the library. -/
theorem RAM_P_eq_P : RAM.P = Complexity.P :=
  Set.Subset.antisymm RAM_P_subset_P
    RAM.TMConfig.Sparse.P_subset_RAM_P

end Machine

end RegisterStore

end RAM

end Complexity

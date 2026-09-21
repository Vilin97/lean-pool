/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Lift
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairValidate.Defs

/-!
# Pair-encoding validator — proof internals

The finite-state fold is related to `unpair?`, then the generic scanner
correctness theorem supplies the executable machine proof and exact time bound.
-/


public section

namespace Complexity

namespace TM

/-- Semantic meaning of a validator state with a yet-unread suffix. The three
prefix states reconstruct the pending decoder input; the absorbing states have
constant verdicts. -/
private def pairValidateSuffix : PairValidateState → List Bool → Bool
  | .next, bits => (unpair? bits).isSome
  | .afterZero, bits => (unpair? (false :: bits)).isSome
  | .afterOne, bits => (unpair? (true :: bits)).isSome
  | .suffix, _ => true
  | .invalid, _ => false

/-- Folding the validator over a suffix produces exactly the semantic verdict
associated with the incoming control state. -/
private theorem pairValidate_fold_correct (state : PairValidateState) (bits : List Bool) :
    pairValidateAccept (bits.foldl pairValidateStep state) =
      pairValidateSuffix state bits := by
  induction bits generalizing state with
  | nil =>
      cases state <;> simp [pairValidateAccept, pairValidateSuffix, unpair?]
  | cons bit bits ih =>
      rw [List.foldl_cons, ih]
      cases state <;> cases bit <;>
        simp [pairValidateStep, pairValidateSuffix, unpair?]

/-- The pair-validator fold accepts exactly when `unpair?` succeeds. -/
theorem pairValidateAccept_fold_eq_true_iff_internal (bits : List Bool) :
    pairValidateAccept (bits.foldl pairValidateStep .next) = true ↔
      (unpair? bits).isSome = true := by
  rw [pairValidate_fold_correct]
  rfl

/-- The finite-state pair validator decides all well-formed pair encodings in
the generic scanner's exact `n + 2` time bound. -/
theorem pairValidateTM_decidesInTime_internal :
    pairValidateTM.DecidesInTime validPairEncoding (fun n => n + 2) := by
  apply scannerTM_decidesInTime .next pairValidateStep pairValidateAccept
  intro bits
  change (unpair? bits).isSome = true ↔
    pairValidateAccept (bits.foldl pairValidateStep .next) = true
  exact (pairValidateAccept_fold_eq_true_iff_internal bits).symm

/-- Frame-rich initialized specification for the lifted validator. -/
theorem pairValidateTM_lift_hoareTime_internal (workTapes : ℕ) (bits : List Bool) :
    (pairValidateTM.liftTM workTapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (bits.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        AllTapesWF inp work out ∧
        inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
        inp.head ≤ bits.length + 2 ∧
        (∀ i, work i = (Tape.init []).move Dir3.right) ∧
        out.head ≤ bits.length + 2 ∧
        (bits ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (bits ∉ validPairEncoding → out.cells 1 = Γ.zero))
      (bits.length + 2) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    scannerTM_reachesIn .next pairValidateStep
      (fun state => if pairValidateAccept state then .one else .zero) bits
  let C := pairValidateTM.liftCfg workTapes c'
  have hreachLift :
      (pairValidateTM.liftTM workTapes).reachesIn (bits.length + 2)
        ((pairValidateTM.liftTM workTapes).initCfg bits) C := by
    exact liftTM_reachesIn_initCfg_of_pos pairValidateTM workTapes bits
      (by omega) hreach
  have hinputCells :
      c'.input.cells = (Tape.init (bits.map Γ.ofBool)).cells :=
    input_cells_eq_of_reachesIn hreach
  have hheads := head_le_of_reachesIn pairValidateTM hreach
  have hwork : ∀ i, C.work i = (Tape.init []).move Dir3.right := by
    intro i
    exact liftCfg_work_ge pairValidateTM workTapes c' i (by omega)
  have houtput0 : c'.output.cells 0 = Γ.start :=
    output_cells_zero_eq_start_of_reachesIn hreach rfl
  have houtputNoStart : ∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start :=
    output_cells_ne_start_of_reachesIn hreach (by
      intro j hj
      cases j with
      | zero => omega
      | succ j => simp [Tape.init])
  have hwf : AllTapesWF C.input C.work C.output := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [liftCfg_input, hinputCells]
      rfl
    · intro j hj
      rw [liftCfg_input, hinputCells]
      exact Tape.init_ofBool_cells_ne_start bits j hj
    · intro i
      rw [hwork i]
      rfl
    · intro i j hj
      rw [hwork i]
      cases j with
      | zero => omega
      | succ j => simp [Tape.move, Tape.init]
    · simpa only [liftCfg_output] using houtput0
    · simpa only [liftCfg_output] using houtputNoStart
  have hyes : bits ∈ validPairEncoding → C.output.cells 1 = Γ.one := by
    intro hmem
    rw [show C.output = c'.output from rfl, hout]
    have haccept :
        pairValidateAccept (bits.foldl pairValidateStep .next) = true :=
      (pairValidateAccept_fold_eq_true_iff_internal bits).2 hmem
    simp [haccept]
  have hno : bits ∉ validPairEncoding → C.output.cells 1 = Γ.zero := by
    intro hmem
    rw [show C.output = c'.output from rfl, hout]
    have haccept :
        pairValidateAccept (bits.foldl pairValidateStep .next) = false := by
      cases hstate : pairValidateAccept (bits.foldl pairValidateStep .next) with
      | false => rfl
      | true =>
          exact absurd
            ((pairValidateAccept_fold_eq_true_iff_internal bits).1 hstate) hmem
    simp [haccept]
  refine ⟨C, bits.length + 2, le_rfl, hreachLift, ?_, hwf, ?_, ?_, hwork, ?_,
    hyes, hno⟩
  · exact hhalt
  · exact hinputCells
  · exact hheads.1
  · exact hheads.2.1

end TM

end Complexity

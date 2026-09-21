/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# Clearing a binary work tape — proof internals

This module packages the legacy rich clear/rewind proof behind a literal frame
contract and proves that its component machines never move the output head
left.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

theorem clearWorkTM_hoareTime_frame_internal
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx =
      (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (clearWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (clearWorkTimeBound bits.length) := by
  let Frame : TapePred n := fun inp work out =>
    inp = inp₀ ∧ (∀ i, i ≠ idx → work i = work₀ i) ∧ out = out₀
  have hclear := clearWorkTM_hoareTime_frame_of_binaryString idx bits
    (P := Frame) (by
      intro inp work out inp' work' out' hframe _htarget hinp' hout' hwork'
      rcases hframe with ⟨hinp₀, hwork₀, hout₀⟩
      refine ⟨hinp'.trans hinp₀, ?_, hout'.trans hout₀⟩
      intro i hi
      exact (hwork' i hi).trans (hwork₀ i hi))
  refine hclear.consequence ?_ ?_ (by simp [clearWorkTimeBound]; omega)
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨htarget, hinp.read_ne_start, hout.read_ne_start, hout.1, ?_, ?_⟩
    · intro i hi
      exact ⟨(hother i hi).read_ne_start, (hother i hi).1⟩
    · exact ⟨rfl, fun _ _ => rfl, rfl⟩
  · rintro inp work out ⟨htarget', hinp', hother', hout'⟩
    refine ⟨hinp', ?_, hout'⟩
    funext i
    by_cases hi : i = idx
    · subst i
      rw [Function.update_self]
      exact htarget'
    · rw [Function.update_of_ne hi]
      exact hother' i hi

theorem clearWorkTM_hoareTimeSpace_frame_internal
    (idx : Fin n) (bits : List Bool) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx =
      (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀)
    (hinitial :
      ({ state := (clearWorkTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (clearWorkTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (clearWorkTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (clearWorkTimeBound bits.length) inputLength
      (initialSpace + clearWorkTimeBound bits.length) := by
  apply (clearWorkTM_hoareTime_frame_internal idx bits inp₀ work₀ out₀
    htarget hinp hother hout).toHoareTimeSpace
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact hinitial

theorem blankWorkTM_isTransducer_internal (idx : Fin n) :
    (blankWorkTM idx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | scanning =>
      simp only [blankWorkTM]
      split <;> simp [idleDir] <;> split <;> decide
  | done =>
      simp [blankWorkTM, allIdle, idleDir]
      split <;> decide

theorem rewindWorkTM_isTransducer_internal (idx : Fin n) :
    (rewindWorkTM idx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | moveLeft =>
      simp only [rewindWorkTM]
      split <;> simp [idleDir] <;> split <;> decide
  | moveRight =>
      simp [rewindWorkTM, idleDir]
      split <;> decide
  | done =>
      simp [rewindWorkTM, allIdle, idleDir]
      split <;> decide

theorem clearWorkTM_isTransducer_internal (idx : Fin n) :
    (clearWorkTM idx).IsTransducer :=
  (blankWorkTM_isTransducer_internal idx).seqTM
    (rewindWorkTM_isTransducer_internal idx)

end TM

end Complexity

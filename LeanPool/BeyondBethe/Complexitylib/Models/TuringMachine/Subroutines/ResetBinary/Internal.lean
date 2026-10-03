/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Defs

/-!
# Resetting a binary work tape — proof internals
-/


@[expose] public section

namespace Complexity

namespace TM

theorem rewindBinaryWorkTM_hoareTime_frame_internal {n : ℕ}
    (idx : Fin n) (bits : List Bool) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ idx).HasBinaryContent bits)
    (htargetStart : (work₀ idx).cells 0 = Γ.start)
    (htargetHead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work idx = (Tape.init (bits.map Γ.ofBool)).move Dir3.right ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out = out₀)
      (headBound + 2) := by
  let RewindFrame : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work idx).HasBinaryContent bits ∧
    (work idx).cells 0 = Γ.start ∧
    (∀ i, i ≠ idx → work i = work₀ i) ∧
    out = out₀
  have hrewindBase := rewindWorkTM_hoareTime_frame idx headBound
    (P := RewindFrame) (by
      intro inp work out inp' work' out' hframe hcells _hhead hwork hinp
        houtCells houtHead
      rcases hframe with ⟨hframeInput, hframeContent, hframeStart,
        hframeOther, hframeOutput⟩
      refine ⟨hinp.trans hframeInput, ?_, ?_, ?_, ?_⟩
      · simpa only [Tape.HasBinaryContent, hcells] using hframeContent
      · rw [hcells]
        exact hframeStart
      · intro i hi
        exact (hwork i hi).trans (hframeOther i hi)
      · exact (Tape.ext houtHead houtCells).trans hframeOutput)
  apply hrewindBase.consequence (b' := headBound + 2)
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨htargetStart, htarget.cells_ne_start, htargetHead.2,
      hinput.read_ne_start, houtput.read_ne_start, houtput.1, ?_,
      rfl, htarget, htargetStart, (fun _ _ => rfl), rfl⟩
    intro i hi
    exact ⟨(hother i hi).read_ne_start, (hother i hi).1⟩
  · intro inp work out hpost
    rcases hpost with ⟨hhead, hframeInput, hcontent, hstart,
      hframeOther, hframeOutput⟩
    refine ⟨hframeInput, ?_, hframeOther, hframeOutput⟩
    exact Tape.eq_init_move_right_of_hasBinaryString
      (hcontent.hasBinaryString hhead) hstart
  · exact le_rfl

theorem resetBinaryWorkTM_hoareTime_frame_internal {n : ℕ}
    (idx : Fin n) (bits : List Bool) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ idx).HasBinaryContent bits)
    (htargetStart : (work₀ idx).cells 0 = Γ.start)
    (htargetHead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (resetBinaryWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (resetBinaryWorkTime headBound bits.length) := by
  have hrewind := rewindBinaryWorkTM_hoareTime_frame_internal idx bits
    headBound inp₀ work₀ out₀ htarget htargetStart htargetHead hinput
    hother houtput
  let ClearFrame : TapePred n := fun inp work out =>
    inp = inp₀ ∧ (∀ i, i ≠ idx → work i = work₀ i) ∧ out = out₀
  have hclear := clearWorkTM_hoareTime_frame_of_binaryString idx bits
    (P := ClearFrame) (by
      intro inp work out inp' work' out' hframe _htarget hinp hout hwork
      rcases hframe with ⟨hframeInput, hframeOther, hframeOutput⟩
      exact ⟨hinp.trans hframeInput, fun i hi =>
        (hwork i hi).trans (hframeOther i hi), hout.trans hframeOutput⟩)
  have hclear' : (clearWorkTM idx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        work idx = (Tape.init (bits.map Γ.ofBool)).move Dir3.right ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (clearWorkTimeBound bits.length) := by
    apply hclear.consequence (b' := clearWorkTimeBound bits.length)
    · intro inp work out hpre
      rcases hpre with ⟨hinp, htargetEq, hwork, hout⟩
      refine ⟨htargetEq, ?_, ?_, ?_, ?_, hinp, hwork, hout⟩
      · rw [hinp]
        exact hinput.read_ne_start
      · rw [hout]
        exact houtput.read_ne_start
      · rw [hout]
        exact houtput.1
      · intro i hi
        rw [hwork i hi]
        exact ⟨(hother i hi).read_ne_start, (hother i hi).1⟩
    · intro inp work out hpost
      rcases hpost with ⟨htargetEq, hinp, hwork, hout⟩
      refine ⟨hinp, ?_, hout⟩
      funext i
      by_cases hi : i = idx
      · subst i
        rw [Function.update_self]
        exact htargetEq
      · rw [Function.update_of_ne hi]
        exact hwork i hi
    · unfold clearWorkTimeBound
      omega
  unfold resetBinaryWorkTM resetBinaryWorkTime
  exact seqTM_hoareTime (rewindWorkTM idx) (clearWorkTM idx) hrewind
    (by
      intro inp work out hmid
      rcases hmid with ⟨hinp, htargetEq, hwork, hout⟩
      have hreads : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hi : i = idx
        · subst i
          rw [htargetEq]
          exact Tape.init_ofBool_move_right_read_ne_start bits
        · rw [hwork i hi]
          exact (hother i hi).read_ne_start
      obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
        phaseTransition_eq_self_of_reads_ne_start
          (hinp ▸ hinput.read_ne_start) hreads (hout ▸ houtput.read_ne_start)
      rw [hinputTransition, hworkTransition, houtputTransition]
      exact ⟨hinp, htargetEq, hwork, hout⟩)
    hclear'

end TM

end Complexity

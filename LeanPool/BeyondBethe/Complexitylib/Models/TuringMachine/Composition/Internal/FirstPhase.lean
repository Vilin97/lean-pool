/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Placement.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal

/-!
# Function composition: first-phase boundary

This module runs the first function machine with its output redirected to the
raw-output work tape, places that run in the composite layout, and exposes the
exact tape facts required by the normalization tail.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

/-- Start-tape well-formedness is preserved over a deterministic run. -/
private theorem reachesIn_startInvariant {n : ℕ} {tm : TM n}
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (hin : c.input.StartInvariant)
    (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
      c'.output.StartInvariant := by
  induction hreach with
  | zero => exact ⟨hin, hwork, hout⟩
  | step hstep _ ih =>
      obtain ⟨hin1, hwork1, hout1⟩ := Tape.StartInvariant.step tm hstep hin hwork hout
      exact ih hin1 hwork1 hout1

/-- A phase-boundary work-tape action preserves the start invariant and moves
the head off the left-end marker. -/
private theorem transitionTape_boundary {t : Tape} (h : t.StartInvariant) :
    (transitionTape t).StartInvariant ∧ 1 ≤ (transitionTape t).head := by
  refine ⟨⟨?_, ?_⟩, one_le_head_transitionTape t h.1⟩
  · rw [transitionTape_cells t h.2]
    exact h.1
  · intro j hj
    rw [transitionTape_cells t h.2]
    exact h.2 j hj

/-- The input counterpart of `transitionTape_boundary`. -/
private theorem transitionInput_boundary {t : Tape} (h : t.StartInvariant) :
    (transitionInput t).StartInvariant ∧ 1 ≤ (transitionInput t).head := by
  refine ⟨⟨?_, ?_⟩, transitionInput_head_ge t h.1⟩
  · rw [transitionInput_cells]
    exact h.1
  · intro j hj
    rw [transitionInput_cells]
    exact h.2 j hj

/-- A blank output tape whose head is still at zero or one becomes the
canonical parked blank tape at a phase boundary. -/
private theorem transitionTape_blank_eq_parked {t : Tape}
    (hcells : t.cells = (Tape.init []).cells) (hhead : t.head ≤ 1) :
    transitionTape t = (Tape.init []).move Dir3.right := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hhead with hzero | hone
  · have ht : t = Tape.init [] := Tape.ext hzero hcells
    subst ht
    rfl
  · have ht : t = (Tape.init []).move Dir3.right := by
      apply Tape.ext
      · exact hone
      · simpa only [Tape.move_cells] using hcells
    subst ht
    exact transitionTape_eq_self (by decide)

/-- The first computation reaches a halted composite-layout boundary within
its original time bound. The raw output remains readable, the destination for
the canonical virtual input is still fresh, and every seam tape is parked in
a start-invariant state. -/
theorem compositionFirstTM_boundary_internal (tmF : TM nf) (ng : ℕ)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : tmF.ComputesInTime f T) (x : List Bool) :
    ∃ (C : Cfg (compositionTapeCount nf ng) (compositionFirstTM tmF ng).Q)
      (t : ℕ),
      t ≤ T x.length ∧
      (compositionFirstTM tmF ng).reachesIn t
        ((compositionFirstTM tmF ng).initCfg x) C ∧
      (compositionFirstTM tmF ng).halted C ∧
      (transitionTape (C.work (compositionRawOutputIdx nf ng))).HasOutput (f x) ∧
      (transitionTape (C.work (compositionRawOutputIdx nf ng))).head ≤ t + 1 ∧
      transitionTape (C.work (compositionVirtualInputIdx nf ng)) =
        (Tape.init []).move Dir3.right ∧
      (∀ j : Fin ng,
        transitionTape (C.work (compositionSecondWorkIdx nf ng j)) =
          (Tape.init []).move Dir3.right) ∧
      (transitionInput C.input).StartInvariant ∧
      1 ≤ (transitionInput C.input).head ∧
      (∀ i, (transitionTape (C.work i)).StartInvariant ∧
        1 ≤ (transitionTape (C.work i)).head) ∧
      transitionTape C.output = (Tape.init []).move Dir3.right := by
  obtain ⟨cR, t, ht, hreachR, hhaltR, hrawR, houtCells, houtHead⟩ :=
    retargetOutput_computesInTime_boundary tmF hcomp x
  obtain ⟨C, hreachC, hstateC, _hinputC, houtputC, hshapeC⟩ :=
    placeWorkTM_reachesIn_init_internal tmF.retargetOutput 0 (ng + 1) x hreachR
  have hreachFirst : (compositionFirstTM tmF ng).reachesIn t
      ((compositionFirstTM tmF ng).initCfg x) C := by
    simpa [compositionFirstTM] using hreachC
  have hhaltFirst : (compositionFirstTM tmF ng).halted C := by
    show C.state = (compositionFirstTM tmF ng).qhalt
    rw [hstateC]
    exact hhaltR
  have hrawC : (C.work (compositionRawOutputIdx nf ng)).HasOutput (f x) := by
    rcases hshapeC with ht0 | hC
    · subst t
      cases hreachR
      cases hreachC
      simpa [compositionFirstTM, compositionRawOutputIdx, Cfg.init] using hrawR
    · rw [hC, compositionRawOutputIdx_eq_firstPlacedLast]
      have hmiddle := placeWorkCfg_work_middle tmF.retargetOutput 0 (ng + 1)
        (fun _ => (Tape.init []).move Dir3.right) cR (Fin.last nf)
      have houtput := hmiddle ▸ hrawR
      simpa only [placeWorkParkedCfg] using! houtput
  have hvirtual : transitionTape (C.work (compositionVirtualInputIdx nf ng)) =
      (Tape.init []).move Dir3.right := by
    rcases hshapeC with ht0 | hC
    · subst t
      cases hreachC
      rfl
    · rw [hC]
      have hnot : ¬placeWorkInMiddle 0 (nf + 1)
          (compositionVirtualInputIdx nf ng) := by
        simp [placeWorkInMiddle, compositionVirtualInputIdx]
      change transitionTape
        ((placeWorkCfg tmF.retargetOutput 0 (ng + 1)
          (fun _ => (Tape.init []).move Dir3.right) cR).work
            (compositionVirtualInputIdx nf ng)) = _
      have hextra := placeWorkCfg_work_extra tmF.retargetOutput 0 (ng + 1)
        (fun _ => (Tape.init []).move Dir3.right) cR _ hnot
      exact (congrArg transitionTape hextra).trans
        (transitionTape_eq_self (t := (Tape.init []).move Dir3.right) (by decide))
  have hscratch : ∀ j : Fin ng,
      transitionTape (C.work (compositionSecondWorkIdx nf ng j)) =
        (Tape.init []).move Dir3.right := by
    intro j
    let idx := compositionSecondWorkIdx nf ng j
    change transitionTape (C.work idx) = _
    rcases hshapeC with ht0 | hC
    · subst t
      cases hreachC
      rfl
    · rw [hC]
      have hnot : ¬placeWorkInMiddle 0 (nf + 1) idx := by
        simp [placeWorkInMiddle, idx]
      change transitionTape
        ((placeWorkCfg tmF.retargetOutput 0 (ng + 1)
          (fun _ => (Tape.init []).move Dir3.right) cR).work idx) = _
      have hextra := placeWorkCfg_work_extra tmF.retargetOutput 0 (ng + 1)
        (fun _ => (Tape.init []).move Dir3.right) cR _ hnot
      exact (congrArg transitionTape hextra).trans
        (transitionTape_eq_self (t := (Tape.init []).move Dir3.right) (by decide))
  have hinvariants := reachesIn_startInvariant hreachFirst
    (Tape.StartInvariant.init_ofBool x)
    (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil
  have hinBoundary := transitionInput_boundary hinvariants.1
  have hworkBoundary : ∀ i, (transitionTape (C.work i)).StartInvariant ∧
      1 ≤ (transitionTape (C.work i)).head :=
    fun i => transitionTape_boundary (hinvariants.2.1 i)
  have hrawOutput :
      (transitionTape (C.work (compositionRawOutputIdx nf ng))).HasOutput (f x) := by
    exact (Tape.hasOutput_congr
      (transitionTape_cells _ (hinvariants.2.1 _).2) (f x)).mpr hrawC
  have hheads := head_le_of_reachesIn (compositionFirstTM tmF ng) hreachFirst
  have hrawHead :
      (transitionTape (C.work (compositionRawOutputIdx nf ng))).head ≤ t + 1 :=
    head_transitionTape_le (hinvariants.2.1 _).1 (hheads.2.2 _)
  have houtputParked : transitionTape C.output =
      (Tape.init []).move Dir3.right := by
    rw [houtputC]
    exact transitionTape_blank_eq_parked houtCells houtHead
  exact ⟨C, t, ht, hreachFirst, hhaltFirst, hrawOutput, hrawHead, hvirtual,
    hscratch, hinBoundary.1, hinBoundary.2, hworkBoundary, houtputParked⟩

end TM

end Complexity

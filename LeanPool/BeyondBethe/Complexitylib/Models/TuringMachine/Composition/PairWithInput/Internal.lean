/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.PairWithInput.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.OutputBounds
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairEmit

/-!
# Pair a computed value with the original input — proof internals

This module verifies the generic fanout pipeline defined in
`Composition.PairWithInput.Defs`.
-/


public section

namespace Complexity

namespace TM

variable {nf : ℕ}

/-- Boundary contract after the source computation has redirected its output.
Both source heads remain within `B`, every tape is safely parked away from the
left marker, and the real output is fresh for pair emission. -/
def PairWithInputTailPre (nf : ℕ) (first second : List Bool) (B : ℕ)
    (inp : Tape) (work : Fin (pairWithInputTapeCount nf) → Tape)
    (out : Tape) : Prop :=
  let raw := pairWithInputRawOutputIdx nf
  (work raw).HasOutput first ∧
  (work raw).StartInvariant ∧
  (work raw).head ≤ B ∧
  inp.cells = (Tape.init (second.map Γ.ofBool)).cells ∧
  inp.StartInvariant ∧
  1 ≤ inp.head ∧
  inp.head ≤ B ∧
  (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
  out = (Tape.init []).move Dir3.right

/-- Boundary after rewinding the raw computed output. -/
private def PairWithInputAfterRaw (nf : ℕ) (first second : List Bool) (B : ℕ)
    (inp : Tape) (work : Fin (pairWithInputTapeCount nf) → Tape)
    (out : Tape) : Prop :=
  let raw := pairWithInputRawOutputIdx nf
  (work raw).head = 1 ∧
  (work raw).HasOutput first ∧
  inp.cells = (Tape.init (second.map Γ.ofBool)).cells ∧
  inp.StartInvariant ∧
  1 ≤ inp.head ∧
  inp.head ≤ B ∧
  (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
  out = (Tape.init []).move Dir3.right

/-- Boundary after also rewinding the immutable original input. -/
private def PairWithInputEmitterPre (nf : ℕ) (first second : List Bool)
    (inp : Tape) (work : Fin (pairWithInputTapeCount nf) → Tape)
    (out : Tape) : Prop :=
  let raw := pairWithInputRawOutputIdx nf
  inp = (Tape.init (second.map Γ.ofBool)).move Dir3.right ∧
  (work raw).head = 1 ∧
  (work raw).HasOutput first ∧
  (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
  out = (Tape.init []).move Dir3.right

/-- The normalization-and-emission tail turns a raw delimited source output
and the original input into their canonical pair. -/
theorem pairWithInputTailTM_hoareTime_internal (nf : ℕ)
    (first second : List Bool) (B : ℕ) :
    (pairWithInputTailTM nf).HoareTime
      (PairWithInputTailPre nf first second B)
      (fun _inp _work out => out.HasOutput (pair first second))
      (2 * B + pairInputWorkTime first second + 6) := by
  let raw := pairWithInputRawOutputIdx nf
  let RawFrame : TapePred (pairWithInputTapeCount nf) :=
    fun inp work out =>
      (work raw).HasOutput first ∧
      inp.cells = (Tape.init (second.map Γ.ofBool)).cells ∧
      inp.StartInvariant ∧
      1 ≤ inp.head ∧
      inp.head ≤ B ∧
      (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
      out = (Tape.init []).move Dir3.right
  have hrewRaw := rewindWorkTM_hoareTime_frame raw B
    (P := RawFrame) (by
      intro inp work out inp' work' out' hframe hrawCells hrawHead
        hother hinp houtCells houtHead
      rcases hframe with
        ⟨hrawOutput, hinputCells, hinputInv, hinputHead, hinputBound,
          hworkInv, hout⟩
      have hout' : out' = out := Tape.ext houtHead houtCells
      have hrawOutput' : (work' raw).HasOutput first :=
        (Tape.hasOutput_congr hrawCells first).mpr hrawOutput
      have hrawInv' : (work' raw).StartInvariant := by
        refine ⟨?_, ?_⟩
        · rw [hrawCells]
          exact (hworkInv raw).1.1
        · intro j hj
          rw [hrawCells]
          exact (hworkInv raw).1.2 j hj
      refine ⟨hrawOutput', hinp ▸ hinputCells, hinp ▸ hinputInv,
        hinp ▸ hinputHead, hinp ▸ hinputBound, ?_, hout' ▸ hout⟩
      intro i
      by_cases hi : i = raw
      · subst i
        exact ⟨hrawInv', by omega⟩
      · rw [hother i hi]
        exact hworkInv i)
  have hrewRaw' :
      (rewindWorkTM raw).HoareTime
        (PairWithInputTailPre nf first second B)
        (PairWithInputAfterRaw nf first second B)
        (B + 2) := by
    apply hrewRaw.consequence (b' := B + 2)
    · intro inp work out hpre
      rcases hpre with
        ⟨hrawOutput, hrawInv, hrawBound, hinputCells, hinputInv,
          hinputHead, hinputBound, hworkInv, hout⟩
      refine ⟨hrawInv.1, hrawInv.2, hrawBound,
        hinputInv.read_ne_start hinputHead, ?_, ?_, ?_, ?_⟩
      · rw [hout]
        decide
      · rw [hout]
        simp [Tape.move]
      · intro i hi
        exact ⟨(hworkInv i).1.read_ne_start (hworkInv i).2, (hworkInv i).2⟩
      · exact ⟨hrawOutput, hinputCells, hinputInv, hinputHead,
          hinputBound, hworkInv, hout⟩
    · intro inp work out hpost
      rcases hpost with ⟨hrawHead, hrawOutput, hinputCells,
        hinputInv, hinputHead, hinputBound, hworkInv, hout⟩
      exact ⟨hrawHead, hrawOutput, hinputCells, hinputInv,
        hinputHead, hinputBound, hworkInv, hout⟩
    · exact le_rfl
  let InputFrame : TapePred (pairWithInputTapeCount nf) :=
    fun inp work out =>
      inp.cells = (Tape.init (second.map Γ.ofBool)).cells ∧
      (work raw).head = 1 ∧
      (work raw).HasOutput first ∧
      (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
      out = (Tape.init []).move Dir3.right
  have hrewInput := rewindInputTM_hoareTime_frame B
    (P := InputFrame) (by
      intro inp work out inp' work' out' hframe hinputCells _hinputHead
        hwork hout
      rcases hframe with
        ⟨hcanonical, hrawHead, hrawOutput, hworkInv, houtEq⟩
      subst work'
      subst out'
      exact ⟨hinputCells.trans hcanonical, hrawHead, hrawOutput,
        hworkInv, houtEq⟩)
  have hrewInput' :
      rewindInputTM.HoareTime
        (PairWithInputAfterRaw nf first second B)
        (PairWithInputEmitterPre nf first second)
        (B + 2) := by
    apply hrewInput.consequence (b' := B + 2)
    · intro inp work out hpre
      rcases hpre with
        ⟨hrawHead, hrawOutput, hinputCells, hinputInv,
          hinputHead, hinputBound, hworkInv, hout⟩
      refine ⟨hinputInv.1, hinputInv.2, hinputBound, ?_, ?_, ?_, ?_⟩
      · rw [hout]
        decide
      · rw [hout]
        simp [Tape.move]
      · intro i
        exact ⟨(hworkInv i).1.read_ne_start (hworkInv i).2, (hworkInv i).2⟩
      · exact ⟨hinputCells, hrawHead, hrawOutput, hworkInv, hout⟩
    · intro inp work out hpost
      rcases hpost with
        ⟨hinputHead, hinputCells, hrawHead, hrawOutput, hworkInv, hout⟩
      have hinput : inp =
          (Tape.init (second.map Γ.ofBool)).move Dir3.right := by
        apply Tape.ext
        · simpa [Tape.move] using hinputHead
        · simpa only [Tape.move_cells] using hinputCells
      exact ⟨hinput, hrawHead, hrawOutput, hworkInv, hout⟩
    · exact le_rfl
  have hemitter := pairInputWorkTM_hoareTime raw first second
  have hinner := seqTM_hoareTime rewindInputTM (pairInputWorkTM raw)
    hrewInput' (by
      intro inp work out hpre
      rcases hpre with ⟨hinput, hrawHead, hrawOutput, hworkInv, hout⟩
      have hinputStable : transitionInput inp = inp := by
        apply transitionInput_eq_self
        rw [hinput]
        exact Tape.init_ofBool_move_right_read_ne_start second
      have hworkStable : (fun i => transitionTape (work i)) = work := by
        funext i
        apply transitionTape_eq_self
        exact (hworkInv i).1.read_ne_start (hworkInv i).2
      have hworkStableAt (i) : transitionTape (work i) = work i :=
        congrFun hworkStable i
      have houtStable : transitionTape out = out := by
        apply transitionTape_eq_self
        rw [hout]
        decide
      simpa only [hinputStable, hworkStableAt, houtStable] using
        (show PairWithInputEmitterPre nf first second inp work out from
          ⟨hinput, hrawHead, hrawOutput, hworkInv, hout⟩))
    hemitter
  have htail := seqTM_hoareTime (rewindWorkTM raw)
    (seqTM rewindInputTM (pairInputWorkTM raw)) hrewRaw' (by
      intro inp work out hpre
      rcases hpre with
        ⟨hrawHead, hrawOutput, hinputCells, hinputInv,
          hinputHead, hinputBound, hworkInv, hout⟩
      have hinputStable : transitionInput inp = inp :=
        transitionInput_eq_self (hinputInv.read_ne_start hinputHead)
      have hworkStable : (fun i => transitionTape (work i)) = work := by
        funext i
        apply transitionTape_eq_self
        exact (hworkInv i).1.read_ne_start (hworkInv i).2
      have hworkStableAt (i) : transitionTape (work i) = work i :=
        congrFun hworkStable i
      have houtStable : transitionTape out = out := by
        apply transitionTape_eq_self
        rw [hout]
        decide
      simpa only [hinputStable, hworkStableAt, houtStable] using
        (show PairWithInputAfterRaw nf first second B inp work out from
          ⟨hrawHead, hrawOutput, hinputCells, hinputInv, hinputHead,
            hinputBound, hworkInv, hout⟩))
    hinner
  simpa only [pairWithInputTailTM] using
    htail.mono_bound (by omega)

/-- Internal correctness of the executable fanout combinator. -/
theorem pairWithInputTM_computesInTime_internal
    {tmF : TM nf} {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : tmF.ComputesInTime f T) :
    (pairWithInputTM tmF).ComputesInTime
      (fun x => pair (f x) x) (pairWithInputTime T) := by
  intro x
  obtain ⟨C, t, ht, hreachF, hhaltF, hrawOutput, hrawHead,
      _hvirtual, _hscratch, hinputInv, hinputHead, hworkBoundary,
      houtputParked⟩ :=
    compositionFirstTM_boundary_internal tmF 0 hcomp x
  let boundaryInput := transitionInput C.input
  let boundaryWork : Fin (pairWithInputTapeCount nf) → Tape :=
    fun i => transitionTape (C.work i)
  let boundaryOutput := transitionTape C.output
  have hinputCells : boundaryInput.cells =
      (Tape.init (x.map Γ.ofBool)).cells := by
    dsimp only [boundaryInput]
    rw [transitionInput_cells,
      input_cells_eq_of_reachesIn hreachF]
  have hinputBound : boundaryInput.head ≤ T x.length + 1 := by
    have hhead := (head_le_of_reachesIn
      (compositionFirstTM tmF 0) hreachF).1
    have hmove := Tape.head_move_le C.input (idleDir C.input.read)
    change (C.input.move (idleDir C.input.read)).head ≤ T x.length + 1
    omega
  have htail := pairWithInputTailTM_hoareTime_internal nf
    (f x) x (T x.length + 1)
  obtain ⟨D, u, hu, hreachTail, hhaltTail, houtTail⟩ :=
    htail boundaryInput boundaryWork boundaryOutput (by
      refine ⟨hrawOutput, (hworkBoundary _).1, ?_, hinputCells,
        hinputInv, hinputHead, hinputBound, hworkBoundary, houtputParked⟩
      dsimp only [boundaryWork]
      change (transitionTape
        (C.work (compositionRawOutputIdx nf 0))).head ≤ T x.length + 1
      omega)
  let first := pairWithInputFirstTM tmF
  let tail := pairWithInputTailTM nf
  let final := phase2Wrap first tail D
  refine ⟨final, t + 1 + u, ?_, ?_, ?_, ?_⟩
  · have hlength : (f x).length ≤ T x.length := hcomp.output_length_le x
    have hu' : u ≤ 2 * (T x.length + 1) +
        pairInputWorkTime (f x) x + 6 := hu
    change t + 1 + u ≤ 5 * T x.length + x.length + 12
    simp only [pairInputWorkTime] at hu'
    omega
  · have hreach := seqTM_reachesIn_of_reachesIn first tail
      hreachF hhaltF hreachTail
    simpa [pairWithInputTM, pairWithInputFirstTM, first, tail, final,
      boundaryInput, boundaryWork, boundaryOutput] using hreach
  · show (pairWithInputTM tmF).halted final
    simpa [pairWithInputTM, first, tail, final] using
      (phase2Wrap_halted_iff first tail D).2 hhaltTail
  · simpa [final, phase2Wrap] using houtTail

end TM

end Complexity

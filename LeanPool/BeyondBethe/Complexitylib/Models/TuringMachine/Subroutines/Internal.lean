/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# TM Subroutines: proof internals

Simulation lemmas and `HoareTime` proofs for the rewind, blank, clear, and
copy subroutine machines defined in
`Complexitylib.Models.TuringMachine.Subroutines`. Each subroutine gets a
basic Hoare-style spec, and where needed a rich "frame" variant that threads
an arbitrary predicate `P` on the untouched tapes through the run.

## Main results

- `writeTM_hoareTime` — writes `sym.toΓ` to output cell 1
- `rewindWorkTM_hoareTime` — rewinds work tape `idx` to cell 1
- `rewindWorkTM_hoareTime_frame` — work-tape rewind preserving a predicate P
- `rewindInputTM_hoareTime` — rewinds the input tape to cell 1
- `rewindInputTM_hoareTime_frame` — input rewind preserving a predicate P
- `rewindInputTM_toNTM_hoareTime` — NTM-lifted input rewind spec
- `rewindInputTM_toNTM_hoareTime_frame` — NTM-lifted rich input rewind spec
- `blankWorkTM_started_hoareTime` — blank a started work tape in linear time
- `blankWorkTM_hoareTime_frame_of_binaryString` — frame-preserving blank
- `clearWorkTM_hoareTime_frame_of_binaryString` — blank then rewind to the
  started empty tape, preserving the frame
- `copyInputToWorkTM_started_hoareTime` — copy the Boolean input to a work tape
- `copyWorkToWorkTM_started_hoareTime` — copy one started work tape to another
- `copyWorkToWorkTM_hoareTime_frame_of_binaryString` — frame-preserving
  work-to-work copy
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: rewind loop
-- ════════════════════════════════════════════════════════════════════════

private theorem writeTM_rewind_step_left (sym : Γw) (c : Cfg n (writeTM sym).Q)
    (hst : c.state = WritePhase.rewind) (hread : c.output.read ≠ Γ.start)
    (_ : c.output.cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (writeTM sym).step c = some c' ∧
      c'.state = WritePhase.rewind ∧
      c'.output.head = c.output.head - 1 ∧
      c'.output.cells = c.output.cells := by
  simp only [TM.step, ↓reduceIte, hst, writeTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp only [Tape.writeAndMove, Tape.move]
    rw [toΓ_readBackWrite_of_ne_start hread]
    simp only [Tape.write, Tape.read]; split <;> simp
  · simp only [Tape.writeAndMove, Tape.move_cells]
    rw [toΓ_readBackWrite_of_ne_start hread]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

private theorem writeTM_rewind_step_base (sym : Γw) (c : Cfg n (writeTM sym).Q)
    (hst : c.state = WritePhase.rewind) (hread : c.output.read = Γ.start)
    (_ : c.output.cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (writeTM sym).step c = some c' ∧
      c'.state = WritePhase.goRight ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells := by
  have hhead : c.output.head = 0 := by
    by_contra h; exact hns c.output.head (by omega) (by rwa [Tape.read] at hread)
  simp only [TM.step, ↓reduceIte, hst, writeTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]

private theorem writeTM_rewind_loop (sym : Γw) :
    ∀ (h : ℕ) (c : Cfg n (writeTM sym).Q),
    c.state = WritePhase.rewind →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = h →
    ∃ c',
      (writeTM sym).reachesIn (h + 1) c c' ∧
      c'.state = WritePhase.goRight ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells :=
  exists_reachesIn_of_rewindStep_output (writeTM sym)
    (fun c hst hread hc0 hns => writeTM_rewind_step_left sym c hst hread hc0 hns)
    (fun c hst hread hc0 hns => writeTM_rewind_step_base sym c hst hread hc0 hns)

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: goRight and write steps
-- ════════════════════════════════════════════════════════════════════════

private theorem writeTM_goRight_to_done (sym : Γw) (c : Cfg n (writeTM sym).Q)
    (hstate : c.state = WritePhase.goRight)
    (hhead : c.output.head = 1)
    (hnostart1 : c.output.cells 1 ≠ Γ.start) :
    ∃ c',
      (writeTM sym).reachesIn 2 c c' ∧
      (writeTM sym).halted c' ∧
      c'.output.cells 1 = sym.toΓ := by
  have hoDir : idleDir (c.output.read) = Dir3.stay := by
    simp [idleDir, Tape.read, hhead, hnostart1]
  -- Step 1: goRight → write
  have hstep1 : ∃ c₁, (writeTM sym).step c = some c₁ ∧
      c₁.state = WritePhase.write ∧
      c₁.output.head = 1 ∧
      c₁.output.cells 1 = Γ.blank := by
    simp only [TM.step, hstate, writeTM]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead, hoDir]
    · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead, hoDir,
            Function.update_self, Γw.toΓ]
  obtain ⟨c₁, hstep1', hst1, hhead1, hcell1_blank⟩ := hstep1
  -- Step 2: write → done
  have hoDir2 : idleDir (c₁.output.read) = Dir3.stay := by
    simp [idleDir, Tape.read, hhead1, hcell1_blank]
  have hstep2 : ∃ c₂, (writeTM sym).step c₁ = some c₂ ∧
      c₂.state = WritePhase.done ∧
      c₂.output.cells 1 = sym.toΓ := by
    simp only [TM.step, hst1, writeTM]
    refine ⟨_, rfl, rfl, ?_⟩
    simp [Tape.writeAndMove, Tape.move, Tape.write, hhead1, hoDir2,
          Function.update_self]
  obtain ⟨c₂, hstep2', hst2, hcells2⟩ := hstep2
  exact ⟨c₂, .step hstep1' (.step hstep2' .zero), hst2, hcells2⟩

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `writeTM sym` writes `sym.toΓ` to output cell 1 and halts.
    **Pre**: output tape well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷), head ≤ B.
    **Post**: output cell 1 = sym.toΓ.
    **Time**: B + 3 steps. -/
theorem writeTM_hoareTime (sym : Γw) (B : ℕ) :
    (writeTM (n := n) sym).HoareTime
      (fun _ _ out => out.cells 0 = Γ.start ∧
                      (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
                      out.head ≤ B)
      (fun _ _ out => out.cells 1 = sym.toΓ)
      (B + 3) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  obtain ⟨c_go, hreach_rw, hst_go, hhead_go, hcells_go⟩ :=
    writeTM_rewind_loop sym out.head
      { state := WritePhase.rewind, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
  have hnostart_go : c_go.output.cells 1 ≠ Γ.start := by
    rw [hcells_go]; exact hnostart 1 (by omega)
  obtain ⟨c_done, hreach_wr, hhalt, hwrite⟩ :=
    writeTM_goRight_to_done sym c_go hst_go hhead_go hnostart_go
  refine ⟨c_done, (out.head + 1) + 2, ?_,
    reachesIn_trans (writeTM sym) hreach_rw hreach_wr, hhalt, hwrite⟩
  omega

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: rewind loop
-- ════════════════════════════════════════════════════════════════════════

private theorem rewindWorkTM_rewind_step_left (idx : Fin n) (c : Cfg n (rewindWorkTM idx).Q)
    (hst : c.state = RewindPhase.moveLeft) (hread : (c.work idx).read ≠ Γ.start)
    (_ : (c.work idx).cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) :
    ∃ c', (rewindWorkTM idx).step c = some c' ∧
      c'.state = RewindPhase.moveLeft ∧
      (c'.work idx).head = (c.work idx).head - 1 ∧
      (c'.work idx).cells = (c.work idx).cells := by
  simp only [TM.step, ↓reduceIte, hst, rewindWorkTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · dsimp only []; simp only [↓reduceIte, Tape.writeAndMove, Tape.move]
    rw [toΓ_readBackWrite_of_ne_start hread]
    simp only [Tape.write, Tape.read]; split <;> simp
  · dsimp only []; simp only [↓reduceIte, Tape.writeAndMove, Tape.move_cells]
    rw [toΓ_readBackWrite_of_ne_start hread]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

private theorem rewindWorkTM_rewind_step_base (idx : Fin n) (c : Cfg n (rewindWorkTM idx).Q)
    (hst : c.state = RewindPhase.moveLeft) (hread : (c.work idx).read = Γ.start)
    (_ : (c.work idx).cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) :
    ∃ c', (rewindWorkTM idx).step c = some c' ∧
      c'.state = RewindPhase.moveRight ∧
      (c'.work idx).head = 1 ∧
      (c'.work idx).cells = (c.work idx).cells := by
  have hhead : (c.work idx).head = 0 := by
    by_contra h; exact hns (c.work idx).head (by omega) (by rwa [Tape.read] at hread)
  simp only [TM.step, ↓reduceIte, hst, rewindWorkTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · dsimp only []; simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · dsimp only []; simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]

private theorem rewindWorkTM_rewind_loop (idx : Fin n) :
    ∀ (h : ℕ) (c : Cfg n (rewindWorkTM idx).Q),
    c.state = RewindPhase.moveLeft →
    (c.work idx).cells 0 = Γ.start →
    (∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) →
    (c.work idx).head = h →
    ∃ c',
      (rewindWorkTM idx).reachesIn (h + 1) c c' ∧
      c'.state = RewindPhase.moveRight ∧
      (c'.work idx).head = 1 ∧
      (c'.work idx).cells = (c.work idx).cells :=
  exists_reachesIn_of_rewindStep_tape (rewindWorkTM idx) (fun c => c.work idx)
    (fun c hst hread hc0 hns => rewindWorkTM_rewind_step_left idx c hst hread hc0 hns)
    (fun c hst hread hc0 hns => rewindWorkTM_rewind_step_base idx c hst hread hc0 hns)

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: moveRight step
-- ════════════════════════════════════════════════════════════════════════

private theorem rewindWorkTM_moveRight_to_done (idx : Fin n)
    (c : Cfg n (rewindWorkTM idx).Q)
    (hstate : c.state = RewindPhase.moveRight)
    (hread_ne : (c.work idx).read ≠ Γ.start) :
    ∃ c',
      (rewindWorkTM idx).reachesIn 1 c c' ∧
      (rewindWorkTM idx).halted c' ∧
      (c'.work idx).head = (c.work idx).head := by
  have hoDir : idleDir ((c.work idx).read) = Dir3.stay := by
    simp [idleDir, hread_ne]
  have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
      (rewindWorkTM idx).halted c' ∧
      (c'.work idx).head = (c.work idx).head := by
    simp only [TM.step, hstate, rewindWorkTM, allIdle]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only []
    rw [Tape.writeAndMove, hoDir]
    simp [Tape.move, Tape.write]
    split <;> rfl
  obtain ⟨c', hstep', hhalt, hhead⟩ := hstep
  exact ⟨c', .step hstep' .zero, hhalt, hhead⟩

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `rewindWorkTM idx` rewinds work tape `idx` to cell 1 and halts.
    **Pre**: work tape `idx` well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷), head ≤ B.
    **Post**: work tape `idx` head = 1.
    **Time**: B + 2 steps. -/
theorem rewindWorkTM_hoareTime (idx : Fin n) (B : ℕ) :
    (rewindWorkTM idx).HoareTime
      (fun _ work _ => (work idx).cells 0 = Γ.start ∧
                       (∀ j, j ≥ 1 → (work idx).cells j ≠ Γ.start) ∧
                       (work idx).head ≤ B)
      (fun _ work _ => (work idx).head = 1)
      (B + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  obtain ⟨c_mr, hreach_rw, hst_mr, hhead_mr, hcells_mr⟩ :=
    rewindWorkTM_rewind_loop idx (work idx).head
      { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
  have hread_mr : (c_mr.work idx).read ≠ Γ.start := by
    simp [Tape.read, hhead_mr, hcells_mr]; exact hnostart 1 (by omega)
  obtain ⟨c_done, hreach_mr, hhalt, hhead_done⟩ :=
    rewindWorkTM_moveRight_to_done idx c_mr hst_mr hread_mr
  refine ⟨c_done, ((work idx).head + 1) + 1, ?_,
    reachesIn_trans (rewindWorkTM idx) hreach_rw hreach_mr, hhalt,
    by dsimp only []; rw [hhead_done, hhead_mr]⟩
  omega

-- ════════════════════════════════════════════════════════════════════════
-- rewindInputTM: rewind loop
-- ════════════════════════════════════════════════════════════════════════

private theorem rewindInputTM_rewind_step_left (c : Cfg n (rewindInputTM (n := n)).Q)
    (hst : c.state = RewindPhase.moveLeft) (hread : c.input.read ≠ Γ.start)
    (_ : c.input.cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) :
    ∃ c', (rewindInputTM (n := n)).step c = some c' ∧
      c'.state = RewindPhase.moveLeft ∧
      c'.input.head = c.input.head - 1 ∧
      c'.input.cells = c.input.cells := by
  simp only [TM.step, ↓reduceIte, hst, rewindInputTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [Tape.move, moveLeftDir, hread]
  · simp [Tape.move_cells]

private theorem rewindInputTM_rewind_step_base (c : Cfg n (rewindInputTM (n := n)).Q)
    (hst : c.state = RewindPhase.moveLeft) (hread : c.input.read = Γ.start)
    (_ : c.input.cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) :
    ∃ c', (rewindInputTM (n := n)).step c = some c' ∧
      c'.state = RewindPhase.moveRight ∧
      c'.input.head = 1 ∧
      c'.input.cells = c.input.cells := by
  have hhead : c.input.head = 0 := by
    by_contra h; exact hns c.input.head (by omega) (by rwa [Tape.read] at hread)
  simp only [TM.step, ↓reduceIte, hst, rewindInputTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [Tape.move, hhead]
  · simp [Tape.move_cells]

private theorem rewindInputTM_rewind_loop :
    ∀ (h : ℕ) (c : Cfg n (rewindInputTM (n := n)).Q),
    c.state = RewindPhase.moveLeft →
    c.input.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    c.input.head = h →
    ∃ c',
      (rewindInputTM (n := n)).reachesIn (h + 1) c c' ∧
      c'.state = RewindPhase.moveRight ∧
      c'.input.head = 1 ∧
      c'.input.cells = c.input.cells :=
  exists_reachesIn_of_rewindStep_tape (rewindInputTM (n := n)) (fun c => c.input)
    (fun c hst hread hc0 hns => rewindInputTM_rewind_step_left c hst hread hc0 hns)
    (fun c hst hread hc0 hns => rewindInputTM_rewind_step_base c hst hread hc0 hns)

-- ════════════════════════════════════════════════════════════════════════
-- rewindInputTM: moveRight step
-- ════════════════════════════════════════════════════════════════════════

private theorem rewindInputTM_moveRight_to_done
    (c : Cfg n (rewindInputTM (n := n)).Q)
    (hstate : c.state = RewindPhase.moveRight)
    (hread_ne : c.input.read ≠ Γ.start) :
    ∃ c',
      (rewindInputTM (n := n)).reachesIn 1 c c' ∧
      (rewindInputTM (n := n)).halted c' ∧
      c'.input.head = c.input.head ∧
      c'.input.cells = c.input.cells := by
  have hiDir : idleDir c.input.read = Dir3.stay := by
    simp [idleDir, hread_ne]
  have hstep : ∃ c', (rewindInputTM (n := n)).step c = some c' ∧
      (rewindInputTM (n := n)).halted c' ∧
      c'.input.head = c.input.head ∧
      c'.input.cells = c.input.cells := by
    simp only [TM.step, hstate, rewindInputTM]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · simp [Tape.move, hiDir]
    · simp [Tape.move_cells]
  obtain ⟨c', hstep', hhalt, hhead, hcells⟩ := hstep
  exact ⟨c', .step hstep' .zero, hhalt, hhead, hcells⟩

-- ════════════════════════════════════════════════════════════════════════
-- rewindInputTM: main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `rewindInputTM` rewinds the input tape to cell 1 and halts.
    **Pre**: input tape well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷), head ≤ B.
    **Post**: input head = 1.
    **Time**: B + 2 steps. -/
theorem rewindInputTM_hoareTime (B : ℕ) :
    (rewindInputTM (n := n)).HoareTime
      (fun inp _ _ => inp.cells 0 = Γ.start ∧
                      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
                      inp.head ≤ B)
      (fun inp _ _ => inp.head = 1)
      (B + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  obtain ⟨c_mr, hreach_rw, hst_mr, hhead_mr, hcells_mr⟩ :=
    rewindInputTM_rewind_loop (n := n) inp.head
      { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
  have hread_mr : c_mr.input.read ≠ Γ.start := by
    simp [Tape.read, hhead_mr, hcells_mr]; exact hnostart 1 (by omega)
  obtain ⟨c_done, hreach_mr, hhalt, hhead_done, _hcells_done⟩ :=
    rewindInputTM_moveRight_to_done (n := n) c_mr hst_mr hread_mr
  refine ⟨c_done, (inp.head + 1) + 1, ?_,
    reachesIn_trans (rewindInputTM (n := n)) hreach_rw hreach_mr, hhalt,
    by dsimp only []; rw [hhead_done, hhead_mr]⟩
  omega

-- ════════════════════════════════════════════════════════════════════════
-- rewindInputTM: rich HoareTime preserving arbitrary data
-- ════════════════════════════════════════════════════════════════════════

/-- Rich HoareTime for `rewindInputTM` that preserves an arbitrary predicate P
    through the rewind, provided P is stable when the input cells are unchanged
    and the input head is reset to 1. Work and output tapes are preserved
    exactly under the usual non-start-under-head side conditions. -/
theorem rewindInputTM_hoareTime_frame {n : ℕ} (B_input : ℕ)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      inp'.cells = inp.cells →
      inp'.head = 1 →
      work' = work →
      out' = out →
      P inp' work' out') :
    (rewindInputTM (n := n)).HoareTime
      (fun inp work out =>
        inp.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
        inp.head ≤ B_input ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        inp.head = 1 ∧
        P inp work out)
      (B_input + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le, hout_ns, hout_h, hwork_wf, hP⟩
  have tape_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start → t.head ≥ 1 →
      t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
    intro t hns hh
    simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
    split
    · omega
    · simp only [Tape.read] at hns ⊢
      rw [toΓ_readBackWrite_of_ne_start hns, Function.update_eq_self]
  have input_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start →
      t.move (idleDir t.read) = t := by
    intro t hns
    simp [idleDir, hns, Tape.move]
  suffices h_loop : ∀ (h : ℕ) (c : Cfg n (rewindInputTM (n := n)).Q),
      c.state = RewindPhase.moveLeft →
      c.input.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      c.input.head = h →
      c.work = work → c.output = out →
      ∃ c',
        (rewindInputTM (n := n)).reachesIn (h + 2) c c' ∧
        (rewindInputTM (n := n)).halted c' ∧
        c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
        c'.work = work ∧ c'.output = out by
    obtain ⟨c', hreach, hhalt, hh1, hcells, hwork', hout'⟩ :=
      h_loop inp.head
        { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
        rfl hcell0 hnostart rfl rfl rfl
    refine ⟨c', _, by omega, hreach, hhalt, hh1, ?_⟩
    exact hP_preserved inp work out c'.input c'.work c'.output hP
      (by rw [hcells]) hh1 hwork' hout'
  intro h; induction h with
  | zero =>
    intro c hstate hcell0_c hnostart_c hhead hwork_c hout_c
    have hread : c.input.read = Γ.start := by simp [Tape.read, hhead, hcell0_c]
    have hstep1 : ∃ c₁,
        (rewindInputTM (n := n)).step c = some c₁ ∧
        c₁.state = RewindPhase.moveRight ∧
        c₁.input.head = 1 ∧ c₁.input.cells = c.input.cells ∧
        c₁.work = work ∧ c₁.output = out := by
      simp only [TM.step, ↓reduceIte, hstate, rewindInputTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [Tape.move, hhead]
      · simp [Tape.move_cells]
      · funext i; dsimp only []
        rw [hwork_c]
        exact tape_idle_preserve (work i) (hwork_wf i).1 (hwork_wf i).2
      · dsimp only []; rw [hout_c]
        exact tape_idle_preserve out hout_ns hout_h
    obtain ⟨c₁, hstep1', hst1, hh1, hcells1, hwork1, hout1⟩ := hstep1
    have hread1 : c₁.input.read ≠ Γ.start := by
      simp [Tape.read, hh1, hcells1]; exact hnostart_c 1 (by omega)
    have hstep2 : ∃ c₂,
        (rewindInputTM (n := n)).step c₁ = some c₂ ∧
        (rewindInputTM (n := n)).halted c₂ ∧
        c₂.input.head = 1 ∧ c₂.input.cells = c₁.input.cells ∧
        c₂.work = work ∧ c₂.output = out := by
      simp only [TM.step, hst1, rewindInputTM]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · have := input_idle_preserve c₁.input hread1
        show (c₁.input.move (idleDir c₁.input.read)).head = 1
        rw [this]; exact hh1
      · have := input_idle_preserve c₁.input hread1
        show (c₁.input.move (idleDir c₁.input.read)).cells = c₁.input.cells
        rw [this]
      · funext i; dsimp only []
        rw [hwork1]
        exact tape_idle_preserve (work i) (hwork_wf i).1 (hwork_wf i).2
      · dsimp only []; rw [hout1]
        exact tape_idle_preserve out hout_ns hout_h
    obtain ⟨c₂, hstep2', hhalt, hh2, hcells2, hwork2, hout2⟩ := hstep2
    exact ⟨c₂, .step hstep1' (.step hstep2' .zero), hhalt, hh2,
      by rw [hcells2, hcells1], hwork2, hout2⟩
  | succ h ih =>
    intro c hstate hcell0_c hnostart_c hhead hwork_c hout_c
    have hread_ne : c.input.read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart_c (h + 1) (by omega)
    have hstep : ∃ c₁,
        (rewindInputTM (n := n)).step c = some c₁ ∧
        c₁.state = RewindPhase.moveLeft ∧
        c₁.input.head = h ∧ c₁.input.cells = c.input.cells ∧
        c₁.work = work ∧ c₁.output = out := by
      simp only [TM.step, ↓reduceIte, hstate, rewindInputTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [Tape.move, moveLeftDir, hread_ne, hhead]
      · simp [Tape.move_cells]
      · funext i; dsimp only []
        rw [hwork_c]
        exact tape_idle_preserve (work i) (hwork_wf i).1 (hwork_wf i).2
      · dsimp only []; rw [hout_c]
        exact tape_idle_preserve out hout_ns hout_h
    obtain ⟨c₁, hstep', hst1, hh1, hcells1, hwork1, hout1⟩ := hstep
    obtain ⟨c_f, hreach_f, hhalt_f, hh_f, hcells_f, hwork_f, hout_f⟩ :=
      ih c₁ hst1 (by rw [hcells1]; exact hcell0_c)
        (by intro j hj; rw [hcells1]; exact hnostart_c j hj) hh1 hwork1 hout1
    exact ⟨c_f, .step hstep' hreach_f, hhalt_f, hh_f,
      by rw [hcells_f, hcells1], hwork_f, hout_f⟩

/-- Nondeterministic form of `rewindInputTM_hoareTime`, for phase compositions
    that run deterministic setup subroutines through `TM.toNTM`. -/
theorem rewindInputTM_toNTM_hoareTime (B : ℕ) :
    ((rewindInputTM (n := n)).toNTM).HoareTime
      (fun inp _ _ => inp.cells 0 = Γ.start ∧
                      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
                      inp.head ≤ B)
      (fun inp _ _ => inp.head = 1)
      (B + 2) :=
  (rewindInputTM_hoareTime (n := n) B).toNTM

/-- Nondeterministic form of `rewindInputTM_hoareTime_frame`. -/
theorem rewindInputTM_toNTM_hoareTime_frame {n : ℕ} (B_input : ℕ)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      inp'.cells = inp.cells →
      inp'.head = 1 →
      work' = work →
      out' = out →
      P inp' work' out') :
    ((rewindInputTM (n := n)).toNTM).HoareTime
      (fun inp work out =>
        inp.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
        inp.head ≤ B_input ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        inp.head = 1 ∧
        P inp work out)
      (B_input + 2) :=
  (rewindInputTM_hoareTime_frame (n := n) B_input hP_preserved).toNTM

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: rich HoareTime preserving arbitrary data
-- ════════════════════════════════════════════════════════════════════════

/-- Rich HoareTime for `rewindWorkTM` that preserves an arbitrary predicate P
    through the rewind, provided P depends on cells (not heads) of the target
    tape. This is the key tool for threading invariants (e.g., simulation state,
    encoded data) through rewind steps in `seqTM` compositions.

    The caller provides `hP_preserved` showing that P is stable under:
    - target tape cells unchanged, head set to 1
    - all other work tapes unchanged
    - input and output unchanged -/
theorem rewindWorkTM_hoareTime_frame {n : ℕ} (idx : Fin n) (B_tape : ℕ)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' idx).cells = (work idx).cells →
      (work' idx).head = 1 →
      (∀ i, i ≠ idx → work' i = work i) →
      inp' = inp →
      out'.cells = out.cells →
      out'.head = out.head →
      P inp' work' out') :
    (rewindWorkTM idx).HoareTime
      (fun inp work out =>
        (work idx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work idx).cells j ≠ Γ.start) ∧
        (work idx).head ≤ B_tape ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        (work idx).head = 1 ∧
        P inp work out)
      (B_tape + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le, hinp_ns, hout_ns, hout_h, hother_wf, hP⟩
  -- Helper: idle-step identity for stable tapes
  have tape_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start → t.head ≥ 1 →
      t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
    intro t hns hh
    simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
    split
    · omega
    · simp only [Tape.read] at hns ⊢
      rw [toΓ_readBackWrite_of_ne_start hns, Function.update_eq_self]
  -- Rich rewind loop: tracks ALL tapes, not just work tape idx
  suffices h_loop : ∀ (h : ℕ) (c : Cfg n (rewindWorkTM idx).Q),
      c.state = RewindPhase.moveLeft →
      (c.work idx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) →
      (c.work idx).head = h →
      c.input = inp → c.output = out → (∀ i, i ≠ idx → c.work i = work i) →
      ∃ c',
        (rewindWorkTM idx).reachesIn (h + 2) c c' ∧
        (rewindWorkTM idx).halted c' ∧
        (c'.work idx).head = 1 ∧ (c'.work idx).cells = (c.work idx).cells ∧
        c'.input = inp ∧ c'.output = out ∧ (∀ i, i ≠ idx → c'.work i = work i) by
    obtain ⟨c', hreach, hhalt, hh1, hcells, hinp', hout', hw'⟩ :=
      h_loop (work idx).head
        { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
        rfl hcell0 hnostart rfl rfl rfl (fun _ _ => rfl)
    refine ⟨c', _, by omega, hreach, hhalt, hh1, ?_⟩
    exact hP_preserved inp work out c'.input c'.work c'.output hP
      (by rw [hcells]) hh1 hw' hinp'
      (by rw [hout']) (by rw [hout'])
  intro h; induction h with
  | zero =>
    intro c hstate hcell0_c hnostart_c hhead hinp_c hout_c hw_c
    have hread : (c.work idx).read = Γ.start := by simp [Tape.read, hhead, hcell0_c]
    -- Step 1: moveLeft, read ▷ → moveRight
    have hstep1 : ∃ c₁,
        (rewindWorkTM idx).step c = some c₁ ∧
        c₁.state = RewindPhase.moveRight ∧
        (c₁.work idx).head = 1 ∧ (c₁.work idx).cells = (c.work idx).cells ∧
        c₁.input = inp ∧ c₁.output = out ∧ (∀ i, i ≠ idx → c₁.work i = work i) := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []; simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []; simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
      · dsimp only []; rw [hinp_c]; simp only [idleDir, hinp_ns, ↓reduceIte, Tape.move]
      · dsimp only []; rw [hout_c]; exact tape_idle_preserve out hout_ns hout_h
      · intro i hne; dsimp only []
        simp only [show ¬(i = idx) from hne, ↓reduceIte]
        rw [hw_c i hne]; exact tape_idle_preserve (work i) (hother_wf i hne).1 (hother_wf i hne).2
    obtain ⟨c₁, hstep1', hst1, hh1, hcells1, hinp1, hout1, hw1⟩ := hstep1
    -- Step 2: moveRight → done
    have hread1 : (c₁.work idx).read ≠ Γ.start := by
      simp [Tape.read, hh1, hcells1]; exact hnostart_c 1 (by omega)
    have hstep2 : ∃ c₂,
        (rewindWorkTM idx).step c₁ = some c₂ ∧
        (rewindWorkTM idx).halted c₂ ∧
        (c₂.work idx).head = 1 ∧ (c₂.work idx).cells = (c₁.work idx).cells ∧
        c₂.input = inp ∧ c₂.output = out ∧ (∀ i, i ≠ idx → c₂.work i = work i) := by
      simp only [TM.step, hst1, rewindWorkTM]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        have := tape_idle_preserve (c₁.work idx) hread1 (by omega)
        show ((c₁.work idx).writeAndMove (readBackWrite (c₁.work idx).read)
          (idleDir (c₁.work idx).read)).head = 1
        rw [this]; exact hh1
      · dsimp only []
        have := tape_idle_preserve (c₁.work idx) hread1 (by omega)
        show ((c₁.work idx).writeAndMove (readBackWrite (c₁.work idx).read)
          (idleDir (c₁.work idx).read)).cells = (c₁.work idx).cells
        rw [this]
      · dsimp only []; rw [hinp1]; simp only [idleDir, hinp_ns, ↓reduceIte, Tape.move]
      · dsimp only []; rw [hout1]; exact tape_idle_preserve out hout_ns hout_h
      · intro i hne; dsimp only []
        rw [hw1 i hne]; exact tape_idle_preserve (work i) (hother_wf i hne).1 (hother_wf i hne).2
    obtain ⟨c₂, hstep2', hhalt, hh2, hcells2, hinp2, hout2, hw2⟩ := hstep2
    exact ⟨c₂, .step hstep1' (.step hstep2' .zero), hhalt, hh2,
      by rw [hcells2, hcells1], hinp2, hout2, hw2⟩
  | succ h ih =>
    intro c hstate hcell0_c hnostart_c hhead hinp_c hout_c hw_c
    have hread_ne : (c.work idx).read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart_c (h + 1) (by omega)
    -- Step: moveLeft, read non-▷ → stay in moveLeft, move left
    have hstep : ∃ c₁,
        (rewindWorkTM idx).step c = some c₁ ∧
        c₁.state = RewindPhase.moveLeft ∧
        (c₁.work idx).head = h ∧ (c₁.work idx).cells = (c.work idx).cells ∧
        c₁.input = inp ∧ c₁.output = out ∧ (∀ i, i ≠ idx → c₁.work i = work i) := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move]
        rw [toΓ_readBackWrite_of_ne_start hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hhead]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move_cells]
        rw [toΓ_readBackWrite_of_ne_start hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · dsimp only []; rw [hinp_c]; simp only [idleDir, hinp_ns, ↓reduceIte, Tape.move]
      · dsimp only []; rw [hout_c]; exact tape_idle_preserve out hout_ns hout_h
      · intro i hne; dsimp only []
        simp only [show ¬(i = idx) from hne, ↓reduceIte]
        rw [hw_c i hne]; exact tape_idle_preserve (work i) (hother_wf i hne).1 (hother_wf i hne).2
    obtain ⟨c₁, hstep', hst1, hh1, hcells1, hinp1, hout1, hw1⟩ := hstep
    obtain ⟨c_f, hreach_f, hhalt_f, hh_f, hcells_f, hinp_f, hout_f, hw_f⟩ :=
      ih c₁ hst1 (by rw [hcells1]; exact hcell0_c)
        (by intro j hj; rw [hcells1]; exact hnostart_c j hj) hh1 hinp1 hout1 hw1
    exact ⟨c_f, .step hstep' hreach_f, hhalt_f, hh_f,
      by rw [hcells_f, hcells1], hinp_f, hout_f, hw_f⟩

/-- Starting from cell `k + 1` of a started Boolean work tape whose first `k`
cells have already been blanked, `blankWorkTM idx` clears the remaining suffix
and halts with the entire tape blank from cell `1` onward. -/
private theorem blankWorkTM_loop {n : ℕ} (idx : Fin n) (x : List Bool) :
    ∀ rem k (c : Cfg n (blankWorkTM idx).Q),
      rem = x.length - k →
      k ≤ x.length →
      c.state = ScanPhase.scanning →
      (c.work idx).head = k + 1 →
      (c.work idx).cells 0 = Γ.start →
      (∀ i, i < k → (c.work idx).cells (i + 1) = Γ.blank) →
      (∀ i, ∀ _ : k ≤ i, ∀ hi : i < x.length,
        (c.work idx).cells (i + 1) = Γ.ofBool (x[i]'hi)) →
      (∀ i, x.length ≤ i → (c.work idx).cells (i + 1) = Γ.blank) →
      ∃ c',
        (blankWorkTM idx).reachesIn (rem + 1) c c' ∧
        (blankWorkTM idx).halted c' ∧
        (c'.work idx).head = x.length + 1 ∧
        (c'.work idx).cells 0 = Γ.start ∧
        (∀ i, (c'.work idx).cells (i + 1) = Γ.blank) := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hk_le hstate hhead hcell0 hblank_prefix hdata hblank_tail
      have hk_eq : k = x.length := by omega
      subst hk_eq
      have hread : (c.work idx).read = Γ.blank := by
        simp [Tape.read, hhead, hblank_tail x.length le_rfl]
      have hstep :
          ∃ c1,
            (blankWorkTM idx).step c = some c1 ∧
            (blankWorkTM idx).halted c1 ∧
            (c1.work idx).head = x.length + 1 ∧
            (c1.work idx).cells 0 = Γ.start ∧
            (∀ i, (c1.work idx).cells (i + 1) = Γ.blank) := by
        let c1 : Cfg n (blankWorkTM idx).Q :=
          { state := ScanPhase.done
            input := c.input.move (TM.idleDir c.input.read)
            work := fun i =>
              (c.work i).writeAndMove (TM.readBackWrite ((c.work i).read)).toΓ
                (TM.idleDir ((c.work i).read))
            output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
              (TM.idleDir c.output.read) }
        have hkeep : c1.work idx = c.work idx := by
          have hread_ne : (c.work idx).read ≠ Γ.start := by simp [hread]
          simpa [c1, hread, TM.transitionTape] using
            (TM.transitionTape_eq_self (t := c.work idx) hread_ne)
        refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
        · simp [TM.step, hstate, blankWorkTM, hread, c1, allIdle]
        · rw [hkeep, hhead]
        · rw [hkeep]
          exact hcell0
        · intro i
          rw [hkeep]
          by_cases hi : i < x.length
          · exact hblank_prefix i hi
          · exact hblank_tail i (by omega)
      obtain ⟨c1, hstep1, hhalt1, hhead1, hcell01, hblank1⟩ := hstep
      exact ⟨c1, .step hstep1 .zero, hhalt1, hhead1, hcell01, hblank1⟩
  | succ rem ih =>
      intro k c hrem hk_le hstate hhead hcell0 hblank_prefix hdata hblank_tail
      have hk_lt : k < x.length := by omega
      have hread : (c.work idx).read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hdata k le_rfl hk_lt]
      have hstep :
          ∃ c1,
            (blankWorkTM idx).step c = some c1 ∧
            c1.state = ScanPhase.scanning ∧
            (c1.work idx).head = k + 2 ∧
            (c1.work idx).cells 0 = Γ.start ∧
            (∀ i, i < k + 1 → (c1.work idx).cells (i + 1) = Γ.blank) ∧
            (∀ i, ∀ _ : k + 1 ≤ i, ∀ hi : i < x.length,
              (c1.work idx).cells (i + 1) = Γ.ofBool (x[i]'hi)) ∧
            (∀ i, x.length ≤ i → (c1.work idx).cells (i + 1) = Γ.blank) := by
        cases hbit : x[k]'hk_lt with
        | false =>
            have hread0 : (c.work idx).read = Γ.zero := by simpa [hbit] using hread
            let c1 : Cfg n (blankWorkTM idx).Q :=
              { state := ScanPhase.scanning
                input := c.input.move (TM.idleDir c.input.read)
                work := fun i =>
                  (c.work i).writeAndMove
                    ((if i = idx then Γw.blank else TM.readBackWrite ((c.work i).read)).toΓ)
                    (if i = idx then Dir3.right else TM.idleDir ((c.work i).read))
                output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                  (TM.idleDir c.output.read) }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, blankWorkTM, hread0, c1]
            · simp [c1, hhead, Tape.writeAndMove, Tape.move, Tape.write_head]
            · simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcell0]
            · intro i hi
              by_cases hik : i < k
              · have hblanki := hblank_prefix i hik
                have hne : i + 1 ≠ k + 1 := by omega
                simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
                rw [Function.update_of_ne hne]
                exact hblanki
              · have hik_eq : i = k := by omega
                subst hik_eq
                simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
            · intro i hi hix
              have hcell := hdata i (by omega) hix
              have hne : i + 1 ≠ k + 1 := by omega
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
              rw [Function.update_of_ne hne]
              exact hcell
            · intro i hi
              have hcell := hblank_tail i hi
              have hne : i + 1 ≠ k + 1 := by omega
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
              rw [Function.update_of_ne hne]
              exact hcell
        | true =>
            have hread1 : (c.work idx).read = Γ.one := by simpa [hbit] using hread
            let c1 : Cfg n (blankWorkTM idx).Q :=
              { state := ScanPhase.scanning
                input := c.input.move (TM.idleDir c.input.read)
                work := fun i =>
                  (c.work i).writeAndMove
                    ((if i = idx then Γw.blank else TM.readBackWrite ((c.work i).read)).toΓ)
                    (if i = idx then Dir3.right else TM.idleDir ((c.work i).read))
                output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                  (TM.idleDir c.output.read) }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, blankWorkTM, hread1, c1]
            · simp [c1, hhead, Tape.writeAndMove, Tape.move, Tape.write_head]
            · simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcell0]
            · intro i hi
              by_cases hik : i < k
              · have hblanki := hblank_prefix i hik
                have hne : i + 1 ≠ k + 1 := by omega
                simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
                rw [Function.update_of_ne hne]
                exact hblanki
              · have hik_eq : i = k := by omega
                subst hik_eq
                simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
            · intro i hi hix
              have hcell := hdata i (by omega) hix
              have hne : i + 1 ≠ k + 1 := by omega
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
              rw [Function.update_of_ne hne]
              exact hcell
            · intro i hi
              have hcell := hblank_tail i hi
              have hne : i + 1 ≠ k + 1 := by omega
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
              rw [Function.update_of_ne hne]
              exact hcell
      obtain ⟨c1, hstep1, hstate1, hhead1, hcell01, hblank_prefix1,
        hdata1, hblank_tail1⟩ := hstep
      have hrem1 : rem = x.length - (k + 1) := by omega
      obtain ⟨c', hreach, hhalt, hhead', hcell0', hblank'⟩ :=
        ih (k + 1) c1 hrem1 (by omega) hstate1 hhead1 hcell01 hblank_prefix1 hdata1 hblank_tail1
      exact ⟨c', .step hstep1 hreach, hhalt, hhead', hcell0', hblank'⟩

/-- If work tape `idx` holds a started Boolean string `x`, then `blankWorkTM
idx` clears that tape in `|x| + 1` steps and leaves the head at the first
blank cell after the erased string. -/
theorem blankWorkTM_started_hoareTime {n : ℕ}
    (idx : Fin n) (x : List Bool) :
    (blankWorkTM idx).HoareTime
      (fun _inp work _out =>
        work idx = (Tape.init (x.map Γ.ofBool)).move Dir3.right)
      (fun _inp work _out =>
        (work idx).head = x.length + 1 ∧
        (work idx).cells 0 = Γ.start ∧
        (∀ i, (work idx).cells (i + 1) = Γ.blank))
      (x.length + 1) := by
  intro inp work out hpre
  have hwork : work idx = (Tape.init (x.map Γ.ofBool)).move Dir3.right := hpre
  have hhead0 : (work idx).head = 1 := by
    rw [hwork]
    simp [Tape.move, Tape.init]
  have hcell00 : (work idx).cells 0 = Γ.start := by
    rw [hwork]
    simp [Tape.move, Tape.init]
  have hblank0 : ∀ i, i < 0 → (work idx).cells (i + 1) = Γ.blank := by
    intro i hi
    exact (Nat.not_lt_zero i hi).elim
  have hdata0 : ∀ i, ∀ _ : 0 ≤ i, ∀ hi : i < x.length,
      (work idx).cells (i + 1) = Γ.ofBool (x[i]'hi) := by
    intro i _ hi
    rw [hwork]
    exact Tape.init_ofBool_cells_lt x i hi
  have htail0 : ∀ i, x.length ≤ i → (work idx).cells (i + 1) = Γ.blank := by
    intro i hi
    rw [hwork]
    exact Tape.init_ofBool_cells_ge x i hi
  obtain ⟨c', hreach, hhalt, hhead, hcell0, hblank⟩ :=
    blankWorkTM_loop idx x x.length 0
      { state := ScanPhase.scanning, input := inp, work := work, output := out }
      (by simp)
      (Nat.zero_le _)
      rfl
      hhead0 hcell00 hblank0 hdata0 htail0
  refine ⟨c', x.length + 1, le_rfl, hreach, hhalt, hhead, hcell0, hblank⟩

/-- Rich HoareTime for `blankWorkTM`: erase a started Boolean work tape while
preserving arbitrary frame data on the input tape, output tape, and all other
work tapes. This is the form needed to recycle a staged work tape inside a
larger verifier pipeline. -/
theorem blankWorkTM_hoareTime_frame_of_binaryString {n : ℕ}
    (idx : Fin n) (x : List Bool)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' idx).head = x.length + 1 →
      (work' idx).cells 0 = Γ.start →
      (∀ i, (work' idx).cells (i + 1) = Γ.blank) →
      inp' = inp →
      out' = out →
      (∀ i, i ≠ idx → work' i = work i) →
      P inp' work' out') :
    (blankWorkTM idx).HoareTime
      (fun inp work out =>
        work idx = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        (work idx).head = x.length + 1 ∧
        (work idx).cells 0 = Γ.start ∧
        (∀ i, (work idx).cells (i + 1) = Γ.blank) ∧
        P inp work out)
      (x.length + 1) := by
  intro inp work out ⟨hwork, hinp_ns, hout_ns, hout_h, hother_wf, hP⟩
  have tape_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start → t.head ≥ 1 →
      t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
    intro t hns hh
    simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
    split
    · omega
    · simp only [Tape.read] at hns ⊢
      rw [toΓ_readBackWrite_of_ne_start hns, Function.update_eq_self]
  have input_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start →
      t.move (idleDir t.read) = t := by
    intro t hns
    simp [idleDir, hns, Tape.move]
  suffices h_loop : ∀ rem k (c : Cfg n (blankWorkTM idx).Q),
      rem = x.length - k →
      k ≤ x.length →
      c.state = ScanPhase.scanning →
      (c.work idx).head = k + 1 →
      (c.work idx).cells 0 = Γ.start →
      (∀ i, i < k → (c.work idx).cells (i + 1) = Γ.blank) →
      (∀ i, ∀ _ : k ≤ i, ∀ hi : i < x.length,
        (c.work idx).cells (i + 1) = Γ.ofBool (x[i]'hi)) →
      (∀ i, x.length ≤ i → (c.work idx).cells (i + 1) = Γ.blank) →
      c.input = inp →
      c.output = out →
      (∀ i, i ≠ idx → c.work i = work i) →
      ∃ c',
        (blankWorkTM idx).reachesIn (rem + 1) c c' ∧
        (blankWorkTM idx).halted c' ∧
        (c'.work idx).head = x.length + 1 ∧
        (c'.work idx).cells 0 = Γ.start ∧
        (∀ i, (c'.work idx).cells (i + 1) = Γ.blank) ∧
        c'.input = inp ∧
        c'.output = out ∧
        (∀ i, i ≠ idx → c'.work i = work i) by
    have hhead0 : (work idx).head = 1 := by
      rw [hwork]
      simp [Tape.move, Tape.init]
    have hcell00 : (work idx).cells 0 = Γ.start := by
      rw [hwork]
      simp [Tape.move, Tape.init]
    have hblank0 : ∀ i, i < 0 → (work idx).cells (i + 1) = Γ.blank := by
      intro i hi
      exact (Nat.not_lt_zero i hi).elim
    have hdata0 : ∀ i, ∀ _ : 0 ≤ i, ∀ hi : i < x.length,
        (work idx).cells (i + 1) = Γ.ofBool (x[i]'hi) := by
      intro i _ hi
      rw [hwork]
      exact Tape.init_ofBool_cells_lt x i hi
    have htail0 : ∀ i, x.length ≤ i → (work idx).cells (i + 1) = Γ.blank := by
      intro i hi
      rw [hwork]
      exact Tape.init_ofBool_cells_ge x i hi
    obtain ⟨c', hreach, hhalt, hhead, hcell0, hblank, hinp', hout', hwork'⟩ :=
      h_loop x.length 0
        { state := ScanPhase.scanning, input := inp, work := work, output := out }
        (by simp)
        (Nat.zero_le _)
        rfl
        hhead0 hcell00 hblank0 hdata0 htail0
        rfl rfl (fun _ _ => rfl)
    refine ⟨c', x.length + 1, le_rfl, hreach, hhalt, hhead, hcell0, hblank, ?_⟩
    exact hP_preserved inp work out c'.input c'.work c'.output hP
      hhead hcell0 hblank hinp' hout' hwork'
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hk_le hstate hhead hcell0 hblank_prefix hdata hblank_tail
        hinp_c hout_c hw_c
      have hk_eq : k = x.length := by omega
      subst hk_eq
      have hread : (c.work idx).read = Γ.blank := by
        simp [Tape.read, hhead, hblank_tail x.length le_rfl]
      let c1 : Cfg n (blankWorkTM idx).Q :=
        { state := ScanPhase.done
          input := c.input.move (TM.idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove (TM.readBackWrite ((c.work i).read)).toΓ
              (TM.idleDir ((c.work i).read))
          output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
            (TM.idleDir c.output.read) }
      have hstep1 : (blankWorkTM idx).step c = some c1 := by
        simp [TM.step, hstate, blankWorkTM, hread, c1]
      have hinput_keep : c1.input = inp := by
        change c.input.move (TM.idleDir c.input.read) = inp
        rw [hinp_c]
        exact input_idle_preserve _ hinp_ns
      have htarget_keep : c1.work idx = c.work idx := by
        have hread_ne : (c.work idx).read ≠ Γ.start := by
          simp [hread]
        have hh : (c.work idx).head ≥ 1 := by
          rw [hhead]
          omega
        change (c.work idx).writeAndMove (TM.readBackWrite ((c.work idx).read)).toΓ
          (TM.idleDir ((c.work idx).read)) = c.work idx
        exact tape_idle_preserve (c.work idx) hread_ne hh
      have hout_keep : c1.output = out := by
        change c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
          (TM.idleDir c.output.read) = out
        rw [hout_c]
        exact tape_idle_preserve out hout_ns hout_h
      have hwork_keep : ∀ i, i ≠ idx → c1.work i = work i := by
        intro i hi
        change (c.work i).writeAndMove (TM.readBackWrite ((c.work i).read)).toΓ
          (TM.idleDir ((c.work i).read)) = work i
        rw [hw_c i hi]
        exact tape_idle_preserve (work i) (hother_wf i hi).1 (hother_wf i hi).2
      have hblank_all : ∀ i, (c1.work idx).cells (i + 1) = Γ.blank := by
        intro i
        rw [htarget_keep]
        by_cases hi : i < x.length
        · exact hblank_prefix i hi
        · exact hblank_tail i (by omega)
      exact ⟨c1, .step hstep1 .zero, rfl, by rw [htarget_keep, hhead],
        by rw [htarget_keep]; exact hcell0,
        hblank_all, hinput_keep, hout_keep, hwork_keep⟩
  | succ rem ih =>
      intro k c hrem hk_le hstate hhead hcell0 hblank_prefix hdata hblank_tail
        hinp_c hout_c hw_c
      have hk_lt : k < x.length := by omega
      have hread : (c.work idx).read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hdata k le_rfl hk_lt]
      cases hbit : x[k]'hk_lt with
      | false =>
          have hread0 : (c.work idx).read = Γ.zero := by simpa [hbit] using hread
          let c1 : Cfg n (blankWorkTM idx).Q :=
            { state := ScanPhase.scanning
              input := c.input.move (TM.idleDir c.input.read)
              work := fun i =>
                (c.work i).writeAndMove
                  ((if i = idx then Γw.blank else TM.readBackWrite ((c.work i).read)).toΓ)
                  (if i = idx then Dir3.right else TM.idleDir ((c.work i).read))
              output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                (TM.idleDir c.output.read) }
          have hstep1 : (blankWorkTM idx).step c = some c1 := by
            simp [TM.step, hstate, blankWorkTM, hread0, c1]
          have hinput_keep : c1.input = inp := by
            simpa [c1, hinp_c] using input_idle_preserve inp hinp_ns
          have houtput_keep : c1.output = out := by
            simpa [c1, hout_c] using tape_idle_preserve out hout_ns hout_h
          have hwork_keep : ∀ i, i ≠ idx → c1.work i = work i := by
            intro i hi
            simpa [c1, hi, hw_c i hi] using
              tape_idle_preserve (work i) (hother_wf i hi).1 (hother_wf i hi).2
          have hhead1 : (c1.work idx).head = k + 2 := by
            simp [c1, hhead, Tape.writeAndMove, Tape.move, Tape.write_head]
          have hcell01 : (c1.work idx).cells 0 = Γ.start := by
            simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcell0]
          have hblank_prefix1 : ∀ i, i < k + 1 → (c1.work idx).cells (i + 1) = Γ.blank := by
            intro i hi
            by_cases hik : i < k
            · have hblanki := hblank_prefix i hik
              have hne : i + 1 ≠ k + 1 := by omega
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
              rw [Function.update_of_ne hne]
              exact hblanki
            · have hik_eq : i = k := by omega
              subst hik_eq
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
          have hdata1 : ∀ i, ∀ _ : k + 1 ≤ i, ∀ hi : i < x.length,
              (c1.work idx).cells (i + 1) = Γ.ofBool (x[i]'hi) := by
            intro i _ hix
            have hcell := hdata i (by omega) hix
            have hne : i + 1 ≠ k + 1 := by omega
            simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
            rw [Function.update_of_ne hne]
            exact hcell
          have hblank_tail1 : ∀ i, x.length ≤ i → (c1.work idx).cells (i + 1) = Γ.blank := by
            intro i hi
            have hcell := hblank_tail i hi
            have hne : i + 1 ≠ k + 1 := by omega
            simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
            rw [Function.update_of_ne hne]
            exact hcell
          have hrem1 : rem = x.length - (k + 1) := by omega
          obtain ⟨c', hreach, hhalt, hhead', hcell0', hblank', hinp', hout', hwork'⟩ :=
            ih (k + 1) c1 hrem1 (by omega) rfl hhead1 hcell01 hblank_prefix1 hdata1
              hblank_tail1 hinput_keep houtput_keep hwork_keep
          exact ⟨c', .step hstep1 hreach, hhalt, hhead', hcell0', hblank', hinp', hout', hwork'⟩
      | true =>
          have hread1 : (c.work idx).read = Γ.one := by simpa [hbit] using hread
          let c1 : Cfg n (blankWorkTM idx).Q :=
            { state := ScanPhase.scanning
              input := c.input.move (TM.idleDir c.input.read)
              work := fun i =>
                (c.work i).writeAndMove
                  ((if i = idx then Γw.blank else TM.readBackWrite ((c.work i).read)).toΓ)
                  (if i = idx then Dir3.right else TM.idleDir ((c.work i).read))
              output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                (TM.idleDir c.output.read) }
          have hstep1 : (blankWorkTM idx).step c = some c1 := by
            simp [TM.step, hstate, blankWorkTM, hread1, c1]
          have hinput_keep : c1.input = inp := by
            simpa [c1, hinp_c] using input_idle_preserve inp hinp_ns
          have houtput_keep : c1.output = out := by
            simpa [c1, hout_c] using tape_idle_preserve out hout_ns hout_h
          have hwork_keep : ∀ i, i ≠ idx → c1.work i = work i := by
            intro i hi
            simpa [c1, hi, hw_c i hi] using
              tape_idle_preserve (work i) (hother_wf i hi).1 (hother_wf i hi).2
          have hhead1 : (c1.work idx).head = k + 2 := by
            simp [c1, hhead, Tape.writeAndMove, Tape.move, Tape.write_head]
          have hcell01 : (c1.work idx).cells 0 = Γ.start := by
            simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcell0]
          have hblank_prefix1 : ∀ i, i < k + 1 → (c1.work idx).cells (i + 1) = Γ.blank := by
            intro i hi
            by_cases hik : i < k
            · have hblanki := hblank_prefix i hik
              have hne : i + 1 ≠ k + 1 := by omega
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
              rw [Function.update_of_ne hne]
              exact hblanki
            · have hik_eq : i = k := by omega
              subst hik_eq
              simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
          have hdata1 : ∀ i, ∀ _ : k + 1 ≤ i, ∀ hi : i < x.length,
              (c1.work idx).cells (i + 1) = Γ.ofBool (x[i]'hi) := by
            intro i _ hix
            have hcell := hdata i (by omega) hix
            have hne : i + 1 ≠ k + 1 := by omega
            simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
            rw [Function.update_of_ne hne]
            exact hcell
          have hblank_tail1 : ∀ i, x.length ≤ i → (c1.work idx).cells (i + 1) = Γ.blank := by
            intro i hi
            have hcell := hblank_tail i hi
            have hne : i + 1 ≠ k + 1 := by omega
            simp [c1, Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
            rw [Function.update_of_ne hne]
            exact hcell
          have hrem1 : rem = x.length - (k + 1) := by omega
          obtain ⟨c', hreach, hhalt, hhead', hcell0', hblank', hinp', hout', hwork'⟩ :=
            ih (k + 1) c1 hrem1 (by omega) rfl hhead1 hcell01 hblank_prefix1 hdata1
              hblank_tail1 hinput_keep houtput_keep hwork_keep
          exact ⟨c', .step hstep1 hreach, hhalt, hhead', hcell0', hblank', hinp', hout', hwork'⟩

/-- Rich HoareTime for `clearWorkTM`: erase a started Boolean work tape and
rewind it to the standard started blank tape while preserving the external
frame. The user predicate only needs to be stable once the target tape has
reached the final started blank configuration. -/
theorem clearWorkTM_hoareTime_frame_of_binaryString {n : ℕ}
    (idx : Fin n) (x : List Bool)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      work' idx = (Tape.init []).move Dir3.right →
      inp' = inp →
      out' = out →
      (∀ i, i ≠ idx → work' i = work i) →
      P inp' work' out') :
    (clearWorkTM idx).HoareTime
      (fun inp work out =>
        work idx = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        work idx = (Tape.init []).move Dir3.right ∧
        P inp work out)
      ((x.length + 1) + 1 + (x.length + 1 + 2)) := by
  intro inp work out hpre
  rcases hpre with ⟨hwork, hinp_ns, hout_ns, hout_h, hother_wf, hP⟩
  let FrameEq : TapePred n := fun inp' work' out' =>
    inp' = inp ∧
    out' = out ∧
    (∀ i, i ≠ idx → work' i = work i)
  let BlankFrame : TapePred n := fun inp' work' out' =>
    FrameEq inp' work' out' ∧
    (work' idx).cells 0 = Γ.start ∧
    (∀ j, (work' idx).cells (j + 1) = Γ.blank)
  have hblank :
      (blankWorkTM idx).HoareTime
        (fun inp work out =>
          work idx = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
          inp.read ≠ Γ.start ∧
          out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
          (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
          FrameEq inp work out)
        (fun inp work out =>
          (work idx).head = x.length + 1 ∧
          (work idx).cells 0 = Γ.start ∧
          (∀ j, (work idx).cells (j + 1) = Γ.blank) ∧
          FrameEq inp work out)
        (x.length + 1) := by
    refine blankWorkTM_hoareTime_frame_of_binaryString idx x ?_
    intro inp0 work0 out0 inp' work' out' hframe _hhead _hcell0 _hblank hinp' hout' hwork'
    rcases hframe with ⟨hinp0, hout0, hwork0⟩
    exact ⟨by rw [hinp', hinp0], by rw [hout', hout0], by
      intro i hi
      rw [hwork' i hi, hwork0 i hi]⟩
  have hrew :
      (rewindWorkTM idx).HoareTime
        (fun inp work out =>
          (work idx).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work idx).cells j ≠ Γ.start) ∧
          (work idx).head ≤ x.length + 1 ∧
          inp.read ≠ Γ.start ∧
          out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
          (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
          BlankFrame inp work out)
        (fun inp work out =>
          (work idx).head = 1 ∧
          BlankFrame inp work out)
        (x.length + 1 + 2) := by
    refine rewindWorkTM_hoareTime_frame idx (x.length + 1) ?_
    intro inp0 work0 out0 inp' work' out' hblankframe hcells _hhead hwork_eq hinp'
      hout_cells hout_head
    rcases hblankframe with ⟨hframe, hcell0, hblank⟩
    rcases hframe with ⟨hinp0, hout0, hwork0⟩
    have hout_eq0 : out' = out0 := by
      cases out'
      cases out0
      simp at hout_cells hout_head
      simp [hout_cells, hout_head]
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨by rw [hinp', hinp0], by rw [hout_eq0, hout0], by
        intro i hi
        rw [hwork_eq i hi, hwork0 i hi]⟩
    · rw [hcells]
      exact hcell0
    · intro j
      rw [hcells]
      exact hblank j
  have hseq :
      (clearWorkTM idx).HoareTime
        (fun inp work out =>
          work idx = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
          inp.read ≠ Γ.start ∧
          out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
          (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
          FrameEq inp work out)
        (fun inp work out =>
          (work idx).head = 1 ∧
          BlankFrame inp work out)
        ((x.length + 1) + 1 + (x.length + 1 + 2)) :=
    seqTM_hoareTime (blankWorkTM idx) (rewindWorkTM idx)
      hblank
      (by
        intro inp1 work1 out1 hmid
        rcases hmid with ⟨hhead1, hcell01, hblank1, hframe1⟩
        rcases hframe1 with ⟨hinp1, hout1, hwork1⟩
        have htarget_read_ne : (work1 idx).read ≠ Γ.start := by
          rw [Tape.read, hhead1, hblank1 x.length]
          decide
        have htarget_tr : TM.transitionTape (work1 idx) = work1 idx :=
          TM.transitionTape_eq_self htarget_read_ne
        have hinput_tr : TM.transitionInput inp1 = inp1 := by
          rw [hinp1]
          exact TM.transitionInput_eq_self hinp_ns
        have hout_tr : TM.transitionTape out1 = out1 := by
          rw [hout1]
          exact TM.transitionTape_eq_self hout_ns
        have hwork_tr : ∀ i, i ≠ idx → TM.transitionTape (work1 i) = work1 i := by
          intro i hi
          rw [hwork1 i hi]
          exact TM.transitionTape_eq_self (hother_wf i hi).1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · change (TM.transitionTape (work1 idx)).cells 0 = Γ.start
          rw [htarget_tr]
          exact hcell01
        · intro j hj
          cases j with
          | zero => omega
          | succ j =>
              change (TM.transitionTape (work1 idx)).cells j.succ ≠ Γ.start
              rw [htarget_tr]
              rw [show j.succ = j + 1 by omega, hblank1 j]
              decide
        · change (TM.transitionTape (work1 idx)).head ≤ x.length + 1
          rw [htarget_tr, hhead1]
        · rw [hinput_tr, hinp1]
          exact hinp_ns
        · change (TM.transitionTape out1).read ≠ Γ.start
          rw [hout_tr, hout1]
          exact hout_ns
        · change (TM.transitionTape out1).head ≥ 1
          rw [hout_tr, hout1]
          exact hout_h
        · intro i hi
          constructor
          · change (TM.transitionTape (work1 i)).read ≠ Γ.start
            rw [hwork_tr i hi, hwork1 i hi]
            exact (hother_wf i hi).1
          · change (TM.transitionTape (work1 i)).head ≥ 1
            rw [hwork_tr i hi, hwork1 i hi]
            exact (hother_wf i hi).2
        · refine ⟨?_, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · change TM.transitionInput inp1 = inp
              rw [hinput_tr, hinp1]
            · change TM.transitionTape out1 = out
              rw [hout_tr, hout1]
            · intro i hi
              change TM.transitionTape (work1 i) = work i
              rw [hwork_tr i hi, hwork1 i hi]
          · change (TM.transitionTape (work1 idx)).cells 0 = Γ.start
            rw [htarget_tr]
            exact hcell01
          · intro j
            change (TM.transitionTape (work1 idx)).cells (j + 1) = Γ.blank
            rw [htarget_tr]
            exact hblank1 j)
      hrew
  have hclear := hseq.strengthen_post (by
    intro inp' work' out' hpost
    rcases hpost with ⟨hhead, hblankframe⟩
    rcases hblankframe with ⟨hframe, hcell0, hblank⟩
    rcases hframe with ⟨hinp', hout', hwork'⟩
    have hbits : (work' idx).HasBinaryString [] := by
      refine ⟨hhead, ?_, ?_⟩
      · intro i hi
        exact (Nat.not_lt_zero i hi).elim
      · intro i _
        exact hblank i
    have hclear : work' idx = (Tape.init []).move Dir3.right :=
      Tape.eq_init_move_right_of_hasBinaryString hbits hcell0
    exact show work' idx = (Tape.init []).move Dir3.right ∧ P inp' work' out' from
      ⟨hclear, hP_preserved inp work out inp' work' out' hP hclear hinp' hout' hwork'⟩)
  exact hclear inp work out ⟨hwork, hinp_ns, hout_ns, hout_h, hother_wf, ⟨rfl, rfl, fun _ _ => rfl⟩⟩

/-- Starting from cell `k + 1` of a Boolean input tape and an already-copied
prefix `x.take k` on work tape `idx`, `copyInputToWorkTM idx` copies the
remaining suffix and halts with the full prefix `x` on the target tape. -/
private theorem copyInputToWorkTM_loop {n : ℕ} (idx : Fin n) (x : List Bool) :
    ∀ rem k (c : Cfg n (copyInputToWorkTM idx).Q),
      rem = x.length - k →
      c.state = CopyPhase.copying →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      (c.work idx).HasBinaryPrefix (x.take k) →
      k ≤ x.length →
      ∃ c',
        (copyInputToWorkTM idx).reachesIn (rem + 1) c c' ∧
        (copyInputToWorkTM idx).halted c' ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        (c'.work idx).HasBinaryPrefix x := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_eq : k = x.length := by
        omega
      subst hk_eq
      have hread : c.input.read = Γ.blank := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hprefix_full : (c.work idx).HasBinaryPrefix x := by
        simpa using hprefix
      have hwork_blank : (c.work idx).read = Γ.blank := by
        have hblank := hprefix_full.2.2 x.length le_rfl
        simp [Tape.read, hprefix_full.1, hblank]
      have hstep :
          ∃ c1,
            (copyInputToWorkTM idx).step c = some c1 ∧
            (copyInputToWorkTM idx).halted c1 ∧
            c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
            c1.input.head = x.length + 1 ∧
            (c1.work idx).HasBinaryPrefix x := by
        let c1 : Cfg n (copyInputToWorkTM idx).Q :=
          { state := CopyPhase.done
            input := c.input.move (TM.idleDir c.input.read)
            work := fun i =>
              (c.work i).writeAndMove Γ.blank (TM.idleDir ((c.work i).read))
            output := c.output.writeAndMove Γ.blank (TM.idleDir c.output.read) }
        have hinput_keep :
            c.input.move (TM.idleDir c.input.read) = c.input := by
          simp [TM.idleDir, hread, Tape.move]
        have hwork_keep :
            (c.work idx).writeAndMove Γ.blank (TM.idleDir ((c.work idx).read)) = c.work idx := by
          simpa [transitionTape, hwork_blank] using
            (transitionTape_eq_self (t := c.work idx) (by simp [hwork_blank]))
        refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
        · simp [TM.step, hstate, copyInputToWorkTM, hread, c1, allIdle]
        · rw [show c1.input = c.input by simpa [c1] using hinput_keep]
          exact hcells
        · rw [show c1.input = c.input by simpa [c1] using hinput_keep]
          exact hhead
        · rw [show c1.work idx = c.work idx by
              simpa [c1] using hwork_keep]
          exact hprefix_full
      obtain ⟨c1, hstep1, hhalt1, hcells1, hhead1, hprefix1⟩ := hstep
      exact ⟨c1, .step hstep1 .zero, hhalt1, hcells1, hhead1, hprefix1⟩
  | succ rem ih =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_lt : k < x.length := by
        omega
      have hread : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hprefix_next :
          ((c.work idx).writeAndMove (Γ.ofBool (x[k]'hk_lt)) Dir3.right).HasBinaryPrefix
            (x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk_lt) hprefix
        simpa [List.take_concat_get' x k hk_lt] using hwrite
      have hstep :
          ∃ c1,
            (copyInputToWorkTM idx).step c = some c1 ∧
            c1.state = CopyPhase.copying ∧
            c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
            c1.input.head = k + 2 ∧
            (c1.work idx).HasBinaryPrefix (x.take (k + 1)) := by
        cases hbit : x[k]'hk_lt with
        | false =>
            have hread0 : c.input.read = Γ.zero := by
              simpa [hbit] using hread
            let c1 : Cfg n (copyInputToWorkTM idx).Q :=
              { state := CopyPhase.copying
                input := c.input.move Dir3.right
                work := fun i =>
                  (c.work i).writeAndMove
                    ((if i = idx then Γw.zero else Γw.blank).toΓ)
                    (if i = idx then Dir3.right else TM.idleDir ((c.work i).read))
                output := c.output.writeAndMove Γ.blank (TM.idleDir c.output.read) }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, copyInputToWorkTM, hread0, c1]
            · simpa [c1, Tape.move_cells] using hcells
            · simp [c1, Tape.move, hhead]
            · have hwidx :
                  c1.work idx = (c.work idx).writeAndMove Γ.zero Dir3.right := by
                simp [c1]
              rw [hwidx]
              simpa [hbit] using hprefix_next
        | true =>
            have hread1 : c.input.read = Γ.one := by
              simpa [hbit] using hread
            let c1 : Cfg n (copyInputToWorkTM idx).Q :=
              { state := CopyPhase.copying
                input := c.input.move Dir3.right
                work := fun i =>
                  (c.work i).writeAndMove
                    ((if i = idx then Γw.one else Γw.blank).toΓ)
                    (if i = idx then Dir3.right else TM.idleDir ((c.work i).read))
                output := c.output.writeAndMove Γ.blank (TM.idleDir c.output.read) }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, copyInputToWorkTM, hread1, c1]
            · simpa [c1, Tape.move_cells] using hcells
            · simp [c1, Tape.move, hhead]
            · have hwidx :
                  c1.work idx = (c.work idx).writeAndMove Γ.one Dir3.right := by
                simp [c1]
              rw [hwidx]
              simpa [hbit] using hprefix_next
      obtain ⟨c1, hstep1, hstate1, hcells1, hhead1, hprefix1⟩ := hstep
      have hrem1 : rem = x.length - (k + 1) := by
        omega
      obtain ⟨c', hreach, hhalt, hcells', hhead', hprefix'⟩ :=
        ih (k + 1) c1 hrem1 hstate1 hcells1 hhead1 hprefix1 (by omega)
      exact ⟨c', .step hstep1 hreach, hhalt, hcells', hhead', hprefix'⟩

/-- `copyInputToWorkTM idx` can be started with the input and target work tape
already positioned at cell `1`: it copies the entire Boolean input to a binary
prefix on work tape `idx` and halts within `|x| + 1` steps. -/
theorem copyInputToWorkTM_started_hoareTime {n : ℕ} (idx : Fin n) (x : List Bool) :
    (copyInputToWorkTM idx).HoareTime
      (fun inp work _out =>
        inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        (work idx).HasBinaryPrefix [])
      (fun inp work _out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work idx).HasBinaryPrefix x)
      (x.length + 1) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hprefix⟩
  subst inp
  obtain ⟨c', hreach, hhalt, hcells, hhead, hprefix'⟩ :=
    copyInputToWorkTM_loop idx x x.length 0
      { state := CopyPhase.copying
        input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
        work := work
        output := out }
      (by simp)
      rfl
      (by simp [Tape.move])
      rfl
      (by simpa using hprefix)
      (Nat.zero_le _)
  refine ⟨c', x.length + 1, le_rfl, hreach, hhalt, hcells, hhead, hprefix'⟩

private theorem copyWorkToWorkTM_loop {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) :
    ∀ rem k (c : Cfg n (copyWorkToWorkTM src dst).Q),
      rem = x.length - k →
      c.state = CopyPhase.copying →
      (c.work src).cells = (Tape.init (x.map Γ.ofBool)).cells →
      (c.work src).head = k + 1 →
      (c.work dst).HasBinaryPrefix (x.take k) →
      k ≤ x.length →
      ∃ c',
        (copyWorkToWorkTM src dst).reachesIn (rem + 1) c c' ∧
        (copyWorkToWorkTM src dst).halted c' ∧
        (c'.work src).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (c'.work src).head = x.length + 1 ∧
        (c'.work dst).HasBinaryPrefix x := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hsrc_cells hsrc_head hprefix hk_le
      have hk_eq : k = x.length := by
        omega
      subst hk_eq
      have hsrc_read : (c.work src).read = Γ.blank := by
        simp [Tape.read, hsrc_head, hsrc_cells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hprefix_full : (c.work dst).HasBinaryPrefix x := by
        simpa using hprefix
      have hdst_read : (c.work dst).read = Γ.blank := by
        have hblank := hprefix_full.2.2 x.length le_rfl
        simp [Tape.read, hprefix_full.1, hblank]
      have hstep :
          ∃ c1,
            (copyWorkToWorkTM src dst).step c = some c1 ∧
            (copyWorkToWorkTM src dst).halted c1 ∧
            (c1.work src).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
            (c1.work src).head = x.length + 1 ∧
            (c1.work dst).HasBinaryPrefix x := by
        let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
          { state := CopyPhase.done
            input := c.input.move (TM.idleDir c.input.read)
            work := fun i =>
              (c.work i).writeAndMove (TM.readBackWrite ((c.work i).read)).toΓ
                (TM.idleDir ((c.work i).read))
            output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
              (TM.idleDir c.output.read) }
        have hsrc_keep : c1.work src = c.work src := by
          have hsrc_ne : (c.work src).read ≠ Γ.start := by
            rw [hsrc_read]
            decide
          simpa [c1, hsrc_read, TM.transitionTape] using
            (TM.transitionTape_eq_self (t := c.work src) hsrc_ne)
        have hdst_keep : c1.work dst = c.work dst := by
          have hdst_ne : (c.work dst).read ≠ Γ.start := by
            rw [hdst_read]
            decide
          simpa [c1, hdst_read, TM.transitionTape] using
            (TM.transitionTape_eq_self (t := c.work dst) hdst_ne)
        refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
        · simp [TM.step, hstate, copyWorkToWorkTM, hsrc_read, c1, allIdle]
        · rw [hsrc_keep]
          exact hsrc_cells
        · rw [hsrc_keep, hsrc_head]
        · rw [hdst_keep]
          exact hprefix_full
      obtain ⟨c1, hstep1, hhalt1, hsrc_cells1, hsrc_head1, hprefix1⟩ := hstep
      exact ⟨c1, .step hstep1 .zero, hhalt1, hsrc_cells1, hsrc_head1, hprefix1⟩
  | succ rem ih =>
      intro k c hrem hstate hsrc_cells hsrc_head hprefix hk_le
      have hk_lt : k < x.length := by
        omega
      have hsrc_read : (c.work src).read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hsrc_head, hsrc_cells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hprefix_next :
          ((c.work dst).writeAndMove (Γ.ofBool (x[k]'hk_lt)) Dir3.right).HasBinaryPrefix
            (x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk_lt) hprefix
        simpa [List.take_concat_get' x k hk_lt] using hwrite
      have hstep :
          ∃ c1,
            (copyWorkToWorkTM src dst).step c = some c1 ∧
            c1.state = CopyPhase.copying ∧
            (c1.work src).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
            (c1.work src).head = k + 2 ∧
            (c1.work dst).HasBinaryPrefix (x.take (k + 1)) := by
        cases hbit : x[k]'hk_lt with
        | false =>
            have hread0 : (c.work src).read = Γ.zero := by
              simpa [hbit] using hsrc_read
            let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
              { state := CopyPhase.copying
                input := c.input.move (TM.idleDir c.input.read)
                work := fun i =>
                  (c.work i).writeAndMove
                    ((if i = dst then Γw.zero else TM.readBackWrite ((c.work i).read)).toΓ)
                    (if i = dst then Dir3.right else if i = src then Dir3.right
                     else TM.idleDir ((c.work i).read))
                output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                  (TM.idleDir c.output.read) }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, copyWorkToWorkTM, hread0, c1, TM.readBackWrite]
            · have hsrc_ne : (c.work src).read ≠ Γ.start := by
                rw [hread0]
                decide
              have hsrc_pres :
                  (c1.work src).cells = (c.work src).cells := by
                simpa [c1, hread0, hne, TM.readBackWrite] using
                  (TM.tape_readBackWrite_preserves (c.work src) Dir3.right (Or.inr hsrc_ne))
              rw [hsrc_pres]
              exact hsrc_cells
            · simp [c1, hsrc_head, hne, Tape.writeAndMove, Tape.move, Tape.write_head]
            · have hdst :
                  c1.work dst = (c.work dst).writeAndMove Γ.zero Dir3.right := by
                simp [c1]
              rw [hdst]
              simpa [hbit] using hprefix_next
        | true =>
            have hread1 : (c.work src).read = Γ.one := by
              simpa [hbit] using hsrc_read
            let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
              { state := CopyPhase.copying
                input := c.input.move (TM.idleDir c.input.read)
                work := fun i =>
                  (c.work i).writeAndMove
                    ((if i = dst then Γw.one else TM.readBackWrite ((c.work i).read)).toΓ)
                    (if i = dst then Dir3.right else if i = src then Dir3.right
                     else TM.idleDir ((c.work i).read))
                output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                  (TM.idleDir c.output.read) }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, copyWorkToWorkTM, hread1, c1, TM.readBackWrite]
            · have hsrc_ne : (c.work src).read ≠ Γ.start := by
                rw [hread1]
                decide
              have hsrc_pres :
                  (c1.work src).cells = (c.work src).cells := by
                simpa [c1, hread1, hne, TM.readBackWrite] using
                  (TM.tape_readBackWrite_preserves (c.work src) Dir3.right (Or.inr hsrc_ne))
              rw [hsrc_pres]
              exact hsrc_cells
            · simp [c1, hsrc_head, hne, Tape.writeAndMove, Tape.move, Tape.write_head]
            · have hdst :
                  c1.work dst = (c.work dst).writeAndMove Γ.one Dir3.right := by
                simp [c1]
              rw [hdst]
              simpa [hbit] using hprefix_next
      obtain ⟨c1, hstep1, hstate1, hsrc_cells1, hsrc_head1, hprefix1⟩ := hstep
      have hrem1 : rem = x.length - (k + 1) := by
        omega
      obtain ⟨c', hreach, hhalt, hsrc_cells', hsrc_head', hprefix'⟩ :=
        ih (k + 1) c1 hrem1 hstate1 hsrc_cells1 hsrc_head1 hprefix1 (by omega)
      exact ⟨c', .step hstep1 hreach, hhalt, hsrc_cells', hsrc_head', hprefix'⟩

/-- If `src` holds a started Boolean string `x` and `dst` is a started blank
work tape, then `copyWorkToWorkTM src dst` copies `x` onto `dst` within
`|x| + 1` steps. The source contents are preserved, while its head advances
to the first blank cell after the copied data. -/
theorem copyWorkToWorkTM_started_hoareTime {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) :
    (copyWorkToWorkTM src dst).HoareTime
      (fun _inp work _out =>
        work src = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        (work dst).HasBinaryPrefix [])
      (fun _inp work _out =>
        (work src).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work src).head = x.length + 1 ∧
        (work dst).HasBinaryPrefix x)
      (x.length + 1) := by
  intro inp work out hpre
  rcases hpre with ⟨hsrc, hdst⟩
  have hsrc_cells0 : (work src).cells = (Tape.init (x.map Γ.ofBool)).cells := by
    rw [hsrc]
    exact Tape.move_cells _ _
  have hsrc_head0 : (work src).head = 1 := by
    rw [hsrc]
    simp [Tape.move, Tape.init]
  obtain ⟨c', hreach, hhalt, hsrc_cells, hsrc_head, hprefix⟩ :=
    copyWorkToWorkTM_loop src dst hne x x.length 0
      { state := CopyPhase.copying
        input := inp
        work := work
        output := out }
      (by simp)
      rfl
      hsrc_cells0
      hsrc_head0
      (by simpa using hdst)
      (Nat.zero_le _)
  refine ⟨c', x.length + 1, le_rfl, hreach, hhalt, hsrc_cells, hsrc_head, hprefix⟩

/-- Rich HoareTime for `copyWorkToWorkTM`: copy a started Boolean work tape to
another started blank work tape while preserving arbitrary frame data on the
input tape, output tape, and all unrelated work tapes. The source cells are
preserved while its head advances to the first blank after the copied string,
and the destination accumulates the copied prefix without losing its left-end
marker. -/
theorem copyWorkToWorkTM_hoareTime_frame_of_binaryString {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' src).cells = (Tape.init (x.map Γ.ofBool)).cells →
      (work' src).head = x.length + 1 →
      (work' dst).HasBinaryPrefix x →
      (work' dst).cells 0 = Γ.start →
      inp' = inp →
      out' = out →
      (∀ i, i ≠ src → i ≠ dst → work' i = work i) →
      P inp' work' out') :
    (copyWorkToWorkTM src dst).HoareTime
      (fun inp work out =>
        work src = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work dst = (Tape.init []).move Dir3.right ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ src → i ≠ dst → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        (work src).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work src).head = x.length + 1 ∧
        (work dst).HasBinaryPrefix x ∧
        (work dst).cells 0 = Γ.start ∧
        P inp work out)
      (x.length + 1) := by
  intro inp work out hpre
  rcases hpre with ⟨hsrc, hdst, hinp_ns, hout_ns, hout_h, hother_wf, hP⟩
  have tape_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start → t.head ≥ 1 →
      t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
    intro t hns hh
    simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
    split
    · omega
    · simp only [Tape.read] at hns ⊢
      rw [toΓ_readBackWrite_of_ne_start hns, Function.update_eq_self]
  have input_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start →
      t.move (idleDir t.read) = t := by
    intro t hns
    simp [idleDir, hns, Tape.move]
  suffices h_loop : ∀ rem k (c : Cfg n (copyWorkToWorkTM src dst).Q),
      rem = x.length - k →
      c.state = CopyPhase.copying →
      (c.work src).cells = (Tape.init (x.map Γ.ofBool)).cells →
      (c.work src).head = k + 1 →
      (c.work dst).HasBinaryPrefix (x.take k) →
      (c.work dst).cells 0 = Γ.start →
      k ≤ x.length →
      c.input = inp →
      c.output = out →
      (∀ i, i ≠ src → i ≠ dst → c.work i = work i) →
      ∃ c',
        (copyWorkToWorkTM src dst).reachesIn (rem + 1) c c' ∧
        (copyWorkToWorkTM src dst).halted c' ∧
        (c'.work src).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (c'.work src).head = x.length + 1 ∧
        (c'.work dst).HasBinaryPrefix x ∧
        (c'.work dst).cells 0 = Γ.start ∧
        c'.input = inp ∧
        c'.output = out ∧
        (∀ i, i ≠ src → i ≠ dst → c'.work i = work i) by
    have hsrc_cells0 : (work src).cells = (Tape.init (x.map Γ.ofBool)).cells := by
      rw [hsrc]
      exact Tape.move_cells _ _
    have hsrc_head0 : (work src).head = 1 := by
      rw [hsrc]
      simp [Tape.move, Tape.init]
    have hdst_prefix0 : (work dst).HasBinaryPrefix [] := by
      rw [hdst]
      exact Tape.init_nil_move_right_hasBinaryPrefix_nil
    have hdst_cell00 : (work dst).cells 0 = Γ.start := by
      rw [hdst]
      simp [Tape.move, Tape.init]
    obtain ⟨c', hreach, hhalt, hsrc_cells, hsrc_head, hprefix, hcell0, hinp', hout',
      hwork'⟩ :=
      h_loop x.length 0
        { state := CopyPhase.copying, input := inp, work := work, output := out }
        (by simp)
        rfl
        hsrc_cells0
        hsrc_head0
        hdst_prefix0
        hdst_cell00
        (Nat.zero_le _)
        rfl
        rfl
        (fun _ _ _ => rfl)
    refine ⟨c', x.length + 1, le_rfl, hreach, hhalt, hsrc_cells, hsrc_head, hprefix,
      hcell0, ?_⟩
    exact hP_preserved inp work out c'.input c'.work c'.output hP
      hsrc_cells hsrc_head hprefix hcell0 hinp' hout' hwork'
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hsrc_cells hsrc_head hprefix hdst_cell0 hk_le hinp_c hout_c hw_c
      have hk_eq : k = x.length := by
        omega
      subst hk_eq
      have hsrc_read : (c.work src).read = Γ.blank := by
        simp [Tape.read, hsrc_head, hsrc_cells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hprefix_full : (c.work dst).HasBinaryPrefix x := by
        simpa using hprefix
      have hdst_read : (c.work dst).read = Γ.blank := by
        have hblank := hprefix_full.2.2 x.length le_rfl
        simp [Tape.read, hprefix_full.1, hblank]
      let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
        { state := CopyPhase.done
          input := c.input.move (TM.idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove (TM.readBackWrite ((c.work i).read)).toΓ
              (TM.idleDir ((c.work i).read))
          output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
            (TM.idleDir c.output.read) }
      have hstep1 : (copyWorkToWorkTM src dst).step c = some c1 := by
        simp [TM.step, hstate, copyWorkToWorkTM, hsrc_read, c1, allIdle]
      have hinput_keep : c1.input = inp := by
        simpa [c1, hinp_c] using input_idle_preserve inp hinp_ns
      have houtput_keep : c1.output = out := by
        simpa [c1, hout_c] using tape_idle_preserve out hout_ns hout_h
      have hother_keep : ∀ i, i ≠ src → i ≠ dst → c1.work i = work i := by
        intro i hi_src hi_dst
        simpa [c1, hi_src, hi_dst, hw_c i hi_src hi_dst] using
          tape_idle_preserve (work i) (hother_wf i hi_src hi_dst).1 (hother_wf i hi_src hi_dst).2
      have hsrc_keep : c1.work src = c.work src := by
        have hsrc_ne : (c.work src).read ≠ Γ.start := by
          rw [hsrc_read]
          decide
        simpa [c1, hsrc_read, TM.transitionTape] using
          (TM.transitionTape_eq_self (t := c.work src) hsrc_ne)
      have hdst_keep : c1.work dst = c.work dst := by
        have hdst_ne : (c.work dst).read ≠ Γ.start := by
          rw [hdst_read]
          decide
        simpa [c1, hdst_read, TM.transitionTape] using
          (TM.transitionTape_eq_self (t := c.work dst) hdst_ne)
      refine ⟨c1, .step hstep1 .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrc_keep]
        exact hsrc_cells
      · rw [hsrc_keep, hsrc_head]
      · rw [hdst_keep]
        exact hprefix_full
      · rw [hdst_keep]
        exact hdst_cell0
      · exact hinput_keep
      · exact houtput_keep
      · exact hother_keep
  | succ rem ih =>
      intro k c hrem hstate hsrc_cells hsrc_head hprefix hdst_cell0 hk_le hinp_c hout_c hw_c
      have hk_lt : k < x.length := by
        omega
      have hsrc_read : (c.work src).read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hsrc_head, hsrc_cells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hprefix_next :
          ((c.work dst).writeAndMove (Γ.ofBool (x[k]'hk_lt)) Dir3.right).HasBinaryPrefix
            (x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk_lt) hprefix
        simpa [List.take_concat_get' x k hk_lt] using hwrite
      cases hbit : x[k]'hk_lt with
      | false =>
          have hread0 : (c.work src).read = Γ.zero := by
            simpa [hbit] using hsrc_read
          let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
            { state := CopyPhase.copying
              input := c.input.move (TM.idleDir c.input.read)
              work := fun i =>
                (c.work i).writeAndMove
                  ((if i = dst then Γw.zero else TM.readBackWrite ((c.work i).read)).toΓ)
                  (if i = dst then Dir3.right else if i = src then Dir3.right
                    else TM.idleDir ((c.work i).read))
              output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                (TM.idleDir c.output.read) }
          have hstep1 : (copyWorkToWorkTM src dst).step c = some c1 := by
            simp [TM.step, hstate, copyWorkToWorkTM, hread0, c1, TM.readBackWrite]
          have hinput_keep : c1.input = inp := by
            simpa [c1, hinp_c] using input_idle_preserve inp hinp_ns
          have houtput_keep : c1.output = out := by
            simpa [c1, hout_c] using tape_idle_preserve out hout_ns hout_h
          have hother_keep : ∀ i, i ≠ src → i ≠ dst → c1.work i = work i := by
            intro i hi_src hi_dst
            simpa [c1, hi_src, hi_dst, hw_c i hi_src hi_dst] using
              tape_idle_preserve (work i) (hother_wf i hi_src hi_dst).1
                (hother_wf i hi_src hi_dst).2
          have hsrc_cells1 : (c1.work src).cells = (Tape.init (x.map Γ.ofBool)).cells := by
            have hsrc_ne : (c.work src).read ≠ Γ.start := by
              rw [hread0]
              decide
            have hsrc_pres :
                (c1.work src).cells = (c.work src).cells := by
              simpa [c1, hread0, hne, TM.readBackWrite] using
                (TM.tape_readBackWrite_preserves (c.work src) Dir3.right (Or.inr hsrc_ne))
            rw [hsrc_pres]
            exact hsrc_cells
          have hsrc_head1 : (c1.work src).head = k + 2 := by
            simp [c1, hsrc_head, hne, Tape.writeAndMove, Tape.move, Tape.write_head]
          have hdst_prefix1 : (c1.work dst).HasBinaryPrefix (x.take (k + 1)) := by
            have hdst :
                c1.work dst = (c.work dst).writeAndMove Γ.zero Dir3.right := by
              simp [c1]
            rw [hdst]
            simpa [hbit] using hprefix_next
          have hdst_cell01 : (c1.work dst).cells 0 = Γ.start := by
            have hdst :
                c1.work dst = (c.work dst).writeAndMove Γ.zero Dir3.right := by
              simp [c1]
            rw [hdst]
            exact Tape.hasBinaryPrefix_write_bit_cell0 false hprefix hdst_cell0
          have hrem1 : rem = x.length - (k + 1) := by
            omega
          obtain ⟨c', hreach, hhalt, hsrc_cells', hsrc_head', hprefix', hcell0', hinp',
            hout', hwork'⟩ :=
            ih (k + 1) c1 hrem1 rfl hsrc_cells1 hsrc_head1 hdst_prefix1 hdst_cell01
              (by omega) hinput_keep houtput_keep hother_keep
          exact ⟨c', .step hstep1 hreach, hhalt, hsrc_cells', hsrc_head', hprefix', hcell0',
            hinp', hout', hwork'⟩
      | true =>
          have hread1 : (c.work src).read = Γ.one := by
            simpa [hbit] using hsrc_read
          let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
            { state := CopyPhase.copying
              input := c.input.move (TM.idleDir c.input.read)
              work := fun i =>
                (c.work i).writeAndMove
                  ((if i = dst then Γw.one else TM.readBackWrite ((c.work i).read)).toΓ)
                  (if i = dst then Dir3.right else if i = src then Dir3.right
                    else TM.idleDir ((c.work i).read))
              output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
                (TM.idleDir c.output.read) }
          have hstep1 : (copyWorkToWorkTM src dst).step c = some c1 := by
            simp [TM.step, hstate, copyWorkToWorkTM, hread1, c1, TM.readBackWrite]
          have hinput_keep : c1.input = inp := by
            simpa [c1, hinp_c] using input_idle_preserve inp hinp_ns
          have houtput_keep : c1.output = out := by
            simpa [c1, hout_c] using tape_idle_preserve out hout_ns hout_h
          have hother_keep : ∀ i, i ≠ src → i ≠ dst → c1.work i = work i := by
            intro i hi_src hi_dst
            simpa [c1, hi_src, hi_dst, hw_c i hi_src hi_dst] using
              tape_idle_preserve (work i) (hother_wf i hi_src hi_dst).1
                (hother_wf i hi_src hi_dst).2
          have hsrc_cells1 : (c1.work src).cells = (Tape.init (x.map Γ.ofBool)).cells := by
            have hsrc_ne : (c.work src).read ≠ Γ.start := by
              rw [hread1]
              decide
            have hsrc_pres :
                (c1.work src).cells = (c.work src).cells := by
              simpa [c1, hread1, hne, TM.readBackWrite] using
                (TM.tape_readBackWrite_preserves (c.work src) Dir3.right (Or.inr hsrc_ne))
            rw [hsrc_pres]
            exact hsrc_cells
          have hsrc_head1 : (c1.work src).head = k + 2 := by
            simp [c1, hsrc_head, hne, Tape.writeAndMove, Tape.move, Tape.write_head]
          have hdst_prefix1 : (c1.work dst).HasBinaryPrefix (x.take (k + 1)) := by
            have hdst :
                c1.work dst = (c.work dst).writeAndMove Γ.one Dir3.right := by
              simp [c1]
            rw [hdst]
            simpa [hbit] using hprefix_next
          have hdst_cell01 : (c1.work dst).cells 0 = Γ.start := by
            have hdst :
                c1.work dst = (c.work dst).writeAndMove Γ.one Dir3.right := by
              simp [c1]
            rw [hdst]
            exact Tape.hasBinaryPrefix_write_bit_cell0 true hprefix hdst_cell0
          have hrem1 : rem = x.length - (k + 1) := by
            omega
          obtain ⟨c', hreach, hhalt, hsrc_cells', hsrc_head', hprefix', hcell0', hinp',
            hout', hwork'⟩ :=
            ih (k + 1) c1 hrem1 rfl hsrc_cells1 hsrc_head1 hdst_prefix1 hdst_cell01
              (by omega) hinput_keep houtput_keep hother_keep
          exact ⟨c', .step hstep1 hreach, hhalt, hsrc_cells', hsrc_head', hprefix', hcell0',
            hinp', hout', hwork'⟩

end TM

end Complexity

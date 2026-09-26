/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal

/-!
# Complement TM: proof internals

This file provides the simulation lemmas for `TM.complementTM`, showing that
the complement machine correctly flips the output of the original TM.
-/


@[expose] public section

namespace Complexity

variable {n : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Configuration embedding
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a configuration of `tm` into `tm.complementTM` by tagging the state
    with `Sum.inl` and keeping all tapes unchanged. -/
def complementCfg (tm : TM n) (c : Cfg n tm.Q) : Cfg n (tm.complementTM.Q) :=
  { state := Sum.inl c.state, input := c.input, work := c.work, output := c.output }

/-- Embedding the initial configuration of `tm` on input `x` yields the initial
    configuration of `tm.complementTM` on `x`. -/
theorem compCfg_initCfg (tm : TM n) (x : List Bool) :
    complementCfg tm (tm.initCfg x) = tm.complementTM.initCfg x := rfl

/-- The embedding sends configurations in `tm`'s start state to configurations in
    `tm.complementTM`'s start state, preserving all tapes. -/
theorem compCfg_qstart (tm : TM n) (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    complementCfg tm ⟨tm.qstart, inp, work, out⟩ =
      ⟨tm.complementTM.qstart, inp, work, out⟩ := rfl

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: Simulation (via generic simulation lifting)
-- ════════════════════════════════════════════════════════════════════════

private theorem complementTM_step_sim (tm : TM n) {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c') :
    tm.complementTM.step (complementCfg tm c) = some (complementCfg tm c') := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, complementTM, complementCfg] at hstep ⊢
  have hne2 : (Sum.inl c.state : ComplementQ tm.Q) ≠ Sum.inr .done := nofun
  simp only [hne, hne2, ↓reduceIte, Option.some.injEq] at hstep ⊢
  rw [← hstep]

/-- `tm.complementTM` simulates `tm` step-for-step on embedded configurations: a
    `t`-step run of `tm` lifts to a `t`-step run of the complement machine. -/
theorem complementTM_simulation (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (hreach : tm.reachesIn t c c') :
    tm.complementTM.reachesIn t (complementCfg tm c) (complementCfg tm c') :=
  reachesIn_map (tm' := tm.complementTM) (complementCfg tm)
    (fun _ _ => complementTM_step_sim tm) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop (via generic rewind)
-- ════════════════════════════════════════════════════════════════════════

/-- One rewind step: at head > 0, move left, preserve cells. -/
private theorem complement_rewind_step_left (tm : TM n) (c : Cfg n tm.complementTM.Q)
    (hstate : c.state = Sum.inr ComplementPhase.rewind)
    (hread_ne : c.output.read ≠ Γ.start)
    (_ : c.output.cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', tm.complementTM.step c = some c' ∧
      c'.state = Sum.inr ComplementPhase.rewind ∧
      c'.output.head = c.output.head - 1 ∧
      c'.output.cells = c.output.cells := by
  simp only [TM.step, ↓reduceIte, hstate, complementTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp only [Tape.writeAndMove, Tape.move]
    rw [toΓ_readBackWrite_of_ne_start hread_ne]
    simp only [Tape.write, Tape.read]; split
    · omega
    · simp
  · simp only [Tape.writeAndMove, Tape.move_cells]
    rw [toΓ_readBackWrite_of_ne_start hread_ne]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

/-- Base rewind step: at head = 0 (reading ▷), move right to cell 1, enter flip. -/
private theorem complement_rewind_step_base (tm : TM n) (c : Cfg n tm.complementTM.Q)
    (hstate : c.state = Sum.inr ComplementPhase.rewind)
    (hread : c.output.read = Γ.start)
    (_ : c.output.cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', tm.complementTM.step c = some c' ∧
      c'.state = Sum.inr ComplementPhase.flip ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells := by
  have hhead : c.output.head = 0 := by
    by_contra hne
    have hge : c.output.head ≥ 1 := by omega
    exact hnostart c.output.head hge (by simp only [Tape.read] at hread; exact hread)
  simp only [TM.step, ↓reduceIte, hstate, complementTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]

/-- From rewind state with output head at position `h`, reach flip state
    at cell 1 with output cells preserved, in `h + 1` steps. -/
private theorem rewind_loop (tm : TM n) :
    ∀ (h : ℕ) (c : Cfg n tm.complementTM.Q),
    c.state = Sum.inr ComplementPhase.rewind →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = h →
    ∃ c_flip,
      tm.complementTM.reachesIn (h + 1) c c_flip ∧
      c_flip.state = Sum.inr ComplementPhase.flip ∧
      c_flip.output.head = 1 ∧
      c_flip.output.cells = c.output.cells :=
  exists_reachesIn_of_rewindStep_output tm.complementTM
    (fun c hst hread hc0 hns => complement_rewind_step_left tm c hst hread hc0 hns)
    (fun c hst hread hc0 hns => complement_rewind_step_base tm c hst hread hc0 hns)

-- ════════════════════════════════════════════════════════════════════════
-- Combined: halt → rewind → flip → done
-- ════════════════════════════════════════════════════════════════════════

/-- From halted complementCfg, reach done state with flipped output.
    Takes ≤ `output.head + 4` steps. -/
theorem complementTM_rewind_and_flip (tm : TM n)
    (c_halt : Cfg n tm.Q)
    (hhalt : tm.halted c_halt)
    (hcell0 : c_halt.output.cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → c_halt.output.cells j ≠ Γ.start) :
    ∃ c_done t_rw,
      tm.complementTM.reachesIn t_rw (complementCfg tm c_halt) c_done ∧
      tm.complementTM.halted c_done ∧
      c_done.output.cells 1 = (flipBit (c_halt.output.cells 1)).toΓ ∧
      t_rw ≤ c_halt.output.head + 4 := by
  -- Step 1: halt → rewind (1 step)
  have hne : (complementCfg tm c_halt).state ≠ Sum.inr ComplementPhase.done := nofun
  have hstep1 : ∃ c_rw, tm.complementTM.step (complementCfg tm c_halt) = some c_rw ∧
      c_rw.state = Sum.inr ComplementPhase.rewind ∧
      c_rw.output.cells = c_halt.output.cells ∧
      c_rw.output.head ≤ c_halt.output.head + 1 := by
    simp only [TM.step, ↓reduceIte,
      show (complementCfg tm c_halt).state = Sum.inl c_halt.state from rfl,
               complementTM, hhalt]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · dsimp only [complementCfg]
      simp only [Tape.writeAndMove, Tape.move_cells]
      by_cases hread : c_halt.output.read = Γ.start
      · have hh0 : c_halt.output.head = 0 := by
          have h := hread; simp only [Tape.read] at h
          by_contra hne; exact hnostart _ (by omega) h
        simp [Tape.write, hh0]
      · rw [toΓ_readBackWrite_of_ne_start hread]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
    · dsimp only [complementCfg]
      exact Tape.head_writeAndMove_le _ _ _
  obtain ⟨c_rw, hstep1', hst_rw, hcells_rw, hhead_rw⟩ := hstep1
  -- Step 2: rewind loop (c_rw.output.head + 1 steps)
  have hcell0_rw : c_rw.output.cells 0 = Γ.start := by rw [hcells_rw]; exact hcell0
  have hnostart_rw : ∀ j, j ≥ 1 → c_rw.output.cells j ≠ Γ.start := by
    intro j hj; rw [hcells_rw]; exact hnostart j hj
  obtain ⟨c_flip, hreach_rw, hst_flip, hhead_flip, hcells_flip⟩ :=
    rewind_loop tm c_rw.output.head c_rw hst_rw hcell0_rw hnostart_rw rfl
  -- Step 3: flip (1 step)
  have hne_flip : c_flip.state ≠ Sum.inr ComplementPhase.done := by rw [hst_flip]; nofun
  have hnostart_flip : c_flip.output.read ≠ Γ.start := by
    simp [Tape.read, hhead_flip, hcells_flip, hcells_rw]
    exact hnostart 1 (by omega)
  have hne1 : c_halt.output.cells 1 ≠ Γ.start := hnostart 1 (by omega)
  have hstep3 : ∃ c_done, tm.complementTM.step c_flip = some c_done ∧
      c_done.state = Sum.inr ComplementPhase.done ∧
      c_done.output.cells 1 = (flipBit (c_halt.output.cells 1)).toΓ := by
    simp only [TM.step, hst_flip, complementTM]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [Tape.writeAndMove, Tape.move, Tape.write, Tape.read, hhead_flip,
               hcells_flip, hcells_rw]
    have hdir2 : idleDir (c_halt.output.cells 1) = Dir3.stay := by
      simp [idleDir, hne1]
    simp [hdir2, Function.update_self]
  obtain ⟨c_done, hstep3', hst_done, hflip⟩ := hstep3
  refine ⟨c_done, ((c_rw.output.head + 1) + 1) + 1,
    reachesIn_trans tm.complementTM (.step hstep1' hreach_rw) (.step hstep3' .zero),
    hst_done, hflip, by omega⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- If `tm` decides `L` in time `f`, then `complementTM tm` decides `Lᶜ`
    in time `2 * f + 4`. -/
theorem complementTM_decidesInTime (tm : TM n) {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    tm.complementTM.DecidesInTime Lᶜ (fun n => 2 * f n + 4) := by
  intro x
  obtain ⟨c', t, hle, hreach, hhalt, hyes, hno⟩ := hdec x
  have hsim := complementTM_simulation tm hreach
  rw [compCfg_initCfg] at hsim
  have ⟨_, hout_head, _⟩ := head_le_of_reachesIn tm hreach
  have hcell0 := output_cells_zero_eq_start_of_reachesIn hreach (by simp [Tape.init])
  have hnostart := output_cells_ne_start_of_reachesIn hreach (by
    intro i hi; simp [Tape.init]; omega)
  obtain ⟨c_done, t_rw, hreach_rw, hhalt_done, hflip, hle_rw⟩ :=
    complementTM_rewind_and_flip tm c' hhalt hcell0 hnostart
  have htotal := reachesIn_trans tm.complementTM hsim hreach_rw
  refine ⟨c_done, t + t_rw, ?_, htotal, hhalt_done, ?_, ?_⟩
  · show t + t_rw ≤ 2 * f x.length + 4
    have : t_rw ≤ t + 4 := le_trans hle_rw (by omega)
    omega
  · intro hxc; rw [hflip, hno hxc]; simp [flipBit]
  · intro hxc
    simp only [Set.mem_compl_iff, not_not] at hxc
    rw [hflip, hyes hxc]; simp [flipBit]

end TM

end Complexity

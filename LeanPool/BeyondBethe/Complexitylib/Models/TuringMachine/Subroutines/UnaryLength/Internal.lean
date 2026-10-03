/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.UnaryLength.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Unary input-length transducer — proof internals

This module proves the exact execution contract for `TM.unaryLengthTM`.
Starting from an initial configuration on `x`, it skips the left-end marker,
writes one `true` bit per input bit, and halts on the first input blank after
exactly `|x| + 2` transitions.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- From the first unvisited input cell and an output containing `k` unary
marks, the scan consumes the remaining `|x| - k` bits and the terminating
blank. -/
private theorem unaryLengthTM_loop {n : ℕ} (x : List Bool) :
    ∀ rem k (c : Cfg n (unaryLengthTM (n := n)).Q),
      rem = x.length - k →
      c.state = UnaryLengthPhase.copying →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      c.output.HasBinaryPrefix (List.replicate k true) →
      k ≤ x.length →
      ∃ c',
        (unaryLengthTM (n := n)).reachesIn (rem + 1) c c' ∧
        (unaryLengthTM (n := n)).halted c' ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        c'.output.HasBinaryPrefix (List.replicate x.length true) := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hcells hhead hprefix hk
      have hk_eq : k = x.length := by omega
      subst k
      have hread : c.input.read = Γ.blank := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge x x.length]
      have houtputRead : c.output.read = Γ.blank := hprefix.read_blank
      let c' : Cfg n (unaryLengthTM (n := n)).Q :=
        { state := UnaryLengthPhase.done
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) }
      have hinputKeep : c.input.move (idleDir c.input.read) = c.input := by
        simp [idleDir, hread, Tape.move]
      have houtputKeep :
          c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read) = c.output := by
        exact transitionTape_eq_self (by simp [houtputRead])
      have hstep : (unaryLengthTM (n := n)).step c = some c' := by
        simp [TM.step, hstate, unaryLengthTM, hread, c']
      refine ⟨c', .step hstep .zero, rfl, ?_, ?_, ?_⟩
      · rw [show c'.input = c.input by simpa [c'] using hinputKeep]
        exact hcells
      · rw [show c'.input = c.input by simpa [c'] using hinputKeep]
        exact hhead
      · rw [show c'.output = c.output by simpa [c'] using houtputKeep]
        exact hprefix
  | succ rem ih =>
      intro k c hrem hstate hcells hhead hprefix hk
      have hk_lt : k < x.length := by omega
      have hread : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hnotBlank : c.input.read ≠ Γ.blank := by
        rw [hread]
        exact Γ.ofBool_ne_blank _
      have hreplicate :
          List.replicate k true ++ [true] = List.replicate (k + 1) true := by
        change List.replicate k true ++ List.replicate 1 true = _
        rw [← List.replicate_add]
      have hprefix' :
          (c.output.writeAndMove Γ.one Dir3.right).HasBinaryPrefix
            (List.replicate (k + 1) true) := by
        rw [← hreplicate]
        exact Tape.hasBinaryPrefix_write_bit true hprefix
      let c' : Cfg n (unaryLengthTM (n := n)).Q :=
        { state := UnaryLengthPhase.copying
          input := c.input.move Dir3.right
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (idleDir (c.work i).read)
          output := c.output.writeAndMove Γ.one Dir3.right }
      have hstep : (unaryLengthTM (n := n)).step c = some c' := by
        simp [TM.step, hstate, unaryLengthTM, hnotBlank, c']
      have hcells' : c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
        simpa [c', Tape.move_cells] using hcells
      have hhead' : c'.input.head = (k + 1) + 1 := by
        simp [c', Tape.move, hhead]
      have hrem' : rem = x.length - (k + 1) := by omega
      obtain ⟨c'', hreach, hhalt, hcells'', hhead'', hprefix''⟩ :=
        ih (k + 1) c' hrem' rfl hcells' hhead' (by simpa [c'] using hprefix') (by omega)
      exact ⟨c'', .step hstep hreach, hhalt, hcells'', hhead'', hprefix''⟩

/-- Internal implementation theorem: `unaryLengthTM` emits the unary input
length within the linear bound `m + 2`. -/
theorem unaryLengthTM_computesInTime_internal (n : ℕ) :
    (unaryLengthTM (n := n)).ComputesInTime
      (fun x => List.replicate x.length true) (fun m => m + 2) := by
  intro x
  let c₁ : Cfg n (unaryLengthTM (n := n)).Q :=
    { state := UnaryLengthPhase.copying
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right }
  have hstep :
      (unaryLengthTM (n := n)).step ((unaryLengthTM (n := n)).initCfg x) = some c₁ := by
    simp [TM.step, unaryLengthTM, c₁, Tape.read, Tape.init, readBackWrite,
      idleDir, Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨c', hreach, hhalt, _hcells, _hhead, hprefix⟩ :=
    unaryLengthTM_loop (n := n) x x.length 0 c₁ (by simp) rfl
      (by simp [c₁, Tape.move]) (by simp [c₁, Tape.move])
      (by simpa [c₁] using Tape.init_nil_move_right_hasBinaryPrefix_nil)
      (Nat.zero_le _)
  refine ⟨c', x.length + 2, le_rfl, ?_, hhalt, ?_⟩
  · simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach
  · exact hprefix.hasOutput

end TM

end Complexity

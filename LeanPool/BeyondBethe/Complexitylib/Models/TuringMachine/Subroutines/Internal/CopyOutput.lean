/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Input-to-output copy correctness

Exact simulation proof for `TM.copyInputToOutputTM`. Starting from the initial
configuration on `x`, the machine skips the two left-end markers, copies one
Boolean symbol per step, and halts at the first input blank after exactly
`|x| + 2` steps with output `x`.

The public theorem is stated in
`Complexitylib.Models.TuringMachine.Subroutines.CopyOutput`.
-/


public section

namespace Complexity

namespace TM

/-! ## Copy loop -/

/-- From the first uncopied input cell and an output holding `x.take k`, the
copy loop consumes the remaining `rem = |x| - k` bits and one terminating
blank step. -/
private theorem copyInputToOutputTM_loop {n : ℕ} (x : List Bool) :
    ∀ rem k (c : Cfg n (copyInputToOutputTM (n := n)).Q),
      rem = x.length - k →
      c.state = CopyPhase.copying →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      c.output.HasBinaryPrefix (x.take k) →
      k ≤ x.length →
      ∃ c',
        (copyInputToOutputTM (n := n)).reachesIn (rem + 1) c c' ∧
        (copyInputToOutputTM (n := n)).halted c' ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        c'.output.HasBinaryPrefix x := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_eq : k = x.length := by omega
      subst hk_eq
      have hread : c.input.read = Γ.blank := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hprefix_full : c.output.HasBinaryPrefix x := by
        simpa using hprefix
      have houtput_blank : c.output.read = Γ.blank := by
        have hblank := hprefix_full.2.2 x.length le_rfl
        simp [Tape.read, hprefix_full.1, hblank]
      let c1 : Cfg n (copyInputToOutputTM (n := n)).Q :=
        { state := CopyPhase.done
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) }
      have hinput_keep : c.input.move (idleDir c.input.read) = c.input := by
        simp [idleDir, hread, Tape.move]
      have houtput_keep :
          c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read) = c.output := by
        exact transitionTape_eq_self (t := c.output) (by simp [houtput_blank])
      have hstep : (copyInputToOutputTM (n := n)).step c = some c1 := by
        simp [TM.step, hstate, copyInputToOutputTM, hread, c1]
      refine ⟨c1, .step hstep .zero, rfl, ?_, ?_, ?_⟩
      · rw [show c1.input = c.input by simpa [c1] using hinput_keep]
        exact hcells
      · rw [show c1.input = c.input by simpa [c1] using hinput_keep]
        exact hhead
      · rw [show c1.output = c.output by simpa [c1] using houtput_keep]
        exact hprefix_full
  | succ rem ih =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_lt : k < x.length := by omega
      have hread : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hprefix_next :
          (c.output.writeAndMove (Γ.ofBool (x[k]'hk_lt)) Dir3.right).HasBinaryPrefix
            (x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk_lt) hprefix
        simpa [List.take_concat_get' x k hk_lt] using hwrite
      have hstep :
          ∃ c1,
            (copyInputToOutputTM (n := n)).step c = some c1 ∧
            c1.state = CopyPhase.copying ∧
            c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
            c1.input.head = k + 2 ∧
            c1.output.HasBinaryPrefix (x.take (k + 1)) := by
        cases hbit : x[k]'hk_lt with
        | false =>
            have hread0 : c.input.read = Γ.zero := by
              simpa [Γ.ofBool, transitionTape, Γw.toΓ, hbit] using hread
            let c1 : Cfg n (copyInputToOutputTM (n := n)).Q :=
              { state := CopyPhase.copying
                input := c.input.move Dir3.right
                work := fun i =>
                  (c.work i).writeAndMove (readBackWrite (c.work i).read)
                    (idleDir (c.work i).read)
                output := c.output.writeAndMove Γ.zero Dir3.right }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, copyInputToOutputTM, hread0, c1, readBackWrite]
            · simpa [c1, Tape.move_cells] using hcells
            · simp [c1, Tape.move, hhead]
            · simpa [c1, hbit] using! hprefix_next
        | true =>
            have hread1 : c.input.read = Γ.one := by
              simpa [Γ.ofBool, transitionTape, Γw.toΓ, hbit] using hread
            let c1 : Cfg n (copyInputToOutputTM (n := n)).Q :=
              { state := CopyPhase.copying
                input := c.input.move Dir3.right
                work := fun i =>
                  (c.work i).writeAndMove (readBackWrite (c.work i).read)
                    (idleDir (c.work i).read)
                output := c.output.writeAndMove Γ.one Dir3.right }
            refine ⟨c1, ?_, rfl, ?_, ?_, ?_⟩
            · simp [TM.step, hstate, copyInputToOutputTM, hread1, c1, readBackWrite]
            · simpa [c1, Tape.move_cells] using hcells
            · simp [c1, Tape.move, hhead]
            · simpa [c1, hbit] using! hprefix_next
      obtain ⟨c1, hstep1, hstate1, hcells1, hhead1, hprefix1⟩ := hstep
      have hrem1 : rem = x.length - (k + 1) := by omega
      obtain ⟨c', hreach, hhalt, hcells', hhead', hprefix'⟩ :=
        ih (k + 1) c1 hrem1 hstate1 hcells1 hhead1 hprefix1 (by omega)
      exact ⟨c', .step hstep1 hreach, hhalt, hcells', hhead', hprefix'⟩

/-! ## Initial-configuration correctness -/

/-- Internal implementation theorem: the copy machine computes identity in
the exact linear bound `m + 2`. -/
theorem copyInputToOutputTM_computesInTime_internal (n : ℕ) :
    (copyInputToOutputTM (n := n)).ComputesInTime id (fun m => m + 2) := by
  intro x
  let c1 : Cfg n (copyInputToOutputTM (n := n)).Q :=
    { state := CopyPhase.copying
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right }
  have hstep :
      (copyInputToOutputTM (n := n)).step
          ((copyInputToOutputTM (n := n)).initCfg x) = some c1 := by
    simp [TM.step, copyInputToOutputTM, c1, Tape.read, Tape.init, readBackWrite,
      idleDir, Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨c', hreach, hhalt, _hcells, _hhead, hprefix⟩ :=
    copyInputToOutputTM_loop (n := n) x x.length 0 c1 (by simp) rfl
      (by simp [c1, Tape.move]) (by simp [c1, Tape.move])
      (by simpa [c1] using Tape.init_nil_move_right_hasBinaryPrefix_nil)
      (Nat.zero_le _)
  refine ⟨c', x.length + 2, le_rfl, ?_, hhalt, ?_⟩
  · simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach
  · simpa using (show c'.output.HasOutput x from
      ⟨hprefix.2.1, hprefix.2.2 x.length le_rfl⟩)

end TM

end Complexity

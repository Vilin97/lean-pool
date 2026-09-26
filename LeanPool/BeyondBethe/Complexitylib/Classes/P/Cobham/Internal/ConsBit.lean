/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Counter
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# The bit successor — proof internals

`Cobham.consBitTM b` prepends the fixed bit `b` to its input: the machine behind
the `bit` constructor of Cobham's algebra.

## Main results

- `Cobham.cons_mem_FP` — prepending a fixed bit is in `FP`
-/


@[expose] public section

namespace Complexity

namespace Cobham

open Complexity.TM

/-! ### The bit-successor transducer

A small machine computing `x ↦ b :: x`: skip the left marker, emit `b`, then copy
the input verbatim after it. Modelled on `TM.copyInputToOutputTM`. -/


/-- Control states of `consBitTM`: skip the `▷` marker, emit the fixed bit, copy
the input, halt. -/
inductive ConsPhase where
  | skip | emit | copy | done
  deriving DecidableEq

instance : Fintype ConsPhase where
  elems := {.skip, .emit, .copy, .done}
  complete := fun x => by cases x <;> simp

/-- The bit-successor machine: on input `x` it writes `b :: x` to the output tape
in `|x| + 3` steps. First `skip` advances past the left markers, `emit` writes `b`
into output cell 1, and `copy` copies the input bits after it. -/
def consBitTM (b : Bool) : TM 0 where
  Q := ConsPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.emit, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .emit =>
        (.copy, fun i => readBackWrite (wHeads i), Γw.ofBool b, idleDir iHead,
          fun i => idleDir (wHeads i), Dir3.right)
    | .copy =>
        if iHead = Γ.blank then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.copy, fun i => readBackWrite (wHeads i), readBackWrite iHead,
            Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .emit =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .copy =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- The copy phase of `consBitTM`: from a configuration whose output already holds
`b :: x.take k` and whose input head is at the first uncopied cell, the remaining
`rem = |x| - k` bits are copied and the machine halts with output `b :: x`. -/
private theorem consBitTM_copy_loop (b : Bool) (x : List Bool) :
    ∀ rem k (c : Cfg 0 (consBitTM b).Q),
      rem = x.length - k →
      c.state = ConsPhase.copy →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      c.output.HasBinaryPrefix (b :: x.take k) →
      k ≤ x.length →
      ∃ c',
        (consBitTM b).reachesIn (rem + 1) c c' ∧
        (consBitTM b).halted c' ∧
        c'.output.HasBinaryPrefix (b :: x) := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_eq : k = x.length := by omega
      subst hk_eq
      have hread : c.input.read = Γ.blank := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hprefix_full : c.output.HasBinaryPrefix (b :: x) := by
        simpa using hprefix
      have houtput_blank : c.output.read = Γ.blank := hprefix_full.read_blank
      let c1 : Cfg 0 (consBitTM b).Q :=
        { state := ConsPhase.done
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
        rw [writeAndMove_readBack c.output (by simp [houtput_blank]),
          idleDir, ite_eq_right (by simp [houtput_blank]), Tape.move]
      have hstep : (consBitTM b).step c = some c1 := by
        simp [TM.step, hstate, consBitTM, hread, c1]
      refine ⟨c1, .step hstep .zero, rfl, ?_⟩
      rw [show c1.output = c.output by simpa [c1] using houtput_keep]
      exact hprefix_full
  | succ rem ih =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_lt : k < x.length := by omega
      have hread : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hread_ne : c.input.read ≠ Γ.blank := by
        rw [hread]; cases x[k]'hk_lt <;> simp [Γ.ofBool]
      have hprefix_next :
          (c.output.writeAndMove (Γ.ofBool (x[k]'hk_lt)) Dir3.right).HasBinaryPrefix
            (b :: x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk_lt) hprefix
        have heq : (b :: x.take k) ++ [x[k]'hk_lt] = b :: x.take (k + 1) := by
          rw [List.cons_append, List.take_concat_get' x k hk_lt]
        rwa [heq] at hwrite
      let c1 : Cfg 0 (consBitTM b).Q :=
        { state := ConsPhase.copy
          input := c.input.move Dir3.right
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
      have hstep : (consBitTM b).step c = some c1 := by
        simp [TM.step, hstate, consBitTM, hread_ne, c1]
      have hcells1 : c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
        simpa [c1, Tape.move_cells] using hcells
      have hhead1 : c1.input.head = (k + 1) + 1 := by simp [c1, Tape.move, hhead]
      have hprefix1 : c1.output.HasBinaryPrefix (b :: x.take (k + 1)) := by
        have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool (x[k]'hk_lt) := by
          rw [hread]; cases x[k]'hk_lt <;> rfl
        show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ) Dir3.right).HasBinaryPrefix
          (b :: x.take (k + 1))
        rw [hco]; exact hprefix_next
      obtain ⟨c', hreach, hhalt, hprefix'⟩ :=
        ih (k + 1) c1 (by omega) rfl hcells1 hhead1 hprefix1 (by omega)
      exact ⟨c', .step hstep hreach, hhalt, hprefix'⟩

/-- `consBitTM b` computes `x ↦ b :: x` within the linear bound `|x| + 3`. -/
theorem consBitTM_computesInTime (b : Bool) :
    (consBitTM b).ComputesInTime (fun x => b :: x) (fun m => m + 3) := by
  intro x
  -- Step 1: `skip` advances past the left markers.
  let c1 : Cfg 0 (consBitTM b).Q :=
    { state := ConsPhase.emit
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).writeAndMove (readBackWrite (Tape.init []).read)
        (idleDir (Tape.init []).read)
      output := (Tape.init []).move Dir3.right }
  have hstep1 : (consBitTM b).step ((consBitTM b).initCfg x) = some c1 := by
    simp [TM.step, consBitTM, c1, Tape.read, Tape.init, idleDir, Tape.writeAndMove,
      Tape.write, Tape.move]
  -- The input head after `skip` reads a data/blank cell, never the marker.
  have hne : c1.input.read ≠ Γ.start := by
    cases x with
    | nil => simp [c1, Tape.read, Tape.move, Tape.init]
    | cons a t => cases a <;> simp [c1, Tape.read, Tape.move, Tape.init, Γ.ofBool]
  -- Step 2: `emit` writes `b` into output cell 1.
  let c2 : Cfg 0 (consBitTM b).Q :=
    { state := ConsPhase.copy
      input := c1.input.move (idleDir c1.input.read)
      work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
        (idleDir (c1.work i).read)
      output := c1.output.writeAndMove (Γw.ofBool b) Dir3.right }
  have hstep2 : (consBitTM b).step c1 = some c2 := by
    simp [TM.step, consBitTM, c1, c2]
  have hc2_input_cells : c2.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
    simp [c2, c1, Tape.move_cells]
  have hc2_input_head : c2.input.head = 0 + 1 := by
    show (c1.input.move (idleDir c1.input.read)).head = 0 + 1
    rw [idleDir, ite_eq_right hne]
    simp [Tape.move, c1, Tape.init]
  have hc2_output : c2.output.HasBinaryPrefix (b :: x.take 0) := by
    have hbase : ((Tape.init []).move Dir3.right).HasBinaryPrefix [] :=
      Tape.init_nil_move_right_hasBinaryPrefix_nil
    have hw := Tape.hasBinaryPrefix_write_bit (t := (Tape.init []).move Dir3.right) b hbase
    show (c1.output.writeAndMove ((Γw.ofBool b).toΓ) Dir3.right).HasBinaryPrefix (b :: x.take 0)
    rw [Γw.ofBool_toΓ, show c1.output = (Tape.init []).move Dir3.right from rfl]
    simpa using hw
  obtain ⟨c', hreach, hhalt, hprefix⟩ :=
    consBitTM_copy_loop b x x.length 0 c2 (by simp) rfl hc2_input_cells
      hc2_input_head hc2_output (Nat.zero_le _)
  refine ⟨c', x.length + 3, le_rfl, ?_, hhalt, (hprefix.hasOutput)⟩
  have : (consBitTM b).reachesIn (x.length + 1 + 1 + 1) ((consBitTM b).initCfg x) c' :=
    .step hstep1 (.step hstep2 hreach)
  simpa [Nat.add_assoc] using this

/-- Prepending a fixed bit is polynomial-time — the string-successor underlying
the `bit` constructor. Witnessed by `consBitTM`. -/
theorem cons_mem_FP (b : Bool) : (fun x : List Bool => b :: x) ∈ FP := by
  refine ⟨1, 0, consBitTM b, (fun m => m + 3), consBitTM_computesInTime b, ?_⟩
  have hn : (fun m : ℕ => m) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun m : ℕ => m)
  exact BigO.add hn (BigO.const_le_pow 3 1)

end Cobham

end Complexity

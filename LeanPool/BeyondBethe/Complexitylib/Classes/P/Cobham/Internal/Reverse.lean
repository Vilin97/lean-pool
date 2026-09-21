/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Polynomial-time string reversal — proof internals

The transducer `reverseTM` has one work tape and four control states: it copies
the input onto the work tape left to right, then walks the work head back to the
left-end marker, emitting each cell to the output as it passes. The result is the
input read backwards, in `2 · |x| + 3` steps.

Reversal is what turns a right-to-left recursion into a left-to-right loop:
recursion on notation peels the *head* of a string, so an iterative evaluation
consumes the *last* bit first.

## Main results

- `Complexity.reverse_mem_FP` — reversal is in `FP`
-/


public section

namespace Complexity

open Complexity.TM

/-- Control states of `reverseTM`. -/
inductive RevPhase where
  /-- Move every head off the left-end marker. -/
  | skip
  /-- Copy the input onto the work tape, left to right. -/
  | copy
  /-- Walk the work head back, emitting each cell to the output. -/
  | emit
  /-- Halt. -/
  | done
  deriving DecidableEq

instance : Fintype RevPhase where
  elems := {.skip, .copy, .emit, .done}
  complete := fun x => by cases x <;> simp

/-- **The reversal transducer.** Copies the input onto its work tape, then
sweeps the work head back to the left-end marker, writing each cell it passes to
the output tape. Computes `List.reverse`. -/
def reverseTM : TM 1 where
  Q := RevPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.copy, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          Dir3.right, fun _ => Dir3.right, Dir3.right)
    | .copy =>
        match iHead with
        | Γ.zero =>
            (.copy, fun _ => Γw.zero, readBackWrite oHead,
              Dir3.right, fun _ => Dir3.right, idleDir oHead)
        | Γ.one =>
            (.copy, fun _ => Γw.one, readBackWrite oHead,
              Dir3.right, fun _ => Dir3.right, idleDir oHead)
        | _ =>
            (.emit, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => moveLeftDir (wHeads i), idleDir oHead)
    | .emit =>
        if wHeads 0 = Γ.zero then
          (.emit, fun i => readBackWrite (wHeads i), Γw.zero,
            idleDir iHead, fun i => moveLeftDir (wHeads i), Dir3.right)
        else if wHeads 0 = Γ.one then
          (.emit, fun i => readBackWrite (wHeads i), Γw.one,
            idleDir iHead, fun i => moveLeftDir (wHeads i), Dir3.right)
        else
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    | .copy =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            by first | exact fun _ _ => rfl | exact fun _ => moveLeftDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .emit =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => moveLeftDir_right_of_start,
            fun _ => rfl⟩
        · split
          · exact ⟨idleDir_right_of_start, fun _ => moveLeftDir_right_of_start,
              fun _ => rfl⟩
          · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
              idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- A content-preserving idle step on a tape whose head is off the left marker. -/
private theorem rev_idle_eq {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack t h, idleDir, if_neg h, Tape.move]

/-- The copy phase: from `copy` with the input cursor on `w` and the work tape
holding `acc`, the machine appends `w` to the work tape and enters `emit` with
the work head on the last copied cell. -/
private theorem reverseTM_copy_loop :
    ∀ (w acc : List Bool) (c : Cfg 1 reverseTM.Q),
      c.state = RevPhase.copy →
      c.input.HasBinarySuffix w →
      (c.work 0).HasBinaryPrefix acc →
      (c.work 0).cells 0 = Γ.start →
      c.output.HasBinaryPrefix [] →
      ∃ c', reverseTM.reachesIn (w.length + 1) c c' ∧
        c'.state = RevPhase.emit ∧
        (c'.work 0).HasBinaryContent (acc ++ w) ∧
        (c'.work 0).cells 0 = Γ.start ∧
        (c'.work 0).head = (acc ++ w).length ∧
        c'.input.read ≠ Γ.start ∧
        c'.output.HasBinaryPrefix [] := by
  intro w
  induction w with
  | nil =>
      intro acc c hstate hsuf hwork hw0 hout
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hout.read_blank]; decide
      have hwread : (c.work 0).read = Γ.blank := by
        rw [Tape.read, hwork.1]
        exact hwork.2.2 acc.length le_rfl
      have hwne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
      have hinp_eq : c.input.move (idleDir Γ.blank) = c.input := by
        rw [idleDir, if_neg (by decide), Tape.move]
      have hwmove : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (moveLeftDir ((c.work i).read))) = fun i => (c.work i).move Dir3.left := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        rw [moveLeftDir, if_neg hwne]
        exact writeAndMove_readBack _ hwne _
      refine ⟨{ state := RevPhase.emit
                input := c.input
                work := fun i => (c.work i).move Dir3.left
                output := c.output }, ?_, rfl, ?_, ?_, ?_, by rw [hread]; decide, by simpa⟩
      · refine .step ?_ .zero
        simp only [TM.step, hstate, reverseTM, hread, hinp_eq, reduceCtorEq, if_false]
        rw [hwmove, rev_idle_eq houtne]
      · have hc : (c.work 0).HasBinaryContent acc := hwork.2
        simpa using hc.move Dir3.left
      · show ((c.work 0).move Dir3.left).cells 0 = _
        rw [Tape.move_cells]; exact hw0
      · show ((c.work 0).move Dir3.left).head = _
        simp only [Tape.move, hwork.1, List.append_nil]
        omega
  | cons b w ih =>
      intro acc c hstate hsuf hwork hw0 hout
      have hread : c.input.read = Γ.ofBool b := hsuf.read_cons
      have houtne : c.output.read ≠ Γ.start := by rw [hout.read_blank]; decide
      set c1 : Cfg 1 reverseTM.Q :=
        { state := RevPhase.copy
          input := c.input.move Dir3.right
          work := fun i => (c.work i).writeAndMove (Γ.ofBool b) Dir3.right
          output := c.output } with hc1
      have hstep : reverseTM.step c = some c1 := by
        cases b <;>
          · simp only [TM.step, hstate, reverseTM, hread, Γ.ofBool, hc1,
              reduceCtorEq, if_false]
            rw [rev_idle_eq houtne]
            rfl
      obtain ⟨c', hreach, hst, hcont, hcz, hhd, hinp, hpre⟩ :=
        ih (acc ++ [b]) c1 rfl hsuf.move_right_cons
          (by rw [hc1]; exact Tape.hasBinaryPrefix_write_bit b hwork)
          (by
            show ((c.work 0).writeAndMove (Γ.ofBool b) Dir3.right).cells 0 = Γ.start
            exact Tape.write_move_cell0 _ _ hw0)
          (by rw [hc1]; exact hout)
      refine ⟨c', .step hstep hreach, hst, ?_, hcz, ?_, hinp, hpre⟩
      · simpa using hcont
      · simpa using hhd

/-- The emit phase: from `emit` with the work tape holding `bits` and its head on
cell `j`, the machine writes `bits.take j` backwards to the output and halts. -/
private theorem reverseTM_emit_loop :
    ∀ (j : ℕ) (bits acc : List Bool) (c : Cfg 1 reverseTM.Q),
      c.state = RevPhase.emit →
      (c.work 0).HasBinaryContent bits →
      (c.work 0).cells 0 = Γ.start →
      (c.work 0).head = j → j ≤ bits.length →
      c.input.read ≠ Γ.start →
      c.output.HasBinaryPrefix acc →
      ∃ c', reverseTM.reachesIn (j + 1) c c' ∧ reverseTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ (bits.take j).reverse) := by
  intro j
  induction j with
  | zero =>
      intro bits acc c hstate hcont hw0 hhead _ hinp hout
      have hwread : (c.work 0).read = Γ.start := by rw [Tape.read, hhead]; exact hw0
      have hwne0 : ¬ (c.work 0).read = Γ.zero := by rw [hwread]; decide
      have hwne1 : ¬ (c.work 0).read = Γ.one := by rw [hwread]; decide
      have houtne : c.output.read ≠ Γ.start := by rw [hout.read_blank]; decide
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, if_neg hinp, Tape.move]
      refine ⟨{ state := RevPhase.done
                input := c.input
                work := fun i => (c.work i).move Dir3.right
                output := c.output }, ?_, rfl, by simpa using hout⟩
      refine .step ?_ .zero
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = fun i => (c.work i).move Dir3.right := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        rw [Tape.writeAndMove, Tape.write, if_pos (by omega : (c.work 0).head = 0),
          idleDir, if_pos hwread]
      simp only [TM.step, hstate, reverseTM, hinp_eq, hwne0, hwne1, reduceCtorEq,
        if_false]
      rw [hwork, rev_idle_eq houtne]
  | succ j ih =>
      intro bits acc c hstate hcont hw0 hhead hjb hinp hout
      have hjlt : j < bits.length := by omega
      have hwread : (c.work 0).read = Γ.ofBool (bits[j]'hjlt) := by
        rw [Tape.read, hhead]; exact hcont.1 j hjlt
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [hwread]; exact Γ.ofBool_ne_start _
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, if_neg hinp, Tape.move]
      have hwmove : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (moveLeftDir ((c.work i).read))) = fun i => (c.work i).move Dir3.left := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        rw [moveLeftDir, if_neg hwne]
        exact writeAndMove_readBack _ hwne _
      set c1 : Cfg 1 reverseTM.Q :=
        { state := RevPhase.emit
          input := c.input
          work := fun i => (c.work i).move Dir3.left
          output := c.output.writeAndMove (Γ.ofBool (bits[j]'hjlt)) Dir3.right } with hc1
      have hstep : reverseTM.step c = some c1 := by
        rcases hb : bits[j]'hjlt with _ | _
        · have h0 : (c.work 0).read = Γ.zero := by rw [hwread, hb]; rfl
          simp only [TM.step, hstate, reverseTM, hinp_eq, h0, hc1, hb, Γ.ofBool,
            reduceCtorEq, if_false, reduceIte]
          rw [hwmove]
          rfl
        · have h1 : (c.work 0).read = Γ.one := by rw [hwread, hb]; rfl
          simp only [TM.step, hstate, reverseTM, hinp_eq, h1, hc1, hb, Γ.ofBool,
            reduceCtorEq, if_false, reduceIte]
          rw [hwmove]
          rfl
      obtain ⟨c', hreach, hhalt, hfin⟩ :=
        ih bits (acc ++ [bits[j]'hjlt]) c1 rfl
          (by rw [hc1]; exact hcont.move Dir3.left)
          (by rw [hc1]; show ((c.work 0).move Dir3.left).cells 0 = _
              rw [Tape.move_cells]; exact hw0)
          (by rw [hc1]; show ((c.work 0).move Dir3.left).head = _
              simp only [Tape.move, hhead]; omega)
          (by omega)
          (by rw [hc1]; exact hinp)
          (by rw [hc1]; exact Tape.hasBinaryPrefix_write_bit _ hout)
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      have hsplit : bits.take (j + 1) = bits.take j ++ [bits[j]'hjlt] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjlt]
        rfl
      have heq : acc ++ (bits.take (j + 1)).reverse
          = (acc ++ [bits[j]'hjlt]) ++ (bits.take j).reverse := by
        rw [hsplit]; simp
      rw [heq]
      exact hfin

/-- `reverseTM` computes `List.reverse` in `2 · |x| + 3` steps. -/
theorem reverseTM_computesInTime :
    reverseTM.ComputesInTime (fun x : List Bool => x.reverse) (fun n => 2 * n + 3) := by
  intro x
  set c1 : Cfg 1 reverseTM.Q :=
    { state := RevPhase.copy
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right } with hc1
  have hstep1 : reverseTM.step (reverseTM.initCfg x) = some c1 := by
    simp [TM.step, reverseTM, hc1, Tape.read, Tape.init, readBackWrite,
      Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨c2, hreach2, hst2, hcont2, hcz2, hhd2, hinp2, hout2⟩ :=
    reverseTM_copy_loop x [] c1 rfl
      (by rw [hc1]; exact Tape.init_move_right_hasBinarySuffix x)
      (by rw [hc1]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil)
      (by rw [hc1]; show ((Tape.init ([] : List Γ)).move Dir3.right).cells 0 = _
          rw [Tape.move_cells]; simp)
      (by rw [hc1]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil)
  obtain ⟨c', hreach', hhalt', hfin⟩ :=
    reverseTM_emit_loop x.length x [] c2 hst2 (by simpa using hcont2) hcz2
      (by simpa using hhd2) le_rfl hinp2 hout2
  refine ⟨c', ((x.length + 1) + (x.length + 1)) + 1, by simp; omega,
    .step hstep1 (reverseTM.reachesIn_trans hreach2 hreach'), hhalt', ?_⟩
  rw [List.nil_append, List.take_length] at hfin
  exact hfin.hasOutput

/-- Internal proof that string reversal is in `FP`. -/
theorem reverse_mem_FP :
    (fun x : List Bool => x.reverse) ∈ FP := by
  refine ⟨1, 1, reverseTM, (fun n => 2 * n + 3), reverseTM_computesInTime, ?_⟩
  have hn : (fun n : ℕ => 2 * n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa [pow_one] using (BigO.refl (fun n : ℕ => n)).const_mul_left 2
  exact BigO.add hn (BigO.const_le_pow 3 1)

end Complexity

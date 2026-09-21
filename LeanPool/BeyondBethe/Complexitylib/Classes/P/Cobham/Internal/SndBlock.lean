/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.BlockScan
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Counter
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# The block-suffix decoder — proof internals

`Cobham.sndBlockTM` scans the doubled payload two bits at a time until the
`[false, true]` separator, then copies the rest of the input to the output.
Malformed input halts with empty output, matching `unpair? = none`.

## Main results

- `Cobham.sndBlock_mem_FP` — the suffix decoder is in `FP`
-/


public section

namespace Complexity

namespace Cobham

open Complexity.TM

/-- The suffix decoder: scan doubled payload bits until the `[false, true]`
separator, then copy the remaining input (the suffix `y` of `pair x y`) to the
output. On malformed input it halts with empty output. Computes `sndBlock`. -/
def sndBlockTM : TM 0 where
  Q := ScanPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .scanA =>
        match iHead with
        | Γ.zero =>
            (.scanBfalse, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.one =>
            (.scanBtrue, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBfalse =>
        match iHead with
        | Γ.one =>
            (.emit, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.zero =>
            (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBtrue =>
        match iHead with
        | Γ.one =>
            (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .emit =>
        if iHead = Γ.blank then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.emit, fun i => readBackWrite (wHeads i), readBackWrite iHead,
            Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .scanA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanBfalse =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanBtrue =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .emit =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- The copy phase of `sndBlockTM`: from `emit` with input cursor on suffix `y`
and output holding `acc`, the machine copies `y` after `acc` and halts. -/
private theorem sndBlockTM_emit_loop :
    ∀ (y acc : List Bool) (c : Cfg 0 sndBlockTM.Q),
      c.state = ScanPhase.emit →
      c.input.HasBinarySuffix y →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ y.length + 1 ∧ sndBlockTM.reachesIn t c c' ∧ sndBlockTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ y) := by
  intro y
  induction y with
  | nil =>
      intro acc c hstate hsuf hpre
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hout : c.output.read = Γ.blank := hpre.read_blank
      have houtne : c.output.read ≠ Γ.start := by rw [hout]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, sndBlockTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from by
            rw [writeAndMove_readBack c.output houtne, idleDir, ite_eq_right houtne, Tape.move]]
      simpa using hpre
  | cons bit y ih =>
      intro acc c hstate hsuf hpre
      have hread : c.input.read = Γ.ofBool bit := hsuf.read_cons
      have hne : c.input.read ≠ Γ.blank := by rw [hread]; cases bit <;> decide
      let c1 : Cfg 0 sndBlockTM.Q :=
        { state := ScanPhase.emit
          input := c.input.move Dir3.right
          work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
      have hstep : sndBlockTM.step c = some c1 := by
        simp [TM.step, hstate, sndBlockTM, hne, c1]
      have hpre1 : c1.output.HasBinaryPrefix (acc ++ [bit]) := by
        have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool bit := by
          rw [hread]; cases bit <;> rfl
        show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ) Dir3.right).HasBinaryPrefix
          (acc ++ [bit])
        rw [hco]; exact Tape.hasBinaryPrefix_write_bit bit hpre
      obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
        ih (acc ++ [bit]) c1 rfl hsuf.move_right_cons hpre1
      refine ⟨c', t + 1, by simp; omega, .step hstep hreach, hhalt, ?_⟩
      rwa [List.append_assoc, List.cons_append, List.nil_append] at hout

/-- The scan phase of `sndBlockTM`: from `scanA` with input cursor on `w`, the
machine parses doubled pairs to the separator and copies the suffix, halting with
output `sndBlock w`. `fuel` bounds the recursion by the input length. -/
private theorem sndBlockTM_scan_loop :
    ∀ (fuel : ℕ) (w : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 sndBlockTM.Q),
      c.state = ScanPhase.scanA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix [] →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ sndBlockTM.reachesIn t c c' ∧ sndBlockTM.halted c' ∧
        c'.output.HasOutput (sndBlock w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hout : c.output.read = Γ.blank := hpre.read_blank
      have houtne : c.output.read ≠ Γ.start := by rw [hout]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, sndBlockTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from by
            rw [writeAndMove_readBack c.output houtne, idleDir, ite_eq_right houtne, Tape.move]]
      simpa [sndBlock] using hpre.hasOutput
  | succ fuel ih =>
      intro w hw c hstate hsuf hpre
      -- Halting helper for the malformed / end-of-input branches.
      have hout : c.output.read = Γ.blank := hpre.read_blank
      have houtne : c.output.read ≠ Γ.start := by rw [hout]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ScanPhase.done
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, sndBlockTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from by
                rw [writeAndMove_readBack c.output houtne, idleDir, ite_eq_right houtne, Tape.move]]
          simpa [sndBlock] using hpre.hasOutput
      | [false] =>
          -- scanA reads false → scanBfalse; next reads blank → done.
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have hout1 : c1.output.read = Γ.blank := hpre1.read_blank
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hout1]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, sndBlockTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from by
                rw [writeAndMove_readBack c1.output houtne1, idleDir, ite_eq_right houtne1, Tape.move]]
          simpa [sndBlock] using hpre1.hasOutput
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have hout1 : c1.output.read = Γ.blank := hpre1.read_blank
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hout1]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, sndBlockTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from by
                rw [writeAndMove_readBack c1.output houtne1, idleDir, ite_eq_right houtne1, Tape.move]]
          simpa [sndBlock] using hpre1.hasOutput
      | false :: true :: y =>
          -- separator: scanA false → scanBfalse → (reads true) → emit; copy y.
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.emit
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : sndBlockTM.step c1 = some c2 := by
            simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix y := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix [] := by
            have hout1 : c1.output.read ≠ Γ.start := by
              rw [hpre1.read_blank]; decide
            rw [show c2.output = c1.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ hout1]
            exact hpre1
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            sndBlockTM_emit_loop y [] c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have : sndBlock (false :: true :: y) = y := by simp [sndBlock, unpair?]
          rw [this]
          simpa using hcout.hasOutput
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : sndBlockTM.step c1 = some c2 := by
            simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix [] := by
            have hout1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
            rw [show c2.output = c1.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ hout1]
            exact hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have : sndBlock (false :: false :: z) = sndBlock z := by
            cases h : unpair? z <;> simp [sndBlock, unpair?, h]
          rw [this]; exact hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : sndBlockTM.step c1 = some c2 := by
            simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix [] := by
            have hout1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
            rw [show c2.output = c1.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ hout1]
            exact hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have : sndBlock (true :: true :: z) = sndBlock z := by
            cases h : unpair? z <;> simp [sndBlock, unpair?, h]
          rw [this]; exact hcout
      | true :: false :: rest =>
          -- malformed: scanA true → scanBtrue → reads false → done, empty output.
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have hout1 : c1.output.read = Γ.blank := hpre1.read_blank
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hout1]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from by
                rw [writeAndMove_readBack c1.output houtne1, idleDir, ite_eq_right houtne1, Tape.move]]
          have : sndBlock (true :: false :: rest) = [] := by simp [sndBlock, unpair?]
          rw [this]; simpa using hpre1.hasOutput

/-- `sndBlock` is polynomial-time, via the `sndBlockTM` scanner. -/
theorem sndBlock_mem_FP : sndBlock ∈ FP := by
  refine ⟨1, 0, sndBlockTM, (fun m => 2 * m + 3), ?_, ?_⟩
  · intro z
    -- Step 1: skip past ▷, positioning both cursors.
    let c1 : Cfg 0 sndBlockTM.Q :=
      { state := ScanPhase.scanA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : sndBlockTM.step (sndBlockTM.initCfg z) = some c1 := by
      simp [TM.step, sndBlockTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      sndBlockTM_scan_loop z.length z le_rfl c1 rfl hsuf hpre
    exact ⟨c', t + 1, by show t + 1 ≤ 2 * z.length + 3; omega,
      .step hstep1 hreach, hhalt, hcout⟩
  · have hn : (fun m : ℕ => 2 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 2
    exact BigO.add hn (BigO.const_le_pow 3 1)

end Cobham

end Complexity

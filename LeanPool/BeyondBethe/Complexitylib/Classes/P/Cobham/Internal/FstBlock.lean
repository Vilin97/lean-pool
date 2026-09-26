/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.BlockScan
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Counter
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# The block-payload decoder — proof internals

`Cobham.fstBlockTM` is the same scan as `Cobham.sndBlockTM`, emitting each
decoded payload bit as it goes and stopping at the separator. Malformed input
halts with empty output.

## Main results

- `Cobham.fstBlock_mem_FP` — the payload decoder is in `FP`
-/


@[expose] public section

namespace Complexity

namespace Cobham

open Complexity.TM

/-- The payload decoder: scan doubled payload bits, emitting each decoded bit to
the output, until the `[false, true]` separator or end of input. Computes
`fstBlock`. -/
def fstBlockTM : TM 0 where
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
        | Γ.zero =>
            (.scanA, fun i => readBackWrite (wHeads i), Γw.ofBool false,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBtrue =>
        match iHead with
        | Γ.one =>
            (.scanA, fun i => readBackWrite (wHeads i), Γw.ofBool true,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .emit => allIdle .done iHead wHeads oHead
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
    | .emit => exact rightOfStart_allIdle iHead wHeads oHead
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- An incomplete final payload bit stops the first-block scanner without emitting output. -/
private theorem fstBlockTM_scan_single
    (b : Bool) (acc : List Bool) (c : Cfg 0 fstBlockTM.Q)
    (hstate : c.state = ScanPhase.scanA)
    (hsuf : c.input.HasBinarySuffix [b])
    (hpre : c.output.HasBinaryPrefix acc) :
    ∃ c' t, t ≤ 2 * [b].length + 2 ∧ fstBlockTM.reachesIn t c c' ∧
      fstBlockTM.halted c' ∧ c'.output.HasBinaryPrefix (acc ++ fstBlock [b]) := by
  have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
  cases b with
  | false =>
      have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
      let c1 : Cfg 0 fstBlockTM.Q :=
        { state := ScanPhase.scanBfalse
          input := c.input.move Dir3.right
          work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) }
      have hstep : fstBlockTM.step c = some c1 := by
        simp [TM.step, hstate, fstBlockTM, hread, Γ.ofBool, c1]
      have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
      have hpre1 : c1.output.HasBinaryPrefix acc := by
        rw [show c1.output = c.output from
          Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
        exact hpre
      have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
      have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
      refine ⟨{ state := ScanPhase.done
                input := c1.input.move (idleDir c1.input.read)
                work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                  (idleDir (c1.work i).read)
                output := c1.output.writeAndMove (readBackWrite c1.output.read)
                  (idleDir c1.output.read) }, 2, by simp,
        .step hstep (.step (by simp [TM.step, fstBlockTM, hread1, c1]) .zero), rfl, ?_⟩
      rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
          = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
      simpa [fstBlock] using hpre1
  | true =>
      have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
      let c1 : Cfg 0 fstBlockTM.Q :=
        { state := ScanPhase.scanBtrue
          input := c.input.move Dir3.right
          work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) }
      have hstep : fstBlockTM.step c = some c1 := by
        simp [TM.step, hstate, fstBlockTM, hread, Γ.ofBool, c1]
      have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
      have hpre1 : c1.output.HasBinaryPrefix acc := by
        rw [show c1.output = c.output from
          Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
        exact hpre
      have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
      have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
      refine ⟨{ state := ScanPhase.done
                input := c1.input.move (idleDir c1.input.read)
                work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                  (idleDir (c1.work i).read)
                output := c1.output.writeAndMove (readBackWrite c1.output.read)
                  (idleDir c1.output.read) }, 2, by simp,
        .step hstep (.step (by simp [TM.step, fstBlockTM, hread1, c1]) .zero), rfl, ?_⟩
      rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
          = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
      simpa [fstBlock] using hpre1

/-- The scan of `fstBlockTM`: from `scanA` on input `w` with output holding `acc`,
the machine emits the decoded payload of `w`, halting with `acc ++ fstBlock w`. -/
private theorem fstBlockTM_scan_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 fstBlockTM.Q),
      c.state = ScanPhase.scanA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ fstBlockTM.reachesIn t c c' ∧ fstBlockTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ fstBlock w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, fstBlockTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
      simpa [fstBlock] using hpre
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ScanPhase.done
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, fstBlockTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
          simpa [fstBlock] using hpre
      | [false] => exact fstBlockTM_scan_single false acc c hstate hsuf hpre
      | [true] => exact fstBlockTM_scan_single true acc c hstate hsuf hpre
      | false :: true :: y =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [fstBlock] using hpre1
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [fstBlock] using hpre1
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool false) Dir3.right }
          have hstepB : fstBlockTM.step c1 = some c2 := by
            simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false]) := by
            show (c1.output.writeAndMove ((Γw.ofBool false).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit false hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [false]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hfb : fstBlock (false :: false :: z) = false :: fstBlock z := rfl
          rw [hfb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool true) Dir3.right }
          have hstepB : fstBlockTM.step c1 = some c2 := by
            simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [true]) := by
            show (c1.output.writeAndMove ((Γw.ofBool true).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit true hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [true]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hfb : fstBlock (true :: true :: z) = true :: fstBlock z := rfl
          rw [hfb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hcout

/-- `fstBlock` is polynomial-time, via the `fstBlockTM` scanner. -/
theorem fstBlock_mem_FP : fstBlock ∈ FP := by
  refine ⟨1, 0, fstBlockTM, (fun m => 2 * m + 3), ?_, ?_⟩
  · intro z
    let c1 : Cfg 0 fstBlockTM.Q :=
      { state := ScanPhase.scanA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : fstBlockTM.step (fstBlockTM.initCfg z) = some c1 := by
      simp [TM.step, fstBlockTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      fstBlockTM_scan_loop z.length z [] le_rfl c1 rfl hsuf hpre
    refine ⟨c', t + 1, by show t + 1 ≤ 2 * z.length + 3; omega,
      .step hstep1 hreach, hhalt, ?_⟩
    simpa using hcout.hasOutput
  · have hn : (fun m : ℕ => 2 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 2
    exact BigO.add hn (BigO.const_le_pow 3 1)

end Cobham

end Complexity

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Counter
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.SndBlock

/-!
# Concatenating two blocks — proof internals

`Cobham.catBlocks` appends the payloads of two consecutive blocks, the string
concatenation behind `Cobham.appendFn_mem_FP`, together with the `Cobham.catTM`
scanner that computes it.

## Main results

- `Cobham.catBlocks_mem_FP` — concatenation is in `FP`
-/


@[expose] public section

namespace Complexity

namespace Cobham

open Complexity.TM

/-! ### Concatenation

`catBlocks` is `fstBlock` and `sndBlock` fused: decode the leading block's
payload *and* keep the suffix, so on a genuine pair it is concatenation. Its
machine is `sndBlockTM` with the scan also emitting each decoded bit — the one
`FP` primitive that lets two computed strings be joined. -/

/-- Decode the leading self-delimiting block's payload and keep the suffix. On
`pair x y` this is `x ++ y` (`catBlocks_pair`); on malformed input it returns the
bits decoded so far. -/
def catBlocks : List Bool → List Bool
  | false :: false :: z => false :: catBlocks z
  | true :: true :: z => true :: catBlocks z
  | false :: true :: z => z
  | _ => []

@[simp] theorem catBlocks_pair (x y : List Bool) : catBlocks (pair x y) = x ++ y := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> (rw [pair_cons_eq]; simp [catBlocks, ih])

/-- The concatenator: like `sndBlockTM`, but the scan also emits each decoded
payload bit, so the output ends up holding the payload followed by the suffix.
Computes `catBlocks`. -/
def catTM : TM 0 where
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

/-- The copy phase of `catTM`: from `emit` with input cursor on suffix `y` and
output holding `acc`, the machine copies `y` after `acc` and halts. -/
private theorem catTM_emit_loop :
    ∀ (y acc : List Bool) (c : Cfg 0 catTM.Q),
      c.state = ScanPhase.emit →
      c.input.HasBinarySuffix y →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ y.length + 1 ∧ catTM.reachesIn t c c' ∧ catTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ y) := by
  intro y
  induction y with
  | nil =>
      intro acc c hstate hsuf hpre
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, catTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
      simpa using hpre
  | cons bit y ih =>
      intro acc c hstate hsuf hpre
      have hread : c.input.read = Γ.ofBool bit := hsuf.read_cons
      have hne : c.input.read ≠ Γ.blank := by rw [hread]; cases bit <;> decide
      let c1 : Cfg 0 catTM.Q :=
        { state := ScanPhase.emit
          input := c.input.move Dir3.right
          work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
      have hstep : catTM.step c = some c1 := by
        simp [TM.step, hstate, catTM, hne, c1]
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

/-- A one-step halt from a scan state whose input reads a symbol that ends the
block: the output is untouched. -/
private theorem catTM_halt_step {c : Cfg 0 catTM.Q} {acc : List Bool}
    (hstep : catTM.step c = some
      { state := ScanPhase.done
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) })
    (hpre : c.output.HasBinaryPrefix acc) :
    ∃ c' t, t ≤ 1 ∧ catTM.reachesIn t c c' ∧ catTM.halted c' ∧
      c'.output.HasBinaryPrefix acc := by
  have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
  refine ⟨_, 1, le_rfl, .step hstep .zero, rfl, ?_⟩
  rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
      = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
  exact hpre

/-- The scan phase of `catTM`: from `scanA` with input cursor on `w` and output
holding `acc`, the machine halts with output `acc ++ catBlocks w`. -/
private theorem catTM_scan_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 catTM.Q),
      c.state = ScanPhase.scanA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ catTM.reachesIn t c c' ∧ catTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ catBlocks w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
        catTM_halt_step (c := c) (acc := acc)
          (by simp [TM.step, hstate, catTM, hread]) hpre
      exact ⟨c', t, by omega, hreach, hhalt, by simpa [catBlocks] using hout⟩
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
            catTM_halt_step (c := c) (acc := acc)
              (by simp [TM.step, hstate, catTM, hread]) hpre
          exact ⟨c', t, by omega, hreach, hhalt, by simpa [catBlocks] using hout⟩
      | [b0] =>
          have hread : c.input.read = Γ.ofBool b0 := hsuf.read_cons
          let c1 : Cfg 0 catTM.Q :=
            { state := if b0 then ScanPhase.scanBtrue else ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : catTM.step c = some c1 := by
            cases b0 <;> simp [TM.step, hstate, catTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            show (c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read)).HasBinaryPrefix acc
            rw [Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
            catTM_halt_step (c := c1) (acc := acc)
              (by cases b0 <;> simp [TM.step, catTM, hread1, c1]) hpre1
          exact ⟨c', t + 1, by simp; omega, .step hstep hreach, hhalt,
            by cases b0 <;> simpa [catBlocks] using hout⟩
      | false :: true :: y =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 catTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : catTM.step c = some c1 := by
            simp [TM.step, hstate, catTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            show (c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read)).HasBinaryPrefix acc
            rw [Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          let c2 : Cfg 0 catTM.Q :=
            { state := ScanPhase.emit
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : catTM.step c1 = some c2 := by
            simp [TM.step, catTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix y := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix acc := by
            show (c1.output.writeAndMove (readBackWrite c1.output.read)
              (idleDir c1.output.read)).HasBinaryPrefix acc
            rw [Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]; exact hpre1
          obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := catTM_emit_loop y acc c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          simpa [catBlocks] using hout
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 catTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : catTM.step c = some c1 := by
            simp [TM.step, hstate, catTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            show (c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read)).HasBinaryPrefix acc
            rw [Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
            catTM_halt_step (c := c1) (acc := acc)
              (by simp [TM.step, catTM, hreadB, Γ.ofBool, c1]) hpre1
          exact ⟨c', t + 1, by simp only [List.length_cons]; omega,
            .step hstepA hreach, hhalt, by simpa [catBlocks] using hout⟩
      | false :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 catTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : catTM.step c = some c1 := by
            simp [TM.step, hstate, catTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            show (c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read)).HasBinaryPrefix acc
            rw [Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 catTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool false) Dir3.right }
          have hstepB : catTM.step c1 = some c2 := by
            simp [TM.step, catTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix rest := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false]) := by
            show (c1.output.writeAndMove ((Γw.ofBool false).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit false hpre1
          have hrfuel : rest.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
            ih rest (acc ++ [false]) hrfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hcb : catBlocks (false :: false :: rest) = false :: catBlocks rest := rfl
          rw [hcb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hout
      | true :: true :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 catTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : catTM.step c = some c1 := by
            simp [TM.step, hstate, catTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            show (c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read)).HasBinaryPrefix acc
            rw [Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 catTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool true) Dir3.right }
          have hstepB : catTM.step c1 = some c2 := by
            simp [TM.step, catTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix rest := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [true]) := by
            show (c1.output.writeAndMove ((Γw.ofBool true).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit true hpre1
          have hrfuel : rest.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
            ih rest (acc ++ [true]) hrfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hcb : catBlocks (true :: true :: rest) = true :: catBlocks rest := rfl
          rw [hcb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hout

/-- **Concatenation is polynomial-time.** -/
theorem catBlocks_mem_FP : catBlocks ∈ FP := by
  refine ⟨1, 0, catTM, (fun m => 2 * m + 3), ?_, ?_⟩
  · intro z
    let c1 : Cfg 0 catTM.Q :=
      { state := ScanPhase.scanA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : catTM.step (catTM.initCfg z) = some c1 := by
      simp [TM.step, catTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      catTM_scan_loop z.length z [] le_rfl c1 rfl hsuf hpre
    refine ⟨c', t + 1, by show t + 1 ≤ 2 * z.length + 3; omega,
      .step hstep1 hreach, hhalt, ?_⟩
    simpa using hcout.hasOutput
  · have hn : (fun m : ℕ => 2 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 2
    exact BigO.add hn (BigO.const_le_pow 3 1)

end Cobham

end Complexity

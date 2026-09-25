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
# Dropping the third component of a triple — proof internals

`Cobham.reorder` turns `pair A (pair B C)` into `pair A B`: copy the leading
block verbatim, then decode the next block's payload. It is the one machine the
`comp` constructor needs, via `Cobham.pairFn_mem_FP`.

## Main results

- `Cobham.reorder_mem_FP` — the triple reorder is in `FP`
-/


@[expose] public section

namespace Complexity

namespace Cobham

open Complexity.TM

/-- Drop the third component of a right-nested triple. Copy doubled payload bits
verbatim until the `[false, true]` separator, then decode the *next* block's
payload (`fstBlock`). On a valid triple this satisfies
`reorder (pair A (pair B C)) = pair A B` (`reorder_pair_pair`). The incremental
recursion (writing before knowing validity) is what the `reorderTM` scanner
computes; it is total and needs no sub-machines. -/
def reorder : List Bool → List Bool
  | false :: false :: z => false :: false :: reorder z
  | true :: true :: z => true :: true :: reorder z
  | false :: true :: z => false :: true :: fstBlock z
  | c :: _ => [c]
  | [] => []

theorem reorder_pair_pair (A B C : List Bool) :
    reorder (pair A (pair B C)) = pair A B := by
  induction A with
  | nil =>
      show false :: true :: fstBlock (pair B C) = false :: true :: B
      rw [fstBlock_pair]
  | cons a A ih =>
      rw [pair_cons_eq]
      cases a
      · show false :: false :: reorder (pair A (pair B C)) = pair (false :: A) B
        rw [ih, pair_cons_eq]
      · show true :: true :: reorder (pair A (pair B C)) = pair (true :: A) B
        rw [ih, pair_cons_eq]

/-- Control states of `reorderTM`: skip the marker; phase 1 (`rcopyA`/`rcopyBf`/
`rcopyBt`) copies doubled pairs verbatim until the separator; phase 2
(`rdecA`/`rdecBf`/`rdecBt`) decodes the next block's payload; then halt. -/
inductive ReorderPhase where
  | rskip | rcopyA | rcopyBf | rcopyBt | rdecA | rdecBf | rdecBt | rdone
  deriving DecidableEq

instance : Fintype ReorderPhase where
  elems := {.rskip, .rcopyA, .rcopyBf, .rcopyBt, .rdecA, .rdecBf, .rdecBt, .rdone}
  complete := fun x => by cases x <;> simp

/-- The reorder transducer computing `reorder`: copy the leading block verbatim
(phase 1) up to and including the `[false,true]` separator, then decode and emit
the payload of the following block (phase 2). -/
def reorderTM : TM 0 where
  Q := ReorderPhase
  qstart := .rskip
  qhalt := .rdone
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rskip =>
        (.rcopyA, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .rcopyA =>
        match iHead with
        | Γ.zero =>
            (.rcopyBf, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | Γ.one =>
            (.rcopyBt, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rcopyBf =>
        match iHead with
        | Γ.zero =>
            (.rcopyA, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | Γ.one =>
            (.rdecA, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rcopyBt =>
        match iHead with
        | Γ.one =>
            (.rcopyA, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdecA =>
        match iHead with
        | Γ.zero =>
            (.rdecBf, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.one =>
            (.rdecBt, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdecBf =>
        match iHead with
        | Γ.zero =>
            (.rdecA, fun i => readBackWrite (wHeads i), Γw.ofBool false,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdecBt =>
        match iHead with
        | Γ.one =>
            (.rdecA, fun i => readBackWrite (wHeads i), Γw.ofBool true,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdone => allIdle .rdone iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rskip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .rcopyA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rcopyBf =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rcopyBt =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdecA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdecBf =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdecBt =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdone => exact rightOfStart_allIdle iHead wHeads oHead

/-- Phase 2 of `reorderTM`: from `rdecA` on input `w` with output holding `acc`,
decode and emit `fstBlock w`, halting with `acc ++ fstBlock w`. Identical in shape
to `fstBlockTM_scan_loop`. -/
private theorem reorderTM_dec_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 reorderTM.Q),
      c.state = ReorderPhase.rdecA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ reorderTM.reachesIn t c c' ∧ reorderTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ fstBlock w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ReorderPhase.rdone
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
      simpa [fstBlock] using hpre
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ReorderPhase.rdone
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
          simpa [fstBlock] using hpre
      | [false] =>
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [fstBlock] using hpre1
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [fstBlock] using hpre1
      | false :: true :: y =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [fstBlock] using hpre1
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [fstBlock] using hpre1
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool false) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
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
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from
              Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
            exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool true) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
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

/-- Phase 1 of `reorderTM`: from `rcopyA` on input `w` with output holding `acc`,
copy `w`'s leading block verbatim and decode the following block, halting with
`acc ++ reorder w`. The separator case hands off to `reorderTM_dec_loop`. -/
private theorem reorderTM_copy_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 reorderTM.Q),
      c.state = ReorderPhase.rcopyA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 3 * w.length + 3 ∧ reorderTM.reachesIn t c c' ∧ reorderTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ reorder w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ReorderPhase.rdone
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
      simpa [reorder] using hpre
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      -- The `rcopyA` step emits the first bit `c1` verbatim.
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ReorderPhase.rdone
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne]
          simpa [reorder] using hpre
      | [false] =>
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [false]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool false := by rw [hread]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit false hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [reorder] using hpre1
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [true]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool true := by rw [hread]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit true hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          simpa [reorder] using hpre1
      | false :: true :: y =>
          -- separator: copy `false` then `true`, then decode `y`.
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [false]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool false := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit false hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.input.read) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix y := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false, true]) := by
            have hco : (readBackWrite c1.input.read).toΓ = Γ.ofBool true := by rw [hreadB]; rfl
            show (c1.output.writeAndMove ((readBackWrite c1.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false, true])
            rw [hco]
            have := Tape.hasBinaryPrefix_write_bit true hpre1
            rwa [List.append_assoc] at this
          have hyfuel : y.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            reorderTM_dec_loop fuel y (acc ++ [false, true]) hyfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hr : reorder (false :: true :: y) = false :: true :: fstBlock y := rfl
          rw [hr]
          rwa [List.append_assoc] at hcout
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [false]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool false := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit false hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.input.read) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false, false]) := by
            have hco : (readBackWrite c1.input.read).toΓ = Γ.ofBool false := by rw [hreadB]; rfl
            show (c1.output.writeAndMove ((readBackWrite c1.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false, false])
            rw [hco]
            have := Tape.hasBinaryPrefix_write_bit false hpre1
            rwa [List.append_assoc] at this
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [false, false]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hr : reorder (false :: false :: z) = false :: false :: reorder z := rfl
          rw [hr]
          rwa [List.append_assoc] at hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [true]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool true := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit true hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.input.read) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [true, true]) := by
            have hco : (readBackWrite c1.input.read).toΓ = Γ.ofBool true := by rw [hreadB]; rfl
            show (c1.output.writeAndMove ((readBackWrite c1.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true, true])
            rw [hco]
            have := Tape.hasBinaryPrefix_write_bit true hpre1
            rwa [List.append_assoc] at this
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [true, true]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hr : reorder (true :: true :: z) = true :: true :: reorder z := rfl
          rw [hr]
          rwa [List.append_assoc] at hcout
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [true]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool true := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit true hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from Tape.writeAndMove_readBack_idle_of_ne_start _ houtne1]
          have hr : reorder (true :: false :: rest) = [true] := rfl
          rw [hr]
          exact hpre1

/-- `reorder` is polynomial-time, via the `reorderTM` scanner. -/
theorem reorder_mem_FP : reorder ∈ FP := by
  refine ⟨1, 0, reorderTM, (fun m => 3 * m + 4), ?_, ?_⟩
  · intro z
    let c1 : Cfg 0 reorderTM.Q :=
      { state := ReorderPhase.rcopyA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : reorderTM.step (reorderTM.initCfg z) = some c1 := by
      simp [TM.step, reorderTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      reorderTM_copy_loop z.length z [] le_rfl c1 rfl hsuf hpre
    refine ⟨c', t + 1, by show t + 1 ≤ 3 * z.length + 4; omega,
      .step hstep1 hreach, hhalt, ?_⟩
    simpa using hcout.hasOutput
  · have hn : (fun m : ℕ => 3 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 3
    exact BigO.add hn (BigO.const_le_pow 4 1)

end Cobham

end Complexity

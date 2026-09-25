/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Truncating to the length of a leading block — proof internals

`takeLen (pair c y) = y.take |c|`: the leading self-delimiting block acts as a
*ruler* and the verbatim suffix is truncated to its length. Carrying a width
bound as a string rather than as a number is what keeps an iterated `FP` step
function polynomial-time — each iteration truncates its state to the ruler, so no
intermediate value can grow beyond it.

The transducer `takeLenTM` has one work tape: *scan* parses the leading block two
symbols at a time, writing one unary mark per payload bit; *rewind* returns the
work head to cell one; *copy* emits one input symbol per remaining mark.
Malformed input halts with empty output, matching `unpair? = none`.

## Main results

- `Complexity.takeLen_pair` — the defining equation on genuine pairs
- `Complexity.takeLen_mem_FP` — the truncation is in `FP`
-/


@[expose] public section

namespace Complexity

open Complexity.TM

/-! ## The function computed by the scanner -/

/-- The remaining output of the truncation scanner when `k` payload bits of the
leading block have already been counted and `w` is the unread part of the input:
the suffix truncated to the total ruler length, and nothing at all when the block
framing is broken. -/
def takeLenAux (k : ℕ) (w : List Bool) : List Bool :=
  match unpair? w with
  | some (x, y) => y.take (k + x.length)
  | none => []

/-- Truncate the verbatim suffix of a pair to the length of its leading block. -/
def takeLen (p : List Bool) : List Bool := takeLenAux 0 p

@[simp] theorem takeLenAux_nil (k : ℕ) : takeLenAux k [] = [] := rfl

@[simp] theorem takeLenAux_singleton (k : ℕ) (b : Bool) : takeLenAux k [b] = [] := by
  cases b <;> rfl

/-- Reaching the separator ends the ruler: the suffix is truncated to `k`. -/
@[simp] theorem takeLenAux_sep (k : ℕ) (z : List Bool) :
    takeLenAux k (false :: true :: z) = z.take k := by
  simp [takeLenAux, unpair?]

/-- A doubled payload bit lengthens the ruler by one. -/
theorem takeLenAux_double (k : ℕ) (b : Bool) (z : List Bool) :
    takeLenAux k (b :: b :: z) = takeLenAux (k + 1) z := by
  cases b <;>
    · simp only [takeLenAux, unpair?]
      cases h : unpair? z with
      | none => simp
      | some xy =>
          obtain ⟨x, y⟩ := xy
          simp only [Option.map_some, List.length_cons]
          rw [show k + (x.length + 1) = k + 1 + x.length from by omega]

/-- A broken doubling halts the scan with no output. -/
@[simp] theorem takeLenAux_broken (k : ℕ) (z : List Bool) :
    takeLenAux k (true :: false :: z) = [] := rfl

/-- On a genuine pair the leading block is the ruler. -/
theorem takeLen_pair (c y : List Bool) : takeLen (pair c y) = y.take c.length := by
  simp [takeLen, takeLenAux]

section TakeLenMachine

/-- Control states of `takeLenTM`. -/
inductive TakePhase where
  /-- Move every head off the left-end marker. -/
  | skip
  /-- Read the first symbol of a doubled payload bit. -/
  | scanA
  /-- The first symbol of the pair was `0`. -/
  | scanB0
  /-- The first symbol of the pair was `1`. -/
  | scanB1
  /-- Rewind the work head to cell one. -/
  | rew
  /-- Emit one input symbol per remaining mark. -/
  | copy
  /-- Halt. -/
  | done
  deriving DecidableEq

instance : Fintype TakePhase where
  elems := {.skip, .scanA, .scanB0, .scanB1, .rew, .copy, .done}
  complete := fun x => by cases x <;> simp

/-- **The truncation scanner.** Parses the leading self-delimiting block into
`|c|` unary marks on its work tape, then copies that many input symbols to the
output. Computes `takeLen`. -/
def takeLenTM : TM 1 where
  Q := TakePhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          Dir3.right, fun _ => Dir3.right, Dir3.right)
    | .scanA =>
        match iHead with
        | Γ.zero =>
            (.scanB0, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.one =>
            (.scanB1, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanB0 =>
        match iHead with
        | Γ.zero =>
            (.scanA, fun _ => Γw.one, readBackWrite oHead,
              Dir3.right, fun _ => Dir3.right, idleDir oHead)
        | Γ.one =>
            (.rew, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanB1 =>
        match iHead with
        | Γ.one =>
            (.scanA, fun _ => Γw.one, readBackWrite oHead,
              Dir3.right, fun _ => Dir3.right, idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rew =>
        if wHeads 0 = Γ.start then
          (.copy, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun _ => Dir3.right, idleDir oHead)
        else
          (.rew, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => moveLeftDir (wHeads i), idleDir oHead)
    | .copy =>
        if wHeads 0 = Γ.one then
          match iHead with
          | Γ.zero =>
              (.copy, fun i => readBackWrite (wHeads i), Γw.zero,
                Dir3.right, fun _ => Dir3.right, Dir3.right)
          | Γ.one =>
              (.copy, fun i => readBackWrite (wHeads i), Γw.one,
                Dir3.right, fun _ => Dir3.right, Dir3.right)
          | _ =>
              (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
                idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    | .scanA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanB0 =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            by first | exact fun _ _ => rfl | exact fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanB1 =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            by first | exact fun _ _ => rfl | exact fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rew =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ _ => rfl, idleDir_right_of_start⟩
        · exact ⟨idleDir_right_of_start, fun _ => moveLeftDir_right_of_start,
            idleDir_right_of_start⟩
    | .copy =>
        dsimp only []
        split
        · cases iHead <;>
            exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
              by first | exact fun _ _ => rfl | exact fun _ => idleDir_right_of_start,
              by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-! ## Correctness of the scanner -/

/-- A content-preserving idle step on a tape whose head is off the left marker. -/
private theorem take_idle_eq {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack t h, idleDir, ite_eq_right h, Tape.move]

/-- The copy phase: with `r` marks left under and to the right of the work head,
the machine emits the first `r` symbols of the remaining input. -/
private theorem takeLenTM_copy_loop :
    ∀ (r h m : ℕ), h + r = m + 1 → 1 ≤ h →
      ∀ (y acc : List Bool) (c : Cfg 1 takeLenTM.Q),
      c.state = TakePhase.copy →
      (c.work 0).cells = regCells m →
      (c.work 0).head = h →
      c.input.HasBinarySuffix y →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ r + 1 ∧ takeLenTM.reachesIn t c c' ∧ takeLenTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ y.take r) := by
  intro r
  induction r with
  | zero =>
      intro h m hsum hh y acc c hstate hcells hhead hsuf hpre
      have hwread : (c.work 0).read = Γ.blank := by
        rw [Tape.read, hcells, hhead]; exact regCells_blank (by omega)
      have hwne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
      have hwne1 : ¬ (c.work 0).read = Γ.one := by rw [hwread]; decide
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hsuf.read_ne_start, Tape.move]
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact take_idle_eq hwne
      refine ⟨{ state := TakePhase.done
                input := c.input
                work := c.work
                output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
      refine .step ?_ .zero
      simp only [TM.step, hstate, takeLenTM, hwne1, hinp_eq, reduceCtorEq, ite_false]
      rw [hwork, take_idle_eq houtne]
  | succ r ih =>
      intro h m hsum hh y acc c hstate hcells hhead hsuf hpre
      have hwread : (c.work 0).read = Γ.one := by
        rw [Tape.read, hcells, hhead]; exact regCells_one (by omega) (by omega)
      have hwne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hsuf.read_ne_start, Tape.move]
      have hworkIdle : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact take_idle_eq hwne
      have hworkR : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          Dir3.right) = fun i => (c.work i).move Dir3.right := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact writeAndMove_readBack _ hwne _
      have hidleB : ∀ t : Tape, t.move (idleDir Γ.blank) = t := by
        intro t; rw [idleDir, ite_eq_right (by decide)]; rfl
      match y with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := TakePhase.done
                    input := c.input
                    work := c.work
                    output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
          refine .step ?_ .zero
          simp only [TM.step, hstate, takeLenTM, hwread, hread, hidleB, reduceCtorEq,
            ite_false, reduceIte]
          rw [hworkIdle, take_idle_eq houtne]
      | b :: y =>
          have hread : c.input.read = Γ.ofBool b := hsuf.read_cons
          set c1 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.copy
              input := c.input.move Dir3.right
              work := fun i => (c.work i).move Dir3.right
              output := c.output.writeAndMove (Γ.ofBool b) Dir3.right } with hc1
          have hstep : takeLenTM.step c = some c1 := by
            cases b <;>
              · simp only [TM.step, hstate, takeLenTM, hwread, hread, hc1, Γ.ofBool,
                  reduceCtorEq, ite_false, reduceIte]
                rw [hworkR]
                rfl
          obtain ⟨c', t, ht, hreach, hhalt, hfin⟩ :=
            ih (h + 1) m (by omega) (by omega) y (acc ++ [b]) c1 rfl
              (by rw [hc1]; simpa using! hcells)
              (by rw [hc1]; simp [Tape.move, hhead])
              (by rw [hc1]; exact hsuf.move_right_cons)
              (by rw [hc1]; exact Tape.hasBinaryPrefix_write_bit b hpre)
          refine ⟨c', t + 1, by omega, .step hstep hreach, hhalt, ?_⟩
          simpa using hfin

/-- The rewind phase: walk the work head back to the left-end marker and enter
`copy` with the work head at cell one. -/
private theorem takeLenTM_rew_loop :
    ∀ (h m : ℕ) (c : Cfg 1 takeLenTM.Q),
      c.state = TakePhase.rew →
      (c.work 0).cells = regCells m →
      (c.work 0).head = h →
      c.input.read ≠ Γ.start →
      c.output.read ≠ Γ.start →
      ∃ c', takeLenTM.reachesIn (h + 1) c c' ∧
        c'.state = TakePhase.copy ∧
        (c'.work 0).cells = regCells m ∧
        (c'.work 0).head = 1 ∧
        c'.input = c.input ∧
        c'.output = c.output := by
  intro h
  induction h with
  | zero =>
      intro m c hstate hcells hhead hinp hout
      have hwread : (c.work 0).read = Γ.start := by
        rw [Tape.read, hcells, hhead]; rfl
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hinp, Tape.move]
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          Dir3.right) = fun i => (c.work i).move Dir3.right := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        show ((c.work 0).write _).move Dir3.right = (c.work 0).move Dir3.right
        rw [Tape.write, ite_eq_left hhead]
      refine ⟨{ state := TakePhase.copy
                input := c.input
                work := fun i => (c.work i).move Dir3.right
                output := c.output }, ?_, rfl, by simp [Tape.move_cells, hcells],
        by simp [Tape.move, hhead], rfl, rfl⟩
      refine .step ?_ .zero
      simp only [TM.step, hstate, takeLenTM, hwread, hinp_eq, reduceIte, reduceCtorEq,
        ite_false]
      rw [hwork, take_idle_eq hout]
  | succ h ih =>
      intro m c hstate hcells hhead hinp hout
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [Tape.read, hcells, hhead]; exact regCells_ne_start (by omega)
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hinp, Tape.move]
      set c1 : Cfg 1 takeLenTM.Q :=
        { state := TakePhase.rew
          input := c.input
          work := fun i => (c.work i).move Dir3.left
          output := c.output } with hc1
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (moveLeftDir ((c.work i).read))) = fun i => (c.work i).move Dir3.left := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        rw [moveLeftDir, ite_eq_right hwne]
        exact writeAndMove_readBack _ hwne _
      have hstep : takeLenTM.step c = some c1 := by
        simp only [TM.step, hstate, takeLenTM, hinp_eq, hc1, ite_eq_right hwne, reduceCtorEq,
          ite_false]
        rw [hwork, take_idle_eq hout]
      obtain ⟨c', hreach, hst, hcl, hhd, hin, hou⟩ :=
        ih m c1 rfl (by rw [hc1]; simpa [Tape.move_cells] using hcells)
          (by rw [hc1]; simp [Tape.move, hhead])
          (by rw [hc1]; simpa using hinp) (by rw [hc1]; simpa using hout)
      exact ⟨c', .step hstep hreach, hst, hcl, hhd, by rw [hin, hc1], by rw [hou, hc1]⟩

/-- The scan phase: from `scanA` with `k` ruler bits already counted and `w`
unread, the machine runs to a halt with `takeLenAux k w` on the output tape. -/
private theorem takeLenTM_scan_loop :
    ∀ (N : ℕ) (w : List Bool) (k : ℕ), k + w.length ≤ N →
      ∀ (c : Cfg 1 takeLenTM.Q),
      c.state = TakePhase.scanA →
      (c.work 0).cells = regCells k →
      (c.work 0).head = k + 1 →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix [] →
      ∃ c' t, t ≤ 3 * N + 5 ∧ takeLenTM.reachesIn t c c' ∧
        takeLenTM.halted c' ∧
        c'.output.HasBinaryPrefix (takeLenAux k w) := by
  intro N
  induction N with
  | zero =>
      intro w k hN c hstate hcells hhead hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (by omega)
      subst hwnil
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [Tape.read, hcells, hhead]; exact regCells_ne_start (by omega)
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact take_idle_eq hwne
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hidleB : ∀ t : Tape, t.move (idleDir Γ.blank) = t := by
        intro t; rw [idleDir, ite_eq_right (by decide)]; rfl
      refine ⟨{ state := TakePhase.done
                input := c.input
                work := c.work
                output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
      refine .step ?_ .zero
      simp only [TM.step, hstate, takeLenTM, hread, hidleB, reduceCtorEq, ite_false]
      rw [hwork, take_idle_eq houtne]
  | succ N ih =>
      intro w k hN c hstate hcells hhead hsuf hpre
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [Tape.read, hcells, hhead]; exact regCells_ne_start (by omega)
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact take_idle_eq hwne
      have hidleB : ∀ t : Tape, t.move (idleDir Γ.blank) = t := by
        intro t; rw [idleDir, ite_eq_right (by decide)]; rfl
      have hidleZ : ∀ t : Tape, t.move (idleDir Γ.zero) = t := by
        intro t; rw [idleDir, ite_eq_right (by decide)]; rfl
      have hstepA : ∀ b : Bool,
          c.input.read = Γ.ofBool b →
          takeLenTM.step c = some
            { state := (bif b then TakePhase.scanB1 else TakePhase.scanB0)
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } := by
        intro b hread
        cases b <;>
          · simp only [TM.step, hstate, takeLenTM, hread, Γ.ofBool, reduceCtorEq, ite_false,
              Bool.cond_true, Bool.cond_false]
            rw [hwork, take_idle_eq houtne]
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := TakePhase.done
                    input := c.input
                    work := c.work
                    output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
          refine .step ?_ .zero
          simp only [TM.step, hstate, takeLenTM, hread, hidleB, reduceCtorEq, ite_false]
          rw [hwork, take_idle_eq houtne]
      | [b] =>
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix [] := hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.blank := hsuf1.read_nil
          refine ⟨{ state := TakePhase.done
                    input := c.input.move Dir3.right
                    work := c.work
                    output := c.output }, 2, by omega, ?_, rfl, by
                      simpa [takeLenAux_singleton] using hpre⟩
          refine .step (hstepA b hsuf.read_cons) (.step ?_ .zero)
          cases b <;>
            · simp only [TM.step, takeLenTM, hread1, hidleB, reduceCtorEq, ite_false,
                Bool.cond_true, Bool.cond_false]
              rw [hwork, take_idle_eq houtne]
      | true :: false :: z =>
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (false :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.zero := hsuf1.read_cons
          refine ⟨{ state := TakePhase.done
                    input := c.input.move Dir3.right
                    work := c.work
                    output := c.output }, 2, by omega, ?_, rfl, by
                      simpa [takeLenAux_broken] using hpre⟩
          refine .step (hstepA true hsuf.read_cons) (.step ?_ .zero)
          simp only [TM.step, takeLenTM, hread1, hidleZ, reduceCtorEq, ite_false, Bool.cond_true]
          rw [hwork, take_idle_eq houtne]
      | false :: true :: z =>
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (true :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.one := hsuf1.read_cons
          set c1 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.scanB0
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } with hc1
          have hstep1 : takeLenTM.step c = some c1 := hstepA false hsuf.read_cons
          set c2 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.rew
              input := (c.input.move Dir3.right).move Dir3.right
              work := c.work
              output := c.output } with hc2
          have hstep2 : takeLenTM.step c1 = some c2 := by
            simp only [TM.step, hc1, hc2, takeLenTM, hread1, reduceCtorEq, ite_false]
            rw [hwork, take_idle_eq houtne]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          obtain ⟨c3, hreach3, hst3, hcl3, hhd3, hin3, hou3⟩ :=
            takeLenTM_rew_loop (k + 1) k c2 rfl (by rw [hc2]; exact hcells)
              (by rw [hc2]; exact hhead) hsuf2.read_ne_start (by rw [hc2]; exact houtne)
          obtain ⟨c', t, ht, hreach', hhalt', hout'⟩ :=
            takeLenTM_copy_loop k 1 k (by omega) (by omega) z [] c3 hst3 hcl3 hhd3
              (by rw [hin3]; exact hsuf2) (by rw [hou3]; exact hpre)
          refine ⟨c', (k + 1 + 1 + t) + 1 + 1, ?_, ?_, hhalt', ?_⟩
          · simp only [List.length_cons] at hN
            omega
          · exact .step hstep1 (.step hstep2 (takeLenTM.reachesIn_trans hreach3 hreach'))
          · rw [takeLenAux_sep]
            simpa using hout'
      | false :: false :: z =>
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (false :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.zero := hsuf1.read_cons
          set c1 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.scanB0
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } with hc1
          have hstep1 : takeLenTM.step c = some c1 := hstepA false hsuf.read_cons
          set c2 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.scanA
              input := (c.input.move Dir3.right).move Dir3.right
              work := fun i => ((c.work i).write Γ.one).move Dir3.right
              output := c.output } with hc2
          have hwmark : (fun i => (c.work i).writeAndMove (Γw.one).toΓ Dir3.right)
              = fun i => ((c.work i).write Γ.one).move Dir3.right := rfl
          have hstep2 : takeLenTM.step c1 = some c2 := by
            simp only [TM.step, hc1, hc2, takeLenTM, hread1, reduceCtorEq, ite_false]
            rw [hwmark, take_idle_eq houtne]
          have hcells2 : (c2.work 0).cells = regCells (k + 1) := by
            rw [hc2]
            show (((c.work 0).write Γ.one).move Dir3.right).cells = _
            rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhead]; omega)]
            show Function.update (c.work 0).cells ((c.work 0).head) Γ.one = _
            rw [hcells, hhead, regCells_update_succ]
          have hhead2 : (c2.work 0).head = k + 1 + 1 := by
            rw [hc2]
            show (((c.work 0).write Γ.one).move Dir3.right).head = _
            rw [Tape.move, Tape.write_head, hhead]
          obtain ⟨c', t, ht, hreach', hhalt', hout'⟩ :=
            ih z (k + 1) (by simp only [List.length_cons] at hN; omega) c2 rfl hcells2
              hhead2 (by rw [hc2]; exact hsuf1.move_right_cons) (by rw [hc2]; exact hpre)
          refine ⟨c', t + 1 + 1, by omega, .step hstep1 (.step hstep2 hreach'), hhalt', ?_⟩
          rwa [takeLenAux_double]
      | true :: true :: z =>
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (true :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.one := hsuf1.read_cons
          set c1 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.scanB1
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } with hc1
          have hstep1 : takeLenTM.step c = some c1 := hstepA true hsuf.read_cons
          set c2 : Cfg 1 takeLenTM.Q :=
            { state := TakePhase.scanA
              input := (c.input.move Dir3.right).move Dir3.right
              work := fun i => ((c.work i).write Γ.one).move Dir3.right
              output := c.output } with hc2
          have hwmark : (fun i => (c.work i).writeAndMove (Γw.one).toΓ Dir3.right)
              = fun i => ((c.work i).write Γ.one).move Dir3.right := rfl
          have hstep2 : takeLenTM.step c1 = some c2 := by
            simp only [TM.step, hc1, hc2, takeLenTM, hread1, reduceCtorEq, ite_false]
            rw [hwmark, take_idle_eq houtne]
          have hcells2 : (c2.work 0).cells = regCells (k + 1) := by
            rw [hc2]
            show (((c.work 0).write Γ.one).move Dir3.right).cells = _
            rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhead]; omega)]
            show Function.update (c.work 0).cells ((c.work 0).head) Γ.one = _
            rw [hcells, hhead, regCells_update_succ]
          have hhead2 : (c2.work 0).head = k + 1 + 1 := by
            rw [hc2]
            show (((c.work 0).write Γ.one).move Dir3.right).head = _
            rw [Tape.move, Tape.write_head, hhead]
          obtain ⟨c', t, ht, hreach', hhalt', hout'⟩ :=
            ih z (k + 1) (by simp only [List.length_cons] at hN; omega) c2 rfl hcells2
              hhead2 (by rw [hc2]; exact hsuf1.move_right_cons) (by rw [hc2]; exact hpre)
          refine ⟨c', t + 1 + 1, by omega, .step hstep1 (.step hstep2 hreach'), hhalt', ?_⟩
          rwa [takeLenAux_double]

/-- The blank work tape of the initial configuration is the zero register. -/
private theorem take_init_nil_cells :
    (Tape.init ([] : List Γ)).cells = regCells 0 := by
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Tape.init_cells_ge _ _ (by simp), regCells_blank (by omega)]

/-- `takeLenTM` computes `takeLen` in `3 · |p| + 6` steps. -/
theorem takeLenTM_computesInTime :
    takeLenTM.ComputesInTime takeLen (fun n => 3 * n + 6) := by
  intro p
  set c1 : Cfg 1 takeLenTM.Q :=
    { state := TakePhase.scanA
      input := (Tape.init (p.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right } with hc1
  have hstep1 : takeLenTM.step (takeLenTM.initCfg p) = some c1 := by
    simp [TM.step, takeLenTM, hc1, Tape.read, Tape.init, readBackWrite,
      Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
    takeLenTM_scan_loop p.length p 0 (by omega) c1 rfl
      (by rw [hc1]; show ((Tape.init []).move Dir3.right).cells = _
          rw [Tape.move_cells, take_init_nil_cells])
      (by rw [hc1]; show ((Tape.init []).move Dir3.right).head = _
          simp [Tape.move])
      (by rw [hc1]; exact Tape.init_move_right_hasBinarySuffix p)
      (by rw [hc1]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil)
  exact ⟨c', t + 1, by simp; omega, .step hstep1 hreach, hhalt, hout.hasOutput⟩

end TakeLenMachine

/-- Internal proof that ruler-truncation is in `FP`. -/
theorem takeLen_mem_FP : takeLen ∈ FP := by
  refine ⟨1, 1, takeLenTM, (fun n => 3 * n + 6), takeLenTM_computesInTime, ?_⟩
  have hn : (fun n : ℕ => 3 * n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa [pow_one] using (BigO.refl (fun n : ℕ => n)).const_mul_left 3
  exact BigO.add hn (BigO.const_le_pow 6 1)

end Complexity

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
# Multiplying the block lengths of a pair — proof internals

This module builds the one quadratic-output transducer needed by Cobham's
soundness direction: from `pair A B` it emits `|A| · |B|` copies of `false`,
which is exactly the length behaviour of `Complexity.smash`. The soundness proof
then applies `unaryLength_mem_FP` to turn this internal zero-filled ruler into
Cobham's all-one smash word.

The machine `mulLenTM` is self-contained (one work tape, eight control states):

1. *scan* — parse the leading self-delimiting block two symbols at a time,
   writing one unary mark on the work tape per payload bit, so the work tape
   ends up holding `|A|` in unary;
2. *outer loop* — for every remaining input symbol (i.e. `|B|` times) run the
   *emit* pass, which walks the `|A|` marks writing one `false` per mark, and
   the *rewind* pass, which returns the work head to cell one.

Malformed input halts with empty output, matching `unpair? = none`.

## Main results

- `Complexity.Cobham.mulUnpair_mem_FP` — the block-length product is `FP`
-/


@[expose] public section

namespace Complexity

namespace Cobham

open Complexity.TM

/-! ## The function computed by the scanner -/

/-- The remaining output of the length-multiplication scanner when `k` payload
bits of the leading block have already been counted and `w` is the unread part
of the input: `|A| · |B|` copies of `false` for a well-formed remainder, and
nothing at all when the block framing is broken. -/
def mulAux (k : ℕ) (w : List Bool) : List Bool :=
  match unpair? w with
  | some (x, y) => List.replicate ((k + x.length) * y.length) false
  | none => []

/-- Emit `|A| · |B|` copies of `false` from a pair `pair A B`; the empty string
on input that is not a valid pair encoding. -/
def mulUnpair (p : List Bool) : List Bool := mulAux 0 p

@[simp] theorem mulAux_nil (k : ℕ) : mulAux k [] = [] := rfl

@[simp] theorem mulAux_singleton (k : ℕ) (b : Bool) : mulAux k [b] = [] := by
  cases b <;> rfl

/-- Reaching the separator ends the block: only the suffix remains. -/
@[simp] theorem mulAux_sep (k : ℕ) (z : List Bool) :
    mulAux k (false :: true :: z) = List.replicate (k * z.length) false := by
  simp [mulAux, unpair?]

/-- A doubled payload bit increments the counted length. -/
theorem mulAux_double (k : ℕ) (b : Bool) (z : List Bool) :
    mulAux k (b :: b :: z) = mulAux (k + 1) z := by
  cases b <;>
    · simp only [mulAux, unpair?]
      cases h : unpair? z with
      | none => simp
      | some xy =>
          obtain ⟨x, y⟩ := xy
          simp only [Option.map_some, List.length_cons]
          congr 2
          omega

/-- A broken doubling halts the scan with no output. -/
@[simp] theorem mulAux_broken (k : ℕ) (z : List Bool) :
    mulAux k (true :: false :: z) = [] := rfl

/-- On a genuine pair the scanner emits `|A| · |B|` copies of `false`. -/
theorem mulUnpair_pair (A B : List Bool) :
    mulUnpair (pair A B) = List.replicate (A.length * B.length) false := by
  simp [mulUnpair, mulAux]

/-! ## The scanner -/

section MulLenMachine

/-- Control states of `mulLenTM`. -/
inductive MulPhase where
  /-- Move every head off the left-end marker. -/
  | skip
  /-- Read the first symbol of a doubled payload bit. -/
  | scanA
  /-- The first symbol of the pair was `0`. -/
  | scanB0
  /-- The first symbol of the pair was `1`. -/
  | scanB1
  /-- Consume one symbol of the suffix, or halt at its end. -/
  | outer
  /-- Walk the unary marks, emitting one `false` per mark. -/
  | emit
  /-- Rewind the work head to cell one. -/
  | rew
  /-- Halt. -/
  | done
  deriving DecidableEq

instance : Fintype MulPhase where
  elems := {.skip, .scanA, .scanB0, .scanB1, .outer, .emit, .rew, .done}
  complete := fun x => by cases x <;> simp

/-- **The length-multiplication scanner.** Parses the leading self-delimiting
block into `|A|` unary marks on its work tape, then emits `|A|` zeros for each
of the `|B|` remaining input symbols. Computes `mulUnpair`. -/
def mulLenTM : TM 1 where
  Q := MulPhase
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
    | .outer =>
        if iHead = Γ.blank then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.emit, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .emit =>
        if wHeads 0 = Γ.one then
          (.emit, fun i => readBackWrite (wHeads i), Γw.zero,
            idleDir iHead, fun _ => Dir3.right, Dir3.right)
        else
          (.rew, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rew =>
        if wHeads 0 = Γ.start then
          (.outer, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun _ => Dir3.right, idleDir oHead)
        else
          (.rew, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => moveLeftDir (wHeads i), idleDir oHead)
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
    | .outer =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
    | .emit =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ _ => rfl, fun _ => rfl⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
    | .rew =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ _ => rfl, idleDir_right_of_start⟩
        · exact ⟨idleDir_right_of_start, fun _ => moveLeftDir_right_of_start,
            idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-! ## Correctness of the scanner -/

/-- A content-preserving idle step on a tape whose head is off the left marker. -/
private theorem idle_eq {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack t h, idleDir, ite_eq_right h, Tape.move]

/-- The emit pass: from `emit`, with `m` marks on the work tape and the work
head at cell `k + 1`, the machine writes one `false` for each of the `r`
remaining marks and enters `rew` with the work head past the last mark. -/
private theorem mulLenTM_emit_loop :
    ∀ (r k m : ℕ), k + r = m → ∀ (acc : List Bool) (c : Cfg 1 mulLenTM.Q),
      c.state = MulPhase.emit →
      (c.work 0).cells = regCells m →
      (c.work 0).head = k + 1 →
      c.input.read ≠ Γ.start →
      c.output.HasBinaryPrefix acc →
      ∃ c', mulLenTM.reachesIn (r + 1) c c' ∧
        c'.state = MulPhase.rew ∧
        (c'.work 0).cells = regCells m ∧
        (c'.work 0).head = m + 1 ∧
        c'.input = c.input ∧
        c'.output.HasBinaryPrefix (acc ++ List.replicate r false) := by
  intro r
  induction r with
  | zero =>
      intro k m hkm acc c hstate hcells hhead hinp hpre
      have hwread : (c.work 0).read = Γ.blank := by
        rw [Tape.read, hcells, hhead]; exact regCells_blank (by omega)
      have hwne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hinp, Tape.move]
      refine ⟨{ state := MulPhase.rew
                input := c.input
                work := c.work
                output := c.output }, ?_, rfl, hcells, by rw [hhead]; omega, rfl, by simpa⟩
      refine .step ?_ .zero
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read))
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have : i = 0 := Subsingleton.elim i 0
        subst this
        exact idle_eq hwne
      simp only [TM.step, hstate, mulLenTM, hwread, hinp_eq, reduceCtorEq, ite_false]
      rw [hwork, idle_eq houtne]
  | succ r ih =>
      intro k m hkm acc c hstate hcells hhead hinp hpre
      have hwread : (c.work 0).read = Γ.one := by
        rw [Tape.read, hcells, hhead]; exact regCells_one (by omega) (by omega)
      have hwne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hinp, Tape.move]
      set c1 : Cfg 1 mulLenTM.Q :=
        { state := MulPhase.emit
          input := c.input
          work := fun i => (c.work i).move Dir3.right
          output := c.output.writeAndMove (Γ.ofBool false) Dir3.right } with hc1
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          Dir3.right) = fun i => (c.work i).move Dir3.right := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact writeAndMove_readBack _ hwne _
      have hstep : mulLenTM.step c = some c1 := by
        simp only [TM.step, hstate, mulLenTM, hwread, hinp_eq, hc1, reduceCtorEq, ite_false,
          reduceIte]
        rw [hwork]
        rfl
      obtain ⟨c', hreach, hst, hcl, hhd, hin, hout⟩ :=
        ih (k + 1) m (by omega) (acc ++ [false]) c1 rfl
          (by rw [hc1]; simpa using! hcells)
          (by rw [hc1]; simp [Tape.move, hhead])
          (by rw [hc1]; simpa using hinp)
          (by rw [hc1]; exact Tape.hasBinaryPrefix_write_bit false hpre)
      refine ⟨c', .step hstep hreach, hst, hcl, hhd, by rw [hin, hc1], ?_⟩
      rw [List.append_assoc] at hout
      simpa using! hout

/-- The rewind pass: from `rew` with the work head at cell `h`, the machine walks
back to the left-end marker and re-enters `outer` with the work head at cell one,
leaving every tape's contents untouched. -/
private theorem mulLenTM_rew_loop :
    ∀ (h m : ℕ) (c : Cfg 1 mulLenTM.Q),
      c.state = MulPhase.rew →
      (c.work 0).cells = regCells m →
      (c.work 0).head = h →
      c.input.read ≠ Γ.start →
      c.output.read ≠ Γ.start →
      ∃ c', mulLenTM.reachesIn (h + 1) c c' ∧
        c'.state = MulPhase.outer ∧
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
      refine ⟨{ state := MulPhase.outer
                input := c.input
                work := fun i => (c.work i).move Dir3.right
                output := c.output }, ?_, rfl, by simp [Tape.move_cells, hcells],
        by simp [Tape.move, hhead], rfl, rfl⟩
      refine .step ?_ .zero
      simp only [TM.step, hstate, mulLenTM, hwread, hinp_eq, reduceIte, reduceCtorEq,
        ite_false]
      rw [hwork, idle_eq hout]
  | succ h ih =>
      intro m c hstate hcells hhead hinp hout
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [Tape.read, hcells, hhead]; exact regCells_ne_start (by omega)
      have hinp_eq : c.input.move (idleDir c.input.read) = c.input := by
        rw [idleDir, ite_eq_right hinp, Tape.move]
      set c1 : Cfg 1 mulLenTM.Q :=
        { state := MulPhase.rew
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
      have hstep : mulLenTM.step c = some c1 := by
        simp only [TM.step, hstate, mulLenTM, hinp_eq, hc1, ite_eq_right hwne, reduceCtorEq,
          ite_false]
        rw [hwork, idle_eq hout]
      obtain ⟨c', hreach, hst, hcl, hhd, hin, hou⟩ :=
        ih m c1 rfl (by rw [hc1]; simpa [Tape.move_cells] using hcells)
          (by rw [hc1]; simp [Tape.move, hhead])
          (by rw [hc1]; simpa using hinp) (by rw [hc1]; simpa using hout)
      exact ⟨c', .step hstep hreach, hst, hcl, hhd, by rw [hin, hc1], by rw [hou, hc1]⟩

/-- The outer loop: from `outer`, with `m` marks on the work tape and `B` left to
read, the machine runs one emit-and-rewind pass per symbol of `B` and halts with
`|B| · m` zeros appended to the output. -/
private theorem mulLenTM_outer_loop :
    ∀ (B : List Bool) (m : ℕ) (acc : List Bool) (c : Cfg 1 mulLenTM.Q),
      c.state = MulPhase.outer →
      (c.work 0).cells = regCells m →
      (c.work 0).head = 1 →
      c.input.HasBinarySuffix B →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ B.length * (2 * m + 4) + 1 ∧ mulLenTM.reachesIn t c c' ∧
        mulLenTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ List.replicate (B.length * m) false) := by
  intro B
  induction B with
  | nil =>
      intro m acc c hstate hcells hhead hsuf hpre
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hinp : c.input.read ≠ Γ.start := by rw [hread]; decide
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [Tape.read, hcells, hhead]; exact regCells_ne_start (by omega)
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hinp_eq : c.input.move (idleDir Γ.blank) = c.input := by
        rw [idleDir, ite_eq_right (by decide), Tape.move]
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact idle_eq hwne
      refine ⟨{ state := MulPhase.done
                input := c.input
                work := c.work
                output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
      refine .step ?_ .zero
      simp only [TM.step, hstate, mulLenTM, hread, hinp_eq, reduceIte, reduceCtorEq,
        ite_false]
      rw [hwork, idle_eq houtne]
  | cons b B ih =>
      intro m acc c hstate hcells hhead hsuf hpre
      have hread : c.input.read = Γ.ofBool b := hsuf.read_cons
      have hnb : ¬ c.input.read = Γ.blank := by rw [hread]; cases b <;> decide
      have hwne : (c.work 0).read ≠ Γ.start := by
        rw [Tape.read, hcells, hhead]; exact regCells_ne_start (by omega)
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      have hwork : (fun i => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
          (idleDir ((c.work i).read))) = c.work := by
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact idle_eq hwne
      set c1 : Cfg 1 mulLenTM.Q :=
        { state := MulPhase.emit
          input := c.input.move Dir3.right
          work := c.work
          output := c.output } with hc1
      have hstep : mulLenTM.step c = some c1 := by
        simp only [TM.step, hstate, mulLenTM, hnb, hc1, reduceCtorEq, ite_false]
        rw [hwork, idle_eq houtne]
      have hsuf1 : c1.input.HasBinarySuffix B := hsuf.move_right_cons
      obtain ⟨c2, hreach2, hst2, hcl2, hhd2, hin2, hout2⟩ :=
        mulLenTM_emit_loop m 0 m (by omega) acc c1 rfl (by rw [hc1]; exact hcells)
          (by rw [hc1]; simpa using hhead) hsuf1.read_ne_start (by rw [hc1]; exact hpre)
      obtain ⟨c3, hreach3, hst3, hcl3, hhd3, hin3, hout3⟩ :=
        mulLenTM_rew_loop (m + 1) m c2 hst2 hcl2 hhd2
          (by rw [hin2]; exact hsuf1.read_ne_start)
          (by rw [hout2.read_blank]; decide)
      obtain ⟨c', t, ht, hreach', hhalt', hout'⟩ :=
        ih m (acc ++ List.replicate m false) c3 hst3 hcl3 hhd3
          (by rw [hin3, hin2]; exact hsuf1) (by rw [hout3]; exact hout2)
      refine ⟨c', (m + 1 + (m + 1 + 1 + t)) + 1, ?_, ?_, hhalt', ?_⟩
      · simp only [List.length_cons]
        have : (B.length + 1) * (2 * m + 4) = B.length * (2 * m + 4) + (2 * m + 4) := by ring
        omega
      · exact .step hstep
          (mulLenTM.reachesIn_trans hreach2 (mulLenTM.reachesIn_trans hreach3 hreach'))
      · rw [List.append_assoc, ← List.replicate_add] at hout'
        have : m + B.length * m = (b :: B).length * m := by
          simp only [List.length_cons]; ring
        rwa [this] at hout'

/-- The scan pass: from `scanA`, with `k` payload bits already counted as marks on
the work tape and `w` still unread, the machine runs the rest of the computation
and halts with `mulAux k w` on the output tape. The parameter `N` is a fuel bound
on `k + |w|`, which strictly decreases across the recursive step. -/
private theorem mulLenTM_scan_loop :
    ∀ (N : ℕ) (w : List Bool) (k : ℕ), k + w.length ≤ N →
      ∀ (c : Cfg 1 mulLenTM.Q),
      c.state = MulPhase.scanA →
      (c.work 0).cells = regCells k →
      (c.work 0).head = k + 1 →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix [] →
      ∃ c' t, t ≤ 2 * N ^ 2 + 5 * N + 5 ∧ mulLenTM.reachesIn t c c' ∧
        mulLenTM.halted c' ∧
        c'.output.HasBinaryPrefix (mulAux k w) := by
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
        exact idle_eq hwne
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hinp_eq : c.input.move (idleDir Γ.blank) = c.input := by
        rw [idleDir, ite_eq_right (by decide), Tape.move]
      refine ⟨{ state := MulPhase.done
                input := c.input
                work := c.work
                output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
      refine .step ?_ .zero
      simp only [TM.step, hstate, mulLenTM, hread, hinp_eq, reduceCtorEq, ite_false]
      rw [hwork, idle_eq houtne]
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
        exact idle_eq hwne
      have hidleB : ∀ t : Tape, t.move (idleDir Γ.blank) = t := by
        intro t; rw [idleDir, ite_eq_right (by decide)]; rfl
      have hidleZ : ∀ t : Tape, t.move (idleDir Γ.zero) = t := by
        intro t; rw [idleDir, ite_eq_right (by decide)]; rfl
      -- The one-step transition out of `scanA` on a payload bit.
      have hstepA : ∀ b : Bool,
          c.input.read = Γ.ofBool b →
          mulLenTM.step c = some
            { state := (bif b then MulPhase.scanB1 else MulPhase.scanB0)
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } := by
        intro b hread
        cases b <;>
          · simp only [TM.step, hstate, mulLenTM, hread, Γ.ofBool, reduceCtorEq, ite_false,
              Bool.cond_true, Bool.cond_false]
            rw [hwork, idle_eq houtne]
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := MulPhase.done
                    input := c.input
                    work := c.work
                    output := c.output }, 1, by omega, ?_, rfl, by simpa using hpre⟩
          refine .step ?_ .zero
          simp only [TM.step, hstate, mulLenTM, hread, hidleB, reduceCtorEq, ite_false]
          rw [hwork, idle_eq houtne]
      | [b] =>
          -- One payload symbol then end of input: the block framing is broken.
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix [] := hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.blank := hsuf1.read_nil
          refine ⟨{ state := MulPhase.done
                    input := c.input.move Dir3.right
                    work := c.work
                    output := c.output }, 2, by omega, ?_, rfl, by
                      simpa [mulAux_singleton] using hpre⟩
          refine .step (hstepA b hsuf.read_cons) (.step ?_ .zero)
          cases b <;>
            · simp only [TM.step, mulLenTM, hread1, hidleB, reduceCtorEq, ite_false,
                Bool.cond_true, Bool.cond_false]
              rw [hwork, idle_eq houtne]
      | true :: false :: z =>
          -- A broken doubling: halt with empty output.
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (false :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.zero := hsuf1.read_cons
          refine ⟨{ state := MulPhase.done
                    input := c.input.move Dir3.right
                    work := c.work
                    output := c.output }, 2, by omega, ?_, rfl, by
                      simpa [mulAux_broken] using hpre⟩
          refine .step (hstepA true hsuf.read_cons) (.step ?_ .zero)
          simp only [TM.step, mulLenTM, hread1, hidleZ, reduceCtorEq, ite_false,
            Bool.cond_true]
          rw [hwork, idle_eq houtne]
      | false :: true :: z =>
          -- The separator: rewind the work tape and run the outer loop over `z`.
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (true :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.one := hsuf1.read_cons
          set c1 : Cfg 1 mulLenTM.Q :=
            { state := MulPhase.scanB0
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } with hc1
          have hstep1 : mulLenTM.step c = some c1 := hstepA false hsuf.read_cons
          set c2 : Cfg 1 mulLenTM.Q :=
            { state := MulPhase.rew
              input := (c.input.move Dir3.right).move Dir3.right
              work := c.work
              output := c.output } with hc2
          have hstep2 : mulLenTM.step c1 = some c2 := by
            simp only [TM.step, hc1, hc2, mulLenTM, hread1, reduceCtorEq, ite_false]
            rw [hwork, idle_eq houtne]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          obtain ⟨c3, hreach3, hst3, hcl3, hhd3, hin3, hou3⟩ :=
            mulLenTM_rew_loop (k + 1) k c2 rfl (by rw [hc2]; exact hcells)
              (by rw [hc2]; exact hhead) hsuf2.read_ne_start (by rw [hc2]; exact houtne)
          obtain ⟨c', t, ht, hreach', hhalt', hout'⟩ :=
            mulLenTM_outer_loop z k [] c3 hst3 hcl3 hhd3 (by rw [hin3]; exact hsuf2)
              (by rw [hou3]; exact hpre)
          refine ⟨c', (k + 1 + 1 + t) + 1 + 1, ?_, ?_, hhalt', ?_⟩
          · simp only [List.length_cons] at hN
            have hz : z.length ≤ N := by omega
            have hk : k ≤ N := by omega
            have ht' : t ≤ z.length * (2 * k + 4) + 1 := ht
            have : z.length * (2 * k + 4) ≤ N * (2 * N + 4) := by
              exact Nat.mul_le_mul hz (by omega)
            nlinarith [sq_nonneg N]
          · exact .step hstep1 (.step hstep2 (mulLenTM.reachesIn_trans hreach3 hreach'))
          · rw [mulAux_sep]
            have : z.length * k = k * z.length := Nat.mul_comm _ _
            rw [this] at hout'
            simpa using hout'
      | false :: false :: z =>
          -- A doubled `0`: write one mark and continue scanning.
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (false :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.zero := hsuf1.read_cons
          set c1 : Cfg 1 mulLenTM.Q :=
            { state := MulPhase.scanB0
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } with hc1
          have hstep1 : mulLenTM.step c = some c1 := hstepA false hsuf.read_cons
          set c2 : Cfg 1 mulLenTM.Q :=
            { state := MulPhase.scanA
              input := (c.input.move Dir3.right).move Dir3.right
              work := fun i => ((c.work i).write Γ.one).move Dir3.right
              output := c.output } with hc2
          have hwmark : (fun i => (c.work i).writeAndMove (Γw.one).toΓ Dir3.right)
              = fun i => ((c.work i).write Γ.one).move Dir3.right := rfl
          have hstep2 : mulLenTM.step c1 = some c2 := by
            simp only [TM.step, hc1, hc2, mulLenTM, hread1, reduceCtorEq, ite_false]
            rw [hwmark, idle_eq houtne]
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
            ih z (k + 1) (by simp only [List.length_cons] at hN; omega) c2 rfl hcells2 hhead2
              (by rw [hc2]; exact hsuf1.move_right_cons) (by rw [hc2]; exact hpre)
          refine ⟨c', t + 1 + 1, ?_, .step hstep1 (.step hstep2 hreach'), hhalt', ?_⟩
          · nlinarith [sq_nonneg N]
          · rwa [mulAux_double]
      | true :: true :: z =>
          -- A doubled `1`: write one mark and continue scanning.
          have hsuf1 : (c.input.move Dir3.right).HasBinarySuffix (true :: z) :=
            hsuf.move_right_cons
          have hread1 : (c.input.move Dir3.right).read = Γ.one := hsuf1.read_cons
          set c1 : Cfg 1 mulLenTM.Q :=
            { state := MulPhase.scanB1
              input := c.input.move Dir3.right
              work := c.work
              output := c.output } with hc1
          have hstep1 : mulLenTM.step c = some c1 := hstepA true hsuf.read_cons
          set c2 : Cfg 1 mulLenTM.Q :=
            { state := MulPhase.scanA
              input := (c.input.move Dir3.right).move Dir3.right
              work := fun i => ((c.work i).write Γ.one).move Dir3.right
              output := c.output } with hc2
          have hwmark : (fun i => (c.work i).writeAndMove (Γw.one).toΓ Dir3.right)
              = fun i => ((c.work i).write Γ.one).move Dir3.right := rfl
          have hstep2 : mulLenTM.step c1 = some c2 := by
            simp only [TM.step, hc1, hc2, mulLenTM, hread1, reduceCtorEq, ite_false]
            rw [hwmark, idle_eq houtne]
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
            ih z (k + 1) (by simp only [List.length_cons] at hN; omega) c2 rfl hcells2 hhead2
              (by rw [hc2]; exact hsuf1.move_right_cons) (by rw [hc2]; exact hpre)
          refine ⟨c', t + 1 + 1, ?_, .step hstep1 (.step hstep2 hreach'), hhalt', ?_⟩
          · nlinarith [sq_nonneg N]
          · rwa [mulAux_double]

/-- The blank work tape of the initial configuration is the zero register. -/
private theorem init_nil_cells_eq_regCells_zero :
    (Tape.init ([] : List Γ)).cells = regCells 0 := by
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Tape.init_cells_ge _ _ (by simp), regCells_blank (by omega)]

/-- `mulUnpair` is polynomial-time, via the `mulLenTM` scanner. -/
theorem mulUnpair_mem_FP : mulUnpair ∈ FP := by
  refine ⟨2, 1, mulLenTM, (fun m => 2 * m ^ 2 + 5 * m + 6), ?_, ?_⟩
  · intro z
    -- Step 1: move every head off the left-end marker.
    set c1 : Cfg 1 mulLenTM.Q :=
      { state := MulPhase.scanA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right } with hc1
    have hstep1 : mulLenTM.step (mulLenTM.initCfg z) = some c1 := by
      simp [TM.step, mulLenTM, hc1, Tape.read, Tape.init, readBackWrite,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
      mulLenTM_scan_loop z.length z 0 (by omega) c1 rfl
        (by rw [hc1]; show ((Tape.init []).move Dir3.right).cells = _
            rw [Tape.move_cells, init_nil_cells_eq_regCells_zero])
        (by rw [hc1]; show ((Tape.init []).move Dir3.right).head = _
            simp [Tape.move])
        hsuf hpre
    exact ⟨c', t + 1, by simpa using by omega, .step hstep1 hreach, hhalt,
      hout.hasOutput⟩
  · have h1 : (fun m : ℕ => 2 * m ^ 2) =O ((· ^ 2) : ℕ → ℕ) := by
      simpa using (BigO.refl (fun m : ℕ => m ^ 2)).const_mul_left 2
    have h2 : (fun m : ℕ => 5 * m) =O ((· ^ 2) : ℕ → ℕ) :=
      BigO.const_mul_left 5
        (by simpa [pow_one] using (BigO.pow_le_pow_right (by omega : 1 ≤ 2)))
    exact BigO.add (BigO.add h1 h2) (BigO.const_le_pow 6 2)

end MulLenMachine

end Cobham

end Complexity

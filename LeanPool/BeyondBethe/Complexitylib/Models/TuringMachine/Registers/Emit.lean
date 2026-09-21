/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare

/-!
# Output-emission subroutines

Building blocks for machines that *compute string functions* (`ComputesInTime`):
the output tape is treated as an append-only accumulator, written left to
right. The central predicate `OutAcc ys out` says the output tape holds
exactly the bits `ys` (after the `▷` at cell 0) with the head parked on the
first blank, ready to append; emitters have Hoare specs of the shape

    {OutAcc ys ∧ …} emit {OutAcc (ys ++ w) ∧ …}

which compose by `seqTM` along `List.append` associativity. The final bridge
to `ComputesInTime` is `OutAcc.hasOutput`.

This layer is the foundation for the Cook–Levin reduction emitter
(`docs/A5-ReductionEmitter.md`).

## Main definitions

- `TM.OutAcc` — the output-accumulator predicate
- `TM.bumpTM` — entry adapter: bump every head from `▷` to cell 1
- `TM.emitBitsTM` — append a fixed word to the output
- `TM.emitUnaryTM` — append a register's value as a doubled-unary run
- `TM.emitLitTM` — append one encoded literal (sign bits, unary body, terminator)

## Main results

- `TM.OutAcc.hasOutput` — accumulated output is `HasOutput`
- `TM.OutAcc.eq` — the accumulated word uniquely determines its output tape
- `TM.outAcc_append_bit` — one `writeAndMove _ .right` extends the accumulator
- `TM.emitBitsTM_reachesIn_frame` — exact emission with a complete input/work frame
- `TM.emitBitsTM_hoareTime` — `emitBitsTM w` appends `w` in `|w|` steps,
  preserving the input and work tapes
- `TM.emitBitsTM_isTransducer` — fixed-word emission never moves output left
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- The output accumulator
-- ════════════════════════════════════════════════════════════════════════

/-- **Output accumulator.** The output tape holds exactly the bits `ys`
    (cells `1..|ys|`, after the `▷` at cell 0), all cells beyond are blank,
    and the head is parked on the first blank — ready to append. -/
def OutAcc (ys : List Bool) (out : Tape) : Prop :=
  out.head = ys.length + 1 ∧
  out.cells 0 = Γ.start ∧
  (∀ i, (h : i < ys.length) → out.cells (i + 1) = Γ.ofBool ys[i]) ∧
  (∀ j, ys.length + 1 ≤ j → out.cells j = Γ.blank)

namespace OutAcc

/-- The accumulator head sits just past the `|ys|` stored bits, at cell `|ys| + 1`. -/
theorem head_eq {ys : List Bool} {out : Tape} (h : OutAcc ys out) :
    out.head = ys.length + 1 := h.1

/-- The accumulator reads the first blank. -/
theorem read_blank {ys : List Bool} {out : Tape} (h : OutAcc ys out) :
    out.read = Γ.blank := by
  rw [Tape.read, h.1]; exact h.2.2.2 _ (le_refl _)

/-- An accumulator tape is parked (bits and blanks are never `▷`). -/
theorem parked {ys : List Bool} {out : Tape} (h : OutAcc ys out) : Parked out := by
  refine ⟨by rw [h.1]; omega, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (ys.length + 1) with hlt | hge
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [h.2.2.1 i (by omega)]
    cases ys[i] <;> decide
  · rw [h.2.2.2 j hge]; decide

/-- The bridge to `ComputesInTime`: an accumulated output `HasOutput` its bits. -/
theorem hasOutput {ys : List Bool} {out : Tape} (h : OutAcc ys out) :
    out.HasOutput ys :=
  ⟨fun i hi => h.2.2.1 i hi, h.2.2.2 _ (le_refl _)⟩

/-- An output accumulator is uniquely determined by its accumulated word. -/
theorem eq {ys : List Bool} {first second : Tape}
    (hfirst : OutAcc ys first) (hsecond : OutAcc ys second) :
    first = second := by
  apply Tape.ext
  · rw [hfirst.1, hsecond.1]
  · funext j
    by_cases hj0 : j = 0
    · subst j
      rw [hfirst.2.1, hsecond.2.1]
    · by_cases hj : j ≤ ys.length
      · obtain ⟨i, hi, rfl⟩ : ∃ i, i < ys.length ∧ j = i + 1 := by
          refine ⟨j - 1, by omega, by omega⟩
        rw [hfirst.2.2.1 i hi, hsecond.2.2.1 i hi]
      · rw [hfirst.2.2.2 j (by omega), hsecond.2.2.2 j (by omega)]

end OutAcc

/-- The empty accumulator: a blank output tape with the head bumped to cell 1. -/
theorem outAcc_nil_init : OutAcc [] { head := 1, cells := (Tape.init []).cells } := by
  refine ⟨rfl, by simp [Tape.init], fun i hi => absurd hi (by simp), fun j hj => ?_⟩
  show (Tape.init []).cells j = Γ.blank
  simp only [Tape.init]
  rw [ite_eq_right (by omega : ¬ j = 0)]
  simp

/-- **Appending one bit.** Writing `Γ.ofBool b` at the accumulator head and
    moving right extends the accumulator by `b`. -/
theorem outAcc_append_bit {ys : List Bool} {out : Tape} (h : OutAcc ys out) (b : Bool) :
    OutAcc (ys ++ [b]) (out.writeAndMove (Γ.ofBool b) .right) := by
  obtain ⟨hhead, hc0, hbits, hblank⟩ := h
  have hne : ¬ out.head = 0 := by omega
  have hcells : (out.writeAndMove (Γ.ofBool b) .right).cells
      = Function.update out.cells (ys.length + 1) (Γ.ofBool b) := by
    show ((out.write _).move _).cells = _
    rw [Tape.move]
    show (out.write _).cells = _
    rw [Tape.write, ite_eq_right hne, hhead]
  have hhead' : (out.writeAndMove (Γ.ofBool b) .right).head = out.head + 1 := by
    show ((out.write _).move _).head = _
    rw [Tape.move]
    show (out.write _).head + 1 = _
    rw [Tape.write, ite_eq_right hne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hhead', hhead]; simp
  · rw [hcells, Function.update_of_ne (by omega : ¬ (0 : ℕ) = ys.length + 1)]
    exact hc0
  · intro i hi
    rw [List.length_append, List.length_cons, List.length_nil] at hi
    rcases Nat.lt_or_ge i ys.length with hlt | hge
    · rw [hcells, Function.update_of_ne (by omega : ¬ i + 1 = ys.length + 1),
        List.getElem_append_left hlt]
      exact hbits i hlt
    · obtain rfl : i = ys.length := by omega
      rw [hcells, Function.update_self,
        List.getElem_append_right (le_refl _)]
      simp
  · intro j hj
    rw [List.length_append, List.length_cons, List.length_nil] at hj
    rw [hcells, Function.update_of_ne (by omega : ¬ j = ys.length + 1)]
    exact hblank j (by omega)

-- ════════════════════════════════════════════════════════════════════════
-- bumpTM: the entry adapter
-- ════════════════════════════════════════════════════════════════════════

/-- The two states of `bumpTM`: `go` (initial, about to bump every head right)
    and `done` (halted). -/
inductive BumpPhase where
  | go | done
  deriving DecidableEq

/-- `BumpPhase` is a finite type, as required for TM state spaces. -/
instance : Fintype BumpPhase where
  elems := {.go, .done}
  complete := fun x => by cases x <;> simp

/-- **Entry adapter**: one step moving every head from `▷` (cell 0, the
    initial configuration) to cell 1, establishing the parked discipline:
    blank work tapes become zero registers and the blank output becomes the
    empty accumulator. -/
def bumpTM : TM n where
  Q := BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ _ wHeads _ =>
    (.done, fun i => readBackWrite (wHeads i), .blank,
     Dir3.right, fun _ => Dir3.right, Dir3.right)
  δ_right_of_start := fun _ _ _ _ => ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- The input tape of the initial configuration, bumped to cell 1, is parked. -/
theorem parked_init_input (x : List Bool) :
    Parked { head := 1, cells := (Tape.init (x.map Γ.ofBool)).cells } := by
  refine ⟨le_refl 1, fun j hj => ?_⟩
  show (Tape.init (x.map Γ.ofBool)).cells j ≠ Γ.start
  simp only [Tape.init]
  rw [ite_eq_right (by omega : ¬ j = 0)]
  cases h : (x.map Γ.ofBool)[j - 1]? with
  | none => decide
  | some g =>
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
    cases b <;> decide

/-- **`bumpTM` Hoare specification.** From the initial configuration's tapes,
    one step establishes: parked input (cells intact), zero registers on all
    work tapes, and the empty output accumulator. -/
theorem bumpTM_hoareTime (x : List Bool) :
    (bumpTM (n := n)).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧ (∀ i, work i = Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp = { head := 1, cells := (Tape.init (x.map Γ.ofBool)).cells } ∧
        (∀ i, IsReg 0 (work i)) ∧ OutAcc [] out)
      1 := by
  rintro inp work out ⟨rfl, hwork, rfl⟩
  obtain rfl : work = fun _ => Tape.init [] := funext hwork
  refine ⟨⟨BumpPhase.done, ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩,
      fun _ => ⟨1, (Tape.init []).cells⟩, ⟨1, (Tape.init []).cells⟩⟩, 1, le_refl 1,
    .step ?_ .zero, rfl, rfl, fun _ => reg_zero_init_bumped, outAcc_nil_init⟩
  rfl

-- ════════════════════════════════════════════════════════════════════════
-- emitBitsTM: append a fixed word to the output
-- ════════════════════════════════════════════════════════════════════════

/-- **Append the fixed word `w` to the output** and halt. State `k` = number of
    bits already emitted; each step writes bit `k` and moves the output head
    right; input and work tapes are parked and untouched. -/
def emitBitsTM (w : List Bool) : TM n where
  Q := Fin (w.length + 1)
  qstart := ⟨0, by omega⟩
  qhalt := ⟨w.length, by omega⟩
  δ := fun k iHead wHeads oHead =>
    if h : k.val < w.length then
      (⟨k.val + 1, by omega⟩, fun i => readBackWrite (wHeads i), Γw.ofBool w[k.val],
       idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
    else
      allIdle k iHead wHeads oHead
  δ_right_of_start := by
    intro k iHead wHeads oHead
    by_cases h : k.val < w.length
    · simp only [h, ↓reduceDIte]
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => trivial⟩
    · simp only [h, ↓reduceDIte]
      exact rightOfStart_allIdle iHead wHeads oHead

/-- One emit step: from state `k < |w|`, the machine writes bit `k`, advances
    the accumulator, and leaves the parked input and work tapes unchanged. -/
private theorem emitBitsTM_step (w : List Bool) (c : Cfg n (emitBitsTM (n := n) w).Q)
    (k : ℕ) (hk : k < w.length) (hst : c.state = ⟨k, by omega⟩)
    (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i)) :
    (emitBitsTM (n := n) w).step c = some
      { state := ⟨k + 1, by omega⟩, input := c.input, work := c.work,
        output := c.output.writeAndMove (Γ.ofBool w[k]) .right } := by
  have hne : ¬ c.state = (emitBitsTM (n := n) w).qhalt := by
    rw [hst]
    simp only [emitBitsTM, Fin.mk.injEq]
    omega
  rw [TM.step, ite_eq_right hne]
  simp only [emitBitsTM, hst, hk, ↓reduceDIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · rw [Γw.ofBool_toΓ]

/-- The emit loop: from state `k` with `|w| = k + m`, the machine reaches the
    halt state in exactly `m` steps, appending `w.drop k` and preserving the
    input and work tapes. -/
private theorem emitBitsTM_run (w : List Bool) (m : ℕ) :
    ∀ (k : ℕ) (hk : w.length = k + m),
      ∀ (c : Cfg n (emitBitsTM (n := n) w).Q) (ys : List Bool),
      c.state = ⟨k, by omega⟩ → Parked c.input → (∀ i, Parked (c.work i)) →
      OutAcc ys c.output →
      ∃ c', (emitBitsTM (n := n) w).reachesIn m c c' ∧
        c'.state = ⟨w.length, by omega⟩ ∧ c'.input = c.input ∧ c'.work = c.work ∧
        OutAcc (ys ++ w.drop k) c'.output := by
  induction m with
  | zero =>
    intro k hk c ys hst hinp hwork hout
    refine ⟨c, .zero, ?_, rfl, rfl, ?_⟩
    · rw [hst]; congr 1; omega
    · rw [List.drop_of_length_le (by omega), List.append_nil]
      exact hout
  | succ m ih =>
    intro k hk c ys hst hinp hwork hout
    have hklt : k < w.length := by omega
    have hstep := emitBitsTM_step w c k hklt hst hinp hwork
    set c₁ : Cfg n (emitBitsTM (n := n) w).Q :=
      { state := ⟨k + 1, by omega⟩, input := c.input, work := c.work,
        output := c.output.writeAndMove (Γ.ofBool w[k]) .right } with hc₁
    obtain ⟨c', hreach, hst', hinp', hwork', hout'⟩ :=
      ih (k + 1) (by omega) c₁ (ys ++ [w[k]]) rfl hinp hwork
        (outAcc_append_bit hout w[k])
    refine ⟨c', .step hstep hreach, hst', hinp', hwork', ?_⟩
    rwa [List.append_assoc, List.singleton_append,
      List.getElem_cons_drop] at hout'

/-- Exact fixed-word emission appends `w`, preserves the complete input/work
frame, and reaches the halt state in exactly `|w|` steps. -/
theorem emitBitsTM_reachesIn_frame (w : List Bool) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hout₀ : OutAcc ys out₀) :
    ∃ c',
      (emitBitsTM (n := n) w).reachesIn w.length
        { state := (emitBitsTM (n := n) w).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (emitBitsTM (n := n) w).halted c' ∧
      c'.input = inp₀ ∧
      c'.work = work₀ ∧
      OutAcc (ys ++ w) c'.output := by
  obtain ⟨c', hreach, hhalt, hinput, hwork, houtput⟩ :=
    emitBitsTM_run w w.length 0 (by omega)
      { state := ⟨0, by omega⟩, input := inp₀, work := work₀, output := out₀ }
      ys rfl hinp₀ hwork₀ hout₀
  refine ⟨c', hreach, hhalt, hinput, hwork, ?_⟩
  rwa [List.drop_zero] at houtput

/-- Fixed-word emission satisfies the one-way-output transducer discipline. -/
theorem emitBitsTM_isTransducer (w : List Bool) :
    (emitBitsTM (n := n) w).IsTransducer := by
  intro k iHead wHeads oHead
  by_cases h : k.val < w.length
  · simp [emitBitsTM, h]
  · simp [emitBitsTM, h, allIdle, idleDir]
    split <;> decide

/-- **`emitBitsTM` Hoare specification.** Appends the word `w` to the output
    accumulator in `|w|` steps, leaving the (parked) input and work tapes
    literally unchanged. Ghost-parametrized by the initial tapes for
    `seqTM` composition. -/
theorem emitBitsTM_hoareTime (w : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i)) :
    (emitBitsTM (n := n) w).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ OutAcc (ys ++ w) out)
      w.length := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c', hreach, hst', hinp', hwork', hout'⟩ :=
    emitBitsTM_run w w.length 0 (by omega)
      { state := ⟨0, by omega⟩, input := inp, work := work, output := out }
      ys rfl hinp₀ hwork₀ hout
  refine ⟨c', w.length, le_refl _, hreach, ?_, hinp', hwork', ?_⟩
  · exact hst'
  · rw [List.drop_zero] at hout'
    exact hout'

-- ════════════════════════════════════════════════════════════════════════
-- emitUnaryTM: append a register's value as a doubled-unary run
-- ════════════════════════════════════════════════════════════════════════

/-- The states of `emitUnaryTM`: `emitA`/`emitB` alternate to emit two trues per
    register mark, `back` rewinds the register head to `▷`, `park` steps it to
    cell 1, and `done` halts. -/
inductive EmitUnaryPhase where
  | emitA | emitB | back | park | done
  deriving DecidableEq

/-- `EmitUnaryPhase` is a finite type, as required for TM state spaces. -/
instance : Fintype EmitUnaryPhase where
  elems := {.emitA, .emitB, .back, .park, .done}
  complete := fun x => by cases x <;> simp

/-- **Append `2v` trues to the output, where `v` is the value of register `r`**
    (the doubled-unary body `doubleBits (Unary.encode v)` of a literal's
    variable index), restoring the register exactly. The head sweeps right
    over the register's marks emitting two trues per mark (`emitA`/`emitB`),
    then rewinds to cell 1 (`back`/`park`). -/
def emitUnaryTM (r : Fin n) : TM n where
  Q := EmitUnaryPhase
  qstart := .emitA
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .emitA =>
      if wHeads r = Γ.one then
        (.emitB, fun i => readBackWrite (wHeads i), Γw.one,
         idleDir iHead, fun i => if i = r then Dir3.stay else idleDir (wHeads i),
         Dir3.right)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = r then (if wHeads r = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .emitB =>
      (.emitA, fun i => readBackWrite (wHeads i), Γw.one,
       idleDir iHead, fun i => if i = r then Dir3.right else idleDir (wHeads i),
       Dir3.right)
    | .back =>
      if wHeads r = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = r then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = r then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .emitA =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, fun _ => rfl⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hnone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .emitB =>
      refine ⟨idleDir_right_of_start, fun i hi => ?_, fun _ => rfl⟩
      dsimp only []
      by_cases hir : i = r
      · rw [ite_eq_left hir]
      · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section EmitUnary

variable {r : Fin n}

/-- Not yet halted, from any of the four working phases. -/
private theorem emitUnaryTM_ne_halt {s : EmitUnaryPhase} (h : s ≠ .done)
    {c : Cfg n (emitUnaryTM (n := n) r).Q} (hst : c.state = s) :
    ¬ c.state = (emitUnaryTM (n := n) r).qhalt := by
  rw [hst]
  show ¬ s = EmitUnaryPhase.done
  exact h

/-- `emitA` over a mark: write one `true`, output right, register stays. -/
private theorem emitUnaryTM_step_emitA_one (c : Cfg n (emitUnaryTM (n := n) r).Q)
    (hst : c.state = .emitA) (hone : (c.work r).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i)) :
    (emitUnaryTM (n := n) r).step c = some
      { state := .emitB, input := c.input, work := c.work,
        output := c.output.writeAndMove (Γ.ofBool true) .right } := by
  rw [TM.step, ite_eq_right (emitUnaryTM_ne_halt (by decide) hst)]
  simp only [emitUnaryTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, writeAndMove_readBack _ (by rw [hone]; decide)]
      rfl
    · rw [ite_eq_right hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · rfl

/-- `emitB`: write the second `true`, output right, register advances right. -/
private theorem emitUnaryTM_step_emitB (c : Cfg n (emitUnaryTM (n := n) r).Q)
    (hst : c.state = .emitB) (hone : (c.work r).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i)) :
    (emitUnaryTM (n := n) r).step c = some
      { state := .emitA, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output.writeAndMove (Γ.ofBool true) .right } := by
  rw [TM.step, ite_eq_right (emitUnaryTM_ne_halt (by decide) hst)]
  simp only [emitUnaryTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · rfl

/-- `emitA` over the sentinel blank: turn around (register head left), output
    untouched. -/
private theorem emitUnaryTM_step_emitA_blank (c : Cfg n (emitUnaryTM (n := n) r).Q)
    (hst : c.state = .emitA) (hblank : (c.work r).read = Γ.blank)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (emitUnaryTM (n := n) r).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (emitUnaryTM_ne_halt (by decide) hst)]
  simp only [emitUnaryTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hblank]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` off the sentinel: keep rewinding left, everything else untouched. -/
private theorem emitUnaryTM_step_back_left (c : Cfg n (emitUnaryTM (n := n) r).Q)
    (hst : c.state = .back) (hns : (c.work r).read ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (emitUnaryTM (n := n) r).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (emitUnaryTM_ne_halt (by decide) hst)]
  simp only [emitUnaryTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` on the sentinel `▷` (which, absent spurious `▷`s, means cell 0):
    step right to cell 1 and park. The write is structurally void at cell 0. -/
private theorem emitUnaryTM_step_back_start (c : Cfg n (emitUnaryTM (n := n) r).Q)
    (hst : c.state = .back) (hs : (c.work r).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (emitUnaryTM (n := n) r).step c = some
      { state := .park, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  have h0 : (c.work r).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (emitUnaryTM_ne_halt (by decide) hst)]
  simp only [emitUnaryTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `park`: one idle step into `done`; nothing changes. -/
private theorem emitUnaryTM_step_park (c : Cfg n (emitUnaryTM (n := n) r).Q)
    (hst : c.state = .park) (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i))
    (hout : Parked c.output) :
    (emitUnaryTM (n := n) r).step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (emitUnaryTM_ne_halt (by decide) hst)]
  simp only [emitUnaryTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The emit loop: from `emitA` mid-scan (register head at `k + 1`, register
    value `v = k + m`), the machine emits `2m` trues in `2m` steps and lands
    back in `emitA` on the sentinel blank, register cells untouched. -/
private theorem emitUnaryTM_emit_run (v m : ℕ) :
    ∀ (k : ℕ), v = k + m →
      ∀ (c : Cfg n (emitUnaryTM (n := n) r).Q) (ys : List Bool),
      c.state = .emitA →
      Parked c.input → (∀ i, i ≠ r → Parked (c.work i)) →
      (∀ i, i < v → (c.work r).cells (i + 1) = Γ.one) →
      (∀ j, v + 1 ≤ j → (c.work r).cells j = Γ.blank) →
      (c.work r).head = k + 1 →
      OutAcc ys c.output →
      ∃ c', (emitUnaryTM (n := n) r).reachesIn (2 * m) c c' ∧
        c'.state = .emitA ∧ c'.input = c.input ∧
        (∀ i, i ≠ r → c'.work i = c.work i) ∧
        (c'.work r).cells = (c.work r).cells ∧
        (c'.work r).head = v + 1 ∧
        OutAcc (ys ++ List.replicate (2 * m) true) c'.output := by
  induction m with
  | zero =>
    intro k hk c ys hst hinp hwork _ _ hhead hout
    refine ⟨c, .zero, hst, rfl, fun _ _ => rfl, rfl, ?_, by simpa using hout⟩
    rw [hhead, hk]
  | succ m ih =>
    intro k hk c ys hst hinp hwork hones hblanks hhead hout
    have hone : (c.work r).read = Γ.one := by
      rw [Tape.read, hhead]; exact hones k (by omega)
    have hstepA := emitUnaryTM_step_emitA_one c hst hone hinp hwork
    set c₁ : Cfg n (emitUnaryTM (n := n) r).Q :=
      { state := .emitB, input := c.input, work := c.work,
        output := c.output.writeAndMove (Γ.ofBool true) .right } with hc₁
    have hstepB := emitUnaryTM_step_emitB c₁ rfl hone hinp hwork
    set c₂ : Cfg n (emitUnaryTM (n := n) r).Q :=
      { state := .emitA, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := (c.output.writeAndMove (Γ.ofBool true) .right).writeAndMove
          (Γ.ofBool true) .right } with hc₂
    have hmove_cells : ((c.work r).move .right).cells = (c.work r).cells := rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih (k + 1) (by omega) c₂ (ys ++ [true] ++ [true]) rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work r ((c.work r).move .right) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        (fun i hi => by
          show (Function.update c.work r ((c.work r).move .right) r).cells (i + 1) = Γ.one
          rw [Function.update_self, hmove_cells]
          exact hones i hi)
        (fun j hj => by
          show (Function.update c.work r ((c.work r).move .right) r).cells j = Γ.blank
          rw [Function.update_self, hmove_cells]
          exact hblanks j hj)
        (by
          show (Function.update c.work r ((c.work r).move .right) r).head = (k + 1) + 1
          rw [Function.update_self]
          show (c.work r).head + 1 = (k + 1) + 1
          rw [hhead])
        (outAcc_append_bit (outAcc_append_bit hout true) true)
    refine ⟨c', .step hstepA (.step hstepB hreach), hst', hinp', ?_, ?_, hhead', ?_⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work r ((c.work r).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells']
      show (Function.update c.work r ((c.work r).move .right) r).cells = (c.work r).cells
      rw [Function.update_self, hmove_cells]
    · have he : ys ++ [true] ++ [true] ++ List.replicate (2 * m) true
          = ys ++ List.replicate (2 * (m + 1)) true := by
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by omega, List.replicate_succ,
          List.replicate_succ]
        simp [List.append_assoc]
      rwa [he] at hout'

/-- The rewind loop: from `back` with the register head at `h` (cell 0 holds
    `▷`, no spurious `▷`s beyond), the machine reaches `done` in `h + 2` steps
    with the register parked at cell 1 and everything else untouched. -/
private theorem emitUnaryTM_back_run (h : ℕ) :
    ∀ (c : Cfg n (emitUnaryTM (n := n) r).Q) (ys : List Bool),
      c.state = .back →
      Parked c.input → (∀ i, i ≠ r → Parked (c.work i)) →
      (c.work r).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start) →
      (c.work r).head = h →
      OutAcc ys c.output →
      ∃ c', (emitUnaryTM (n := n) r).reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ r → c'.work i = c.work i) ∧
        (c'.work r).cells = (c.work r).cells ∧
        (c'.work r).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c ys hst hinp hwork hc0 hcr hhead hout
    have hs : (c.work r).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep₁ := emitUnaryTM_step_back_start c hst hs hcr hinp hwork hout.parked
    set c₁ : Cfg n (emitUnaryTM (n := n) r).Q :=
      { state := .park, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } with hc₁
    have hworkP : ∀ i, Parked (c₁.work i) := by
      intro i
      by_cases hir : i = r
      · subst hir
        show Parked (Function.update c.work i ((c.work i).move .right) i)
        rw [Function.update_self]
        exact ⟨by show (c.work i).head + 1 ≥ 1; omega, fun j hj => hcr j hj⟩
      · show Parked (Function.update c.work r ((c.work r).move .right) i)
        rw [Function.update_of_ne hir]
        exact hwork i hir
    have hstep₂ := emitUnaryTM_step_park c₁ rfl hinp hworkP hout.parked
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work r ((c.work r).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work r ((c.work r).move .right) r).cells = (c.work r).cells
      rw [Function.update_self]
      rfl
    · show (Function.update c.work r ((c.work r).move .right) r).head = 1
      rw [Function.update_self]
      show (c.work r).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c ys hst hinp hwork hc0 hcr hhead hout
    have hns : (c.work r).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep₁ := emitUnaryTM_step_back_left c hst hns hinp hwork hout.parked
    set c₁ : Cfg n (emitUnaryTM (n := n) r).Q :=
      { state := .back, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } with hc₁
    have hupd_cells : (c₁.work r).cells = (c.work r).cells := by
      show (Function.update c.work r ((c.work r).move .left) r).cells = _
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih c₁ ys rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work r ((c.work r).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        (by rw [hupd_cells]; exact hc0)
        (fun j hj => by rw [hupd_cells]; exact hcr j hj)
        (by
          show (Function.update c.work r ((c.work r).move .left) r).head = h
          rw [Function.update_self]
          show (c.work r).head - 1 = h
          rw [hhead]
          omega)
        hout
    refine ⟨c', .step hstep₁ hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work r ((c.work r).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd_cells]

/-- **`emitUnaryTM` Hoare specification.** Appends `2v` trues (the doubled
    unary body of a literal with variable index `v`) to the output accumulator
    in `3v + 3` steps, restoring all tapes exactly: the scanned register `r`
    included. -/
theorem emitUnaryTM_hoareTime (r : Fin n) (v : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, i ≠ r → Parked (work₀ i))
    (hreg : IsReg v (work₀ r)) :
    (emitUnaryTM (n := n) r).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧
        OutAcc (ys ++ List.replicate (2 * v) true) out)
      (3 * v + 3) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c₁, hreach₁, hst₁, hinp₁, hwork₁, hcells₁, hhead₁, hout₁⟩ :=
    emitUnaryTM_emit_run v v 0 (by omega)
      { state := .emitA, input := inp, work := work, output := out } ys rfl
      hinp₀ hwork₀ (fun i hi => hreg.cells_one hi) (fun j hj => hreg.cells_blank hj)
      (by show (work r).head = 0 + 1; rw [hreg.head_eq]) hout
  have hinpP₁ : Parked c₁.input := by rw [hinp₁]; exact hinp₀
  have hworkP₁ : ∀ i, i ≠ r → Parked (c₁.work i) := fun i hi => by
    rw [hwork₁ i hi]
    exact hwork₀ i hi
  have hblank₁ : (c₁.work r).read = Γ.blank := by
    rw [Tape.read, hhead₁, hcells₁]
    exact hreg.cells_blank (le_refl _)
  have hstep₂ := emitUnaryTM_step_emitA_blank c₁ hst₁ hblank₁ hinpP₁ hworkP₁ hout₁.parked
  set c₂ : Cfg n (emitUnaryTM (n := n) r).Q :=
    { state := .back, input := c₁.input,
      work := Function.update c₁.work r ((c₁.work r).move .left),
      output := c₁.output } with hc₂
  have hupd_cells₂ : (c₂.work r).cells = (work r).cells := by
    show (Function.update c₁.work r ((c₁.work r).move .left) r).cells = _
    rw [Function.update_self]
    show (c₁.work r).cells = _
    rw [hcells₁]
  obtain ⟨c₃, hreach₃, hst₃, hinp₃, hwork₃, hcells₃, hhead₃, hout₃⟩ :=
    emitUnaryTM_back_run v c₂ (ys ++ List.replicate (2 * v) true) rfl hinpP₁
      (fun i hi => by
        show Parked (Function.update c₁.work r ((c₁.work r).move .left) i)
        rw [Function.update_of_ne hi]
        exact hworkP₁ i hi)
      (by rw [hupd_cells₂]; exact hreg.cell0)
      (fun j hj => by rw [hupd_cells₂]; exact hreg.cells_ne_start hj)
      (by
        show (Function.update c₁.work r ((c₁.work r).move .left) r).head = v
        rw [Function.update_self]
        show (c₁.work r).head - 1 = v
        rw [hhead₁]
        omega)
      hout₁
  refine ⟨c₃, 2 * v + ((v + 2) + 1), by omega,
    reachesIn_trans _ hreach₁ (.step hstep₂ hreach₃), hst₃, ?_, ?_, ?_⟩
  · rw [hinp₃]; exact hinp₁
  · funext i
    by_cases hir : i = r
    · subst hir
      refine Tape.ext ?_ ?_
      · rw [hhead₃, hreg.head_eq]
      · rw [hcells₃, hupd_cells₂]
    · rw [hwork₃ i hir]
      show Function.update c₁.work r ((c₁.work r).move .left) i = work i
      rw [Function.update_of_ne hir]
      exact hwork₁ i hir
  · rw [hout₃]
    exact hout₁

end EmitUnary

-- ════════════════════════════════════════════════════════════════════════
-- seqTM composition glue for ghost-parametrized emit specs
-- ════════════════════════════════════════════════════════════════════════

/-- The standard emit-spec shape: ghost-fixed input and work tapes, output
    accumulator holding `ys`. -/
def EmitPred (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool) : TapePred n :=
  fun inp work out => inp = inp₀ ∧ work = work₀ ∧ OutAcc ys out

/-- Emit-spec states pass through combinator phase boundaries unchanged:
    parked ghosts and the accumulator are fixed points of
    `transitionTape` / `transitionInput`. The `h_trans` obligation of
    `seqTM_hoareTime` for any two composed emitters. -/
theorem emitPred_transition {inp₀ : Tape} {work₀ : Fin n → Tape}
    (hinp₀ : Parked inp₀) (hworkAll : ∀ i, Parked (work₀ i)) (ys : List Bool) :
    ∀ inp work out, EmitPred inp₀ work₀ ys inp work out →
      EmitPred inp₀ work₀ ys (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  refine ⟨Parked.transitionInput_eq_self hinp₀, ?_, ?_⟩
  · funext i
    exact Parked.transitionTape_eq_self (hworkAll i)
  · rw [Parked.transitionTape_eq_self hout.parked]
    exact hout

-- ════════════════════════════════════════════════════════════════════════
-- emitLitTM: append one encoded literal
-- ════════════════════════════════════════════════════════════════════════

/-- **Append one encoded literal** with sign `s` and variable index read from
    register `r`: the bits `[s, s] ++ (2v trues) ++ [false, true]`
    (= `doubleBits (Lit.encodeRaw ⟨s, v⟩) ++ [false, true]`, the form literals
    take inside `Clause.encode`). -/
def emitLitTM (s : Bool) (r : Fin n) : TM n :=
  seqTM (emitBitsTM [s, s]) (seqTM (emitUnaryTM r) (emitBitsTM [false, true]))

/-- **`emitLitTM` Hoare specification.** Appends the encoded literal in
    `3v + 9` steps, preserving the input and work tapes (the scanned register
    included). The first `seqTM`-composed emitter spec; later emitters chain
    the same way. -/
theorem emitLitTM_hoareTime (s : Bool) (r : Fin n) (v : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (ys : List Bool) (hinp₀ : Parked inp₀)
    (hwork₀ : ∀ i, i ≠ r → Parked (work₀ i)) (hreg : IsReg v (work₀ r)) :
    (emitLitTM s r).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ ([s, s] ++ List.replicate (2 * v) true ++ [false, true])))
      (3 * v + 9) := by
  have hworkAll : ∀ i, Parked (work₀ i) := by
    intro i
    by_cases hir : i = r
    · subst hir; exact hreg.parked
    · exact hwork₀ i hir
  have h₂₃ := seqTM_hoareTime (emitUnaryTM r) (emitBitsTM [false, true])
    (emitUnaryTM_hoareTime r v inp₀ work₀ (ys ++ [s, s]) hinp₀ hwork₀ hreg)
    (emitPred_transition hinp₀ hworkAll _)
    (emitBitsTM_hoareTime [false, true] inp₀ work₀
      (ys ++ [s, s] ++ List.replicate (2 * v) true) hinp₀ hworkAll)
  have h := seqTM_hoareTime (emitBitsTM [s, s])
    (seqTM (emitUnaryTM r) (emitBitsTM [false, true]))
    (emitBitsTM_hoareTime [s, s] inp₀ work₀ ys hinp₀ hworkAll)
    (emitPred_transition hinp₀ hworkAll _)
    h₂₃
  refine h.consequence (fun _ _ _ hp => hp) ?_ (by simp; omega)
  rintro inp work out ⟨rfl, rfl, hout⟩
  refine ⟨rfl, rfl, ?_⟩
  rwa [List.append_assoc (ys ++ [s, s]), List.append_assoc ys,
    ← List.append_assoc [s, s]] at hout

end TM

end Complexity

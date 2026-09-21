/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Turing machines

This file defines the library's base model of computation: multi-tape
deterministic and nondeterministic Turing machines over a fixed four-symbol
alphabet, with named input/work/output tapes. The model's shape follows
Arora–Barak (*Computational Complexity: A Modern Approach*, Definitions
1.1–1.4 and 2.1), with the conventions below enforced structurally.

## Main definitions

- `Γ` — the tape alphabet `{0, 1, □, ▷}` (read alphabet)
- `Γw` — the writable alphabet `{0, 1, □}` (write alphabet; `▷` cannot be written)
- `Dir3` — three-way tape head direction (left, right, stay)
- `Tape` — a one-sided infinite tape; cell 0 is leftmost and permanently `▷`
- `Cfg` — a machine configuration with named tapes (input, work, output)
- `TM` — a deterministic multi-tape Turing machine (AB Definition 1.1)
- `NTM` — a nondeterministic TM with two transition functions (AB Definition 2.1)
- `TM.stepRel`, `TM.reaches`, `TM.reachesIn` — deterministic step relation and reachability
- `NTM.trace` — execute an NTM for a fixed choice sequence (canonical NTM execution)
- `Tape.HasOutput` — predicate: tape contains a given binary string as output
- `TM.ComputesInTime` — computing a function in bounded time (AB Definition 1.4)
- `TM.Computes` — computing a function (existential over time bound)
- `TM.Accepts`, `TM.AcceptsInTime` — deterministic acceptance
- `NTM.Accepts`, `NTM.AcceptsInTime` — nondeterministic acceptance (existential)
- `Cfg.WithinAuxSpace`, `Cfg.WithinDecisionSpace` — honest tape-space bounds
- `TM.DecidesInTime`, `NTM.DecidesInTime` — deciding a language within a time bound
- `TM.DecidesInTimeSpace` — deciding with simultaneous time and space bounds
- `NTM.acceptCount`, `NTM.acceptProb` — counting/probabilistic acceptance
- `TM.toNTM` — embed a DTM into an NTM

## Design notes

- **One-sided tapes**: `Tape` uses `head : ℕ` and `cells : ℕ → Γ`. Cell 0 is leftmost;
  moving left at position 0 is a no-op (`Nat` subtraction saturates).
- **Immutable cell 0**: `Tape.write` is a no-op when the head is at position 0, ensuring
  `▷` at cell 0 is permanent. Combined with `Γw` (which excludes `▷`), this guarantees `▷`
  appears only at cell 0 on every tape.
- **Read vs write alphabet**: The transition function reads `Γ = {0, 1, □, ▷}` but writes
  `Γw = {0, 1, □}`, so `δ` structurally cannot write `▷`.
- **Finite state**: `Q` carries `[Fintype Q]`; the state space is finite.
- **Output**: Read from cell 1 of the output tape (first cell after `▷`); machine output
  is the binary string written after `▷`.
- **Named tapes**: `Cfg` has `input`, `work`, `output` fields rather than `Fin k → Tape`,
  making the read-only/read-write distinction structural.
- **NTM execution**: Defined via `trace` (a fixed choice sequence), not a relational step.
-/


@[expose] public section

namespace Complexity

/-- The tape alphabet Γ = {0, 1, □, ▷}. -/
inductive Γ where
  | zero | one | blank | start
  deriving Repr, DecidableEq

instance : Fintype Γ where
  elems := {.zero, .one, .blank, .start}
  complete := fun x => by cases x <;> simp

instance : Inhabited Γ := ⟨Γ.blank⟩

/-- The writable alphabet Γw = {0, 1, □}. The start symbol `▷` cannot be written by a
    transition function — this is enforced structurally by using `Γw` in the output of `δ`. -/
inductive Γw where
  | zero | one | blank
  deriving Repr, DecidableEq

instance : Fintype Γw where
  elems := {.zero, .one, .blank}
  complete := fun x => by cases x <;> simp

/-- Embed a writable symbol into the full alphabet. -/
@[simp] def Γw.toΓ : Γw → Γ
  | .zero => .zero
  | .one => .one
  | .blank => .blank

instance : Coe Γw Γ where coe := Γw.toΓ

/-- A writable symbol is never the left-end marker. -/
theorem Γw.toΓ_ne_start (s : Γw) : s.toΓ ≠ Γ.start := by
  cases s <;> decide

/-- Convert a boolean to an alphabet symbol. -/
def Γ.ofBool : Bool → Γ
  | false => .zero
  | true => .one

/-- A Boolean tape symbol is never the left-end marker. -/
theorem Γ.ofBool_ne_start (b : Bool) : Γ.ofBool b ≠ Γ.start := by
  cases b <;> decide

/-- A Boolean tape symbol is never blank. -/
theorem Γ.ofBool_ne_blank (b : Bool) : Γ.ofBool b ≠ Γ.blank := by
  cases b <;> decide

/-- Convert a boolean to a writable symbol. -/
def Γw.ofBool : Bool → Γw
  | false => .zero
  | true => .one

theorem Γw.ofBool_toΓ (b : Bool) : (Γw.ofBool b).toΓ = Γ.ofBool b := by
  cases b <;> rfl

/-- Three-way tape head direction: left, right, or stay. -/
inductive Dir3 where
  | left | right | stay
  deriving Repr, DecidableEq

instance : Fintype Dir3 where
  elems := {.left, .right, .stay}
  complete := fun x => by cases x <;> simp

/-- A one-sided infinite tape. Cell 0 is the leftmost cell and permanently
    contains `▷`. The head cannot move left of cell 0 (moving left at position 0
    is a no-op via `Nat` subtraction). Writing at cell 0 is a no-op,
    preserving `▷`. -/
@[ext]
structure Tape where
  /-- The head position; cell 0 is the leftmost cell. -/
  head : ℕ
  /-- The tape contents, one symbol per cell. -/
  cells : ℕ → Γ

namespace Tape

/-- Read the symbol under the head. -/
def read (t : Tape) : Γ := t.cells t.head

/-- Write a symbol at the head position. Writing at cell 0 is a no-op,
    preserving the start symbol `▷`. -/
def write (t : Tape) (s : Γ) : Tape :=
  if t.head = 0 then t
  else { t with cells := Function.update t.cells t.head s }

/-- Writing changes tape contents but preserves the head position. -/
theorem write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp only [write]
  split <;> rfl

/-- Move the head according to a three-way direction.
    Moving left at position 0 stays at 0 (`Nat` subtraction saturates). -/
def move (t : Tape) (d : Dir3) : Tape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t

/-- Moving changes the head position but preserves tape contents. -/
theorem move_cells (t : Tape) (d : Dir3) : (t.move d).cells = t.cells := by
  cases d <;> rfl

/-- Moving changes the head position by at most one. -/
theorem head_move_le (t : Tape) (d : Dir3) : (t.move d).head ≤ t.head + 1 := by
  cases d <;> (simp only [move]; omega)

/-- The tape contains output `y : List Bool` starting at cell 1:
    cells 1 through |y| match `y`, and cell |y| + 1 is blank.
    Output is the binary string written on the output tape after `▷`. -/
def HasOutput (t : Tape) (y : List Bool) : Prop :=
  (∀ (i : ℕ) (h : i < y.length),
    t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
  t.cells (y.length + 1) = Γ.blank

/-- `HasOutput` depends only on the tape cells, not the head position. -/
theorem hasOutput_congr {t₁ t₂ : Tape} (h : t₁.cells = t₂.cells) (y : List Bool) :
    t₁.HasOutput y ↔ t₂.HasOutput y := by
  simp only [HasOutput, h]

instance decidableHasOutput (t : Tape) (y : List Bool) : Decidable (t.HasOutput y) :=
  if h : (∀ i : Fin y.length, t.cells (i.val + 1) = Γ.ofBool (y[i.val]'i.isLt)) ∧
         t.cells (y.length + 1) = Γ.blank
  then isTrue ⟨fun i hi => h.1 ⟨i, hi⟩, h.2⟩
  else isFalse (fun ⟨h1, h2⟩ => h ⟨fun i => h1 i.val i.isLt, h2⟩)

/-- Write a symbol and move in one step. -/
abbrev writeAndMove (t : Tape) (s : Γ) (d : Dir3) : Tape :=
  (t.write s).move d

/-- `t.StartInvariant` says the left-end marker `▷` sits at cell 0 and
    nowhere else — the standing shape of every tape reachable from an
    initial configuration, since writes exclude `▷` and cell 0 is
    immutable. -/
def StartInvariant (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧ ∀ j, 1 ≤ j → t.cells j ≠ Γ.start

/-- Under the invariant, a head at position ≥ 1 never reads `▷`. -/
theorem StartInvariant.read_ne_start {t : Tape} (h : t.StartInvariant)
    (hhead : 1 ≤ t.head) : t.read ≠ Γ.start := by
  simp only [read]; exact h.2 t.head hhead

/-- Writing (any `Γw` symbol) preserves the invariant. -/
theorem StartInvariant.write {t : Tape} (h : t.StartInvariant) (s : Γw) :
    (t.write s.toΓ).StartInvariant := by
  unfold Tape.write
  split
  · exact h
  · next hne =>
    refine ⟨?_, fun j hj => ?_⟩
    · show Function.update t.cells t.head s.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]; exact h.1
    · show Function.update t.cells t.head s.toΓ j ≠ Γ.start
      by_cases hje : j = t.head
      · subst hje
        rw [Function.update_self]
        cases s <;> simp [Γw.toΓ]
      · rw [Function.update_of_ne hje]; exact h.2 j hj

/-- Moving preserves the invariant (cells unchanged). -/
theorem StartInvariant.move {t : Tape} (h : t.StartInvariant) (d : Dir3) :
    (t.move d).StartInvariant := by
  cases d <;> exact h

/-- Writing a `Γw` symbol and moving preserves the invariant. -/
theorem StartInvariant.writeAndMove {t : Tape} (h : t.StartInvariant)
    (s : Γw) (d : Dir3) : (t.writeAndMove s.toΓ d).StartInvariant :=
  (h.write s).move d

/-- One write-and-move step advances the head by at most one. -/
theorem head_writeAndMove_le (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).head ≤ t.head + 1 := by
  have h := head_move_le (t.write s) d
  rwa [write_head] at h

end Tape

/-- Initialize a tape: `▷` at cell 0, `contents` at cells 1, 2, ..., `□` elsewhere.
    Head starts at position 0 (on `▷`). -/
def Tape.init (contents : List Γ) : Tape where
  head := 0
  cells := fun i =>
    if i = 0 then Γ.start
    else (contents[i - 1]?).getD Γ.blank

/-- An initialized tape starts with its head on the left-end marker. -/
@[simp] theorem Tape.init_head (contents : List Γ) :
    (Tape.init contents).head = 0 := rfl

/-- Cell zero of an initialized tape is the left-end marker. -/
@[simp] theorem Tape.init_cells_zero (contents : List Γ) :
    (Tape.init contents).cells 0 = Γ.start := by
  simp [Tape.init]

/-- Cell `i + 1` of an initialized tape contains item `i`, or blank when `i`
    lies beyond the initialized contents. -/
theorem Tape.init_cells_succ (contents : List Γ) (i : ℕ) :
    (Tape.init contents).cells (i + 1) = (contents[i]?).getD Γ.blank := by
  simp [Tape.init]

/-- Cells beyond the initialized contents are blank. -/
theorem Tape.init_cells_ge (contents : List Γ) (i : ℕ)
    (h : contents.length ≤ i) :
    (Tape.init contents).cells (i + 1) = Γ.blank := by
  rw [Tape.init_cells_succ, List.getElem?_eq_none h]
  rfl

/-- Every positive-indexed cell of the empty initialized tape is blank. -/
@[simp] theorem Tape.init_nil_cells_succ (i : ℕ) :
    (Tape.init []).cells (i + 1) = Γ.blank := by
  exact Tape.init_cells_ge [] i (by simp)

/-- No positive-indexed cell of the empty initialized tape is a start marker. -/
theorem Tape.init_nil_cells_ne_start (j : ℕ) (hj : 1 ≤ j) :
    (Tape.init []).cells j ≠ Γ.start := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Tape.init_nil_cells_succ]
  decide

/-- Within the initialized Boolean contents, cell `i + 1` stores bit `i`. -/
theorem Tape.init_ofBool_cells_lt (contents : List Bool) (i : ℕ)
    (h : i < contents.length) :
    (Tape.init (contents.map Γ.ofBool)).cells (i + 1) = Γ.ofBool (contents[i]'h) := by
  rw [Tape.init_cells_succ]
  have hmap : i < (contents.map Γ.ofBool).length := by simpa using h
  rw [List.getElem?_eq_getElem hmap]
  simp

/-- Beyond the initialized Boolean contents, cell `i + 1` is blank. -/
theorem Tape.init_ofBool_cells_ge (contents : List Bool) (i : ℕ)
    (h : contents.length ≤ i) :
    (Tape.init (contents.map Γ.ofBool)).cells (i + 1) = Γ.blank := by
  exact Tape.init_cells_ge (contents.map Γ.ofBool) i (by simpa using h)

/-- No positive-indexed cell of a Boolean-initialized tape contains the
    left-end marker. -/
theorem Tape.init_ofBool_cells_ne_start (contents : List Bool) (j : ℕ) (hj : 1 ≤ j) :
    (Tape.init (contents.map Γ.ofBool)).cells j ≠ Γ.start := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < contents.length
  · rw [Tape.init_ofBool_cells_lt contents i hi]
    exact Γ.ofBool_ne_start _
  · rw [Tape.init_ofBool_cells_ge contents i (Nat.le_of_not_gt hi)]
    decide

/-- Moving an empty initialized tape to cell one reads blank. -/
@[simp] theorem Tape.init_nil_move_right_read :
    ((Tape.init []).move Dir3.right).read = Γ.blank := by
  simp [Tape.read, Tape.move]

/-- A Boolean-initialized tape moved to its first data cell never reads the
    left-end marker. -/
theorem Tape.init_ofBool_move_right_read_ne_start (contents : List Bool) :
    ((Tape.init (contents.map Γ.ofBool)).move Dir3.right).read ≠ Γ.start := by
  simp only [Tape.read, Tape.move]
  exact Tape.init_ofBool_cells_ne_start contents 1 (by omega)

/-- An initialized tape whose contents avoid `▷` satisfies the invariant. -/
theorem Tape.StartInvariant.init (xs : List Γ) (hxs : ∀ a ∈ xs, a ≠ Γ.start) :
    (Tape.init xs).StartInvariant := by
  refine ⟨rfl, ?_⟩
  intro j hj
  simp only [Tape.init, show j ≠ 0 by omega, ↓reduceIte]
  cases h : xs[j - 1]? with
  | none => simp
  | some a =>
    simp only [Option.getD_some]
    exact hxs a (List.mem_of_getElem? h)

/-- A Boolean-initialized tape satisfies the invariant. -/
theorem Tape.StartInvariant.init_ofBool (xs : List Bool) :
    (Tape.init (xs.map Γ.ofBool)).StartInvariant := by
  refine Tape.StartInvariant.init _ ?_
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  cases b <;> simp [Γ.ofBool]

/-- The empty initialized tape satisfies the invariant. -/
theorem Tape.StartInvariant.init_nil : (Tape.init []).StartInvariant := by
  refine ⟨rfl, ?_⟩
  intro j hj
  simp only [Tape.init, show j ≠ 0 by omega, ↓reduceIte]
  simp

/-- After stepping onto cell 1 of an empty initialized tape, no positive
    cell holds the left-end marker. -/
theorem Tape.init_nil_move_right_cells_ne_start (j : ℕ) (hj : j ≥ 1) :
    ((Tape.init []).move Dir3.right).cells j ≠ Γ.start := by
  rw [Tape.move_cells]
  simp [Tape.init, show j ≠ 0 by omega]

/-- Moving the head does not introduce a left-end marker in the positive cells
    of a Boolean-initialized tape. -/
theorem Tape.init_ofBool_move_right_cells_ne_start (contents : List Bool) :
    ∀ j, 1 ≤ j →
      ((Tape.init (contents.map Γ.ofBool)).move Dir3.right).cells j ≠ Γ.start := by
  intro j hj
  rw [Tape.move_cells]
  exact Tape.init_ofBool_cells_ne_start contents j hj

/-- A language is a set of binary strings. -/
abbrev Language := Set (List Bool)

/-- A configuration of a Turing machine with `n` work tapes:
    a read-only input tape, `n` read-write work tapes, and a read-write output tape. -/
structure Cfg (n : ℕ) (Q : Type) where
  /-- The current machine state. -/
  state : Q
  /-- The read-only input tape. -/
  input : Tape
  /-- The `n` read-write work tapes. -/
  work : Fin n → Tape
  /-- The read-write output tape. -/
  output : Tape

namespace Cfg

/-- Two machine configurations are equal when their named components agree. -/
@[ext] theorem ext {c c' : Cfg n Q}
    (hstate : c.state = c'.state) (hinput : c.input = c'.input)
    (hwork : c.work = c'.work) (houtput : c.output = c'.output) : c = c' := by
  cases c
  cases c'
  simp_all

/-- Initial configuration for any TM: input on the input tape, all tapes start with `▷`. -/
abbrev init (qstart : Q) (x : List Bool) : Cfg n Q :=
  { state := qstart
    input := Tape.init (x.map Γ.ofBool)
    work := fun _ => Tape.init []
    output := Tape.init [] }

/-- A configuration is halted when its state equals the halt state. -/
abbrev isHalted (qhalt : Q) (c : Cfg n Q) : Prop :=
  c.state = qhalt

/-- The auxiliary-space bound for a configuration on an input of length
    `inputLength`. Work-tape cells through `space` are available, while the
    input itself and its first trailing blank are free; travel farther into the
    input tape's blank tail is charged against `space`.

    This predicate deliberately omits the output tape. It is suitable for
    function computation only when the machine also satisfies the one-way
    output discipline `TM.IsTransducer`. -/
def WithinAuxSpace (c : Cfg n Q) (inputLength space : ℕ) : Prop :=
  (∀ i, (c.work i).head ≤ space) ∧
  c.input.head ≤ inputLength + space + 1

/-- The space bound for a language-decider configuration. In addition to
    `WithinAuxSpace`, the output head is bounded by `space + 1`: cell 1 is the
    free verdict cell, and any farther two-way output-tape travel is charged. -/
def WithinDecisionSpace (c : Cfg n Q) (inputLength space : ℕ) : Prop :=
  c.WithinAuxSpace inputLength space ∧ c.output.head ≤ space + 1

end Cfg

/-- A deterministic Turing machine with `n` work tapes.

    The machine has a read-only input tape, `n` read-write work tapes, and a read-write
    output tape. The transition function reads `Γ` from all tape heads but writes only
    `Γw` (excluding `▷`) to work and output tapes. `Q` is finite. -/
structure TM (n : ℕ) where
  /-- The (finite) type of machine states. -/
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  /-- The designated start state. -/
  qstart : Q
  /-- The designated halt state. -/
  qhalt : Q
  /-- The transition function: from the current state and the symbols under
      the input, work, and output heads, produce the next state, the symbols
      to write on the work and output tapes, and a direction for every head. -/
  δ : Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  /-- Reading the left-end marker forces that head to move right, so no head
      ever falls off the left edge. -/
  δ_right_of_start : ∀ (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

attribute [instance] TM.decEq TM.finQ

/-- A nondeterministic Turing machine with two transition functions.

    The same structure is used for probabilistic TMs — only the acceptance
    criterion differs (existential for NTM, counting for PTM). `Q` is finite. -/
structure NTM (n : ℕ) where
  /-- The (finite) type of machine states. -/
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  /-- The designated start state. -/
  qstart : Q
  /-- The designated halt state. -/
  qhalt : Q
  /-- The two transition functions, selected by the `Bool` choice bit; each
      has the same shape as the deterministic `TM.δ`. -/
  δ : Bool → Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  /-- Reading the left-end marker forces that head to move right, on both
      branches. -/
  δ_right_of_start : ∀ (b : Bool) (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ b q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

attribute [instance] NTM.decEq NTM.finQ

namespace TM

variable {n : ℕ}

/-- Step a deterministic TM by one step. Returns `none` if halted. -/
def step (tm : TM n) (c : Cfg n tm.Q) : Option (Cfg n tm.Q) :=
  if c.state = tm.qhalt then none
  else
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    some
      { state := q'
        input := c.input.move inDir
        work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
        output := c.output.writeAndMove outWrite outDir }

/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
abbrev initCfg (tm : TM n) (x : List Bool) : Cfg n tm.Q :=
  Cfg.init tm.qstart x

/-- A configuration is halted when its state is `qhalt`. -/
abbrev halted (tm : TM n) (c : Cfg n tm.Q) : Prop :=
  Cfg.isHalted tm.qhalt c

/-- If `step` returns `some`, the machine was not halted. -/
theorem state_ne_qhalt_of_step {tm : TM n} {c c' : Cfg n tm.Q}
    (h : tm.step c = some c') : c.state ≠ tm.qhalt :=
  fun heq => by simp [step, heq] at h

/-- One-step relation for a deterministic TM. -/
def stepRel (tm : TM n) (c c' : Cfg n tm.Q) : Prop := tm.step c = some c'

/-- Reflexive-transitive closure of the step relation. -/
def reaches (tm : TM n) : Cfg n tm.Q → Cfg n tm.Q → Prop :=
  Relation.ReflTransGen tm.stepRel

/-- Reachability in exactly `t` steps. -/
inductive reachesIn (tm : TM n) : ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero : reachesIn tm 0 c c
  | step : tm.step c = some c'' → reachesIn tm t c'' c' → reachesIn tm (t + 1) c c'

/-- DTM accepts `x`: reaches `qhalt` with output cell 1 (after `▷`) = `1`. -/
def Accepts (tm : TM n) (x : List Bool) : Prop :=
  ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧ c'.output.cells 1 = Γ.one

/-- DTM accepts `x` within `T` steps. -/
def AcceptsInTime (tm : TM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ c' t, t ≤ T ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.cells 1 = Γ.one

/-- DTM decides `L` within time bound `T(n)`: halts on all inputs within `T(|x|)` steps,
    outputting `1` for `x ∈ L` and `0` for `x ∉ L`. -/
def DecidesInTime (tm : TM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)

/-- DTM computes function `f` in time `T(n)`:
    for every input `x`, the machine halts within `T(|x|)` steps with `f(x)`
    written on the output tape. -/
def ComputesInTime (tm : TM n) (f : List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.HasOutput (f x)

/-- DTM computes function `f` (existential version of `ComputesInTime`). -/
def Computes (tm : TM n) (f : List Bool → List Bool) : Prop :=
  ∃ T, tm.ComputesInTime f T

/-- DTM decides `L` using at most `S(|x|)` auxiliary space. Every reachable
    configuration has work heads at position at most `S(|x|)`, input head at
    position at most `|x| + S(|x|) + 1`, and output head at position at most
    `S(|x|) + 1`. Thus the input region, its first trailing blank, and output
    verdict cell 1 are free, but neither infinite tape can become uncharged
    two-way workspace. The machine halts on all inputs with correct output. -/
def DecidesInSpace (tm : TM n) (L : Language) (S : ℕ → ℕ) : Prop :=
  (∀ x c', tm.reaches (tm.initCfg x) c' →
    c'.WithinDecisionSpace x.length (S x.length)) ∧
  ∀ x, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
    (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)

/-- DTM decides `L` within time `T(|x|)` and space `S(|x|)` simultaneously:
    a single machine halts in bounded time with correct output, and every
    reachable configuration satisfies the honest auxiliary-space convention of
    `Cfg.WithinDecisionSpace`. -/
def DecidesInTimeSpace (tm : TM n) (L : Language) (T S : ℕ → ℕ) : Prop :=
  (∀ x c', tm.reaches (tm.initCfg x) c' →
    c'.WithinDecisionSpace x.length (S x.length)) ∧
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)

/-- The output tape head never moves left — the machine is a *transducer*.
    This prevents earlier output from being reread as workspace while allowing
    unbounded output length. `ComputesInSpace` requires this discipline; the
    decision-space predicates separately bound two-way output-head travel. -/
def IsTransducer (tm : TM n) : Prop :=
  ∀ q iHead wHeads oHead,
    let (_, _, _, _, _, outDir) := tm.δ q iHead wHeads oHead
    outDir ≠ Dir3.left

/-- DTM computes function `f` using at most `S(|x|)` auxiliary space.
    Work-tape travel and input-head travel beyond the input's first trailing
    blank are bounded by `Cfg.WithinAuxSpace`. The output length is not bounded:
    instead, `IsTransducer` makes the output one-way so it cannot serve as
    read-write workspace. -/
def ComputesInSpace (tm : TM n) (f : List Bool → List Bool) (S : ℕ → ℕ) : Prop :=
  tm.IsTransducer ∧
  (∀ x c', tm.reaches (tm.initCfg x) c' → c'.WithinAuxSpace x.length (S x.length)) ∧
  ∀ x, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧ c'.output.HasOutput (f x)

/-- Transitivity: if `c₁` reaches `c₂` in `t₁` steps and `c₂` reaches `c₃`
    in `t₂` steps, then `c₁` reaches `c₃` in `t₁ + t₂` steps. -/
theorem reachesIn_trans (tm : TM n) {t₁ t₂ : ℕ} {c₁ c₂ c₃ : Cfg n tm.Q}
    (h₁ : tm.reachesIn t₁ c₁ c₂) (h₂ : tm.reachesIn t₂ c₂ c₃) :
    tm.reachesIn (t₁ + t₂) c₁ c₃ := by
  induction h₁ with
  | zero => simp; exact h₂
  | step hstep _ ih =>
    show tm.reachesIn (_ + 1 + t₂) _ _
    rw [Nat.add_right_comm]
    exact reachesIn.step hstep (ih h₂)

/-- Bounded reachability implies unbounded reachability. -/
theorem reaches_of_reachesIn {tm : TM n} {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') : tm.reaches c c' := by
  induction h with
  | zero => exact Relation.ReflTransGen.refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs ih

/-- `step` returns `none` exactly when the configuration is halted. The two ways
    a DTM can "stop" — no successor configuration and being in `qhalt` —
    coincide. -/
theorem step_eq_none_iff_halted {tm : TM n} {c : Cfg n tm.Q} :
    tm.step c = none ↔ c.state = tm.qhalt := by
  by_cases h : c.state = tm.qhalt <;> simp [step, h]

/-- Append a single step to the end of a run: reaching `c'` in `t` steps and then
    stepping once to `c''` gives a run of `t + 1` steps. The `snoc` counterpart to
    the `cons`-shaped `reachesIn.step`. -/
theorem reachesIn_snoc {tm : TM n} {t : ℕ} {c c' c'' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') (hstep : tm.step c' = some c'') :
    tm.reachesIn (t + 1) c c'' :=
  tm.reachesIn_trans h (reachesIn.step hstep reachesIn.zero)

/-- A zero-step run goes nowhere. Inversion form of `reachesIn.zero`, usable
    when the machine is a compound expression on which `cases` cannot
    abstract the configuration indices. -/
theorem reachesIn_zero_iff {tm : TM n} {c c' : Cfg n tm.Q} :
    tm.reachesIn 0 c c' ↔ c = c' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ reachesIn.zero⟩

/-- A run of `t + 1` steps factors as one step followed by a run of `t`
    steps. Inversion form of `reachesIn.step`. -/
theorem reachesIn_succ_iff {tm : TM n} {t : ℕ} {c c' : Cfg n tm.Q} :
    tm.reachesIn (t + 1) c c' ↔
      ∃ c'', tm.step c = some c'' ∧ tm.reachesIn t c'' c' :=
  ⟨fun h => by cases h with | step hstep hrest => exact ⟨_, hstep, hrest⟩,
   fun ⟨_, hstep, hrest⟩ => reachesIn.step hstep hrest⟩

/-- `AcceptsInTime` implies `Accepts` — forget the time bound. -/
theorem accepts_of_acceptsInTime {tm : TM n} {x : List Bool} {T : ℕ}
    (h : tm.AcceptsInTime x T) : tm.Accepts x := by
  obtain ⟨c', t, _, hreach, hhalt, hcell⟩ := h
  exact ⟨c', reaches_of_reachesIn hreach, hhalt, hcell⟩

/-- DTM acceptance is monotone in the time bound. -/
theorem AcceptsInTime.mono {tm : TM n} {x : List Bool} {T T' : ℕ} (hle : T ≤ T')
    (h : tm.AcceptsInTime x T) : tm.AcceptsInTime x T' := by
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := h
  exact ⟨c', t, ht.trans hle, hreach, hhalt, hout⟩

/-- DTM decision is monotone under pointwise enlargement of the time bound. -/
theorem DecidesInTime.mono {tm : TM n} {L : Language} {T T' : ℕ → ℕ}
    (hle : ∀ m, T m ≤ T' m) (h : tm.DecidesInTime L T) : tm.DecidesInTime L T' := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ := h x
  exact ⟨c', t, ht.trans (hle x.length), hreach, hhalt, hyes, hno⟩

/-- DTM computation is monotone under pointwise enlargement of the time bound. -/
theorem ComputesInTime.mono {tm : TM n} {f : List Bool → List Bool}
    {T T' : ℕ → ℕ} (hle : ∀ m, T m ≤ T' m) (h : tm.ComputesInTime f T) :
    tm.ComputesInTime f T' := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := h x
  exact ⟨c', t, ht.trans (hle x.length), hreach, hhalt, hout⟩

end TM

namespace NTM

variable {n : ℕ}

/-- Execute an NTM for `T` steps with a fixed choice sequence.
    Stops early if the machine reaches `qhalt`. -/
def trace (tm : NTM n) :
    (T : ℕ) → (Fin T → Bool) → Cfg n tm.Q → Cfg n tm.Q
  | 0, _, c => c
  | T + 1, choices, c =>
    if c.state = tm.qhalt then c
    else
      let b := choices ⟨0, Nat.zero_lt_succ T⟩
      let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
        tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
      let c' : Cfg n tm.Q :=
        { state := q'
          input := c.input.move inDir
          work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
          output := c.output.writeAndMove outWrite outDir }
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c'

/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
abbrev initCfg (tm : NTM n) (x : List Bool) : Cfg n tm.Q :=
  Cfg.init tm.qstart x

/-- A configuration is halted when its state is `qhalt`. -/
abbrev halted (tm : NTM n) (c : Cfg n tm.Q) : Prop :=
  Cfg.isHalted tm.qhalt c

/-- Once halted, the NTM trace stays at the same configuration regardless of
    the remaining choices. -/
theorem trace_halted (tm : NTM n) {c : Cfg n tm.Q}
    (T : ℕ) (choices : Fin T → Bool) (h : tm.halted c) :
    tm.trace T choices c = c := by
  induction T with
  | zero => rfl
  | succ T _ => simp [NTM.trace, h]

/-- An NTM trace preserves the unique left-end marker on the input, work,
    and output tapes. -/
theorem trace_startInvariant (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q)
    (hinp : c.input.StartInvariant)
    (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    (tm.trace T choices c).input.StartInvariant ∧
      (∀ i, ((tm.trace T choices c).work i).StartInvariant) ∧
      (tm.trace T choices c).output.StartInvariant := by
  induction T generalizing c with
  | zero => exact ⟨hinp, hwork, hout⟩
  | succ T ih =>
      by_cases hhalt : c.state = tm.qhalt
      · simpa [trace, hhalt] using And.intro hinp (And.intro hwork hout)
      · simp only [trace, hhalt, if_false]
        apply ih
        · exact hinp.move _
        · intro i
          exact (hwork i).writeAndMove _ _
        · exact hout.writeAndMove _ _

/-- Every tape in a trace from `initCfg` has a unique left-end marker. -/
theorem trace_initCfg_startInvariant (tm : NTM n) (x : List Bool) (T : ℕ)
    (choices : Fin T → Bool) :
    (tm.trace T choices (tm.initCfg x)).input.StartInvariant ∧
      (∀ i, ((tm.trace T choices (tm.initCfg x)).work i).StartInvariant) ∧
      (tm.trace T choices (tm.initCfg x)).output.StartInvariant :=
  tm.trace_startInvariant T choices (tm.initCfg x)
    (Tape.StartInvariant.init_ofBool x) (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil

/-- NTM accepts `x`: there exists a time bound and choice sequence leading to
    `qhalt` with output cell 1 = `1`. -/
def Accepts (tm : NTM n) (x : List Bool) : Prop :=
  ∃ (T : ℕ) (choices : Fin T → Bool),
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one

/-- NTM accepts `x` within `T` steps: there exists a choice sequence of length `T`
    leading to `qhalt` with output cell 1 = `1`. -/
def AcceptsInTime (tm : NTM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ choices : Fin T → Bool,
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one

/-- `AcceptsInTime` implies `Accepts` — package the time bound existentially. -/
theorem accepts_of_acceptsInTime {tm : NTM n} {x : List Bool} {T : ℕ}
    (h : tm.AcceptsInTime x T) : tm.Accepts x :=
  ⟨T, h⟩

/-- `Accepts` is exactly `∃ T, AcceptsInTime x T`. -/
theorem accepts_iff_exists_acceptsInTime {tm : NTM n} {x : List Bool} :
    tm.Accepts x ↔ ∃ T, tm.AcceptsInTime x T := Iff.rfl

/-- Running the NTM trace for more steps preserves the final configuration:
    if the machine halts within `T` steps and the extended choice sequence
    agrees with the original on the first `T` positions, the extra steps are
    no-ops. -/
theorem trace_mono (tm : NTM n) {T T' : ℕ} (hle : T ≤ T')
    {choices : Fin T → Bool} {choices' : Fin T' → Bool} {c : Cfg n tm.Q}
    (hagree : ∀ i : Fin T, choices' ⟨i.val, by omega⟩ = choices i)
    (h : tm.halted (tm.trace T choices c)) :
    tm.trace T' choices' c = tm.trace T choices c := by
  induction T generalizing T' choices' c with
  | zero =>
    have hhalt : tm.halted c := by simpa [NTM.trace] using h
    simpa [NTM.trace] using tm.trace_halted T' choices' hhalt
  | succ T ih =>
    rcases T' with _ | T'
    · omega
    by_cases hc : c.state = tm.qhalt
    · have hcT : tm.trace (T + 1) choices c = c := by simp [NTM.trace, hc]
      have hcT' : tm.trace (T' + 1) choices' c = c := by simp [NTM.trace, hc]
      rw [hcT, hcT']
    · have hch0 := hagree ⟨0, Nat.zero_lt_succ _⟩
      have hle' : T ≤ T' := Nat.le_of_succ_le_succ hle
      simp only [NTM.trace, hc, hch0, if_false] at h ⊢
      exact ih hle' (fun i => hagree ⟨i.val + 1, by omega⟩) h

/-- NTM acceptance is monotone in the time bound: `AcceptsInTime x T` implies
    `AcceptsInTime x T'` for any `T' ≥ T`. Extra steps are no-ops once halted. -/
theorem AcceptsInTime.mono {tm : NTM n} {x : List Bool} {T T' : ℕ} (hle : T ≤ T')
    (h : tm.AcceptsInTime x T) : tm.AcceptsInTime x T' := by
  obtain ⟨choices, hhalt, hout⟩ := h
  let choices' : Fin T' → Bool := fun i =>
    if hi : i.val < T then choices ⟨i.val, hi⟩ else false
  have heq := tm.trace_mono hle (choices := choices) (choices' := choices')
    (c := tm.initCfg x) (fun i => by simp [choices', i.isLt]) hhalt
  exact ⟨choices', heq ▸ hhalt, heq ▸ hout⟩

/-- All computation paths of the NTM halt within `T(|x|)` steps, for every
    input `x` and every choice sequence. This is the core time-boundedness
    condition shared by `DecidesInTime`, `BPTIME`, and `NTM.IsPPT`. -/
def AllPathsHaltIn (tm : NTM n) (T : ℕ → ℕ) : Prop :=
  ∀ x (choices : Fin (T x.length) → Bool),
    tm.halted (tm.trace (T x.length) choices (tm.initCfg x))

/-- NTM decides `L` within time bound `T(n)`:
    all computation paths halt within `T(|x|)` steps, and accepting paths exist
    iff `x ∈ L` (AB Definition 2.1). -/
def DecidesInTime (tm : NTM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  tm.AllPathsHaltIn T ∧
  (∀ x, x ∈ L ↔ tm.AcceptsInTime x (T x.length))

/-- All-paths halting is monotone in the time bound: once halted, the extra
    steps are no-ops. -/
theorem AllPathsHaltIn.mono {tm : NTM n} {T T' : ℕ → ℕ} (hle : ∀ m, T m ≤ T' m)
    (h : tm.AllPathsHaltIn T) : tm.AllPathsHaltIn T' := by
  intro x choices'
  have heq := tm.trace_mono (hle x.length)
    (choices := fun i => choices' ⟨i.val, lt_of_lt_of_le i.isLt (hle x.length)⟩)
    (choices' := choices') (c := tm.initCfg x) (fun i => rfl)
    (h x fun i => choices' ⟨i.val, lt_of_lt_of_le i.isLt (hle x.length)⟩)
  rw [heq]
  exact h x _

/-- With all paths halting within `T`, timed acceptance transfers DOWN from any
    pointwise-larger bound: by `T(|x|)` every path is already frozen. -/
theorem acceptsInTime_of_le_of_allPathsHaltIn {tm : NTM n} {T T' : ℕ → ℕ}
    {x : List Bool} (hle : ∀ m, T m ≤ T' m) (hN : tm.AllPathsHaltIn T)
    (h : tm.AcceptsInTime x (T' x.length)) : tm.AcceptsInTime x (T x.length) := by
  obtain ⟨choices', hhalt', hout'⟩ := h
  have heq := tm.trace_mono (hle x.length)
    (choices := fun i => choices' ⟨i.val, lt_of_lt_of_le i.isLt (hle x.length)⟩)
    (choices' := choices') (c := tm.initCfg x) (fun i => rfl)
    (hN x fun i => choices' ⟨i.val, lt_of_lt_of_le i.isLt (hle x.length)⟩)
  exact ⟨_, hN x _, by rw [heq] at hout'; exact hout'⟩

/-- Deciding within `T` transfers to any pointwise-larger bound `T'`: halting
    is monotone, and acceptance transfers both ways (up by monotonicity, down
    by the all-paths-halt freeze). -/
theorem DecidesInTime.mono {tm : NTM n} {L : Language} {T T' : ℕ → ℕ}
    (hle : ∀ m, T m ≤ T' m) (h : tm.DecidesInTime L T) : tm.DecidesInTime L T' :=
  ⟨h.1.mono hle, fun x => (h.2 x).trans
    ⟨fun ha => AcceptsInTime.mono (hle x.length) ha,
     fun ha => acceptsInTime_of_le_of_allPathsHaltIn hle h.1 ha⟩⟩

/-- Count of accepting choice sequences of length `T`.

    Meaningful when the machine halts on all paths within `T` steps — use in conjunction
    with `NTM.DecidesInTime` or an explicit all-paths-halt hypothesis. -/
noncomputable def acceptCount (tm : NTM n) (x : List Bool) (T : ℕ) : ℕ :=
  (Finset.univ.filter fun (choices : Fin T → Bool) =>
    let c' := tm.trace T choices (tm.initCfg x)
    c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one).card

/-- Acceptance probability = |accepting paths| / 2^T.

    Meaningful when the machine halts on all paths within `T` steps. -/
noncomputable def acceptProb (tm : NTM n) (x : List Bool) (T : ℕ) : ℚ :=
  (tm.acceptCount x T : ℚ) / (2 ^ T : ℚ)

/-- Count of choice sequences of length `T` on which the machine halts with
    output `y` (using `Tape.HasOutput`).

    Meaningful when the machine halts on all paths within `T` steps. -/
noncomputable def outputCount (tm : NTM n) (x : List Bool) (T : ℕ)
    (y : List Bool) : ℕ :=
  (Finset.univ.filter fun (choices : Fin T → Bool) =>
    let c' := tm.trace T choices (tm.initCfg x)
    c'.state = tm.qhalt ∧ c'.output.HasOutput y).card

/-- Probability that the machine outputs `y` on input `x` =
    |output-matching paths| / 2^T.

    Meaningful when the machine halts on all paths within `T` steps.
    This generalizes `acceptProb` from accept/reject to arbitrary output
    strings, as needed for cryptographic definitions. -/
noncomputable def outputProb (tm : NTM n) (x : List Bool) (T : ℕ)
    (y : List Bool) : ℚ :=
  (tm.outputCount x T y : ℚ) / (2 ^ T : ℚ)

/-- NTM decides `L` using at most `S(|x|)` auxiliary space. Every intermediate
    configuration on every path obeys `Cfg.WithinDecisionSpace`: work heads are
    bounded by `S`, the finite input plus first blank is free but farther input
    travel is charged, and only output verdict cell 1 is free. There exists a
    time bound within which all paths halt and decide correctly. -/
def DecidesInSpace (tm : NTM n) (L : Language) (S : ℕ → ℕ) : Prop :=
  ∃ T, tm.DecidesInTime L T ∧
    ∀ x (choices : Fin (T x.length) → Bool) (t' : ℕ) (ht : t' ≤ T x.length),
      (tm.trace t' (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x)).WithinDecisionSpace
        x.length (S x.length)

/-- The output tape head never moves left — the machine is a *transducer*.
    This prevents earlier output from being reread as workspace while allowing
    unbounded output length. Decision-space predicates separately bound two-way
    output-head travel. -/
def IsTransducer (tm : NTM n) : Prop :=
  ∀ b q iHead wHeads oHead,
    let (_, _, _, _, _, outDir) := tm.δ b q iHead wHeads oHead
    outDir ≠ Dir3.left

end NTM

/-- Embed a DTM into an NTM by using the same transition for both choices. -/
def TM.toNTM (tm : TM n) : NTM n where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := fun _ => tm.δ
  δ_right_of_start := fun _ => tm.δ_right_of_start

end Complexity

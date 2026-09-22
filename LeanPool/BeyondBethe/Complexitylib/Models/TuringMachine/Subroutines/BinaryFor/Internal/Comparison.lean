/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Control
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits
public import Mathlib.Algebra.Order.Group.Nat
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Canonical binary count-up loops — comparison internals

This module proves the exact full-width comparison run used by
`TM.binaryForTM`.  The scanner compares two canonical little-endian natural
numbers without changing their contents, then rewinds both cursors.  Under
the loop invariant `value ≤ limitValue`, the run takes exactly
`binaryForCompareTime limitValue` steps and branches to the composite
iteration precisely below the limit, or to `done` precisely at equality.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The alphabet symbol at one zero-based position of a blank-padded binary
string. -/
private def paddedBinarySymbol (bits : List Bool) (i : ℕ) : Γ :=
  if h : i < bits.length then Γ.ofBool bits[i] else Γ.blank

private theorem paddedBinarySymbol_of_lt {bits : List Bool} {i : ℕ}
    (h : i < bits.length) :
    paddedBinarySymbol bits i = Γ.ofBool bits[i] := by
  simp only [paddedBinarySymbol, dif_pos h]

private theorem paddedBinarySymbol_of_ge {bits : List Bool} {i : ℕ}
    (h : bits.length ≤ i) :
    paddedBinarySymbol bits i = Γ.blank := by
  simp only [paddedBinarySymbol, dite_eq_right (Nat.not_lt.mpr h)]

/-- Boolean equality accumulated through the first `width` padded symbols. -/
private def paddedBinaryPrefixEq (left right : List Bool) : ℕ → Bool
  | 0 => true
  | width + 1 =>
      paddedBinaryPrefixEq left right width &&
        decide (paddedBinarySymbol left width = paddedBinarySymbol right width)

private theorem paddedBinaryPrefixEq_symbol_eq {left right : List Bool}
    {width i : ℕ} (heq : paddedBinaryPrefixEq left right width = true)
    (hi : i < width) :
    paddedBinarySymbol left i = paddedBinarySymbol right i := by
  induction width with
  | zero => omega
  | succ width ih =>
      simp only [paddedBinaryPrefixEq, Bool.and_eq_true, decide_eq_true_eq] at heq
      by_cases hlast : i = width
      · simpa [hlast] using heq.2
      · exact ih heq.1 (by omega)

private theorem paddedBinaryPrefixEq_self (bits : List Bool) (width : ℕ) :
    paddedBinaryPrefixEq bits bits width = true := by
  induction width with
  | zero => rfl
  | succ width ih => simp [paddedBinaryPrefixEq, ih]

private theorem ofBool_injective {left right : Bool}
    (h : Γ.ofBool left = Γ.ofBool right) : left = right := by
  cases left <;> cases right <;> simp [Γ.ofBool] at h ⊢

private theorem paddedBinaryPrefixEq_eq_true_iff {left right : List Bool}
    {width : ℕ} (hleft : left.length ≤ width)
    (hright : right.length ≤ width) :
    paddedBinaryPrefixEq left right width = true ↔ left = right := by
  constructor
  · intro heq
    have hlen : left.length = right.length := by
      apply Nat.le_antisymm
      · by_contra hnot
        have hlt : right.length < left.length := Nat.lt_of_not_ge hnot
        have hsymbol := paddedBinaryPrefixEq_symbol_eq heq
          (lt_of_lt_of_le hlt hleft)
        rw [paddedBinarySymbol_of_lt hlt,
          paddedBinarySymbol_of_ge le_rfl] at hsymbol
        exact Γ.ofBool_ne_blank _ hsymbol
      · by_contra hnot
        have hlt : left.length < right.length := Nat.lt_of_not_ge hnot
        have hsymbol := paddedBinaryPrefixEq_symbol_eq heq
          (lt_of_lt_of_le hlt hright)
        rw [paddedBinarySymbol_of_ge le_rfl,
          paddedBinarySymbol_of_lt hlt] at hsymbol
        exact Γ.ofBool_ne_blank _ hsymbol.symm
    apply List.ext_get hlen
    intro i hli hri
    have hsymbol := paddedBinaryPrefixEq_symbol_eq heq
      (lt_of_lt_of_le hli hleft)
    rw [paddedBinarySymbol_of_lt hli,
      paddedBinarySymbol_of_lt hri] at hsymbol
    exact ofBool_injective hsymbol
  · intro heq
    subst right
    exact paddedBinaryPrefixEq_self left width

private theorem HasBinaryContent.cells_paddedBinarySymbol {t : Tape}
    {bits : List Bool} (h : t.HasBinaryContent bits) (i : ℕ) :
    t.cells (i + 1) = paddedBinarySymbol bits i := by
  by_cases hi : i < bits.length
  · rw [paddedBinarySymbol_of_lt hi, h.1 i hi]
  · rw [paddedBinarySymbol_of_ge (Nat.le_of_not_gt hi),
      h.2 i (Nat.le_of_not_gt hi)]

/-- Reset only the head of a tape, preserving all cells. -/
private def tapeAtHead (t : Tape) (head : ℕ) : Tape :=
  { head := head, cells := t.cells }

@[simp] private theorem tapeAtHead_head (t : Tape) (head : ℕ) :
    (tapeAtHead t head).head = head := rfl

@[simp] private theorem tapeAtHead_cells (t : Tape) (head : ℕ) :
    (tapeAtHead t head).cells = t.cells := rfl

private theorem tapeAtHead_eq_self {t : Tape} {head : ℕ}
    (hhead : t.head = head) : tapeAtHead t head = t := by
  ext <;> simp [tapeAtHead, hhead]

/-- Put the two comparison cursors at the same head position and leave every
other work tape untouched. -/
private def binaryForWorkAt (work : Fin n → Tape)
    (counterIdx limitIdx : Fin n) (head : ℕ) : Fin n → Tape :=
  fun i =>
    if i = counterIdx then tapeAtHead (work i) head
    else if i = limitIdx then tapeAtHead (work i) head
    else work i

private theorem binaryForWorkAt_counter (work : Fin n → Tape)
    (counterIdx limitIdx : Fin n) (head : ℕ) :
    binaryForWorkAt work counterIdx limitIdx head counterIdx =
      tapeAtHead (work counterIdx) head := by
  simp [binaryForWorkAt]

private theorem binaryForWorkAt_limit (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx) (head : ℕ) :
    binaryForWorkAt work counterIdx limitIdx head limitIdx =
      tapeAtHead (work limitIdx) head := by
  simp [binaryForWorkAt, Ne.symm hne]

private theorem binaryForWorkAt_other (work : Fin n → Tape)
    {counterIdx limitIdx i : Fin n} (hic : i ≠ counterIdx)
    (hil : i ≠ limitIdx) (head : ℕ) :
    binaryForWorkAt work counterIdx limitIdx head i = work i := by
  simp [binaryForWorkAt, hic, hil]

private theorem binaryForWorkAt_one_eq (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n}
    (hcounter : (work counterIdx).head = 1)
    (hlimit : (work limitIdx).head = 1) :
    binaryForWorkAt work counterIdx limitIdx 1 = work := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    rw [binaryForWorkAt_counter, tapeAtHead_eq_self hcounter]
  · by_cases hil : i = limitIdx
    · subst i
      simp only [binaryForWorkAt, hic, ↓reduceIte]
      exact tapeAtHead_eq_self hlimit
    · exact binaryForWorkAt_other work hic hil 1

private theorem binaryForWorkAt_selected_cells (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (head : ℕ) (i : Fin n)
    (hi : i = counterIdx ∨ i = limitIdx) :
    (binaryForWorkAt work counterIdx limitIdx head i).cells = (work i).cells := by
  rcases hi with rfl | rfl
  · simp [binaryForWorkAt_counter]
  · simp [binaryForWorkAt]

private theorem binaryForWorkAt_move_right (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx) (head : ℕ) :
    Function.update
        (Function.update (binaryForWorkAt work counterIdx limitIdx head)
          counterIdx
          ((binaryForWorkAt work counterIdx limitIdx head counterIdx).move
            Dir3.right))
        limitIdx
        ((binaryForWorkAt work counterIdx limitIdx head limitIdx).move
          Dir3.right) =
      binaryForWorkAt work counterIdx limitIdx (head + 1) := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    simp [Function.update, hne, binaryForWorkAt, tapeAtHead, Tape.move]
  · by_cases hil : i = limitIdx
    · subst i
      simp [Function.update, hic, binaryForWorkAt, tapeAtHead, Tape.move]
    · simp [Function.update, hic, hil, binaryForWorkAt]

private theorem binaryForWorkAt_move_left (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx) (head : ℕ) :
    Function.update
        (Function.update (binaryForWorkAt work counterIdx limitIdx head)
          counterIdx
          ((binaryForWorkAt work counterIdx limitIdx head counterIdx).move
            Dir3.left))
        limitIdx
        ((binaryForWorkAt work counterIdx limitIdx head limitIdx).move
          Dir3.left) =
      binaryForWorkAt work counterIdx limitIdx (head - 1) := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    simp [Function.update, hne, binaryForWorkAt, tapeAtHead, Tape.move]
  · by_cases hil : i = limitIdx
    · subst i
      simp [Function.update, hic, binaryForWorkAt, tapeAtHead, Tape.move]
    · simp [Function.update, hic, hil, binaryForWorkAt]

/-- A comparison-phase configuration with synchronized counter and limit
cursors. -/
private def binaryForCompareCfg (body : TM n)
    (counterIdx limitIdx : Fin n) (phase : BinaryForPhase)
    (head : ℕ) (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Cfg n (binaryForTM body counterIdx limitIdx).Q :=
  { state := .inl phase
    input := inp
    work := binaryForWorkAt work counterIdx limitIdx head
    output := out }

private theorem binaryForCompareCfg_one_eq
    (body : TM n) (counterIdx limitIdx : Fin n) (phase : BinaryForPhase)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).head = 1)
    (hlimit : (work limitIdx).head = 1) :
    binaryForCompareCfg body counterIdx limitIdx phase 1 inp work out =
      { state := .inl phase
        input := inp
        work := work
        output := out } := by
  simp only [binaryForCompareCfg, binaryForWorkAt_one_eq work hcounter hlimit]

private theorem binaryForCompareCfg_work_read_ne_start
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (phase : BinaryForPhase) {head : ℕ} (hhead : 1 ≤ head)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start) :
    ∀ i, ((binaryForCompareCfg body counterIdx limitIdx phase head
      inp work out).work i).read ≠ Γ.start := by
  intro i
  by_cases hic : i = counterIdx
  · subst i
    simp only [binaryForCompareCfg, binaryForWorkAt_counter, Tape.read,
      tapeAtHead_head, tapeAtHead_cells]
    exact hcounter.cells_ne_start head hhead
  · by_cases hil : i = limitIdx
    · subst i
      simp only [binaryForCompareCfg, binaryForWorkAt_limit work hne,
        Tape.read, tapeAtHead_head, tapeAtHead_cells]
      exact hlimit.cells_ne_start head hhead
    · rw [show (binaryForCompareCfg body counterIdx limitIdx phase head
          inp work out).work i = work i by
        exact binaryForWorkAt_other work hic hil head]
      exact hother i hic hil

private theorem binaryForCompareCfg_counter_read
    (body : TM n) (work : Fin n → Tape)
    (counterIdx limitIdx : Fin n) (phase : BinaryForPhase)
    (inp out : Tape) {bits : List Bool}
    (hbits : (work counterIdx).HasBinaryContent bits) (i : ℕ) :
    ((binaryForCompareCfg body counterIdx limitIdx phase (i + 1)
      inp work out).work counterIdx).read = paddedBinarySymbol bits i := by
  simp only [binaryForCompareCfg, binaryForWorkAt_counter, Tape.read,
    tapeAtHead_head, tapeAtHead_cells]
  exact HasBinaryContent.cells_paddedBinarySymbol hbits i

private theorem binaryForCompareCfg_limit_read
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (phase : BinaryForPhase) (inp out : Tape) {bits : List Bool}
    (hbits : (work limitIdx).HasBinaryContent bits) (i : ℕ) :
    ((binaryForCompareCfg body counterIdx limitIdx phase (i + 1)
      inp work out).work limitIdx).read = paddedBinarySymbol bits i := by
  simp only [binaryForCompareCfg, binaryForWorkAt_limit work hne,
    Tape.read, tapeAtHead_head, tapeAtHead_cells]
  exact HasBinaryContent.cells_paddedBinarySymbol hbits i

private theorem binaryForCompareCfg_step_scan
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) (i : ℕ) (hi : i < limitBits.length) :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForCompareCfg body counterIdx limitIdx
          (.scan (paddedBinaryPrefixEq counterBits limitBits i))
          (i + 1) inp work out) =
      some (binaryForCompareCfg body counterIdx limitIdx
        (.scan (paddedBinaryPrefixEq counterBits limitBits (i + 1)))
        (i + 1 + 1) inp work out) := by
  let c := binaryForCompareCfg body counterIdx limitIdx
    (.scan (paddedBinaryPrefixEq counterBits limitBits i))
    (i + 1) inp work out
  have hcounterRead : (c.work counterIdx).read =
      paddedBinarySymbol counterBits i :=
    binaryForCompareCfg_counter_read body work counterIdx limitIdx _ inp out
      hcounter i
  have hlimitRead : (c.work limitIdx).read =
      paddedBinarySymbol limitBits i :=
    binaryForCompareCfg_limit_read body work hne _ inp out hlimit i
  have hmore : ¬((c.work counterIdx).read = Γ.blank ∧
      (c.work limitIdx).read = Γ.blank) := by
    intro hblank
    rw [hlimitRead, paddedBinarySymbol_of_lt hi] at hblank
    exact Γ.ofBool_ne_blank _ hblank.2
  have hwork : ∀ j, (c.work j).read ≠ Γ.start := by
    dsimp only [c]
    exact binaryForCompareCfg_work_read_ne_start body work hne
      (.scan (paddedBinaryPrefixEq counterBits limitBits i))
      (head := i + 1) (by omega) inp out hcounter hlimit hother
  have hstep := binaryForTM_step_scan_internal body counterIdx limitIdx hne
    (paddedBinaryPrefixEq counterBits limitBits i) c rfl hmore hinp hwork hout
  rw [hcounterRead, hlimitRead] at hstep
  dsimp only [c, binaryForCompareCfg] at hstep
  rw [binaryForWorkAt_move_right work hne] at hstep
  simpa only [c, binaryForCompareCfg, paddedBinaryPrefixEq] using hstep

private theorem binaryForCompareCfg_scan_reachesIn
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    ∀ width, width ≤ limitBits.length →
      (binaryForTM body counterIdx limitIdx).reachesIn width
        (binaryForCompareCfg body counterIdx limitIdx (.scan true)
          1 inp work out)
        (binaryForCompareCfg body counterIdx limitIdx
          (.scan (paddedBinaryPrefixEq counterBits limitBits width))
          (width + 1) inp work out) := by
  intro width
  induction width with
  | zero =>
      intro _
      simpa only [paddedBinaryPrefixEq] using
        (TM.reachesIn.zero :
          (binaryForTM body counterIdx limitIdx).reachesIn 0
            (binaryForCompareCfg body counterIdx limitIdx (.scan true)
              1 inp work out)
            (binaryForCompareCfg body counterIdx limitIdx (.scan true)
              1 inp work out))
  | succ width ih =>
      intro hwidth
      have hprefix := ih (by omega)
      have hstep := binaryForCompareCfg_step_scan body work hne inp out
        hcounter hlimit hinp hother hout width (by omega)
      exact (binaryForTM body counterIdx limitIdx).reachesIn_snoc hprefix hstep

private theorem binaryForCompareCfg_step_scan_blank
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) (equalSoFar : Bool) (width : ℕ)
    (hcounterWidth : counterBits.length ≤ width)
    (hlimitWidth : limitBits.length ≤ width) :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForCompareCfg body counterIdx limitIdx
          (.scan equalSoFar) (width + 1) inp work out) =
      some (binaryForCompareCfg body counterIdx limitIdx
        (.rewind equalSoFar) width inp work out) := by
  let c := binaryForCompareCfg body counterIdx limitIdx
    (.scan equalSoFar) (width + 1) inp work out
  have hcounterRead : (c.work counterIdx).read = Γ.blank := by
    rw [binaryForCompareCfg_counter_read body work counterIdx limitIdx
      (.scan equalSoFar) inp out hcounter width]
    exact paddedBinarySymbol_of_ge hcounterWidth
  have hlimitRead : (c.work limitIdx).read = Γ.blank := by
    rw [binaryForCompareCfg_limit_read body work hne
      (.scan equalSoFar) inp out hlimit width]
    exact paddedBinarySymbol_of_ge hlimitWidth
  have hwork : ∀ i, (c.work i).read ≠ Γ.start := by
    dsimp only [c]
    exact binaryForCompareCfg_work_read_ne_start body work hne
      (.scan equalSoFar) (head := width + 1) (by omega)
      inp out hcounter hlimit hother
  have hstep := binaryForTM_step_scan_blank_internal body counterIdx
    limitIdx hne equalSoFar c rfl hcounterRead hlimitRead hinp hwork hout
  dsimp only [c, binaryForCompareCfg] at hstep
  rw [binaryForWorkAt_move_left work hne] at hstep
  simpa using! hstep

private theorem binaryForCompareCfg_step_rewind
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) (equalSoFar : Bool) (head : ℕ) :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForCompareCfg body counterIdx limitIdx
          (.rewind equalSoFar) (head + 1) inp work out) =
      some (binaryForCompareCfg body counterIdx limitIdx
        (.rewind equalSoFar) head inp work out) := by
  let c := binaryForCompareCfg body counterIdx limitIdx
    (.rewind equalSoFar) (head + 1) inp work out
  have hwork : ∀ i, (c.work i).read ≠ Γ.start := by
    dsimp only [c]
    exact binaryForCompareCfg_work_read_ne_start body work hne
      (.rewind equalSoFar) (head := head + 1) (by omega)
      inp out hcounter hlimit hother
  have hstep := binaryForTM_step_rewind_internal body counterIdx limitIdx
    hne equalSoFar c rfl hinp hwork hout
  dsimp only [c, binaryForCompareCfg] at hstep
  rw [binaryForWorkAt_move_left work hne] at hstep
  simpa using! hstep

private theorem binaryForCompareCfg_rewind_reachesIn
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) (equalSoFar : Bool) :
    ∀ head,
      (binaryForTM body counterIdx limitIdx).reachesIn head
        (binaryForCompareCfg body counterIdx limitIdx
          (.rewind equalSoFar) head inp work out)
        (binaryForCompareCfg body counterIdx limitIdx
          (.rewind equalSoFar) 0 inp work out) := by
  intro head
  induction head with
  | zero => exact .zero
  | succ head ih =>
      exact .step (binaryForCompareCfg_step_rewind body work hne inp out
        hcounter hlimit hinp hother hout equalSoFar head) ih

private theorem binaryForCompareCfg_step_rewind_true
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape)
    (hcounterStart : (work counterIdx).cells 0 = Γ.start)
    (hlimitStart : (work limitIdx).cells 0 = Γ.start)
    (hcounterHead : (work counterIdx).head = 1)
    (hlimitHead : (work limitIdx).head = 1)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForCompareCfg body counterIdx limitIdx
          (.rewind true) 0 inp work out) =
      some
        { state := .inl .done
          input := inp
          work := work
          output := out } := by
  let c := binaryForCompareCfg body counterIdx limitIdx
    (.rewind true) 0 inp work out
  have hcounterRead : (c.work counterIdx).read = Γ.start := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_counter, tapeAtHead,
      Tape.read, hcounterStart]
  have hlimitRead : (c.work limitIdx).read = Γ.start := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_limit work hne,
      tapeAtHead, Tape.read, hlimitStart]
  have hcounterHead0 : (c.work counterIdx).head = 0 := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_counter]
  have hlimitHead0 : (c.work limitIdx).head = 0 := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_limit work hne]
  have hother' : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (c.work i).read ≠ Γ.start := by
    intro i hic hil
    rw [show c.work i = work i by
      exact binaryForWorkAt_other work hic hil 0]
    exact hother i hic hil
  have hstep := binaryForTM_step_rewind_equal_internal body counterIdx
    limitIdx hne c rfl hcounterRead hlimitRead hcounterHead0 hlimitHead0
    hinp hother' hout
  dsimp only [c, binaryForCompareCfg] at hstep
  rw [binaryForWorkAt_move_right work hne,
    binaryForWorkAt_one_eq work hcounterHead hlimitHead] at hstep
  exact hstep

private theorem binaryForCompareCfg_step_rewind_false
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape)
    (hcounterStart : (work counterIdx).cells 0 = Γ.start)
    (hlimitStart : (work limitIdx).cells 0 = Γ.start)
    (hcounterHead : (work counterIdx).head = 1)
    (hlimitHead : (work limitIdx).head = 1)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForCompareCfg body counterIdx limitIdx
          (.rewind false) 0 inp work out) =
      some
        { state := .inr (binaryForIterationTM body counterIdx).qstart
          input := inp
          work := work
          output := out } := by
  let c := binaryForCompareCfg body counterIdx limitIdx
    (.rewind false) 0 inp work out
  have hcounterRead : (c.work counterIdx).read = Γ.start := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_counter, tapeAtHead,
      Tape.read, hcounterStart]
  have hlimitRead : (c.work limitIdx).read = Γ.start := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_limit work hne,
      tapeAtHead, Tape.read, hlimitStart]
  have hcounterHead0 : (c.work counterIdx).head = 0 := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_counter]
  have hlimitHead0 : (c.work limitIdx).head = 0 := by
    simp [c, binaryForCompareCfg, binaryForWorkAt_limit work hne]
  have hother' : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (c.work i).read ≠ Γ.start := by
    intro i hic hil
    rw [show c.work i = work i by
      exact binaryForWorkAt_other work hic hil 0]
    exact hother i hic hil
  have hstep := binaryForTM_step_rewind_unequal_internal body counterIdx
    limitIdx hne c rfl hcounterRead hlimitRead hcounterHead0 hlimitHead0
    hinp hother' hout
  dsimp only [c, binaryForCompareCfg] at hstep
  rw [binaryForWorkAt_move_right work hne,
    binaryForWorkAt_one_eq work hcounterHead hlimitHead] at hstep
  exact hstep

private theorem binaryForCompareCfg_reachesIn_rewind_zero
    (body : TM n) (work : Fin n → Tape)
    {counterIdx limitIdx : Fin n} (hne : counterIdx ≠ limitIdx)
    (inp out : Tape) {counterBits limitBits : List Bool}
    (hcounter : (work counterIdx).HasBinaryContent counterBits)
    (hlimit : (work limitIdx).HasBinaryContent limitBits)
    (hinp : inp.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) (width : ℕ)
    (hcounterWidth : counterBits.length ≤ width)
    (hlimitWidth : limitBits.length = width) :
    (binaryForTM body counterIdx limitIdx).reachesIn (2 * width + 1)
      (binaryForCompareCfg body counterIdx limitIdx (.scan true)
        1 inp work out)
      (binaryForCompareCfg body counterIdx limitIdx
        (.rewind (paddedBinaryPrefixEq counterBits limitBits width))
        0 inp work out) := by
  have hscan := binaryForCompareCfg_scan_reachesIn body work hne inp out
    hcounter hlimit hinp hother hout width (by omega)
  have hblank := binaryForCompareCfg_step_scan_blank body work hne inp out
    hcounter hlimit hinp hother hout
    (paddedBinaryPrefixEq counterBits limitBits width) width
    hcounterWidth (by omega)
  have hscanRewind :=
    (binaryForTM body counterIdx limitIdx).reachesIn_snoc hscan hblank
  have hrewind := binaryForCompareCfg_rewind_reachesIn body work hne inp out
    hcounter hlimit hinp hother hout
    (paddedBinaryPrefixEq counterBits limitBits width) width
  have hrun := reachesIn_trans (binaryForTM body counterIdx limitIdx)
    hscanRewind hrewind
  convert! hrun using 1
  omega

/-- At equality, the full-width comparison preserves every tape exactly and
reaches the loop's `done` state in the advertised exact time. -/
theorem binaryForTM_compare_reachesIn_frame_of_eq_internal
    (body : TM n) (counterIdx limitIdx : Fin n)
    (hne : counterIdx ≠ limitIdx) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat value)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime value)
      { state := .inl (.scan true)
        input := inp₀
        work := work₀
        output := out₀ }
      { state := .inl .done
        input := inp₀
        work := work₀
        output := out₀ } := by
  have hwidth : value.bits.length = value.size :=
    Nat.size_eq_bits_len value
  have hrewind := binaryForCompareCfg_reachesIn_rewind_zero body work₀ hne
    inp₀ out₀ hcounter.2.2 hlimit.2.2 hinp hother hout value.size
    (by omega) hwidth
  rw [paddedBinaryPrefixEq_self] at hrewind
  have hexit := binaryForCompareCfg_step_rewind_true body work₀ hne
    inp₀ out₀ hcounter.1 hlimit.1 hcounter.2.1 hlimit.2.1
    hinp hother hout
  have hrun :=
    (binaryForTM body counterIdx limitIdx).reachesIn_snoc hrewind hexit
  rw [binaryForCompareCfg_one_eq body counterIdx limitIdx (.scan true)
    inp₀ work₀ out₀ hcounter.2.1 hlimit.2.1] at hrun
  simpa [binaryForCompareTime] using hrun

/-- Strictly below the limit, the full-width comparison preserves every tape
exactly and reaches the composite iteration start in the advertised time. -/
theorem binaryForTM_compare_reachesIn_frame_of_lt_internal
    (body : TM n) (counterIdx limitIdx : Fin n)
    (hne : counterIdx ≠ limitIdx) (value limitValue : ℕ)
    (hlt : value < limitValue)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat value)
    (hlimit : (work₀ limitIdx).HasBinaryNat limitValue)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue)
      { state := .inl (.scan true)
        input := inp₀
        work := work₀
        output := out₀ }
      { state := .inr (binaryForIterationTM body counterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
  have hcounterWidth : value.bits.length ≤ limitValue.size := by
    rw [Nat.size_eq_bits_len value]
    exact Nat.size_le_size (Nat.le_of_lt hlt)
  have hlimitWidth : limitValue.bits.length = limitValue.size :=
    Nat.size_eq_bits_len limitValue
  have hflag : paddedBinaryPrefixEq value.bits limitValue.bits
      limitValue.size = false := by
    cases hprefix : paddedBinaryPrefixEq value.bits limitValue.bits
        limitValue.size with
    | false => rfl
    | true =>
        have hbits := (paddedBinaryPrefixEq_eq_true_iff hcounterWidth
          (by omega)).mp hprefix
        have hvalues := congrArg Nat.fromBitsLE hbits
        simp only [Nat.fromBitsLE_bits] at hvalues
        omega
  have hrewind := binaryForCompareCfg_reachesIn_rewind_zero body work₀ hne
    inp₀ out₀ hcounter.2.2 hlimit.2.2 hinp hother hout
    limitValue.size hcounterWidth hlimitWidth
  rw [hflag] at hrewind
  have hexit := binaryForCompareCfg_step_rewind_false body work₀ hne
    inp₀ out₀ hcounter.1 hlimit.1 hcounter.2.1 hlimit.2.1
    hinp hother hout
  have hrun :=
    (binaryForTM body counterIdx limitIdx).reachesIn_snoc hrewind hexit
  rw [binaryForCompareCfg_one_eq body counterIdx limitIdx (.scan true)
    inp₀ work₀ out₀ hcounter.2.1 hlimit.2.1] at hrun
  simpa [binaryForCompareTime] using hrun

/-- A complete canonical comparison has one exact, fully framed endpoint.
The endpoint enters the composite iteration exactly below the limit and is
the final `done` configuration exactly at equality. -/
theorem binaryForTM_compare_reachesIn_frame_internal
    (body : TM n) (counterIdx limitIdx : Fin n)
    (hne : counterIdx ≠ limitIdx) (value limitValue : ℕ)
    (hle : value ≤ limitValue)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat value)
    (hlimit : (work₀ limitIdx).HasBinaryNat limitValue)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryForTM body counterIdx limitIdx).reachesIn
        (binaryForCompareTime limitValue)
        { state := .inl (.scan true)
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      c'.input = inp₀ ∧
      c'.work = work₀ ∧
      c'.output = out₀ ∧
      (c'.state = .inr (binaryForIterationTM body counterIdx).qstart ↔
        value < limitValue) ∧
      (c'.state = .inl .done ↔ value = limitValue) := by
  by_cases heq : value = limitValue
  · subst limitValue
    have hrun := binaryForTM_compare_reachesIn_frame_of_eq_internal
      body counterIdx limitIdx hne value inp₀ work₀ out₀
      hcounter hlimit hinp hother hout
    refine ⟨_, hrun, rfl, rfl, rfl, ?_, ?_⟩
    · simp
    · simp
      rfl
  · have hlt : value < limitValue := by omega
    have hrun := binaryForTM_compare_reachesIn_frame_of_lt_internal
      body counterIdx limitIdx hne value limitValue hlt inp₀ work₀ out₀
      hcounter hlimit hinp hother hout
    refine ⟨_, hrun, rfl, rfl, rfl, ?_, ?_⟩
    · simp [hlt]
      rfl
    · simp [heq]

end TM

end Complexity

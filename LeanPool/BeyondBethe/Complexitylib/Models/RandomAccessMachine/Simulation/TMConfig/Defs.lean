/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Bounded Turing-machine configurations in RAM registers

This file fixes the register representation used by the Turing-machine to RAM
simulation. Register zero stores the finite-state code, the next `n + 2`
registers store the input/work/output head positions, and the remaining
registers store a dense bounded window of every named tape.

Blank symbols use code zero. Consequently registers outside the representation
and blank cells inside it agree with the RAM's finite-support convention.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

variable {n bound : ℕ}

/-- A field in a bounded configuration: state, a named tape head, or a named
tape cell. Named tapes use input/work/output indices `0, 1..n, n+1`. -/
abbrev Field (n bound : ℕ) :=
  Fin 1 ⊕ (Fin (n + 2) ⊕ (Fin (n + 2) × Fin (bound + 1)))

/-- Number of registers occupied by a configuration with cells `0..bound`. -/
def registerCount (n bound : ℕ) : ℕ :=
  1 + ((n + 2) + (n + 2) * (bound + 1))

/-- Explicit contiguous ordering of all fields in the bounded representation. -/
noncomputable def fieldEquiv (n bound : ℕ) :
    Field n bound ≃ Fin (registerCount n bound) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1))
      ((Equiv.sumCongr (Equiv.refl (Fin (n + 2))) finProdFinEquiv).trans
        finSumFinEquiv)).trans
    finSumFinEquiv

/-- The field holding the Turing-machine state. -/
def stateField : Field n bound := Sum.inl ⟨0, by omega⟩

/-- The field holding one named tape's head position. -/
def headField (tape : Fin (n + 2)) : Field n bound :=
  Sum.inr (Sum.inl tape)

/-- The field holding one cell of one named tape. -/
def cellField (tape : Fin (n + 2)) (position : Fin (bound + 1)) :
    Field n bound :=
  Sum.inr (Sum.inr (tape, position))

/-- Concrete register address of a bounded-configuration field. -/
noncomputable def fieldReg (field : Field n bound) : ℕ :=
  (fieldEquiv n bound field).val

/-- Code the tape alphabet with blank represented by zero. -/
def symbolCode : Γ → ℕ
  | .blank => 0
  | .zero => 1
  | .one => 2
  | .start => 3

/-- Decode a RAM word as a tape symbol; invalid words decode to blank. -/
def symbolDecode : ℕ → Γ
  | 1 => .zero
  | 2 => .one
  | 3 => .start
  | _ => .blank

/-- Canonical numeric code of a finite Turing-machine state. -/
noncomputable def stateCode (tm : TM n) (state : tm.Q) : ℕ :=
  (Fintype.equivFin tm.Q state).val

/-- Decode a valid state code, using the start state as the default for an
invalid RAM word. -/
noncomputable def stateDecode (tm : TM n) (code : ℕ) : tm.Q :=
  if h : code < Fintype.card tm.Q then
    (Fintype.equivFin tm.Q).symm ⟨code, h⟩
  else tm.qstart

/-- Select a named tape by its input/work/output index. -/
def tapeAt (cfg : Complexity.Cfg n Q) (tape : Fin (n + 2)) : Tape :=
  if hinput : tape.val = 0 then cfg.input
  else if houtput : tape.val = n + 1 then cfg.output
  else cfg.work ⟨tape.val - 1, by omega⟩

/-- A tape is contained in the encoded window when every later cell is blank. -/
def TapeBounded (tape : Tape) (bound : ℕ) : Prop :=
  ∀ position, bound < position → tape.cells position = Γ.blank

/-- Every named tape in a configuration is contained in the encoded window. -/
def Bounded (cfg : Complexity.Cfg n Q) (bound : ℕ) : Prop :=
  ∀ tape, TapeBounded (tapeAt cfg tape) bound

/-- Every named head lies inside the encoded cell window. -/
def HeadsBounded (cfg : Complexity.Cfg n Q) (bound : ℕ) : Prop :=
  ∀ tape, (tapeAt cfg tape).head ≤ bound

/-- A configuration can be stepped inside a bounded representation when both
its nonblank cells and every named head lie in the represented window. -/
def WithinWindow (cfg : Complexity.Cfg n Q) (bound : ℕ) : Prop :=
  Bounded cfg bound ∧ HeadsBounded cfg bound

/-- Natural-number value stored for one representation field. -/
noncomputable def fieldValue (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : Field n bound → ℕ
  | Sum.inl _ => stateCode tm cfg.state
  | Sum.inr (Sum.inl tape) => (tapeAt cfg tape).head
  | Sum.inr (Sum.inr (tape, position)) =>
      symbolCode ((tapeAt cfg tape).cells position.val)

/-- Register store containing a bounded Turing-machine configuration. -/
noncomputable def encodeRegs (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ → ℕ :=
  fun reg =>
    if h : reg < registerCount n bound then
      fieldValue tm bound cfg ((fieldEquiv n bound).symm ⟨reg, h⟩)
    else 0

/-- A RAM store represents a bounded TM configuration when every state/head/cell
field has its prescribed value. Scratch registers outside this interface are
deliberately unconstrained, allowing successive simulation blocks to compose. -/
def Represents (tm : TM n) (bound : ℕ) (cfg : Complexity.Cfg n tm.Q)
    (regs : ℕ → ℕ) : Prop :=
  ∀ field, regs (fieldReg field) = fieldValue tm bound cfg field

/-- RAM configuration positioned at the beginning of a simulation block. -/
noncomputable def encode (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : RAM.Cfg :=
  { pc := 0, regs := encodeRegs tm bound cfg }

/-- Decode one tape from its head register and bounded cell block. -/
noncomputable def decodeTape (bound : ℕ) (regs : ℕ → ℕ)
    (tape : Fin (n + 2)) : Tape where
  head := regs (fieldReg (headField (bound := bound) tape))
  cells := fun position =>
    if h : position < bound + 1 then
      symbolDecode (regs (fieldReg (cellField tape ⟨position, h⟩)))
    else Γ.blank

/-- Decode a bounded register layout into a Turing-machine configuration. -/
noncomputable def decode (tm : TM n) (bound : ℕ) (regs : ℕ → ℕ) :
    Complexity.Cfg n tm.Q where
  state := stateDecode tm (regs (fieldReg (stateField (n := n) (bound := bound))))
  input := decodeTape (n := n) bound regs ⟨0, by omega⟩
  work := fun i => decodeTape (n := n) bound regs ⟨i.val + 1, by omega⟩
  output := decodeTape (n := n) bound regs ⟨n + 1, by omega⟩

end TMConfig

end RAM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# Sparse unbounded TM configurations in RAM registers

This layout is independent of an input-length or time bound. State, heads, and
scratch occupy a fixed prefix determined only by the machine's tape count.
Tape cells are interleaved after that prefix at
`cellBase + position * (n + 2) + tape`. A fixed RAM program can therefore
compute every cell address using multiplication and addition while allocating
new tape positions on demand.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- State field followed by every named head and every named tape cell. -/
abbrev Field (n : ℕ) :=
  Fin 1 ⊕ (Fin (n + 2) ⊕ (Fin (n + 2) × ℕ))

/-- State register. -/
def stateReg : ℕ := 0

/-- Fixed head register for one named tape. -/
def headReg (tape : Fin (n + 2)) : ℕ := 1 + tape.val

/-- Constant-zero scratch register. -/
def zeroReg (n : ℕ) : ℕ := n + 3

/-- Constant-one scratch register. -/
def oneReg (n : ℕ) : ℕ := n + 4

/-- Constant `n + 2`, used to compute interleaved cell addresses. -/
def tapeCountReg (n : ℕ) : ℕ := n + 5

/-- Destructive finite-state dispatch register. -/
def stateScratchReg (n : ℕ) : ℕ := n + 6

/-- Indirect cell-address scratch register. -/
def addressReg (n : ℕ) : ℕ := n + 7

/-- Writable-symbol scratch register. -/
def valueReg (n : ℕ) : ℕ := n + 8

/-- Loaded head-symbol register for one named tape. -/
def symbolReg (n : ℕ) (tape : Fin (n + 2)) : ℕ :=
  n + 9 + tape.val

/-- Exclusive end of the fixed control/scratch prefix and first tape-cell
register. -/
def cellBase (n : ℕ) : ℕ := 2 * n + 11

/-- Address of one tape cell in the fixed interleaved layout. -/
def cellReg (n : ℕ) (tape : Fin (n + 2)) (position : ℕ) : ℕ :=
  cellBase n + position * (n + 2) + tape.val

/-- Concrete address of a sparse configuration field. -/
def fieldReg : Field n → ℕ
  | Sum.inl _ => stateReg
  | Sum.inr (Sum.inl tape) => headReg tape
  | Sum.inr (Sum.inr (tape, position)) => cellReg n tape position

/-- Semantic value of one sparse configuration field. -/
noncomputable def fieldValue (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    Field n → ℕ
  | Sum.inl _ => stateCode tm cfg.state
  | Sum.inr (Sum.inl tape) => (tapeAt cfg tape).head
  | Sum.inr (Sum.inr (tape, position)) =>
      symbolCode ((tapeAt cfg tape).cells position)

/-- A store represents the complete unbounded TM configuration. Scratch
registers in the fixed gap are deliberately unconstrained. -/
def Represents (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (store : Structured.Store) : Prop :=
  ∀ field, store (fieldReg field) = fieldValue tm cfg field

/-- Decode the tape slot of an interleaved cell register. -/
def decodeCellTape (n reg : ℕ) : Fin (n + 2) :=
  ⟨(reg - cellBase n) % (n + 2), Nat.mod_lt _ (by omega)⟩

/-- Decode the position of an interleaved cell register. -/
def decodeCellPosition (n reg : ℕ) : ℕ :=
  (reg - cellBase n) / (n + 2)

/-- Canonical sparse register encoding. -/
noncomputable def encodeRegs (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    Structured.Store := fun reg =>
  if hstate : reg = stateReg then stateCode tm cfg.state
  else if hhead : reg < n + 3 then
    (tapeAt cfg ⟨reg - 1, by omega⟩).head
  else if cellBase n ≤ reg then
    symbolCode ((tapeAt cfg (decodeCellTape n reg)).cells
      (decodeCellPosition n reg))
  else 0

/-- Decode one complete sparse tape. -/
noncomputable def decodeTape (n : ℕ) (store : Structured.Store)
    (tape : Fin (n + 2)) : Tape where
  head := store (headReg tape)
  cells := fun position => symbolDecode (store (cellReg n tape position))

/-- Decode a complete sparse store into a TM configuration. -/
noncomputable def decode (tm : TM n) (store : Structured.Store) :
    Complexity.Cfg n tm.Q where
  state := stateDecode tm (store stateReg)
  input := decodeTape n store ⟨0, by omega⟩
  work := fun i => decodeTape n store ⟨i.val + 1, by omega⟩
  output := decodeTape n store ⟨n + 1, by omega⟩

end Sparse

end TMConfig

end RAM

end Complexity

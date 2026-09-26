/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs

/-!
# Tape layouts for sparse-register instructions

Arithmetic and control instruction tape assignments and their injectivity and
non-aliasing facts, shared by the concrete instruction machines.
-/

@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- The three arithmetic operations shared by RAM register instructions. -/
inductive BinaryInstrOp where
  | add
  | sub
  | mul
  deriving DecidableEq

/-- Eighteen pairwise-distinct tapes used by arithmetic followed by sparse
update. Slots `0..12` are the update controller, slots `13` and `14` are the
operands, and slots `15..17` are multiplication scratch. -/
structure BinaryInstructionTapes (n : ℕ) where
  /-- Complete injective physical assignment. -/
  idx : Fin 18 → Fin n
  /-- No two semantic roles alias. -/
  injective : Function.Injective idx

namespace BinaryInstructionTapes

/-- The thirteen-tape sparse-update view. -/
def update {n : ℕ} (tapes : BinaryInstructionTapes n) : EntryUpdateTapes n where
  idx := fun i => tapes.idx ⟨i, by omega⟩
  injective := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val (tapes.injective h)

/-- First looked-up arithmetic operand. -/
def lhs {n : ℕ} (tapes : BinaryInstructionTapes n) : Fin n := tapes.idx 13

/-- Second looked-up arithmetic operand. -/
def rhs {n : ℕ} (tapes : BinaryInstructionTapes n) : Fin n := tapes.idx 14

/-- Multiplication's shifted-multiplicand scratch tape. -/
def shift {n : ℕ} (tapes : BinaryInstructionTapes n) : Fin n := tapes.idx 15

/-- Multiplication's first alternating scratch tape. -/
def tmp {n : ℕ} (tapes : BinaryInstructionTapes n) : Fin n := tapes.idx 16

/-- Multiplication's second alternating scratch tape. -/
def dbl {n : ℕ} (tapes : BinaryInstructionTapes n) : Fin n := tapes.idx 17

/-- Parent-slot inequality gives physical tape inequality. -/
theorem ne {n : ℕ} (tapes : BinaryInstructionTapes n)
    {i j : Fin 18} (hne : i ≠ j) : tapes.idx i ≠ tapes.idx j :=
  fun heq => hne (tapes.injective heq)

theorem update_ne_lhs {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 13) : tapes.update.idx slot ≠ tapes.lhs := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = 13 at hval
  omega

theorem update_ne_rhs {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 13) : tapes.update.idx slot ≠ tapes.rhs := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = 14 at hval
  omega

theorem update_ne_shift {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 13) : tapes.update.idx slot ≠ tapes.shift := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = 15 at hval
  omega

theorem update_ne_tmp {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 13) : tapes.update.idx slot ≠ tapes.tmp := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = 16 at hval
  omega

theorem update_ne_dbl {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 13) : tapes.update.idx slot ≠ tapes.dbl := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = 17 at hval
  omega

/-- Parent slots for a reusable lookup whose destination is `lhs`. -/
def lhsLookupSlot (i : Fin 14) : Fin 18 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 12
  | 11 => 15
  | 12 => 13
  | _ => 11

private theorem lhsLookupSlot_injective : Function.Injective lhsLookupSlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [lhsLookupSlot] at h ⊢

/-- Reusable sparse lookup view targeting the first operand. -/
def lhsLookup {n : ℕ} (tapes : BinaryInstructionTapes n) :
    EntryLookupRestoreTapes n where
  idx := fun i => tapes.idx (lhsLookupSlot i)
  injective := fun _ _ h => by
    exact lhsLookupSlot_injective (tapes.injective h)

/-- Parent slots for a reusable lookup whose destination is `rhs`. -/
def rhsLookupSlot (i : Fin 14) : Fin 18 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 12
  | 11 => 15
  | 12 => 14
  | _ => 11

private theorem rhsLookupSlot_injective : Function.Injective rhsLookupSlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [rhsLookupSlot] at h ⊢

/-- Reusable sparse lookup view targeting the second operand. -/
def rhsLookup {n : ℕ} (tapes : BinaryInstructionTapes n) :
    EntryLookupRestoreTapes n where
  idx := fun i => tapes.idx (rhsLookupSlot i)
  injective := fun _ _ h => by
    exact rhsLookupSlot_injective (tapes.injective h)

@[simp] theorem lhsLookup_count {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.lhsLookup.idx 9 = tapes.update.remaining := rfl

@[simp] theorem rhsLookup_count {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.rhsLookup.idx 9 = tapes.update.remaining := rfl

@[simp] theorem lhsLookup_countSource {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.lhsLookup.countSource = tapes.update.resultCount := rfl

@[simp] theorem rhsLookup_countSource {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.rhsLookup.countSource = tapes.update.resultCount := rfl

@[simp] theorem lhsLookup_querySource {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.lhsLookup.querySource = tapes.shift := rfl

@[simp] theorem rhsLookup_querySource {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.rhsLookup.querySource = tapes.shift := rfl

@[simp] theorem lhsLookup_destination {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.lhsLookup.destination = tapes.lhs := rfl

@[simp] theorem rhsLookup_destination {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.rhsLookup.destination = tapes.rhs := rfl

@[simp] theorem lhsLookup_copyScratch {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.lhsLookup.copyScratch = tapes.update.found := rfl

@[simp] theorem rhsLookup_copyScratch {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.rhsLookup.copyScratch = tapes.update.found := rfl

theorem lhsLookup_ne_rhs {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 14) : tapes.lhsLookup.idx slot ≠ tapes.rhs := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem rhsLookup_ne_lhs {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 14) : tapes.rhsLookup.idx slot ≠ tapes.lhs := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem lhsLookup_ne_tmp {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 14) : tapes.lhsLookup.idx slot ≠ tapes.tmp := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem rhsLookup_ne_tmp {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 14) : tapes.rhsLookup.idx slot ≠ tapes.tmp := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem lhsLookup_ne_dbl {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 14) : tapes.lhsLookup.idx slot ≠ tapes.dbl := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem rhsLookup_ne_dbl {n : ℕ} (tapes : BinaryInstructionTapes n)
    (slot : Fin 14) : tapes.rhsLookup.idx slot ≠ tapes.dbl := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem lhsLookup_ne_replacement {n : ℕ}
    (tapes : BinaryInstructionTapes n) (slot : Fin 14) :
    tapes.lhsLookup.idx slot ≠ tapes.update.replacement := by
  apply tapes.ne
  fin_cases slot <;> decide

theorem rhsLookup_ne_replacement {n : ℕ}
    (tapes : BinaryInstructionTapes n) (slot : Fin 14) :
    tapes.rhsLookup.idx slot ≠ tapes.update.replacement := by
  apply tapes.ne
  fin_cases slot <;> decide

/-- Parent slots for a loaded indirect read. The first operand supplies the
runtime address and the update replacement tape receives the loaded value. -/
def indirectLoadLookupSlot (i : Fin 14) : Fin 18 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 12
  | 11 => 13
  | 12 => 10
  | _ => 11

private theorem indirectLoadLookupSlot_injective :
    Function.Injective indirectLoadLookupSlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [indirectLoadLookupSlot] at h ⊢

/-- Reusable loaded lookup view for indirect `load`. -/
def indirectLoadLookup {n : ℕ} (tapes : BinaryInstructionTapes n) :
    EntryLookupRestoreTapes n where
  idx := fun i => tapes.idx (indirectLoadLookupSlot i)
  injective := fun _ _ h => by
    exact indirectLoadLookupSlot_injective (tapes.injective h)

@[simp] theorem indirectLoadLookup_count {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.indirectLoadLookup.idx 9 = tapes.update.remaining := rfl

@[simp] theorem indirectLoadLookup_countSource {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.indirectLoadLookup.countSource = tapes.update.resultCount := rfl

@[simp] theorem indirectLoadLookup_querySource {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.indirectLoadLookup.querySource = tapes.lhs := rfl

@[simp] theorem indirectLoadLookup_destination {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.indirectLoadLookup.destination = tapes.update.replacement := rfl

@[simp] theorem indirectLoadLookup_copyScratch {n : ℕ}
    (tapes : BinaryInstructionTapes n) :
    tapes.indirectLoadLookup.copyScratch = tapes.update.found := rfl

/-- Multiplication-role parent slots. The accumulator deliberately aliases the
update replacement slot `10`. -/
def mulSlot (i : Fin 6) : Fin 18 :=
  match i.val with
  | 0 => 13
  | 1 => 14
  | 2 => 10
  | 3 => 15
  | 4 => 16
  | _ => 17

private theorem mulSlot_injective : Function.Injective mulSlot := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [mulSlot] at hij ⊢

/-- Six-tape multiplication view, with its accumulator on update replacement. -/
def mul {n : ℕ} (tapes : BinaryInstructionTapes n) : TM.BinaryShiftMulABI n where
  tape :=
    ⟨fun i => tapes.idx (mulSlot i), fun _ _ h =>
      by exact mulSlot_injective (tapes.injective h)⟩

@[simp] theorem mul_lhs {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.mul.lhs = tapes.lhs := rfl

@[simp] theorem mul_rhs {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.mul.rhs = tapes.rhs := rfl

@[simp] theorem mul_acc {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.mul.acc = tapes.update.replacement := rfl

@[simp] theorem mul_shift {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.mul.shift = tapes.shift := rfl

@[simp] theorem mul_tmp {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.mul.tmp = tapes.tmp := rfl

@[simp] theorem mul_dbl {n : ℕ} (tapes : BinaryInstructionTapes n) :
    tapes.mul.dbl = tapes.dbl := rfl

/-- The addition/subtraction operands and result are pairwise distinct. -/
theorem arithmeticDistinct {n : ℕ} (tapes : BinaryInstructionTapes n) :
    TM.BinaryRippleAddDistinct tapes.lhs tapes.rhs
      tapes.update.replacement := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide),
    tapes.ne (by decide)⟩

/-- The same physical inequalities as a subtraction certificate. -/
theorem subtractionDistinct {n : ℕ} (tapes : BinaryInstructionTapes n) :
    TM.BinaryRippleSubDistinct tapes.lhs tapes.rhs
      tapes.update.replacement := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide),
    tapes.ne (by decide)⟩

end BinaryInstructionTapes

/-- The arithmetic/store ABI together with one disjoint canonical program-
counter tape. Nineteen work tapes suffice for every RAM instruction. -/
structure ControlInstructionTapes (n : ℕ) where
  /-- The complete data-instruction assignment. -/
  data : BinaryInstructionTapes n
  /-- Canonical binary program counter. -/
  pc : Fin n
  /-- The program counter aliases no data-instruction role. -/
  pc_ne : ∀ slot, pc ≠ data.idx slot

namespace ControlInstructionTapes

/-- Every data-instruction role is distinct from the program counter. -/
theorem data_ne_pc {n : ℕ} (tapes : ControlInstructionTapes n)
    (slot : Fin 18) : tapes.data.idx slot ≠ tapes.pc :=
  (tapes.pc_ne slot).symm

/-- The first loaded operand is distinct from the program counter. -/
theorem lhs_ne_pc {n : ℕ} (tapes : ControlInstructionTapes n) :
    tapes.data.lhs ≠ tapes.pc := tapes.data_ne_pc 13

/-- The program counter is distinct from the first loaded operand. -/
theorem pc_ne_lhs {n : ℕ} (tapes : ControlInstructionTapes n) :
    tapes.pc ≠ tapes.data.lhs := tapes.pc_ne 13

/-- No tape owned by the first lookup aliases the program counter. -/
theorem lookup_ne_pc {n : ℕ} (tapes : ControlInstructionTapes n)
    (slot : Fin 14) : tapes.data.lhsLookup.idx slot ≠ tapes.pc := by
  exact tapes.data_ne_pc (BinaryInstructionTapes.lhsLookupSlot slot)

end ControlInstructionTapes


end Machine

end RegisterStore

end RAM

end Complexity

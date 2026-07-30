/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.Map
import LeanPool.MRiscX.AbstractSyntax.Instr
import LeanPool.MRiscX.Parser.AssemblySyntax
import Lean

/-!
# AbstractSyntax

This module provides core abstract-syntax types of the MRiscX assembly language.
-/
open Nat
open Lean Lean.Elab
/--
Purpose of this file:
This file establishes the syntax of the MRiscX assembly language, encompassing the definition
of instructions, labels, registers, memory and machine states. Given that the instructionsMap,
labels, registers, and memory are represented as maps, it may be beneficial to review the contents
of the file Maps.lean beforehand.


Next we define some Datatypes for the map keys.
This is because it makes it easier to understand which
map is being processed.
Firstly a register, which will hold a value
-/

abbrev Register := UInt64


instance: Coe Register UInt64 where
 coe c := (c:UInt64)


/--
Next, the memory address. This address will point to a certain
address in the memory which holds some value
-/
abbrev MemoryAddress := UInt64

/--
The InstructionIndex is a serial number which points
to a instruction in the stack
-/
abbrev InstructionIndex := UInt64

/-- The program counter: the index of the instruction currently being executed. -/
abbrev ProgramCounter := UInt64

/--
A total map which holds the instructions of a program
tied to a unsigned 64-bit integers as InstructionIndex. The default value of this map
is the instruction Instr.Panic.

IM := {uint64_1 ↦ instr_1, uint64_2 ↦ instr_2, ..., uint64_n ↦ instr_n}
/ default:  Instr.IPanic
-/
def InstructionMap := TMap InstructionIndex Instr
deriving Repr, Inhabited

instance : ToString InstructionMap where
  toString (instrMap : InstructionMap) := reprStr instrMap

/--
Empty InstructionMap which serves as standard InstructionMap
-/
def EmptyInstructionMap : InstructionMap := TMap.empty Instr.Panic

/--
A partial map LabelMap, which holds all the Labels as key and links these
to an unsigned 64-bit integers.

LM := {l_1 ↦ uint64_1, l_2 ↦ uint64_2, ..., l_n ↦ uint64_n}
-/
def LabelMap := PMap String UInt64
deriving Repr, Inhabited

instance : ToString LabelMap where
  toString (labelMap : LabelMap) := reprStr labelMap


/--
Empty LabelMap which serves as standard LabelMap
-/
def EmptyLabels : LabelMap := PMap.empty


/--
The InstructionMap and the LabelMap are combined into a single structure,
which is refered as `Code`.
-/
structure Code where
  /-- The instruction map, associating each instruction index with an instruction. -/
  instructionMap: InstructionMap
  /-- The label map, associating each label name with its target index. -/
  labels: LabelMap


/--
A default instance of Code, containing an empty `InstructionMap` and an empty `LabelMap`.
-/
def DefaultCode : Code := { instructionMap := EmptyInstructionMap, labels := EmptyLabels }



namespace Code
  /-- Replace the instruction map of a `Code` with `c`. -/
  def setCMap (m : Code) (c : InstructionMap) : Code :=
    { m with instructionMap := c}

  /-- Replace the label map of a `Code` with `l`. -/
  def setLabels (m : Code) (l : LabelMap) : Code :=
    { m with labels := l}

  /-- Add a list of `(name, index)` label bindings to a `Code`. -/
  def addMultipleLabels (m : Code) (l : List (String × UInt64)) : Code :=
  match l with
  | [] => m
  | h :: t => addMultipleLabels {m with labels := p(h.1 ↦ h.2; m.labels)} t

  /-- Insert an instruction `v` at index `id` into the instruction map of a `Code`. -/
  def addCMap (m : Code) (id : InstructionIndex) (v : Instr) : Code :=
    {m with instructionMap := (id ↦ v; m.instructionMap)}

  /-- Insert a label `id ↦ v` into the label map of a `Code`. -/
  def addLabels (m : Code) (id : String) (v : UInt64) : Code :=
    {m with labels := p(id ↦ v; m.labels)}

  /-- Insert both an instruction and a label binding into a `Code`. -/
  def addMaps (m : Code) (id_c : InstructionIndex) (v_c : Instr) (id_l : String)
      (v_l : UInt64) : Code :=
    {m with instructionMap := (id_c ↦ v_c; m.instructionMap), labels :=
    p(id_l ↦ v_l; m.labels)}

  /-- Replace both the instruction map and the label map of a `Code`. -/
  def setMaps (m : Code) (c : InstructionMap) (l : LabelMap) : Code :=
    (m.setCMap c).setLabels l

  /-- Look up the target index of a label in a `Code`. -/
  def getLabel (m : Code) (l : String): Option UInt64 := m.labels.get l

  /-- Look up the instruction stored at index `l` in a `Code`. -/
  def getInstrAt (m : Code) (l : UInt64): Instr := m.instructionMap.get l
end Code




/--
Definiton of the registers
R := {r_1 ↦ w_1, … , r_k ↦ w_k}
-/
def Registers := TMap Register UInt64
  deriving Repr

/--
RegisterMap with default value 0

R := {r_1 ↦ w_1, … , r_k ↦ w_k; 0}
-/
def EmptyRegisters : Registers := TMap.empty 0

/--
Definiton of the memory
M := {m_1 ↦ w_1, … , m_k ↦ w_k}
-/
def Memory := TMap MemoryAddress UInt64
  deriving Repr


/--
MemoryMap with default value 0

M := {m_1 ↦ w_1, … , m_k ↦ w_k; 0}
-/
def EmptyMemory : Memory := TMap.empty 0

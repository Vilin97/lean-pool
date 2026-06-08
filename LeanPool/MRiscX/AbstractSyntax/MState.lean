/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax


/-!
Everything is now brought together in a single structure called MState, which represents
the machine's MState This structure holds the memory, registers, the code, a program counter (PC),
and a termination flag. The program counter points to the next instruction to be executed,
while the termination flag indicates whether the machine state has halted or if further
evaluation should continue.
-/
/-- The state of the abstract machine: its memory, registers, program counter,
loaded code, and termination flag. -/
structure MState where
  /-- The data memory of the machine. -/
  memory: Memory
  /-- The register file of the machine. -/
  registers: Registers
  /-- The program counter, pointing at the next instruction to execute. -/
  pc: ProgramCounter
  /-- The program (code) loaded into the machine. -/
  code: Code
  /-- Whether the machine has halted. -/
  terminated: Bool

/-- The initial machine state: empty memory and registers, program counter `0`,
not terminated, and the default code. -/
def DefaultMState : MState :=
  {registers := EmptyRegisters, memory := EmptyMemory, pc := 0,
    terminated := false, code := DefaultCode}

/-
To perform the operations on the MState like we want to, we need to implement some
functions.
-/
namespace MState

  /-- The instruction at the current program counter. -/
  def currInstruction (ms:MState) : Instr :=
    ms.code.instructionMap.get (ms.pc)

  /-- Increment the program counter by one. -/
  def incPc (ms:MState) : MState :=
    {ms with pc := ms.pc + 1}

  /-- Set the program counter to `p`. -/
  def setPc (ms:MState) (p:UInt64) : MState :=
    {ms with pc := p}

  /-- Replace the register file with `r`. -/
  def setRegister (ms:MState) (r:Registers) : MState :=
    {ms with registers := r}

  /-- Set register `i` to value `v`. -/
  def addRegister (ms:MState) (i:UInt64) (v:UInt64): MState :=
    {ms with registers := (i ↦ v; ms.registers)}

  /-- Read the value of register `i`. -/
  def getRegisterAt (ms:MState) (i:UInt64) : UInt64 :=
    ms.registers.get (i)

  /-- Replace the memory with `m`. -/
  def setMemory (ms:MState) (m:Memory) : MState :=
    {ms with memory := m}

  /-- Set memory address `i` to value `v`. -/
  def addMemory (ms:MState) (i:UInt64) (v:UInt64) : MState :=
    {ms with memory := (i ↦ v; ms.memory)}

  /-- Read the value at memory address `i`. -/
  def getMemoryAt (ms:MState) (i:UInt64) : UInt64 :=
    ms.memory.get (i)

  /-- Replace the instruction map of the loaded code. -/
  def setInstructionMap (ms:MState) (sc:InstructionMap) : MState :=
    {ms with code.instructionMap := sc}

  /-- Replace the loaded code with `code`. -/
  def setCode (ms: MState) (code: Code) : MState :=
    {ms with code := code}

  /-- Replace the label map of the loaded code. -/
  def setLabels (ms:MState) (l:LabelMap) : MState :=
    {ms with code.labels := l}

  /-- Set the termination flag. -/
  def setTerminated (ms:MState) (bool:Bool) : MState :=
    {ms with terminated := bool}

  /-- Look up the target index of label `s`, if present. -/
  def getLabelAt (ms:MState) (s:String) : Option UInt64 :=
    ms.code.labels.get s

  /-- Build a fresh machine state running the code `c`. -/
  def createStandardState (c : Code): MState :=
    {DefaultMState with code := c}

  /--
  This creates a Machine state with the pointer which the label [s] points to.
  If there is no label [s] in code.labels, terminated is set to true.
  -/
  def jump (ms:MState) (s:String) : MState :=
    match ms.code.labels.get s with
    | some i => {ms with pc := i}
    | none => {ms with terminated := true}


end MState

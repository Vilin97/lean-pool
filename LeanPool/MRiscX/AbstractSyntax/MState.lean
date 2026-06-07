/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax


/-
Everything is now brought together in a single structure called MState, which represents
the machine's MState This structure holds the memory, registers, the code, a program counter (PC),
and a termination flag. The program counter points to the next instruction to be executed,
while the termination flag indicates whether the machine state has halted or if further
evaluation should continue.
-/
structure MState where
  memory: Memory
  registers: Registers
  pc: ProgramCounter
  code: Code
  terminated: Bool

def DefaultMState : MState :=
  {registers := EmptyRegisters, memory := EmptyMemory, pc := 0,
    terminated := false, code := DefaultCode}

/-
To perform the operations on the MState like we want to, we need to implement some
functions.
-/
namespace MState

  def currInstruction (ms:MState) : Instr :=
    ms.code.instructionMap.get (ms.pc)

  def incPc (ms:MState) : MState :=
    {ms with pc := ms.pc + 1}

  def setPc (ms:MState) (p:UInt64) : MState :=
    {ms with pc := p}

  def setRegister (ms:MState) (r:Registers) : MState :=
    {ms with registers := r}

  def addRegister (ms:MState) (i:UInt64) (v:UInt64): MState :=
    {ms with registers := (i ↦ v ; ms.registers)}

  def getRegisterAt (ms:MState) (i:UInt64) : UInt64 :=
    ms.registers.get (i)

  def setMemory (ms:MState) (m:Memory) : MState :=
    {ms with memory := m}

  def addMemory (ms:MState) (i:UInt64) (v:UInt64) : MState :=
    {ms with memory := (i ↦ v ; ms.memory)}

  def getMemoryAt (ms:MState) (i:UInt64) : UInt64 :=
    ms.memory.get (i)

  def setInstructionMap (ms:MState) (sc:InstructionMap) : MState :=
    {ms with code.instructionMap := sc}

  def setCode (ms: MState) (code: Code) : MState :=
    {ms with code := code}

  def setLabels (ms:MState) (l:LabelMap) : MState :=
    {ms with code.labels := l}

  def setTerminated (ms:MState) (bool:Bool) : MState :=
    {ms with terminated := bool}

  def getLabelAt (ms:MState) (s:String) : Option UInt64 :=
    ms.code.labels.get s

  def createStandardState (c : Code): MState :=
    {DefaultMState with code := c}

  /-
  This creates a Machine state with the pointer which the label [s] points to.
  If there is no label [s] in code.labels, terminated is set to true.
  -/
  def jump (ms:MState) (s:String) : MState :=
    match ms.code.labels.get s with
    | some i => {ms with pc := i}
    | none => {ms with terminated := true}


end MState

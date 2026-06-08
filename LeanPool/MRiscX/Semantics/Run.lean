/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.AbstractSyntax.MState

/-!
# Run

This module provides the operational `run` semantics of MRiscX.
-/

open Nat

/-
This file holds the functionality of the interpreter of the assembly language.
The function `runOneStep` evaluates each instruction and performs the desired action
on the abstract syntax.
-/

namespace MState

  /-- Conditional jump on one register: jump to `lbl` if `cond` holds of register
  `reg`, otherwise advance the program counter. -/
  def jif (ms: MState) (reg : UInt64) (lbl : String) (cond : UInt64 → Bool) :=
      let regCont := ms.getRegisterAt reg
      if cond regCont then
        ms.jump lbl
      else
        ms.incPc

  /-- Conditional jump on two registers: jump to `lbl` if `cond` holds of registers
  `reg1` and `reg2`, otherwise advance the program counter. -/
  def jif' (ms: MState) (reg1 reg2 :UInt64) (lbl:String) (cond : UInt64 → UInt64 → Bool) :=
      let reg1Cont := ms.getRegisterAt reg1
      let reg2Cont := ms.getRegisterAt reg2
      if cond reg1Cont reg2Cont then
        ms.jump lbl
      else
        ms.incPc


  /--
  This function evaluates the given machine state to a new one.
  Tt represents the **nxt** function from the paper
  `LUNDBERG, Didrik, et al. Hoare-style logic for unstructured programs.
  In: International Conference on Software Engineering and Formal Methods.
  Cham: Springer International Publishing, 2020. S. 193-213.`

  Generally, if the `terminated` of the `State` is `false` and the instruction
  is legal and evaluateable, a new `State` is
  returned holding the next instructions and the updated storage.
  When the instruction is not legal (e.g. jmp s, there is no label `s`),
  `terminated` is set to `true`.
  -/
  def runOneStep (ms:MState) : MState :=
    if ms.terminated then ms
    else
      let instr := ms.currInstruction
      match instr with
      | Instr.LoadAddress (dst:UInt64) (addr : UInt64) =>
        (ms.addRegister dst addr).incPc
      | Instr.LoadImmediate (dst:UInt64) (i:UInt64) =>
        (ms.addRegister dst i).incPc
      | Instr.CopyRegister (dst:UInt64) (src : UInt64) =>
        (ms.addRegister dst (ms.getRegisterAt src)).incPc
      | Instr.AddImmediate (dst:UInt64) (reg:UInt64) (i:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt reg) + i)).incPc
      | Instr.Increment (dst:UInt64) =>
        (ms.addRegister dst (ms.getRegisterAt dst + 1)).incPc
      | Instr.AddRegister (dst:UInt64) (reg1:UInt64) (reg2:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt reg1) + (ms.getRegisterAt reg2))).incPc
      | Instr.SubImmediate (dst:UInt64) (reg:UInt64) (i:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt reg) - i)).incPc
      | Instr.Decrement (dst:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt dst) - 1)).incPc
      | Instr.SubRegister (dst:UInt64) (reg1:UInt64) (reg2:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt reg1) - (ms.getRegisterAt reg2))).incPc
      | Instr.XorImmediate (dst:UInt64) (reg:UInt64) (i:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt reg).xor i)).incPc
      | Instr.XOR (dst:UInt64) (reg1:UInt64) (reg2:UInt64) =>
        (ms.addRegister dst ((ms.getRegisterAt reg1).xor (ms.getRegisterAt reg2))).incPc
      | Instr.LoadWordImmediate (dst:UInt64) (addr:UInt64) =>
        (ms.addRegister dst (ms.getMemoryAt addr)).incPc
      | Instr.LoadWordReg (dst:UInt64) (addr:UInt64) =>
        (ms.addRegister dst (ms.getMemoryAt (ms.getRegisterAt addr))).incPc
      | Instr.StoreWord (reg:UInt64) (dst:UInt64) =>
        (ms.addMemory (ms.getRegisterAt dst) (ms.getRegisterAt reg)).incPc
      | Instr.Jump (lbl:String) =>
        ms.jump lbl
      | Instr.JumpEq (reg1:UInt64) (reg2:UInt64) (lbl:String) =>
        jif' ms reg1 reg2 lbl (fun n m => n == m)
      | Instr.JumpNeq (reg1:UInt64) (reg2:UInt64) (lbl:String) =>
        jif' ms reg1 reg2 lbl (fun n m => n != m)
      | Instr.JumpGt (reg1:UInt64) (reg2:UInt64) (lbl:String) =>
        jif' ms reg1 reg2 lbl (fun n m => n > m)
      | Instr.JumpLe (reg1:UInt64) (reg2:UInt64) (lbl:String) =>
        jif' ms reg1 reg2 lbl (fun n m => n <= m)
      | Instr.JumpEqZero (reg:UInt64) (lbl:String) =>
        jif ms reg lbl (fun n => n == 0)
      | Instr.JumpNeqZero reg (lbl:String) =>
        jif ms reg lbl (fun n => n ≠ 0)
      | Instr.Panic => ms.setTerminated true
      -- | _ => ms.setTerminated true

  /--
  Runs `runOneStep` `n` times.
  It represents the function **nxt^n** from
  `LUNDBERG, Didrik, et al. Hoare-style logic for unstructured programs.
  In: International Conference on Software Engineering and Formal Methods.
  Cham: Springer International Publishing, 2020. S. 193-213.`
  -/
  def runNSteps (ms:MState) (n:Nat) : MState :=
    match n with
    | zero => ms
    | succ n' => ms.runOneStep.runNSteps n'


  /-- Run the machine until it terminates or `fuel` steps have elapsed. -/
  def runUntilTerminatedWithFuel (ms : MState) (fuel : Nat) : MState :=
    match fuel with
    | Nat.zero => ms
    | Nat.succ n' =>
      if ms.terminated then
        ms
      else
        runUntilTerminatedWithFuel ms.runOneStep (n')

  /-- Run the machine until it terminates, bounded by `UInt64.size` steps. -/
  def runUntilTerminated (ms : MState) : MState :=
    runUntilTerminatedWithFuel ms UInt64.size


  /-- The instruction the machine would execute after one more step. -/
  def nextInstruction (ms:MState) : Instr := ms.runOneStep.currInstruction

end MState

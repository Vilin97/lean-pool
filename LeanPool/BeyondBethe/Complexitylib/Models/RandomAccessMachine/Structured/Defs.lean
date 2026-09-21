/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs

/-!
# Structured logarithmic-cost RAM programs — definitions

This file defines a minimal first-order imperative language over RAM register
stores. Atomic commands are the data-manipulating RAM instructions; sequencing,
conditionals, and loops are structured syntax rather than program-counter
arithmetic. The source semantics is independent of compilation and records the
same operand-sensitive logarithmic cost and finite-support space measure as the
target RAM.

`Cmd.compileAt` erases structured control flow into absolute `jz`/`jmp` targets.
The compiler appends no hidden data operations: source and target executions
therefore have equal register effects, logarithmic cost, and peak register space.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

/-- A source store maps register indices to natural-number contents. -/
abbrev Store := ℕ → ℕ

/-- Logarithmic space occupied by a source store. This deliberately matches
`RAM.Cfg.space`, but does not mention a target program counter. -/
noncomputable def Store.space (store : Store) : ℕ :=
  ∑ᶠ i, (if store i = 0 then 0 else bitlen i + bitlen (store i))

namespace Input

/-- Natural-number representation of one input bit. -/
@[simp]
def bitValue (bit : Bool) : ℕ := if bit then 1 else 0

/-- Store a bit string above a reserved register prefix, with its length in a
distinguished register. -/
def bitStore (lengthReg inputBase : ℕ) (bits : List Bool) : Store := fun index =>
  if index = lengthReg then bits.length
  else if inputBase ≤ index then
    match bits[index - inputBase]? with
    | some bit => bitValue bit
    | none => 0
  else 0

end Input

/-- Data-manipulating instructions of the structured source language. Control
flow is represented by `Cmd`, so arbitrary jumps and halt are not source atoms. -/
inductive Basic where
  | imm (dst value : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  deriving Repr, DecidableEq, Inhabited

namespace Basic

/-- Execute one source-level basic instruction on a register store. -/
def exec : Basic → Store → Store
  | .imm dst value, regs => Function.update regs dst value
  | .add dst left right, regs =>
      Function.update regs dst (regs left + regs right)
  | .sub dst left right, regs =>
      Function.update regs dst (regs left - regs right)
  | .mul dst left right, regs =>
      Function.update regs dst (regs left * regs right)
  | .load dst address, regs =>
      Function.update regs dst (regs (regs address))
  | .store address src, regs =>
      Function.update regs (regs address) (regs src)

/-- Erase a source basic instruction to the corresponding RAM instruction. -/
def instr : Basic → Instr
  | .imm dst value => .imm dst value
  | .add dst left right => .add dst left right
  | .sub dst left right => .sub dst left right
  | .mul dst left right => .mul dst left right
  | .load dst address => .load dst address
  | .store address src => .store address src

/-- Operand-sensitive source cost of one basic instruction. -/
def logCost : Basic → Store → ℕ
  | .imm _ value, _ => bitlen value + 1
  | .add _ left right, regs =>
      bitlen (regs left) + bitlen (regs right) +
        bitlen (regs left + regs right) + 1
  | .sub _ left right, regs =>
      bitlen (regs left) + bitlen (regs right) + 1
  | .mul _ left right, regs =>
      bitlen (regs left) + bitlen (regs right) +
        bitlen (regs left * regs right) + 1
  | .load _ address, regs =>
      bitlen (regs address) + bitlen (regs (regs address)) + 1
  | .store address src, regs =>
      bitlen (regs address) + bitlen (regs src) + 1

/-- Execute a straight-line list of basic instructions. -/
def execList : List Basic → Store → Store
  | [], regs => regs
  | op :: rest, regs => execList rest (op.exec regs)

end Basic

/-- Minimal structured imperative syntax over RAM stores. -/
inductive Cmd where
  | skip
  | basic (op : Basic)
  | seq (first second : Cmd)
  | ifZero (test : ℕ) (onZero onNonzero : Cmd)
  | whileNonzero (test : ℕ) (body : Cmd)
  deriving Repr, DecidableEq, Inhabited

namespace Cmd

/-- Number of RAM instructions emitted for a structured command. -/
def codeSize : Cmd → ℕ
  | .skip => 0
  | .basic _ => 1
  | .seq first second => first.codeSize + second.codeSize
  | .ifZero _ onZero onNonzero =>
      2 + onZero.codeSize + onNonzero.codeSize
  | .whileNonzero _ body => body.codeSize + 2

/-- Compile a command whose first instruction will be placed at `start`.
All generated branch destinations are absolute RAM program counters. -/
def compileAt : (start : ℕ) → Cmd → Program
  | _, .skip => []
  | _, .basic op => [op.instr]
  | start, .seq first second =>
      first.compileAt start ++ second.compileAt (start + first.codeSize)
  | start, .ifZero test onZero onNonzero =>
      let nonzeroStart := start + 1
      let zeroStart := nonzeroStart + onNonzero.codeSize + 1
      let done := start + (Cmd.ifZero test onZero onNonzero).codeSize
      [Instr.jz test zeroStart] ++
        onNonzero.compileAt nonzeroStart ++ [Instr.jmp done] ++
        onZero.compileAt zeroStart
  | start, .whileNonzero test body =>
      let done := start + (Cmd.whileNonzero test body).codeSize
      [Instr.jz test done] ++ body.compileAt (start + 1) ++
        [Instr.jmp start]

/-- Compile a closed source command and halt immediately after it finishes. -/
def compile (cmd : Cmd) : Program := cmd.compileAt 0 ++ [Instr.halt]

/-- Right-associated sequential composition of a list of commands. -/
def seqList : List Cmd → Cmd
  | [] => .skip
  | [cmd] => cmd
  | cmd :: next :: rest => .seq cmd (seqList (next :: rest))

/-- Embed a straight-line list of basic instructions as one structured command. -/
def basics (ops : List Basic) : Cmd :=
  seqList (ops.map Cmd.basic)

end Cmd

/-- Independent big-step semantics for structured commands. Besides the final
store, the relation records target instruction steps, exact logarithmic cost,
and peak source-store space. Branch and loop-control costs are explicit. -/
inductive Exec : Cmd → Store → Store → ℕ → ℕ → ℕ → Prop where
  | skip (store : Store) :
      Exec .skip store store 0 0 store.space
  | basic (op : Basic) (store : Store) :
      Exec (.basic op) store (op.exec store) 1 (op.logCost store)
        (max store.space (op.exec store).space)
  | seq {first second : Cmd} {store middle final : Store}
      {firstSteps secondSteps firstCost secondCost firstSpace secondSpace : ℕ}
      (hfirst : Exec first store middle firstSteps firstCost firstSpace)
      (hsecond : Exec second middle final secondSteps secondCost secondSpace) :
      Exec (.seq first second) store final (firstSteps + secondSteps)
        (firstCost + secondCost) (max firstSpace secondSpace)
  | ifZero {test : ℕ} {onZero onNonzero : Cmd} {store final : Store}
      {steps cost space : ℕ} (htest : store test = 0)
      (hbranch : Exec onZero store final steps cost space) :
      Exec (.ifZero test onZero onNonzero) store final (steps + 1)
        (bitlen (store test) + 1 + cost) (max store.space space)
  | ifNonzero {test : ℕ} {onZero onNonzero : Cmd} {store final : Store}
      {steps cost space : ℕ} (htest : store test ≠ 0)
      (hbranch : Exec onNonzero store final steps cost space) :
      Exec (.ifZero test onZero onNonzero) store final (steps + 2)
        (bitlen (store test) + 1 + cost + 1) (max store.space space)
  | whileZero {test : ℕ} {body : Cmd} {store : Store}
      (htest : store test = 0) :
      Exec (.whileNonzero test body) store store 1
        (bitlen (store test) + 1) store.space
  | whileNonzero {test : ℕ} {body : Cmd} {store middle final : Store}
      {bodySteps loopSteps bodyCost loopCost bodySpace loopSpace : ℕ}
      (htest : store test ≠ 0)
      (hbody : Exec body store middle bodySteps bodyCost bodySpace)
      (hloop : Exec (.whileNonzero test body) middle final loopSteps loopCost loopSpace) :
      Exec (.whileNonzero test body) store final
        (bodySteps + loopSteps + 2) (bitlen (store test) + 1 + bodyCost + 1 + loopCost)
        (max bodySpace loopSpace)

end Structured

end RAM

end Complexity

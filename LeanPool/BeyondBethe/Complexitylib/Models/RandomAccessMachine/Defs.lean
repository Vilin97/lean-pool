/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.BigOperators.Finprod
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine
public import Mathlib.Data.Nat.Bits

/-!
# Random access machines: model and cost measures

This file defines a Random Access Machine (RAM) — a register machine with
indirect addressing — together with **logarithmic-cost** time and space
measures. The design follows the standard successor/register RAM of
Cook–Reckhow, *Time bounded random access machines* (JCSS 7 (1973), 354–375)
and the textbook presentations of Papadimitriou (*Computational Complexity*,
§2.6) and van Emde Boas (*Machine models and simulations*, Handbook of
Theoretical Computer Science A, 1990). Conventions are adapted for a clean
formalization where a text is silent or divergent, but the *cost measure* is
kept faithful to the literature, because it is exactly the cost measure that
determines whether the model is a sound stand-in for a Turing machine.

## Why logarithmic cost (the soundness point)

A RAM stores natural numbers of unbounded magnitude in each register. Under the
naive **unit-cost** measure — one time unit per instruction regardless of
operand size — a RAM can square a register repeatedly to build the number
`2 ^ (2 ^ k)` in `O(k)` steps. That number needs `2 ^ k` bits to write down, so
no Turing machine can even emit it in fewer than `2 ^ k` steps: unit-cost RAM
time is **super-polynomially** stronger than Turing time, and the two models are
*not* polynomially equivalent. Adopting unit cost and then comparing to Turing
machines would be a category error — the exact "reward hacking" this model is
designed to avoid. `RAM.logGap_squaring` in the surface file turns this into a
theorem about this very model.

The **logarithmic-cost** measure charges each instruction the total bit-length
of the numbers it manipulates (operand *contents* and, for indirect operands,
the runtime *addresses*), plus a base cost of `1` so every step costs at least
one time unit. Under this measure the RAM is polynomially equivalent to the
multi-tape Turing machine of `Complexitylib.Models.TuringMachine`; the precise
two-way simulation bounds are recorded in the surface module
`Complexitylib.Models.RandomAccessMachine`.

## Main definitions

- `RAM.Instr` — the instruction set (immediate, `add`/`sub`/`mul`, indirect
  `load`/`store`, conditional/unconditional jump, `halt`)
- `RAM.Cfg` — a configuration: a program counter and a register file `ℕ → ℕ`
- `RAM.step`, `RAM.run` — executable single step and fuel-bounded run
- `RAM.bitlen` — the length function `l(v) = Nat.size v` (number of bits)
- `RAM.Instr.logCost` — the logarithmic cost of one instruction in a state
- `RAM.logTimeUpto`, `RAM.unitTimeUpto` — accumulated log-cost / step count
- `RAM.Cfg.space`, `RAM.spaceUpto` — logarithmic-cost space
- `RAM.initCfg` — input convention (length in `R₀`, bits in `R₁ … Rₙ`)
- `RAM.Program.DecidesInTime`, `RAM.Program.DecidesInSpace` — deciding a
  `Language` with the verdict read from `R₀`, mirroring `TM.DecidesInTime`

## Design notes

- **Register file `ℕ → ℕ`**: total and computable, so programs are executable
  witnesses (`#eval`-able). Only finitely many registers are ever nonzero along
  a run; this finite-support invariant makes the space measure well defined.
- **`bitlen v = Nat.size v`**: the number of binary digits, with `bitlen 0 = 0`,
  `bitlen 1 = 1`, `bitlen (2^k) = k + 1`. Instruction costs add `1` so that each
  step costs `≥ 1` regardless of operand sizes.
- **Direct vs. indirect addressing**: register *literals* named in an
  instruction (`d`, `s`, `t`, `a`) are program constants, bounded by the program
  size, so the cost does not separately charge for them; runtime addresses
  (`R a` in `load`/`store`) *are* charged via `bitlen (c.regs a)`. This keeps the
  cost within a constant factor of the Cook–Reckhow measure while remaining
  sound: every value read, computed, or written is charged its bit-length.
- **Out-of-range `pc` halts**: `curInstr` reads `Instr.halt` when `pc` is past the
  program, so a program need not end in `halt` and jumps may target the end.
-/


@[expose] public section

namespace Complexity

namespace RAM

/-- The RAM instruction set. Register indices and jump targets are natural
    numbers. `add`/`sub`/`mul` are three-address; `sub` is truncated
    subtraction (`Nat` monus). `load`/`store` use *indirect* addressing — the
    accessed register index is itself the content of a register — which is what
    makes the machine "random access". -/
inductive Instr where
  /-- `imm d v`: set `R d := v` (load an immediate constant). -/
  | imm (d v : ℕ)
  /-- `add d s t`: set `R d := R s + R t`. -/
  | add (d s t : ℕ)
  /-- `sub d s t`: set `R d := R s ∸ R t` (truncated subtraction). -/
  | sub (d s t : ℕ)
  /-- `mul d s t`: set `R d := R s * R t`. -/
  | mul (d s t : ℕ)
  /-- `load d a`: indirect load `R d := R (R a)`. -/
  | load (d a : ℕ)
  /-- `store a s`: indirect store `R (R a) := R s`. -/
  | store (a s : ℕ)
  /-- `jz s tgt`: if `R s = 0` jump to `tgt`, else fall through. -/
  | jz (s tgt : ℕ)
  /-- `jmp tgt`: unconditional jump to `tgt`. -/
  | jmp (tgt : ℕ)
  /-- `halt`: stop the machine. -/
  | halt
  deriving Repr, DecidableEq, Inhabited

/-- A RAM program is a finite list of instructions, indexed by the program
    counter. -/
abbrev Program := List Instr

/-- A RAM configuration: the program counter and the register file. Register `i`
    currently holds `regs i`. -/
@[ext]
structure Cfg where
  /-- The program counter (index of the next instruction). -/
  pc : ℕ
  /-- The register file: `regs i` is the content of register `i`. -/
  regs : ℕ → ℕ

/-- The length function `l(v)`: the number of binary digits of `v`.
    `bitlen 0 = 0`, `bitlen 1 = 1`, `bitlen (2 ^ k) = k + 1`. This is the
    quantity charged (per operand) by the logarithmic cost measure. -/
def bitlen (v : ℕ) : ℕ := Nat.size v

/-- The instruction the machine is about to execute. A program counter past the
    end of the program reads as `halt`, so programs need not end in `halt`. -/
def curInstr (P : Program) (c : Cfg) : Instr := (P[c.pc]?).getD Instr.halt

/-- A configuration is halted (for a given program) when the current instruction
    is `halt` — including the case of a program counter past the program end. -/
def Halted (P : Program) (c : Cfg) : Prop := curInstr P c = Instr.halt

instance (P : Program) (c : Cfg) : Decidable (Halted P c) := by
  unfold Halted; infer_instance

/-- Execute one instruction, producing the successor configuration. `halt` is a
    no-op here; `step` only applies this to a non-halted configuration. -/
def stepInstr : Instr → Cfg → Cfg
  | .imm d v, c   => { pc := c.pc + 1, regs := Function.update c.regs d v }
  | .add d s t, c => { pc := c.pc + 1, regs := Function.update c.regs d (c.regs s + c.regs t) }
  | .sub d s t, c => { pc := c.pc + 1, regs := Function.update c.regs d (c.regs s - c.regs t) }
  | .mul d s t, c => { pc := c.pc + 1, regs := Function.update c.regs d (c.regs s * c.regs t) }
  | .load d a, c  => { pc := c.pc + 1, regs := Function.update c.regs d (c.regs (c.regs a)) }
  | .store a s, c => { pc := c.pc + 1, regs := Function.update c.regs (c.regs a) (c.regs s) }
  | .jz s tgt, c  => if c.regs s = 0 then { c with pc := tgt } else { c with pc := c.pc + 1 }
  | .jmp tgt, c   => { c with pc := tgt }
  | .halt, c      => c

/-- Step a RAM by one instruction (a no-op on a halted configuration). -/
def step (P : Program) (c : Cfg) : Cfg := stepInstr (curInstr P c) c

/-- The logarithmic cost of executing instruction `i` in configuration `c`: the
    base cost `1` plus the bit-length of every value the instruction reads,
    computes, or writes (and, for indirect operands, the runtime address).

    This is the crux of the model's soundness: every number the instruction
    touches is charged its bit-length, so a run of total log-cost `T` can only
    manipulate numbers of bit-length at most `T`. See the module docstring. -/
def Instr.logCost (i : Instr) (c : Cfg) : ℕ :=
  match i with
  | .imm _ v   => bitlen v + 1
  | .add _ s t => bitlen (c.regs s) + bitlen (c.regs t) + bitlen (c.regs s + c.regs t) + 1
  | .sub _ s t => bitlen (c.regs s) + bitlen (c.regs t) + 1
  | .mul _ s t => bitlen (c.regs s) + bitlen (c.regs t) + bitlen (c.regs s * c.regs t) + 1
  | .load _ a  => bitlen (c.regs a) + bitlen (c.regs (c.regs a)) + 1
  | .store a s => bitlen (c.regs a) + bitlen (c.regs s) + 1
  | .jz s _    => bitlen (c.regs s) + 1
  | .jmp _     => 1
  | .halt      => 1

/-- The logarithmic cost of the machine's next step. -/
def stepLogCost (P : Program) (c : Cfg) : ℕ := (curInstr P c).logCost c

/-- Fuel-bounded run: execute up to `fuel` steps, stopping early once halted.
    Once halted, the configuration is stationary (`run_halted`), so the final
    configuration is independent of any fuel large enough to reach a halt. -/
def run (P : Program) : ℕ → Cfg → Cfg
  | 0, c => c
  | fuel + 1, c => if Halted P c then c else run P fuel (step P c)

/-- Accumulated **logarithmic time** over a fuel-bounded run: the sum of the
    per-step logarithmic costs of the non-halted steps taken. -/
def logTimeUpto (P : Program) : ℕ → Cfg → ℕ
  | 0, _ => 0
  | fuel + 1, c => if Halted P c then 0 else stepLogCost P c + logTimeUpto P fuel (step P c)

/-- Accumulated **unit time** over a fuel-bounded run: simply the number of
    non-halted steps taken. Provided for contrast with `logTimeUpto`; the gap
    between the two is exactly what makes unit cost unsound (see the surface
    theorem `RAM.logGap_squaring`). -/
def unitTimeUpto (P : Program) : ℕ → Cfg → ℕ
  | 0, _ => 0
  | fuel + 1, c => if Halted P c then 0 else 1 + unitTimeUpto P fuel (step P c)

/-- The logarithmic **space content** of a configuration: the total number of
    bits needed to name and store every nonzero register — for each nonzero
    register `i`, its address bits `bitlen i` plus its content bits
    `bitlen (regs i)`. Registers holding `0` are free. The `finsum` is finite
    exactly when the register file has finite support, which is an invariant of
    every run started from `initCfg` (`run_finiteSupport`). -/
noncomputable def Cfg.space (c : Cfg) : ℕ :=
  ∑ᶠ i, (if c.regs i = 0 then 0 else bitlen i + bitlen (c.regs i))

/-- Peak logarithmic space over a fuel-bounded run: the maximum space content of
    any configuration visited (including the halted one). -/
noncomputable def spaceUpto (P : Program) : ℕ → Cfg → ℕ
  | 0, c => c.space
  | fuel + 1, c => if Halted P c then c.space else max c.space (spaceUpto P fuel (step P c))

/-- The input convention. On input `x : List Bool`:
    * register `0` holds the length `|x|`;
    * register `i + 1` holds bit `x[i]` (as `0`/`1`) for `i < |x|`;
    * all other registers hold `0`.

    Register `0` doubles as the accumulator/verdict register on output. -/
def initRegs (x : List Bool) : ℕ → ℕ := fun i =>
  if i = 0 then x.length
  else match x[i - 1]? with
    | some b => if b then 1 else 0
    | none => 0

/-- The initial configuration on input `x`: program counter `0`, registers set by
    `initRegs`. -/
def initCfg (x : List Bool) : Cfg := { pc := 0, regs := initRegs x }

/-- A program *halts within `fuel` steps* on `c` when the fuel-bounded run
    reaches a halted configuration. -/
def HaltsIn (P : Program) (c : Cfg) (fuel : ℕ) : Prop := Halted P (run P fuel c)

/-- A program *halts* on `c` when it halts within some amount of fuel. -/
def Halts (P : Program) (c : Cfg) : Prop := ∃ fuel, HaltsIn P c fuel

/-- The **output** of a decider: register `0` at halt. `1` means accept, `0`
    means reject. -/
def Cfg.verdict (c : Cfg) : ℕ := c.regs 0

/-- `P` decides `L` within logarithmic time `T(n)`: on every input `x`, the run
    halts having spent log-time at most `T |x|`, with verdict `R₀ = 1` when
    `x ∈ L` and `R₀ = 0` when `x ∉ L`. Mirrors `TM.DecidesInTime`. -/
def Program.DecidesInTime (P : Program) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ fuel,
    Halted P (run P fuel (initCfg x)) ∧
    logTimeUpto P fuel (initCfg x) ≤ T x.length ∧
    (x ∈ L → (run P fuel (initCfg x)).verdict = 1) ∧
    (x ∉ L → (run P fuel (initCfg x)).verdict = 0)

/-- `P` decides `L` within logarithmic space `S(n)`: on every input `x`, the run
    halts with the correct verdict and peak space at most `S |x|`. Mirrors
    `TM.DecidesInSpace`. -/
def Program.DecidesInSpace (P : Program) (L : Language) (S : ℕ → ℕ) : Prop :=
  ∀ x, ∃ fuel,
    Halted P (run P fuel (initCfg x)) ∧
    spaceUpto P fuel (initCfg x) ≤ S x.length ∧
    (x ∈ L → (run P fuel (initCfg x)).verdict = 1) ∧
    (x ∉ L → (run P fuel (initCfg x)).verdict = 0)

end RAM

end Complexity

/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import Mathlib.Data.Finset.Sort

/-!
# Sparse RAM register stores on Turing tapes: definitions

This file defines the auditable representation boundary for simulating a RAM
with a Turing machine. A finite register file is represented by a list of
address/value pairs. Zero-valued registers are omitted. Words use a
self-delimiting binary code consisting of a unary width, a zero separator, and
exactly that many binary payload bits. Thus a word of bit-width `w` occupies
`2 * w + 1` tape cells.

`Snapshot` adds the program counter to a finite store. Its bit encoding begins
with the program counter and entry count, followed by the address and value of
each entry. The corresponding decoders are total `Option`-valued functions.

Proofs that the store operations implement functional register reads/writes
and that every codec round-trips live in the internal module.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Instr

/-- Maximum bit-width of an instruction's hardwired register indices,
immediate, and jump target. These literals are fixed with the program and are
therefore not charged as runtime indirect addresses by `Instr.logCost`. -/
def staticWidth : Instr → ℕ
  | .imm destination value => max (bitlen destination) (bitlen value)
  | .add destination source₀ source₁
  | .sub destination source₀ source₁
  | .mul destination source₀ source₁ =>
      max (bitlen destination) (max (bitlen source₀) (bitlen source₁))
  | .load destination addressRegister
  | .store destination addressRegister =>
      max (bitlen destination) (bitlen addressRegister)
  | .jz source target => max (bitlen source) (bitlen target)
  | .jmp target => bitlen target
  | .halt => 0

end Instr

/-- Maximum hardwired literal width appearing in a fixed RAM program. -/
def programStaticWidth : Program → ℕ
  | [] => 0
  | instruction :: rest =>
      max (RegisterStore.Instr.staticWidth instruction) (programStaticWidth rest)

/-- One sparse register entry: an address paired with its nonzero value. -/
abbrev Entry := ℕ × ℕ

/-- A finite sparse register file. -/
abbrev Store := List Entry

/-- Read an address from a sparse store, defaulting to zero. -/
def read : Store → ℕ → ℕ
  | [], _ => 0
  | (storedAddress, value) :: rest, address =>
      if address = storedAddress then value else read rest address

/-- Write one address in a sparse store. Writing zero removes the entry;
writing a nonzero value replaces the first matching entry or appends a fresh
entry when the address is absent. -/
def write : Store → ℕ → ℕ → Store
  | [], address, value => if value = 0 then [] else [(address, value)]
  | entry@(storedAddress, _) :: rest, address, value =>
      if address = storedAddress then
        if value = 0 then rest else (address, value) :: rest
      else entry :: write rest address value

/-- No address occurs twice in a sparse store. -/
def AddressesNodup (store : Store) : Prop :=
  (store.map Prod.fst).Nodup

/-- Every materialized entry carries a nonzero value. -/
def ValuesNonzero (store : Store) : Prop :=
  ∀ entry ∈ store, entry.2 ≠ 0

/-- A canonical sparse store has unique addresses and omits zero values. -/
def Canonical (store : Store) : Prop :=
  AddressesNodup store ∧ ValuesNonzero store

/-- Decode a sparse store into the RAM model's total register file. -/
def decode (store : Store) : ℕ → ℕ :=
  read store

/-- A finite sparse store represents a total RAM register file exactly. -/
def Represents (store : Store) (regs : ℕ → ℕ) : Prop :=
  Canonical store ∧ decode store = regs

/-- Maximum address/value bit-width materialized in a sparse store. -/
def maxWidth : Store → ℕ
  | [] => 0
  | entry :: rest =>
      max (bitlen entry.1) (max (bitlen entry.2) (maxWidth rest))

/-- Materialize the finite support of a total register file as a sparse store. -/
noncomputable def ofRegs (regs : ℕ → ℕ)
    (hfinite : (Function.support regs).Finite) : Store :=
  hfinite.toFinset.toList.map fun address => (address, regs address)

/-- Nonzero public-input registers, selected from the known finite input range. -/
def initialAddresses (input : List Bool) : Finset ℕ :=
  (Finset.range (input.length + 1)).filter fun address => initRegs input address ≠ 0

/-- Canonical sparse materialization of the RAM public-input register file. -/
def initialStore (input : List Bool) : Store :=
  ((initialAddresses input).sort (· ≤ ·)).map fun address =>
    (address, initRegs input address)

/-! ## Self-delimiting binary words -/

namespace WordCode

/-- Encode a natural as unary bit-width, a zero separator, and fixed-width
little-endian payload bits. The payload convention matches the library's
canonical binary-arithmetic work tapes. -/
def encode (value : ℕ) : List Bool :=
  List.replicate (bitlen value) true ++
    false :: Nat.toBitsLE (bitlen value) value

/-- Parse the unary-width prefix, then consume exactly that many payload bits. -/
def decodeAux? : List Bool → ℕ → Option (ℕ × List Bool)
  | [], _ => none
  | true :: rest, width => decodeAux? rest (width + 1)
  | false :: rest, width =>
      if width ≤ rest.length then
        some (Nat.fromBitsLE (rest.take width), rest.drop width)
      else
        none

/-- Parse one self-delimiting binary word and return the unconsumed suffix. -/
def decodePrefix? (bits : List Bool) : Option (ℕ × List Bool) :=
  decodeAux? bits 0

end WordCode

namespace Entry

/-- Serialize an address/value entry as two self-delimiting words. -/
def encode (entry : Entry) : List Bool :=
  WordCode.encode entry.1 ++ WordCode.encode entry.2

/-- Parse one address/value entry and return the unconsumed suffix. -/
def decodePrefix? (bits : List Bool) : Option (Entry × List Bool) := do
  let (address, rest) ← WordCode.decodePrefix? bits
  let (value, rest) ← WordCode.decodePrefix? rest
  pure ((address, value), rest)

end Entry

/-- Number of tape cells occupied by the concatenated self-delimiting codes of
the live sparse-store entries. Unlike `Snapshot.sizeBound`, this charges the
actual width of every entry instead of multiplying the entry count by one
run-wide maximum width. -/
def encodedStoreLength (store : Store) : ℕ :=
  (store.flatMap Entry.encode).length

/-- Parse exactly `count` sparse entries and return the unconsumed suffix. -/
def decodeEntries? : ℕ → List Bool → Option (Store × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (entry, rest) ← Entry.decodePrefix? bits
      let (entries, rest) ← decodeEntries? count rest
      pure (entry :: entries, rest)

/-- A finite RAM snapshot: program counter plus sparse register store. -/
structure Snapshot where
  /-- Program counter of the represented RAM configuration. -/
  pc : ℕ
  /-- Materialized nonzero register entries. -/
  store : Store
  deriving DecidableEq

namespace Snapshot

/-- Decode a finite snapshot to a RAM configuration. -/
def decode (snapshot : Snapshot) : Cfg where
  pc := snapshot.pc
  regs := RegisterStore.decode snapshot.store

/-- Serialize a snapshot as program counter, entry count, and entries. -/
def encode (snapshot : Snapshot) : List Bool :=
  WordCode.encode snapshot.pc ++
    WordCode.encode snapshot.store.length ++
    snapshot.store.flatMap Entry.encode

/-- Parse one snapshot prefix and return the unconsumed suffix. -/
def decodePrefix? (bits : List Bool) : Option (Snapshot × List Bool) := do
  let (pc, rest) ← WordCode.decodePrefix? bits
  let (count, rest) ← WordCode.decodePrefix? rest
  let (store, rest) ← decodeEntries? count rest
  pure ({ pc, store }, rest)

/-- Decode an exact snapshot code, rejecting trailing bits. -/
def decode? (bits : List Bool) : Option Snapshot := do
  let (snapshot, rest) ← decodePrefix? bits
  if rest.isEmpty then pure snapshot else none

/-- A canonical snapshot represents a RAM configuration exactly. -/
def Represents (snapshot : Snapshot) (cfg : Cfg) : Prop :=
  RegisterStore.Canonical snapshot.store ∧ snapshot.decode = cfg

/-- One width envelope for the program counter, entry count, addresses, and
values of a finite snapshot. -/
def width (snapshot : Snapshot) : ℕ :=
  max (bitlen snapshot.pc)
    (max (bitlen snapshot.store.length) (RegisterStore.maxWidth snapshot.store))

/-- Concrete tape-cell envelope for the canonical snapshot encoding. -/
def sizeBound (snapshot : Snapshot) : ℕ :=
  (snapshot.store.length + 1) * (4 * snapshot.width + 2)

/-- One-step width envelope: old width plus one, or a width explicitly exposed
by the instruction literal or its logarithmic runtime charge. -/
def stepWidthBound (instruction : Instr) (snapshot : Snapshot) : ℕ :=
  max (snapshot.width + 1)
    (max (RegisterStore.Instr.staticWidth instruction)
      (instruction.logCost snapshot.decode))

/-- Materialize a RAM configuration whose register support is finite. -/
noncomputable def ofCfg (cfg : Cfg)
    (hfinite : (Function.support cfg.regs).Finite) : Snapshot where
  pc := cfg.pc
  store := RegisterStore.ofRegs cfg.regs hfinite

/-- Canonical finite snapshot of the RAM public-input configuration. -/
def initial (input : List Bool) : Snapshot where
  pc := 0
  store := RegisterStore.initialStore input

/-- The instruction selected by a finite snapshot. -/
def curInstr (program : Program) (snapshot : Snapshot) : Instr :=
  (program[snapshot.pc]?).getD Instr.halt

/-- Execute one RAM instruction directly on the sparse finite store. -/
def stepInstr : Instr → Snapshot → Snapshot
  | .imm destination value, snapshot =>
      { pc := snapshot.pc + 1
        store := write snapshot.store destination value }
  | .add destination source₀ source₁, snapshot =>
      { pc := snapshot.pc + 1
        store := write snapshot.store destination
          (read snapshot.store source₀ + read snapshot.store source₁) }
  | .sub destination source₀ source₁, snapshot =>
      { pc := snapshot.pc + 1
        store := write snapshot.store destination
          (read snapshot.store source₀ - read snapshot.store source₁) }
  | .mul destination source₀ source₁, snapshot =>
      { pc := snapshot.pc + 1
        store := write snapshot.store destination
          (read snapshot.store source₀ * read snapshot.store source₁) }
  | .load destination addressRegister, snapshot =>
      { pc := snapshot.pc + 1
        store := write snapshot.store destination
          (read snapshot.store (read snapshot.store addressRegister)) }
  | .store addressRegister source, snapshot =>
      { pc := snapshot.pc + 1
        store := write snapshot.store (read snapshot.store addressRegister)
          (read snapshot.store source) }
  | .jz source target, snapshot =>
      if read snapshot.store source = 0 then
        { snapshot with pc := target }
      else
        { snapshot with pc := snapshot.pc + 1 }
  | .jmp target, snapshot =>
      { snapshot with pc := target }
  | .halt, snapshot => snapshot

/-- Execute the selected RAM instruction on a sparse snapshot. -/
def step (program : Program) (snapshot : Snapshot) : Snapshot :=
  stepInstr (curInstr program snapshot) snapshot

/-- A sparse snapshot is halted exactly when its selected instruction is halt. -/
def Halted (program : Program) (snapshot : Snapshot) : Prop :=
  curInstr program snapshot = Instr.halt

instance (program : Program) (snapshot : Snapshot) : Decidable (Halted program snapshot) := by
  unfold Halted
  infer_instance

/-- Fuel-bounded sparse execution, stopping at the first halted snapshot. -/
def run (program : Program) : ℕ → Snapshot → Snapshot
  | 0, snapshot => snapshot
  | fuel + 1, snapshot =>
      if Halted program snapshot then snapshot
      else run program fuel (step program snapshot)

end Snapshot

end RegisterStore

end RAM

end Complexity

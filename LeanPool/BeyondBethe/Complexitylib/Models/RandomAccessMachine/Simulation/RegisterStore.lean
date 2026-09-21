/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Internal

/-!
# Sparse RAM register stores on Turing tapes

This module exposes the representation boundary used by the RAM-to-Turing-
machine simulation. A canonical finite list of nonzero address/value pairs
decodes to the RAM model's total register file. Functional reads and writes are
exact, every finite-support register file has a canonical representation, and
the self-delimiting binary snapshot codec round-trips.

The concrete length theorem is the first resource bridge for the reverse
simulation: if the program counter, entry count, addresses, and values all have
bit-width at most `w`, a snapshot with `m` entries occupies at most
`(m + 1) * (4 * w + 2)` tape cells.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

/-- Sparse writing implements functional update exactly when addresses are
unique. -/
theorem read_write (store : Store) (hstore : AddressesNodup store)
    (address value target : ℕ) :
    read (write store address value) target =
      Function.update (read store) address value target :=
  read_write_internal store hstore address value target

/-- Sparse writing preserves unique addresses and omission of zero values. -/
theorem write_canonical (store : Store) (hstore : Canonical store)
    (address value : ℕ) :
    Canonical (write store address value) :=
  write_canonical_internal store hstore address value

/-- Decoding after a sparse write is exactly functional update. -/
theorem decode_write (store : Store) (hstore : AddressesNodup store)
    (address value : ℕ) :
    decode (write store address value) = Function.update (decode store) address value :=
  decode_write_internal store hstore address value

/-- Materializing any finite-support register file gives a canonical exact
representation. -/
theorem ofRegs_represents (regs : ℕ → ℕ)
    (hfinite : (Function.support regs).Finite) :
    Represents (ofRegs regs hfinite) regs :=
  ofRegs_represents_internal regs hfinite

/-- The canonical public-input store has at most one entry per initialized
register. -/
theorem initialStore_length_le (input : List Bool) :
    (initialStore input).length ≤ input.length + 1 :=
  initialStore_length_le_internal input

namespace WordCode

/-- A canonical word code parses to its value and leaves any suffix untouched. -/
theorem decodePrefix?_encode_append (value : ℕ) (suffix : List Bool) :
    decodePrefix? (encode value ++ suffix) = some (value, suffix) :=
  decodePrefix?_encode_append_internal value suffix

/-- One self-delimiting word occupies twice its bit-width plus one cell. -/
theorem encode_length (value : ℕ) :
    (encode value).length = 2 * bitlen value + 1 :=
  encode_length_internal value

end WordCode

namespace Entry

/-- A canonical address/value code parses exactly and leaves its suffix. -/
theorem decodePrefix?_encode_append (entry : Entry) (suffix : List Bool) :
    decodePrefix? (encode entry ++ suffix) = some (entry, suffix) :=
  decodePrefix?_encode_append_internal entry suffix

/-- An encoded entry charges twice the address width, twice the value width,
and two separators. -/
theorem encode_length (entry : Entry) :
    (encode entry).length = 2 * bitlen entry.1 + 2 * bitlen entry.2 + 2 :=
  encode_length_internal entry

end Entry

/-- One sparse write increases the actual encoded store by at most the code of
the address/value pair being written. Replacement and deletion can only make
this estimate smaller. -/
theorem encodedStoreLength_write_le (store : Store) (address value : ℕ) :
    encodedStoreLength (write store address value) ≤
      encodedStoreLength store + (Entry.encode (address, value)).length :=
  encodedStoreLength_write_le_internal store address value

namespace Snapshot

/-- The explicit finite public-input snapshot decodes to `RAM.initCfg`. -/
theorem initial_represents (input : List Bool) :
    (initial input).Represents (RAM.initCfg input) :=
  initial_represents_internal input

/-- The public-input snapshot's intrinsic width is at most the width of
`|input| + 1`. -/
theorem initial_width_le (input : List Bool) :
    (initial input).width ≤ bitlen (input.length + 1) :=
  initial_width_le_internal input

/-- Materializing a finite-support RAM configuration gives a canonical exact
snapshot. -/
theorem ofCfg_represents (cfg : Cfg)
    (hfinite : (Function.support cfg.regs).Finite) :
    (ofCfg cfg hfinite).Represents cfg :=
  ofCfg_represents_internal cfg hfinite

/-- One sparse interpreter instruction preserves canonicality. -/
theorem stepInstr_canonical (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (stepInstr instruction snapshot).store :=
  stepInstr_canonical_internal instruction snapshot hcanonical

/-- Decoding commutes exactly with one sparse interpreter instruction. -/
theorem decode_stepInstr (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (stepInstr instruction snapshot).decode =
      RAM.stepInstr instruction snapshot.decode :=
  decode_stepInstr_internal instruction snapshot hcanonical

/-- The selected sparse step preserves canonicality. -/
theorem step_canonical (program : Program) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (snapshot.step program).store :=
  step_canonical_internal program snapshot hcanonical

/-- Decoding commutes exactly with the selected RAM step. -/
theorem decode_step (program : Program) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.step program).decode = RAM.step program snapshot.decode :=
  decode_step_internal program snapshot hcanonical

/-- One sparse interpreter instruction grows the intrinsic width only to the
maximum of the old width plus one, its fixed literal width, and its charged
logarithmic runtime width. -/
theorem width_stepInstr_le (instruction : Instr) (snapshot : Snapshot) :
    (stepInstr instruction snapshot).width ≤ snapshot.stepWidthBound instruction :=
  width_stepInstr_le_internal instruction snapshot

/-- A selected sparse step is bounded by the fixed program's literal width and
the RAM step's logarithmic charge. -/
theorem width_step_le (program : Program) (snapshot : Snapshot) :
    (snapshot.step program).width ≤
      max (snapshot.width + 1)
        (max (programStaticWidth program) (RAM.stepLogCost program snapshot.decode)) :=
  width_step_le_internal program snapshot

/-- Every finite sparse run preserves canonicality. -/
theorem run_canonical (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (snapshot.run program fuel).store :=
  run_canonical_internal program fuel snapshot hcanonical

/-- The complete sparse interpreter run decodes to the executable RAM run. -/
theorem decode_run (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).decode = RAM.run program fuel snapshot.decode :=
  decode_run_internal program fuel snapshot hcanonical

/-- Each RAM instruction materializes at most one additional sparse entry. -/
theorem length_run_le (program : Program) (fuel : ℕ) (snapshot : Snapshot) :
    Canonical snapshot.store →
    (snapshot.run program fuel).store.length ≤
      snapshot.store.length + RAM.unitTimeUpto program fuel snapshot.decode :=
  length_run_le_internal program fuel snapshot

/-- Along a canonical sparse run, width grows linearly with executed fuel, the
fixed program literal width, and accumulated logarithmic RAM time. -/
theorem width_run_le (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).width ≤
      snapshot.width + RAM.unitTimeUpto program fuel snapshot.decode *
        (programStaticWidth program + 1) +
        RAM.logTimeUpto program fuel snapshot.decode :=
  width_run_le_internal program fuel snapshot hcanonical

/-- The live sparse-store code has amortized growth controlled by the resources actually
charged by the RAM run. In particular, this avoids the spurious product of the
number of entries and the maximum entry width: each executed instruction pays
once for its fixed destination width and for the operand/result bits in its
logarithmic cost. -/
theorem encodedStoreLength_run_le (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    encodedStoreLength (snapshot.run program fuel).store ≤
      encodedStoreLength snapshot.store +
        4 * (RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) :=
  encodedStoreLength_run_le_internal program fuel snapshot hcanonical

/-- Canonical snapshot serialization round-trips exactly. -/
theorem decode?_encode (snapshot : Snapshot) :
    decode? snapshot.encode = some snapshot :=
  decode?_encode_internal snapshot

/-- A width-`w`, `m`-entry RAM snapshot occupies at most
`(m + 1) * (4 * w + 2)` Turing-tape cells. -/
theorem encode_length_le (snapshot : Snapshot) (width : ℕ)
    (hpc : bitlen snapshot.pc ≤ width)
    (hcount : bitlen snapshot.store.length ≤ width)
    (hstore : ∀ entry ∈ snapshot.store,
      bitlen entry.1 ≤ width ∧ bitlen entry.2 ≤ width) :
    snapshot.encode.length ≤ (snapshot.store.length + 1) * (4 * width + 2) :=
  encode_length_le_internal snapshot width hpc hcount hstore

/-- Every canonical snapshot code satisfies its intrinsic concrete tape-cell
envelope, without external side conditions. -/
theorem encode_length_le_sizeBound (snapshot : Snapshot) :
    snapshot.encode.length ≤ snapshot.sizeBound :=
  encode_length_le_sizeBound_internal snapshot

/-- A snapshot code is bounded by its actual live-entry encoding plus the two
header words. This is the width-sensitive alternative to the product envelope
`Snapshot.sizeBound`. -/
theorem encode_length_le_encodedStore (snapshot : Snapshot) :
    snapshot.encode.length ≤
      encodedStoreLength snapshot.store + 4 * snapshot.width + 2 :=
  encode_length_le_encodedStore_internal snapshot

/-- Combining the actual live-store charge with the width invariant gives a
linear-in-accumulated-cost representation bound for every canonical sparse
run, relative to the initial sparse encoding. -/
theorem encode_run_length_le_amortized (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      encodedStoreLength snapshot.store + 4 * snapshot.width +
        8 * (RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2 :=
  encode_run_length_le_amortized_internal program fuel snapshot hcanonical

/-- The materialized public-input store occupies at most one fixed-width entry
per initialized register. This records the current ABI's explicit
`O(n log n)` initialization term. -/
theorem encodedStoreLength_initial_le (input : List Bool) :
    encodedStoreLength (initialStore input) ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) :=
  encodedStoreLength_initial_le_internal input

/-- Public-input specialization of the amortized live-representation bound.
The accumulated part is linear in charged RAM time; the separate
`n * bitlen n` term comes from eagerly materializing all nonzero input
registers in the current snapshot ABI. -/
theorem encode_initial_run_length_le_amortized
    (program : Program) (fuel : ℕ) (input : List Bool) :
    ((initial input).run program fuel).encode.length ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) +
        4 * bitlen (input.length + 1) +
        8 * (RAM.logTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 2)) + 2 :=
  encode_initial_run_length_le_amortized_internal program fuel input

/-- The canonical code of every reachable snapshot has an explicit product
bound: entry count grows by at most one per step, while width grows only with
fixed program literals and charged logarithmic RAM time. -/
theorem encode_run_length_le (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      (snapshot.store.length + RAM.unitTimeUpto program fuel snapshot.decode + 1) *
        (4 * (snapshot.width + RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2) :=
  encode_run_length_le_internal program fuel snapshot hcanonical

/-- Eliminating actual step count via `unitTimeUpto ≤ logTimeUpto` gives a
pure logarithmic-time tape-size envelope. This is the quadratic representation
bound needed by the RAM-to-TM simulation. -/
theorem encode_run_length_le_logTime (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      (snapshot.store.length + RAM.logTimeUpto program fuel snapshot.decode + 1) *
        (4 * (snapshot.width + RAM.logTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2) :=
  encode_run_length_le_logTime_internal program fuel snapshot hcanonical

/-- From the public RAM ABI, every reachable snapshot code has an explicit
quadratic envelope in input length, logarithmic RAM time, and one fixed program
constant. -/
theorem encode_initial_run_length_le_logTime
    (program : Program) (fuel : ℕ) (input : List Bool) :
    ((initial input).run program fuel).encode.length ≤
      (input.length + 1 + RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) *
        (4 * (bitlen (input.length + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input) *
            (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input)) + 2) :=
  encode_initial_run_length_le_logTime_internal program fuel input

end Snapshot

end RegisterStore

end RAM

end Complexity

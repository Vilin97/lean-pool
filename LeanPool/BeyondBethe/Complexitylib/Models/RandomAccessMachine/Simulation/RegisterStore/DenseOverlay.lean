/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Internal

/-!
# Dense public input with a sparse mutable overlay

This module exposes the semantic representation used by the optimized
RAM-to-Turing simulation. The immutable public input is not duplicated in the
mutable snapshot; positive tags make explicit writes of zero distinguishable
from an absent overlay entry.
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace DenseOverlay

/-- With no mutable entries, reads agree exactly with the public RAM input ABI. -/
theorem read_empty (input : List Bool) (address : ℕ) :
    read input [] address = RAM.initRegs input address :=
  read_empty_internal input address

/-- A positive-tag overlay write implements functional update, including an
explicit write of zero over a nonzero public-input bit. -/
theorem read_write (input : List Bool) (overlay : Store)
    (hcanonical : Canonical overlay) (address value : ℕ) :
    read input (write overlay address value) =
      Function.update (read input overlay) address value :=
  read_write_internal input overlay hcanonical address value

/-- Every overlay write preserves unique addresses and positive tags. -/
theorem write_canonical (overlay : Store) (hcanonical : Canonical overlay)
    (address value : ℕ) : Canonical (write overlay address value) :=
  write_canonical_internal overlay hcanonical address value

/-- Materializing a positive tag preserves the invariant that register zero
never falls through to the dense input bank. -/
theorem write_coversZero (overlay : Store) (hcanonical : Canonical overlay)
    (hcovers : CoversZero overlay) (address value : ℕ) :
    CoversZero (write overlay address value) :=
  write_coversZero_internal overlay hcanonical hcovers address value

/-- The empty mutable overlay already decodes to the complete public RAM input
configuration. -/
theorem Snapshot.initial_decode (input : List Bool) :
    (Snapshot.initial input).decode input = RAM.initCfg input :=
  Snapshot.initial_decode_internal input

/-- The initial one-entry overlay is canonical. -/
theorem Snapshot.initial_canonical (input : List Bool) :
    Canonical (Snapshot.initial input).overlay :=
  Snapshot.initial_canonical_internal input

/-- The initial overlay materializes register zero. -/
theorem Snapshot.initial_coversZero (input : List Bool) :
    CoversZero (Snapshot.initial input).overlay :=
  Snapshot.initial_coversZero_internal input

/-- The initial overlay satisfies the full representation invariant. -/
theorem Snapshot.initial_valid (input : List Bool) :
    Valid (Snapshot.initial input).overlay :=
  Snapshot.initial_valid_internal input

/-- Decoding commutes exactly with one selected instruction. -/
theorem Snapshot.decode_stepInstr (input : List Bool) (instruction : Instr)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.overlay) :
    (snapshot.stepInstr input instruction).decode input =
      RAM.stepInstr instruction (snapshot.decode input) :=
  Snapshot.decode_stepInstr_internal input instruction snapshot hcanonical

/-- One selected instruction preserves overlay canonicality. -/
theorem Snapshot.stepInstr_canonical (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    Canonical (snapshot.stepInstr input instruction).overlay :=
  Snapshot.stepInstr_canonical_internal input instruction snapshot hcanonical

/-- One selected instruction preserves materialization of register zero. -/
theorem Snapshot.stepInstr_coversZero (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hvalid : Valid snapshot.overlay) :
    CoversZero (snapshot.stepInstr input instruction).overlay :=
  Snapshot.stepInstr_coversZero_internal input instruction snapshot hvalid

/-- One selected instruction preserves the full overlay invariant. -/
theorem Snapshot.stepInstr_valid (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.stepInstr input instruction).overlay :=
  Snapshot.stepInstr_valid_internal input instruction snapshot hvalid

/-- Decoding commutes exactly with one program-selected RAM step. -/
theorem Snapshot.decode_step (program : Program) (input : List Bool)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.overlay) :
    (snapshot.step program input).decode input =
      RAM.step program (snapshot.decode input) :=
  Snapshot.decode_step_internal program input snapshot hcanonical

/-- Every program-selected step preserves overlay canonicality. -/
theorem Snapshot.step_canonical (program : Program) (input : List Bool)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.overlay) :
    Canonical (snapshot.step program input).overlay :=
  Snapshot.step_canonical_internal program input snapshot hcanonical

/-- One program-selected step preserves the full overlay invariant. -/
theorem Snapshot.step_valid (program : Program) (input : List Bool)
    (snapshot : Snapshot) (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.step program input).overlay :=
  Snapshot.step_valid_internal program input snapshot hvalid

/-- A complete fuel-bounded dense-overlay execution decodes to the ordinary
RAM run. -/
theorem Snapshot.decode_run (program : Program) (input : List Bool)
    (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    (snapshot.run program input fuel).decode input =
      RAM.run program fuel (snapshot.decode input) :=
  Snapshot.decode_run_internal program input fuel snapshot hcanonical

/-- Every fuel-bounded dense-overlay execution remains canonical. -/
theorem Snapshot.run_canonical (program : Program) (input : List Bool)
    (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    Canonical (snapshot.run program input fuel).overlay :=
  Snapshot.run_canonical_internal program input fuel snapshot hcanonical

/-- A complete dense-overlay run preserves the full representation invariant. -/
theorem Snapshot.run_valid (program : Program) (input : List Bool)
    (fuel : ℕ) (snapshot : Snapshot) (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.run program input fuel).overlay :=
  Snapshot.run_valid_internal program input fuel snapshot hvalid

/-- One tagged write adds at most one mutable overlay entry. -/
theorem write_length_le (overlay : Store) (address value : ℕ) :
    (write overlay address value).length ≤ overlay.length + 1 :=
  write_length_le_internal overlay address value

/-- One selected instruction adds at most one mutable overlay entry. -/
theorem Snapshot.length_stepInstr_le (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot) :
    (snapshot.stepInstr input instruction).overlay.length ≤
      snapshot.overlay.length + 1 :=
  Snapshot.length_stepInstr_le_internal input instruction snapshot

/-- A dense-overlay run materializes at most one entry per executed RAM step. -/
theorem Snapshot.length_run_le (program : Program) (input : List Bool)
    (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    (snapshot.run program input fuel).overlay.length ≤
      snapshot.overlay.length +
        RAM.unitTimeUpto program fuel (snapshot.decode input) :=
  Snapshot.length_run_le_internal program input fuel snapshot hcanonical

/-- A tagged write increases the live overlay code by at most the code of its
address and positive value tag. -/
theorem encodedStoreLength_write_le (overlay : Store)
    (address value : ℕ) :
    encodedStoreLength (write overlay address value) ≤
      encodedStoreLength overlay + (Entry.encode (address, value + 1)).length :=
  encodedStoreLength_write_le_internal overlay address value

/-- One selected instruction grows the actual live overlay code linearly in
its fixed literal width and its logarithmic RAM charge. -/
theorem Snapshot.encodedStoreLength_stepInstr_le (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot) :
    encodedStoreLength (snapshot.stepInstr input instruction).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (RegisterStore.Instr.staticWidth instruction +
          instruction.logCost (snapshot.decode input) + 1) :=
  Snapshot.encodedStoreLength_stepInstr_le_internal input instruction snapshot

/-- One program-selected step satisfies the same live-code bound using the
fixed program's maximum literal width. -/
theorem Snapshot.encodedStoreLength_step_le (program : Program)
    (input : List Bool) (snapshot : Snapshot) :
    encodedStoreLength (snapshot.step program input).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (programStaticWidth program +
          RAM.stepLogCost program (snapshot.decode input) + 1) :=
  Snapshot.encodedStoreLength_step_le_internal program input snapshot

/-- The live mutable overlay has amortized encoded growth linear in the work
actually charged by the RAM run; the immutable public input contributes no
repeated sparse-store term. -/
theorem Snapshot.encodedStoreLength_run_le (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    encodedStoreLength (snapshot.run program input fuel).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (RAM.unitTimeUpto program fuel (snapshot.decode input) *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (snapshot.decode input)) :=
  Snapshot.encodedStoreLength_run_le_internal program input fuel snapshot hcanonical

/-- Starting from the public ABI, mutable entry count is bounded solely by the
executed step count. -/
theorem Snapshot.initial_length_run_le (program : Program)
    (input : List Bool) (fuel : ℕ) :
    ((Snapshot.initial input).run program input fuel).overlay.length ≤
      1 + RAM.unitTimeUpto program fuel (RAM.initCfg input) :=
  Snapshot.initial_length_run_le_internal program input fuel

/-- Starting from the public ABI, live mutable code is linear in accumulated
RAM cost and carries no eager `input.length * bitlen input.length` term. -/
theorem Snapshot.initial_encodedStoreLength_run_le
    (program : Program) (input : List Bool) (fuel : ℕ) :
    encodedStoreLength
        ((Snapshot.initial input).run program input fuel).overlay ≤
      2 * bitlen (input.length + 1) + 2 +
        2 * (RAM.unitTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input)) :=
  Snapshot.initial_encodedStoreLength_run_le_internal program input fuel

/-- The initial snapshot contains only the two headers and the tagged `R₀`
length entry; public input bits remain in the immutable bank. -/
theorem Snapshot.initial_encode_length (input : List Bool) :
    (Snapshot.initial input).encode.length =
      2 * bitlen (input.length + 1) + 6 :=
  Snapshot.initial_encode_length_internal input

end DenseOverlay
end RegisterStore
end RAM
end Complexity

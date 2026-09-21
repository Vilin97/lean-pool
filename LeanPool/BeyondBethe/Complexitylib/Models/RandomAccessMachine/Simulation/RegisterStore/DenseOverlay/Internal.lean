/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Internal

/-!
# Dense public input with a sparse mutable overlay -- proof internals
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace DenseOverlay

theorem read_empty_internal (input : List Bool) (address : ℕ) :
    read input [] address = RAM.initRegs input address := by
  simp [read, RegisterStore.read]

theorem read_write_internal (input : List Bool) (overlay : Store)
    (hcanonical : Canonical overlay) (address value : ℕ) :
    read input (write overlay address value) =
      Function.update (read input overlay) address value := by
  funext target
  have htag := RegisterStore.read_write_internal overlay hcanonical.1
    address (value + 1) target
  unfold read write
  rw [htag]
  by_cases htarget : target = address
  · subst target
    simp
  · simp [Function.update, htarget]

theorem write_canonical_internal (overlay : Store)
    (hcanonical : Canonical overlay) (address value : ℕ) :
    Canonical (write overlay address value) := by
  exact RegisterStore.write_canonical_internal overlay hcanonical address
    (value + 1)

theorem write_coversZero_internal (overlay : Store)
    (hcanonical : Canonical overlay) (hcovers : CoversZero overlay)
    (address value : ℕ) : CoversZero (write overlay address value) := by
  have hread := RegisterStore.read_write_internal overlay hcanonical.1
    address (value + 1) 0
  unfold CoversZero write
  rw [hread]
  by_cases haddress : address = 0
  · subst address
    simp
  · simpa [Function.update, haddress, Ne.symm haddress] using hcovers

theorem Snapshot.initial_decode_internal (input : List Bool) :
    (Snapshot.initial input).decode input = RAM.initCfg input := by
  apply RAM.Cfg.ext
  · rfl
  · funext address
    change read input (write [] 0 input.length) address =
      RAM.initRegs input address
    rw [read_write_internal input []
      (by simp [RegisterStore.Canonical, RegisterStore.AddressesNodup,
        RegisterStore.ValuesNonzero])]
    by_cases haddress : address = 0
    · subst address
      simp [Function.update, RAM.initRegs]
    · simp [Function.update, haddress, read_empty_internal, RAM.initRegs]

theorem Snapshot.initial_canonical_internal (input : List Bool) :
    Canonical (Snapshot.initial input).overlay := by
  exact write_canonical_internal []
    (by simp [RegisterStore.Canonical, RegisterStore.AddressesNodup,
      RegisterStore.ValuesNonzero]) 0 input.length

theorem Snapshot.initial_coversZero_internal (input : List Bool) :
    CoversZero (Snapshot.initial input).overlay := by
  unfold Snapshot.initial CoversZero DenseOverlay.write
  simp [RegisterStore.write, RegisterStore.read]

theorem Snapshot.initial_valid_internal (input : List Bool) :
    Valid (Snapshot.initial input).overlay :=
  ⟨Snapshot.initial_canonical_internal input,
    Snapshot.initial_coversZero_internal input⟩

theorem Snapshot.decode_stepInstr_internal (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    (snapshot.stepInstr input instruction).decode input =
      RAM.stepInstr instruction (snapshot.decode input) := by
  cases instruction with
  | imm destination value =>
      apply RAM.Cfg.ext
      · rfl
      · exact read_write_internal input snapshot.overlay hcanonical
          destination value
  | add destination source₀ source₁ =>
      apply RAM.Cfg.ext
      · rfl
      · exact read_write_internal input snapshot.overlay hcanonical destination _
  | sub destination source₀ source₁ =>
      apply RAM.Cfg.ext
      · rfl
      · exact read_write_internal input snapshot.overlay hcanonical destination _
  | mul destination source₀ source₁ =>
      apply RAM.Cfg.ext
      · rfl
      · exact read_write_internal input snapshot.overlay hcanonical destination _
  | load destination addressRegister =>
      apply RAM.Cfg.ext
      · rfl
      · exact read_write_internal input snapshot.overlay hcanonical destination _
  | store addressRegister source =>
      apply RAM.Cfg.ext
      · rfl
      · exact read_write_internal input snapshot.overlay hcanonical _ _
  | jz source target =>
      simp only [Snapshot.stepInstr, RAM.stepInstr, Snapshot.decode]
      split <;> simp_all [DenseOverlay.decode]
  | jmp target => rfl
  | halt => rfl

theorem Snapshot.stepInstr_canonical_internal (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    Canonical (snapshot.stepInstr input instruction).overlay := by
  cases instruction <;> simp only [Snapshot.stepInstr]
  all_goals first
    | exact write_canonical_internal snapshot.overlay hcanonical _ _
    | split <;> exact hcanonical
    | exact hcanonical

theorem Snapshot.stepInstr_coversZero_internal (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hvalid : Valid snapshot.overlay) :
    CoversZero (snapshot.stepInstr input instruction).overlay := by
  cases instruction <;> simp only [Snapshot.stepInstr]
  all_goals first
    | exact write_coversZero_internal snapshot.overlay hvalid.1 hvalid.2 _ _
    | split <;> exact hvalid.2
    | exact hvalid.2

theorem Snapshot.stepInstr_valid_internal (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot)
    (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.stepInstr input instruction).overlay :=
  ⟨Snapshot.stepInstr_canonical_internal input instruction snapshot hvalid.1,
    Snapshot.stepInstr_coversZero_internal input instruction snapshot hvalid⟩

theorem Snapshot.decode_step_internal (program : Program) (input : List Bool)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.overlay) :
    (snapshot.step program input).decode input =
      RAM.step program (snapshot.decode input) := by
  unfold Snapshot.step RAM.step Snapshot.curInstr RAM.curInstr
  rw [Snapshot.decode_stepInstr_internal input _ snapshot hcanonical]
  rfl

theorem Snapshot.step_canonical_internal (program : Program)
    (input : List Bool) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    Canonical (snapshot.step program input).overlay := by
  exact Snapshot.stepInstr_canonical_internal input _ snapshot hcanonical

theorem Snapshot.step_valid_internal (program : Program)
    (input : List Bool) (snapshot : Snapshot)
    (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.step program input).overlay := by
  exact Snapshot.stepInstr_valid_internal input _ snapshot hvalid

theorem Snapshot.decode_run_internal (program : Program) (input : List Bool)
    (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    (snapshot.run program input fuel).decode input =
      RAM.run program fuel (snapshot.decode input) := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      simp only [Snapshot.run, RAM.run]
      have hhalted : snapshot.Halted program ↔
          RAM.Halted program (snapshot.decode input) := by
        unfold Snapshot.Halted RAM.Halted Snapshot.curInstr RAM.curInstr
        rfl
      by_cases hhalt : snapshot.Halted program
      · rw [ite_eq_left hhalt, ite_eq_left (hhalted.mp hhalt)]
      · rw [ite_eq_right hhalt, ite_eq_right (fun h => hhalt (hhalted.mpr h))]
        rw [ih (snapshot.step program input)
          (Snapshot.step_canonical_internal program input snapshot hcanonical)]
        rw [Snapshot.decode_step_internal program input snapshot hcanonical]

theorem Snapshot.run_canonical_internal (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    Canonical (snapshot.run program input fuel).overlay := by
  induction fuel generalizing snapshot with
  | zero => exact hcanonical
  | succ fuel ih =>
      simp only [Snapshot.run]
      split
      · exact hcanonical
      · exact ih (snapshot.step program input)
          (Snapshot.step_canonical_internal program input snapshot hcanonical)

theorem Snapshot.run_valid_internal (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : Snapshot)
    (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.run program input fuel).overlay := by
  induction fuel generalizing snapshot with
  | zero => exact hvalid
  | succ fuel ih =>
      simp only [Snapshot.run]
      split
      · exact hvalid
      · exact ih (snapshot.step program input)
          (Snapshot.step_valid_internal program input snapshot hvalid)

private theorem bitlen_succ_le (value : ℕ) :
    bitlen (value + 1) ≤ bitlen value + 1 := by
  rw [bitlen, bitlen, Nat.size_le]
  have hvalue := Nat.lt_size_self value
  have hpowPos : 0 < 2 ^ value.size := pow_pos (by omega) _
  rw [pow_succ]
  omega

theorem write_length_le_internal (overlay : Store) (address value : ℕ) :
    (write overlay address value).length ≤ overlay.length + 1 := by
  induction overlay with
  | nil => simp [write, RegisterStore.write]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedTag⟩
      by_cases haddress : address = storedAddress
      · subst address
        simp [write, RegisterStore.write]
      · have ih' : (RegisterStore.write rest address (value + 1)).length ≤
            rest.length + 1 := by
          simpa only [write] using ih
        simp only [write, RegisterStore.write, haddress, ite_false,
          List.length_cons]
        omega

theorem Snapshot.length_stepInstr_le_internal (input : List Bool)
    (instruction : Instr) (snapshot : Snapshot) :
    (snapshot.stepInstr input instruction).overlay.length ≤
      snapshot.overlay.length + 1 := by
  cases instruction with
  | imm destination value =>
      exact write_length_le_internal snapshot.overlay destination value
  | add destination source₀ source₁ =>
      exact write_length_le_internal snapshot.overlay destination _
  | sub destination source₀ source₁ =>
      exact write_length_le_internal snapshot.overlay destination _
  | mul destination source₀ source₁ =>
      exact write_length_le_internal snapshot.overlay destination _
  | load destination addressRegister =>
      exact write_length_le_internal snapshot.overlay destination _
  | store addressRegister source =>
      exact write_length_le_internal snapshot.overlay _ _
  | jz source target =>
      simp only [Snapshot.stepInstr]
      split <;> simp
  | jmp target => simp [Snapshot.stepInstr]
  | halt => simp [Snapshot.stepInstr]

theorem Snapshot.length_run_le_internal (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    (snapshot.run program input fuel).overlay.length ≤
      snapshot.overlay.length +
        RAM.unitTimeUpto program fuel (snapshot.decode input) := by
  induction fuel generalizing snapshot with
  | zero => simp [Snapshot.run, RAM.unitTimeUpto]
  | succ fuel ih =>
      rw [Snapshot.run, RAM.unitTimeUpto]
      have hhalted : snapshot.Halted program ↔
          RAM.Halted program (snapshot.decode input) := Iff.rfl
      by_cases hhalt : snapshot.Halted program
      · rw [ite_eq_left hhalt, ite_eq_left (hhalted.mp hhalt)]
        omega
      · rw [ite_eq_right hhalt, ite_eq_right (fun h => hhalt (hhalted.mpr h))]
        have hstep := Snapshot.length_stepInstr_le_internal input
          (snapshot.curInstr program) snapshot
        have hstep' : (snapshot.step program input).overlay.length ≤
            snapshot.overlay.length + 1 := by
          simpa only [Snapshot.step] using hstep
        have hnextCanonical := Snapshot.step_canonical_internal
          program input snapshot hcanonical
        have hrun := ih (snapshot.step program input) hnextCanonical
        rw [Snapshot.decode_step_internal program input snapshot hcanonical] at hrun
        omega

theorem encodedStoreLength_write_le_internal (overlay : Store)
    (address value : ℕ) :
    encodedStoreLength (write overlay address value) ≤
      encodedStoreLength overlay + (Entry.encode (address, value + 1)).length := by
  exact RegisterStore.encodedStoreLength_write_le_internal overlay address
    (value + 1)

theorem Snapshot.encodedStoreLength_stepInstr_le_internal
    (input : List Bool) (instruction : Instr) (snapshot : Snapshot) :
    encodedStoreLength (snapshot.stepInstr input instruction).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (RegisterStore.Instr.staticWidth instruction +
          instruction.logCost (snapshot.decode input) + 1) := by
  cases instruction with
  | imm destination value =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.overlay
        destination value
      have hsucc := bitlen_succ_le value
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost]
      omega
  | add destination source₀ source₁ =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.overlay
        destination
        (read input snapshot.overlay source₀ + read input snapshot.overlay source₁)
      have hsucc := bitlen_succ_le
        (read input snapshot.overlay source₀ + read input snapshot.overlay source₁)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, DenseOverlay.decode]
      omega
  | sub destination source₀ source₁ =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.overlay
        destination
        (read input snapshot.overlay source₀ - read input snapshot.overlay source₁)
      have hsub : bitlen
          (read input snapshot.overlay source₀ - read input snapshot.overlay source₁) ≤
          bitlen (read input snapshot.overlay source₀) :=
        Nat.size_le_size (Nat.sub_le _ _)
      have hsucc := bitlen_succ_le
        (read input snapshot.overlay source₀ - read input snapshot.overlay source₁)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, DenseOverlay.decode]
      omega
  | mul destination source₀ source₁ =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.overlay
        destination
        (read input snapshot.overlay source₀ * read input snapshot.overlay source₁)
      have hsucc := bitlen_succ_le
        (read input snapshot.overlay source₀ * read input snapshot.overlay source₁)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, DenseOverlay.decode]
      omega
  | load destination addressRegister =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.overlay
        destination
        (read input snapshot.overlay (read input snapshot.overlay addressRegister))
      have hsucc := bitlen_succ_le
        (read input snapshot.overlay (read input snapshot.overlay addressRegister))
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, DenseOverlay.decode]
      omega
  | store addressRegister source =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.overlay
        (read input snapshot.overlay addressRegister)
        (read input snapshot.overlay source)
      have hsucc := bitlen_succ_le (read input snapshot.overlay source)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, DenseOverlay.decode]
      omega
  | jz source target =>
      simp only [Snapshot.stepInstr]
      split <;> simp
  | jmp target => simp [Snapshot.stepInstr]
  | halt => simp [Snapshot.stepInstr]

private theorem staticWidth_curInstr_le (program : Program) (pc : ℕ) :
    RegisterStore.Instr.staticWidth ((program[pc]?).getD Instr.halt) ≤
      programStaticWidth program := by
  induction program generalizing pc with
  | nil => simp [programStaticWidth, RegisterStore.Instr.staticWidth]
  | cons instruction rest ih =>
      cases pc with
      | zero => simp [programStaticWidth]
      | succ pc =>
          simp only [List.getElem?_cons_succ]
          exact le_trans (ih pc) (le_max_right _ _)

theorem Snapshot.encodedStoreLength_step_le_internal (program : Program)
    (input : List Bool) (snapshot : Snapshot) :
    encodedStoreLength (snapshot.step program input).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (programStaticWidth program +
          RAM.stepLogCost program (snapshot.decode input) + 1) := by
  have hstep := Snapshot.encodedStoreLength_stepInstr_le_internal input
    (snapshot.curInstr program) snapshot
  have hstatic := staticWidth_curInstr_le program snapshot.pc
  apply le_trans hstep
  apply Nat.add_le_add_left
  have hcost : (snapshot.curInstr program).logCost (snapshot.decode input) =
      RAM.stepLogCost program (snapshot.decode input) := rfl
  rw [hcost]
  exact Nat.mul_le_mul_left 2
    (Nat.add_le_add_right (Nat.add_le_add_right hstatic _) 1)

theorem Snapshot.encodedStoreLength_run_le_internal (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    encodedStoreLength (snapshot.run program input fuel).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (RAM.unitTimeUpto program fuel (snapshot.decode input) *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (snapshot.decode input)) := by
  induction fuel generalizing snapshot with
  | zero => simp [Snapshot.run, RAM.unitTimeUpto, RAM.logTimeUpto]
  | succ fuel ih =>
      rw [Snapshot.run]
      have hhalted : snapshot.Halted program ↔
          RAM.Halted program (snapshot.decode input) := Iff.rfl
      by_cases hhalt : snapshot.Halted program
      · have hramHalted := hhalted.mp hhalt
        simp only [hhalt, hramHalted, if_true, RAM.unitTimeUpto,
          RAM.logTimeUpto]
        simp
      · have hramNotHalted : ¬RAM.Halted program (snapshot.decode input) :=
          fun h => hhalt (hhalted.mpr h)
        rw [ite_eq_right hhalt]
        simp only [RAM.unitTimeUpto, RAM.logTimeUpto, hramNotHalted,
          ite_false]
        have hstep := Snapshot.encodedStoreLength_step_le_internal
          program input snapshot
        have hnextCanonical := Snapshot.step_canonical_internal
          program input snapshot hcanonical
        have htail := ih (snapshot.step program input) hnextCanonical
        have hdecode := Snapshot.decode_step_internal
          program input snapshot hcanonical
        rw [hdecode] at htail
        calc
          encodedStoreLength
                (Snapshot.run program input fuel
                  (snapshot.step program input)).overlay ≤
              encodedStoreLength (snapshot.step program input).overlay +
                2 * (RAM.unitTimeUpto program fuel
                    (RAM.step program (snapshot.decode input)) *
                    (programStaticWidth program + 1) +
                  RAM.logTimeUpto program fuel
                    (RAM.step program (snapshot.decode input))) := htail
          _ ≤ (encodedStoreLength snapshot.overlay +
                2 * (programStaticWidth program +
                  RAM.stepLogCost program (snapshot.decode input) + 1)) +
              2 * (RAM.unitTimeUpto program fuel
                    (RAM.step program (snapshot.decode input)) *
                    (programStaticWidth program + 1) +
                  RAM.logTimeUpto program fuel
                    (RAM.step program (snapshot.decode input))) :=
            Nat.add_le_add_right hstep _
          _ = encodedStoreLength snapshot.overlay +
              2 * ((1 + RAM.unitTimeUpto program fuel
                    (RAM.step program (snapshot.decode input))) *
                    (programStaticWidth program + 1) +
                  (RAM.stepLogCost program (snapshot.decode input) +
                    RAM.logTimeUpto program fuel
                      (RAM.step program (snapshot.decode input)))) := by ring

theorem Snapshot.initial_length_run_le_internal (program : Program)
    (input : List Bool) (fuel : ℕ) :
    ((Snapshot.initial input).run program input fuel).overlay.length ≤
      1 + RAM.unitTimeUpto program fuel (RAM.initCfg input) := by
  have hrun := Snapshot.length_run_le_internal program input fuel
    (Snapshot.initial input) (Snapshot.initial_canonical_internal input)
  rw [Snapshot.initial_decode_internal input] at hrun
  simpa [Snapshot.initial, write, RegisterStore.write] using hrun

theorem Snapshot.initial_encodedStoreLength_run_le_internal
    (program : Program) (input : List Bool) (fuel : ℕ) :
    encodedStoreLength
        ((Snapshot.initial input).run program input fuel).overlay ≤
      2 * bitlen (input.length + 1) + 2 +
        2 * (RAM.unitTimeUpto program fuel (RAM.initCfg input) *
        (programStaticWidth program + 1) +
        RAM.logTimeUpto program fuel (RAM.initCfg input)) := by
  have hrun := Snapshot.encodedStoreLength_run_le_internal program input fuel
    (Snapshot.initial input) (Snapshot.initial_canonical_internal input)
  rw [Snapshot.initial_decode_internal input] at hrun
  have hentry : (Entry.encode (0, input.length + 1)).length =
      2 * bitlen (input.length + 1) + 2 := by
    rw [Entry.encode_length_internal]
    have hz : bitlen 0 = 0 := rfl
    simp [hz]
  simpa [Snapshot.initial, write, RegisterStore.write, encodedStoreLength,
    hentry] using hrun

theorem Snapshot.initial_encode_length_internal (input : List Bool) :
    (Snapshot.initial input).encode.length =
      2 * bitlen (input.length + 1) + 6 := by
  rw [Snapshot.encode, Snapshot.initial, RegisterStore.Snapshot.encode]
  have hz : bitlen 0 = 0 := rfl
  have hone : bitlen 1 = 1 := rfl
  simp [write, RegisterStore.write, Entry.encode, WordCode.encode,
    Nat.length_toBitsLE, hz, hone]
  omega

end DenseOverlay
end RegisterStore
end RAM
end Complexity

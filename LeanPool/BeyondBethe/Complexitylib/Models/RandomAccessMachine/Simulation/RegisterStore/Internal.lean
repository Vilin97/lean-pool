/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Internal
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Sparse RAM register stores on Turing tapes: proof internals

This module proves the finite-store semantics and codec round trips exposed by
the surface module. It is not part of the human-audited definitions layer.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

private theorem read_eq_zero_of_not_mem (store : Store) (address : ℕ)
    (haddress : address ∉ store.map Prod.fst) :
    read store address = 0 := by
  induction store with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨storedAddress, value⟩
    simp only [List.map_cons, List.mem_cons, not_or] at haddress
    simp only [read, haddress.1, ↓reduceIte]
    exact ih haddress.2

theorem read_write_internal (store : Store) (hstore : AddressesNodup store)
    (address value target : ℕ) :
    read (write store address value) target =
      Function.update (read store) address value target := by
  induction store with
  | nil =>
    by_cases hvalue : value = 0 <;> by_cases htarget : target = address
    · simp [write, read, hvalue, htarget, Function.update]
    · simp [write, read, hvalue, htarget, Function.update]
    · simp [write, read, hvalue, htarget, Function.update]
    · simp [write, read, hvalue, htarget, Function.update]
  | cons entry rest ih =>
    rcases entry with ⟨storedAddress, storedValue⟩
    simp only [AddressesNodup, List.map_cons, List.nodup_cons] at hstore
    by_cases haddress : address = storedAddress
    · subst address
      by_cases hvalue : value = 0
      · subst value
        by_cases htarget : target = storedAddress
        · subst target
          simp only [write, ↓reduceIte, read, Function.update_self]
          exact read_eq_zero_of_not_mem rest storedAddress hstore.1
        · simp [write, read, htarget]
      · by_cases htarget : target = storedAddress
        · subst target
          simp [write, read, hvalue]
        · simp [write, read, hvalue, htarget]
    · by_cases htarget : target = storedAddress
      · subst target
        have hne : storedAddress ≠ address := Ne.symm haddress
        simp [write, read, haddress, hne, Function.update]
      · simpa [write, read, haddress, htarget, Function.update] using ih hstore.2

private theorem mem_addresses_write (store : Store) (address value target : ℕ)
    (htarget : target ∈ (write store address value).map Prod.fst) :
    target = address ∨ target ∈ store.map Prod.fst := by
  induction store with
  | nil =>
    by_cases hvalue : value = 0
    · simp [write, hvalue] at htarget
    · simp [write, hvalue] at htarget
      exact Or.inl htarget
  | cons entry rest ih =>
    rcases entry with ⟨storedAddress, storedValue⟩
    by_cases haddress : address = storedAddress
    · subst address
      by_cases hvalue : value = 0
      · simp [write, hvalue] at htarget ⊢
        exact Or.inr htarget
      · simp [write, hvalue] at htarget ⊢
        rcases htarget with htarget | htarget
        · exact Or.inl htarget
        · exact Or.inr htarget
    · simp only [write, haddress, ↓reduceIte, List.map_cons,
        List.mem_cons] at htarget ⊢
      rcases htarget with htarget | htarget
      · exact Or.inr (Or.inl htarget)
      · rcases ih htarget with htarget | htarget
        · exact Or.inl htarget
        · exact Or.inr (Or.inr htarget)

theorem write_addressesNodup_internal (store : Store)
    (hstore : AddressesNodup store) (address value : ℕ) :
    AddressesNodup (write store address value) := by
  induction store with
  | nil =>
    by_cases hvalue : value = 0 <;>
      simp [AddressesNodup, write, hvalue]
  | cons entry rest ih =>
    rcases entry with ⟨storedAddress, storedValue⟩
    simp only [AddressesNodup, List.map_cons, List.nodup_cons] at hstore
    by_cases haddress : address = storedAddress
    · subst address
      by_cases hvalue : value = 0
      · simpa [AddressesNodup, write, hvalue] using hstore.2
      · simpa [AddressesNodup, write, hvalue] using hstore
    · simp only [write, haddress, ↓reduceIte, AddressesNodup,
        List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hstore.2⟩
      intro hmem
      rcases mem_addresses_write rest address value storedAddress hmem with
        heq | hmem
      · exact haddress heq.symm
      · exact hstore.1 hmem

theorem write_valuesNonzero_internal (store : Store)
    (hstore : ValuesNonzero store) (address value : ℕ) :
    ValuesNonzero (write store address value) := by
  induction store with
  | nil =>
    by_cases hvalue : value = 0 <;>
      simp [ValuesNonzero, write, hvalue]
  | cons entry rest ih =>
    rcases entry with ⟨storedAddress, storedValue⟩
    have hstored : storedValue ≠ 0 := hstore (storedAddress, storedValue) (by simp)
    have hrest : ValuesNonzero rest := by
      intro restEntry hmem
      exact hstore restEntry (by simp [hmem])
    by_cases haddress : address = storedAddress
    · subst address
      by_cases hvalue : value = 0
      · simpa [write, hvalue] using hrest
      · simp only [write, hvalue, ↓reduceIte]
        intro current hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst current
          exact hvalue
        · exact hrest current hmem
    · simp only [write, haddress, ↓reduceIte]
      intro current hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst current
        exact hstored
      · exact ih hrest current hmem

theorem write_canonical_internal (store : Store) (hstore : Canonical store)
    (address value : ℕ) :
    Canonical (write store address value) := by
  exact ⟨write_addressesNodup_internal store hstore.1 address value,
    write_valuesNonzero_internal store hstore.2 address value⟩

theorem decode_write_internal (store : Store) (hstore : AddressesNodup store)
    (address value : ℕ) :
    decode (write store address value) = Function.update (decode store) address value := by
  funext target
  exact read_write_internal store hstore address value target

private theorem read_map_entries_of_mem (addresses : List ℕ) (regs : ℕ → ℕ)
    (address : ℕ) (haddress : address ∈ addresses) :
    read (addresses.map fun current => (current, regs current)) address = regs address := by
  induction addresses with
  | nil => simp at haddress
  | cons current rest ih =>
    simp only [List.mem_cons] at haddress
    rcases haddress with haddress | haddress
    · subst current
      simp [read]
    · by_cases heq : address = current
      · subst current
        simp [read]
      · simp [read, heq, ih haddress]

theorem ofRegs_canonical_internal (regs : ℕ → ℕ)
    (hfinite : (Function.support regs).Finite) :
    Canonical (ofRegs regs hfinite) := by
  constructor
  · unfold AddressesNodup ofRegs
    simpa [Function.comp_def] using
      hfinite.toFinset.nodup_toList
  · intro entry hentry
    rcases entry with ⟨address, value⟩
    simp only [ofRegs, List.mem_map] at hentry
    obtain ⟨storedAddress, hstored, heq⟩ := hentry
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact Function.mem_support.mp
      (hfinite.mem_toFinset.mp (Finset.mem_toList.mp hstored))

theorem decode_ofRegs_internal (regs : ℕ → ℕ)
    (hfinite : (Function.support regs).Finite) :
    decode (ofRegs regs hfinite) = regs := by
  funext address
  by_cases haddress : address ∈ Function.support regs
  · unfold ofRegs
    apply read_map_entries_of_mem
    rw [Finset.mem_toList, hfinite.mem_toFinset]
    exact haddress
  · have hnotmem : address ∉ (ofRegs regs hfinite).map Prod.fst := by
      unfold ofRegs
      simpa [Function.comp_def, hfinite.mem_toFinset] using haddress
    rw [decode, read_eq_zero_of_not_mem _ _ hnotmem]
    have hzero : ¬regs address ≠ 0 := by
      simpa only [Function.mem_support] using haddress
    by_contra hne
    exact hzero (Ne.symm hne)

theorem ofRegs_represents_internal (regs : ℕ → ℕ)
    (hfinite : (Function.support regs).Finite) :
    Represents (ofRegs regs hfinite) regs :=
  ⟨ofRegs_canonical_internal regs hfinite, decode_ofRegs_internal regs hfinite⟩

private theorem initRegs_ne_zero_address_lt (input : List Bool) (address : ℕ)
    (hvalue : initRegs input address ≠ 0) :
    address < input.length + 1 := by
  by_contra hlt
  rw [not_lt] at hlt
  have haddress : address ≠ 0 := by omega
  apply hvalue
  simp only [initRegs, haddress, ite_false]
  rw [List.getElem?_eq_none (show input.length ≤ address - 1 by omega)]

private theorem initRegs_le_length_add_one (input : List Bool) (address : ℕ) :
    initRegs input address ≤ input.length + 1 := by
  simp only [initRegs]
  split
  · omega
  · split
    · split <;> omega
    · omega

theorem initialStore_canonical_internal (input : List Bool) :
    Canonical (initialStore input) := by
  constructor
  · unfold AddressesNodup initialStore
    simp [Function.comp_def]
  · intro entry hentry
    rcases entry with ⟨address, value⟩
    simp only [initialStore, List.mem_map] at hentry
    obtain ⟨storedAddress, hstored, heq⟩ := hentry
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact (Finset.mem_filter.mp
      ((Finset.mem_sort (r := (· ≤ ·))).mp hstored)).2

theorem decode_initialStore_internal (input : List Bool) :
    decode (initialStore input) = initRegs input := by
  funext address
  by_cases hvalue : initRegs input address = 0
  · have hnotmem : address ∉ (initialStore input).map Prod.fst := by
      unfold initialStore
      simp [Function.comp_def, initialAddresses, hvalue]
    rw [decode, read_eq_zero_of_not_mem _ _ hnotmem, hvalue]
  · apply read_map_entries_of_mem
    rw [Finset.mem_sort (r := (· ≤ ·)), initialAddresses,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨initRegs_ne_zero_address_lt input address hvalue, hvalue⟩

theorem Snapshot.initial_represents_internal (input : List Bool) :
    (Snapshot.initial input).Represents (RAM.initCfg input) := by
  constructor
  · exact initialStore_canonical_internal input
  · apply Cfg.ext
    · rfl
    · exact decode_initialStore_internal input

theorem initialStore_length_le_internal (input : List Bool) :
    (initialStore input).length ≤ input.length + 1 := by
  unfold initialStore initialAddresses
  simp only [List.length_map, Finset.length_sort]
  simpa using Finset.card_filter_le (Finset.range (input.length + 1))
    (fun address => initRegs input address ≠ 0)

private theorem maxWidth_le (store : Store) (width : ℕ)
    (hwidth : ∀ entry ∈ store,
      bitlen entry.1 ≤ width ∧ bitlen entry.2 ≤ width) :
    maxWidth store ≤ width := by
  induction store with
  | nil => simp [maxWidth]
  | cons entry rest ih =>
    have hentry := hwidth entry (by simp)
    have hrest : ∀ current ∈ rest,
        bitlen current.1 ≤ width ∧ bitlen current.2 ≤ width := by
      intro current hmem
      exact hwidth current (by simp [hmem])
    simp only [maxWidth]
    exact max_le hentry.1 (max_le hentry.2 (ih hrest))

theorem Snapshot.initial_width_le_internal (input : List Bool) :
    (Snapshot.initial input).width ≤ bitlen (input.length + 1) := by
  have hlength := initialStore_length_le_internal input
  have hcount : bitlen (initialStore input).length ≤ bitlen (input.length + 1) :=
    Nat.size_le_size hlength
  have hstore : maxWidth (initialStore input) ≤ bitlen (input.length + 1) := by
    apply maxWidth_le
    intro entry hentry
    rcases entry with ⟨address, value⟩
    simp only [initialStore, List.mem_map] at hentry
    obtain ⟨storedAddress, hstored, heq⟩ := hentry
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hmember := Finset.mem_filter.mp
      ((Finset.mem_sort (r := (· ≤ ·))).mp hstored)
    exact ⟨Nat.size_le_size (Nat.le_of_lt (Finset.mem_range.mp hmember.1)),
      Nat.size_le_size (initRegs_le_length_add_one input storedAddress)⟩
  exact max_le (by simp [Snapshot.initial, bitlen]) (max_le hcount hstore)

theorem Snapshot.ofCfg_represents_internal (cfg : Cfg)
    (hfinite : (Function.support cfg.regs).Finite) :
    (Snapshot.ofCfg cfg hfinite).Represents cfg := by
  constructor
  · exact ofRegs_canonical_internal cfg.regs hfinite
  · apply Cfg.ext
    · rfl
    · exact decode_ofRegs_internal cfg.regs hfinite

theorem Snapshot.stepInstr_canonical_internal (instruction : Instr)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    Canonical (Snapshot.stepInstr instruction snapshot).store := by
  cases instruction with
  | imm destination value =>
      exact write_canonical_internal snapshot.store hcanonical destination value
  | add destination source₀ source₁ =>
      exact write_canonical_internal snapshot.store hcanonical destination _
  | sub destination source₀ source₁ =>
      exact write_canonical_internal snapshot.store hcanonical destination _
  | mul destination source₀ source₁ =>
      exact write_canonical_internal snapshot.store hcanonical destination _
  | load destination addressRegister =>
      exact write_canonical_internal snapshot.store hcanonical destination _
  | store addressRegister source =>
      exact write_canonical_internal snapshot.store hcanonical _ _
  | jz source target =>
      simp only [Snapshot.stepInstr]
      split <;> exact hcanonical
  | jmp target => exact hcanonical
  | halt => exact hcanonical

theorem Snapshot.decode_stepInstr_internal (instruction : Instr)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (Snapshot.stepInstr instruction snapshot).decode =
      RAM.stepInstr instruction snapshot.decode := by
  cases instruction with
  | imm destination value =>
      apply Cfg.ext
      · rfl
      · exact decode_write_internal snapshot.store hcanonical.1 destination value
  | add destination source₀ source₁ =>
      apply Cfg.ext
      · rfl
      · exact decode_write_internal snapshot.store hcanonical.1 destination _
  | sub destination source₀ source₁ =>
      apply Cfg.ext
      · rfl
      · exact decode_write_internal snapshot.store hcanonical.1 destination _
  | mul destination source₀ source₁ =>
      apply Cfg.ext
      · rfl
      · exact decode_write_internal snapshot.store hcanonical.1 destination _
  | load destination addressRegister =>
      apply Cfg.ext
      · rfl
      · exact decode_write_internal snapshot.store hcanonical.1 destination _
  | store addressRegister source =>
      apply Cfg.ext
      · rfl
      · exact decode_write_internal snapshot.store hcanonical.1 _ _
  | jz source target =>
      by_cases hzero : read snapshot.store source = 0 <;>
        simp [Snapshot.stepInstr, RAM.stepInstr, Snapshot.decode,
          RegisterStore.decode, hzero]
  | jmp target => rfl
  | halt => rfl

theorem Snapshot.curInstr_decode_internal (program : Program) (snapshot : Snapshot) :
    RAM.curInstr program snapshot.decode = snapshot.curInstr program :=
  rfl

theorem Snapshot.halted_decode_iff_internal (program : Program) (snapshot : Snapshot) :
    RAM.Halted program snapshot.decode ↔ snapshot.Halted program :=
  Iff.rfl

theorem Snapshot.step_canonical_internal (program : Program) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (snapshot.step program).store :=
  Snapshot.stepInstr_canonical_internal _ snapshot hcanonical

theorem Snapshot.decode_step_internal (program : Program) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.step program).decode = RAM.step program snapshot.decode := by
  exact Snapshot.decode_stepInstr_internal _ snapshot hcanonical

theorem Snapshot.run_canonical_internal (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    Canonical (snapshot.run program fuel).store := by
  induction fuel generalizing snapshot with
  | zero => exact hcanonical
  | succ fuel ih =>
      rw [Snapshot.run]
      by_cases hhalt : snapshot.Halted program
      · rw [ite_eq_left hhalt]
        exact hcanonical
      · rw [ite_eq_right hhalt]
        exact ih (snapshot.step program)
          (Snapshot.step_canonical_internal program snapshot hcanonical)

theorem Snapshot.decode_run_internal (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).decode = RAM.run program fuel snapshot.decode := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      rw [Snapshot.run, RAM.run]
      by_cases hhalt : snapshot.Halted program
      · rw [ite_eq_left hhalt,
          ite_eq_left ((Snapshot.halted_decode_iff_internal program snapshot).mpr hhalt)]
      · rw [ite_eq_right hhalt,
          ite_eq_right (mt (Snapshot.halted_decode_iff_internal program snapshot).mp hhalt)]
        rw [ih (snapshot.step program)
          (Snapshot.step_canonical_internal program snapshot hcanonical)]
        rw [Snapshot.decode_step_internal program snapshot hcanonical]

private theorem bitlen_succ_le (value : ℕ) :
    bitlen (value + 1) ≤ bitlen value + 1 := by
  rw [bitlen, bitlen, Nat.size_le]
  have hvalue := Nat.lt_size_self value
  have hpowPos : 0 < 2 ^ value.size := pow_pos (by omega) _
  rw [pow_succ]
  omega

private theorem length_write_le (store : Store) (address value : ℕ) :
    (write store address value).length ≤ store.length + 1 := by
  induction store with
  | nil =>
      by_cases hvalue : value = 0 <;> simp [write, hvalue]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedValue⟩
      by_cases haddress : address = storedAddress
      · subst address
        by_cases hvalue : value = 0
        · simp [write, hvalue]
          omega
        · simp [write, hvalue]
      · simp [write, haddress, ih]

private theorem maxWidth_write_le (store : Store) (address value : ℕ) :
    maxWidth (write store address value) ≤
      max (maxWidth store) (max (bitlen address) (bitlen value)) := by
  induction store with
  | nil =>
      by_cases hvalue : value = 0 <;> simp [write, maxWidth, hvalue]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedValue⟩
      by_cases haddress : address = storedAddress
      · subst address
        by_cases hvalue : value = 0
        · simp [write, maxWidth, hvalue]
        · simp [write, maxWidth, hvalue]
          omega
      · simp only [write, haddress, ↓reduceIte, maxWidth]
        omega

private theorem Snapshot.width_write_le (snapshot : Snapshot)
    (address value newPC bound : ℕ)
    (hbase : snapshot.width + 1 ≤ bound)
    (hpc : bitlen newPC ≤ bound)
    (haddress : bitlen address ≤ bound)
    (hvalue : bitlen value ≤ bound) :
    Snapshot.width { pc := newPC, store := write snapshot.store address value } ≤ bound := by
  have holdCount : bitlen snapshot.store.length ≤ snapshot.width :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have holdStore : maxWidth snapshot.store ≤ snapshot.width :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hlength := length_write_le snapshot.store address value
  have hcountStep : bitlen (write snapshot.store address value).length ≤
      bitlen (snapshot.store.length + 1) := by
    exact Nat.size_le_size hlength
  have hcountSucc := bitlen_succ_le snapshot.store.length
  have hcount : bitlen (write snapshot.store address value).length ≤ bound := by
    omega
  have hstoreStep := maxWidth_write_le snapshot.store address value
  have hstore : maxWidth (write snapshot.store address value) ≤ bound := by
    exact le_trans hstoreStep
      (max_le (le_trans holdStore (by omega)) (max_le haddress hvalue))
  exact max_le hpc (max_le hcount hstore)

private theorem Snapshot.width_pc_le (snapshot : Snapshot) (newPC bound : ℕ)
    (hbase : snapshot.width + 1 ≤ bound)
    (hpc : bitlen newPC ≤ bound) :
    Snapshot.width { snapshot with pc := newPC } ≤ bound := by
  have hrest : max (bitlen snapshot.store.length) (maxWidth snapshot.store) ≤
      snapshot.width := le_max_right _ _
  exact max_le hpc (le_trans hrest (by omega))

theorem Snapshot.width_stepInstr_le_internal (instruction : Instr)
    (snapshot : Snapshot) :
    (Snapshot.stepInstr instruction snapshot).width ≤
      snapshot.stepWidthBound instruction := by
  let bound := snapshot.stepWidthBound instruction
  have hbase : snapshot.width + 1 ≤ bound := by
    exact le_max_left _ _
  have hstatic : RegisterStore.Instr.staticWidth instruction ≤ bound :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hcost : instruction.logCost snapshot.decode ≤ bound :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have holdPC : bitlen snapshot.pc ≤ snapshot.width := le_max_left _ _
  have hnextPC : bitlen (snapshot.pc + 1) ≤ bound := by
    have := bitlen_succ_le snapshot.pc
    omega
  cases instruction with
  | imm destination value =>
      apply Snapshot.width_write_le snapshot destination value
        (snapshot.pc + 1) bound hbase hnextPC
      · exact le_trans (le_max_left _ _) hstatic
      · exact le_trans (le_max_right _ _) hstatic
  | add destination source₀ source₁ =>
      apply Snapshot.width_write_le snapshot destination
        (read snapshot.store source₀ + read snapshot.store source₁)
        (snapshot.pc + 1) bound hbase hnextPC
      · exact le_trans (le_max_left _ _) hstatic
      · simp only [Instr.logCost, Snapshot.decode, RegisterStore.decode] at hcost
        omega
  | sub destination source₀ source₁ =>
      apply Snapshot.width_write_le snapshot destination
        (read snapshot.store source₀ - read snapshot.store source₁)
        (snapshot.pc + 1) bound hbase hnextPC
      · exact le_trans (le_max_left _ _) hstatic
      · have hsub : bitlen (read snapshot.store source₀ - read snapshot.store source₁) ≤
            bitlen (read snapshot.store source₀) :=
          Nat.size_le_size (Nat.sub_le _ _)
        simp only [Instr.logCost, Snapshot.decode, RegisterStore.decode] at hcost
        omega
  | mul destination source₀ source₁ =>
      apply Snapshot.width_write_le snapshot destination
        (read snapshot.store source₀ * read snapshot.store source₁)
        (snapshot.pc + 1) bound hbase hnextPC
      · exact le_trans (le_max_left _ _) hstatic
      · simp only [Instr.logCost, Snapshot.decode, RegisterStore.decode] at hcost
        omega
  | load destination addressRegister =>
      apply Snapshot.width_write_le snapshot destination
        (read snapshot.store (read snapshot.store addressRegister))
        (snapshot.pc + 1) bound hbase hnextPC
      · exact le_trans (le_max_left _ _) hstatic
      · simp only [Instr.logCost, Snapshot.decode, RegisterStore.decode] at hcost
        omega
  | store addressRegister source =>
      apply Snapshot.width_write_le snapshot
        (read snapshot.store addressRegister) (read snapshot.store source)
        (snapshot.pc + 1) bound hbase hnextPC
      · simp only [Instr.logCost, Snapshot.decode, RegisterStore.decode] at hcost
        omega
      · simp only [Instr.logCost, Snapshot.decode, RegisterStore.decode] at hcost
        omega
  | jz source target =>
      by_cases hzero : read snapshot.store source = 0
      · simp only [Snapshot.stepInstr, hzero, ↓reduceIte]
        apply Snapshot.width_pc_le snapshot target bound hbase
        exact le_trans (le_max_right _ _) hstatic
      · simp only [Snapshot.stepInstr, hzero, ↓reduceIte]
        exact Snapshot.width_pc_le snapshot (snapshot.pc + 1) bound hbase hnextPC
  | jmp target =>
      apply Snapshot.width_pc_le snapshot target bound hbase
      exact hstatic
  | halt =>
      exact le_trans (Nat.le_add_right snapshot.width 1) hbase

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

theorem Snapshot.width_step_le_internal (program : Program) (snapshot : Snapshot) :
    (snapshot.step program).width ≤
      max (snapshot.width + 1)
        (max (programStaticWidth program) (RAM.stepLogCost program snapshot.decode)) := by
  have hstep := Snapshot.width_stepInstr_le_internal
    (snapshot.curInstr program) snapshot
  have hstatic := staticWidth_curInstr_le program snapshot.pc
  apply le_trans hstep
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact le_trans hstatic (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem Snapshot.length_stepInstr_le_internal (instruction : Instr)
    (snapshot : Snapshot) :
    (Snapshot.stepInstr instruction snapshot).store.length ≤
      snapshot.store.length + 1 := by
  cases instruction with
  | imm destination value => exact length_write_le snapshot.store destination value
  | add destination source₀ source₁ => exact length_write_le snapshot.store destination _
  | sub destination source₀ source₁ => exact length_write_le snapshot.store destination _
  | mul destination source₀ source₁ => exact length_write_le snapshot.store destination _
  | load destination addressRegister => exact length_write_le snapshot.store destination _
  | store addressRegister source => exact length_write_le snapshot.store _ _
  | jz source target =>
      simp only [Snapshot.stepInstr]
      split <;> simp
  | jmp target => simp [Snapshot.stepInstr]
  | halt => simp [Snapshot.stepInstr]

theorem Snapshot.length_run_le_internal (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).store.length ≤
      snapshot.store.length + RAM.unitTimeUpto program fuel snapshot.decode := by
  induction fuel generalizing snapshot with
  | zero => simp [Snapshot.run, RAM.unitTimeUpto]
  | succ fuel ih =>
      rw [Snapshot.run, RAM.unitTimeUpto]
      by_cases hhalt : snapshot.Halted program
      · rw [ite_eq_left hhalt,
          ite_eq_left ((Snapshot.halted_decode_iff_internal program snapshot).mpr hhalt)]
        omega
      · rw [ite_eq_right hhalt,
          ite_eq_right (mt (Snapshot.halted_decode_iff_internal program snapshot).mp hhalt)]
        have hstep := Snapshot.length_stepInstr_le_internal
          (snapshot.curInstr program) snapshot
        have hstep' : (snapshot.step program).store.length ≤
            snapshot.store.length + 1 := by
          simpa only [Snapshot.step] using hstep
        have hstepCanonical := Snapshot.step_canonical_internal
          program snapshot hcanonical
        have hrun := ih (snapshot.step program) hstepCanonical
        rw [Snapshot.decode_step_internal program snapshot hcanonical] at hrun
        omega

theorem Snapshot.width_run_le_internal (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).width ≤
      snapshot.width + RAM.unitTimeUpto program fuel snapshot.decode *
        (programStaticWidth program + 1) +
        RAM.logTimeUpto program fuel snapshot.decode := by
  induction fuel generalizing snapshot with
  | zero => simp [Snapshot.run]
  | succ fuel ih =>
      rw [Snapshot.run, RAM.unitTimeUpto, RAM.logTimeUpto]
      by_cases hhalt : snapshot.Halted program
      · rw [ite_eq_left hhalt,
          ite_eq_left ((Snapshot.halted_decode_iff_internal program snapshot).mpr hhalt),
          ite_eq_left ((Snapshot.halted_decode_iff_internal program snapshot).mpr hhalt)]
        omega
      · rw [ite_eq_right hhalt,
          ite_eq_right (mt (Snapshot.halted_decode_iff_internal program snapshot).mp hhalt),
          ite_eq_right (mt (Snapshot.halted_decode_iff_internal program snapshot).mp hhalt)]
        have hstepCanonical := Snapshot.step_canonical_internal
          program snapshot hcanonical
        have hrun := ih (snapshot.step program) hstepCanonical
        rw [Snapshot.decode_step_internal program snapshot hcanonical] at hrun
        have hstep := Snapshot.width_step_le_internal program snapshot
        rw [Nat.add_mul]
        omega

private theorem WordCode.decodeAux?_replicate_true
    (remaining consumed : ℕ) (payload suffix : List Bool)
    (hlength : payload.length = consumed + remaining) :
    WordCode.decodeAux?
        (List.replicate remaining true ++ false :: payload ++ suffix) consumed =
      some (Nat.fromBitsLE payload, suffix) := by
  induction remaining generalizing consumed with
  | zero =>
    have hconsumed : consumed = payload.length := by omega
    subst consumed
    simp [WordCode.decodeAux?]
  | succ remaining ih =>
    simp only [List.replicate_succ, List.cons_append, WordCode.decodeAux?]
    apply ih (consumed + 1)
    omega

theorem WordCode.decodePrefix?_encode_append_internal (value : ℕ)
    (suffix : List Bool) :
    WordCode.decodePrefix? (WordCode.encode value ++ suffix) =
      some (value, suffix) := by
  have hdecode := WordCode.decodeAux?_replicate_true
    (bitlen value) 0 (Nat.toBitsLE (bitlen value) value) suffix
    (by simp [bitlen, Nat.length_toBitsLE])
  have hround : Nat.fromBitsLE (Nat.toBitsLE (bitlen value) value) = value := by
    apply Nat.fromBitsLE_toBitsLE
    simpa [bitlen] using Nat.lt_size_self value
  rw [hround] at hdecode
  simpa [WordCode.decodePrefix?, WordCode.encode, List.append_assoc] using hdecode

theorem WordCode.decodePrefix?_encode_internal (value : ℕ) :
    WordCode.decodePrefix? (WordCode.encode value) = some (value, []) := by
  simpa using WordCode.decodePrefix?_encode_append_internal value []

theorem WordCode.encode_length_internal (value : ℕ) :
    (WordCode.encode value).length = 2 * bitlen value + 1 := by
  simp [WordCode.encode, Nat.length_toBitsLE]
  omega

theorem Entry.decodePrefix?_encode_append_internal (entry : Entry)
    (suffix : List Bool) :
    Entry.decodePrefix? (Entry.encode entry ++ suffix) = some (entry, suffix) := by
  rcases entry with ⟨address, value⟩
  simp [Entry.encode, Entry.decodePrefix?, List.append_assoc,
    WordCode.decodePrefix?_encode_append_internal]

theorem Entry.encode_length_internal (entry : Entry) :
    (Entry.encode entry).length =
      2 * bitlen entry.1 + 2 * bitlen entry.2 + 2 := by
  rw [Entry.encode, List.length_append,
    WordCode.encode_length_internal, WordCode.encode_length_internal]
  omega

theorem encodedStoreLength_write_le_internal (store : Store)
    (address value : ℕ) :
    encodedStoreLength (write store address value) ≤
      encodedStoreLength store + (Entry.encode (address, value)).length := by
  induction store with
  | nil =>
      by_cases hvalue : value = 0 <;>
        simp [encodedStoreLength, write, hvalue]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedValue⟩
      by_cases haddress : address = storedAddress
      · subst address
        by_cases hvalue : value = 0
        · subst value
          simp only [write, ↓reduceIte, encodedStoreLength,
            List.flatMap_cons, List.length_append]
          exact le_trans (Nat.le_add_left _ _)
            (Nat.le_add_right _ _)
        · simp only [write, hvalue, ↓reduceIte, encodedStoreLength,
            List.flatMap_cons, List.length_append]
          calc
            (Entry.encode (storedAddress, value)).length +
                (List.flatMap Entry.encode rest).length =
              (List.flatMap Entry.encode rest).length +
                (Entry.encode (storedAddress, value)).length := by omega
            _ ≤ ((Entry.encode (storedAddress, storedValue)).length +
                  (List.flatMap Entry.encode rest).length) +
                (Entry.encode (storedAddress, value)).length :=
              Nat.add_le_add_right (Nat.le_add_left _ _) _
      · unfold encodedStoreLength at ih
        simp only [write, haddress, ↓reduceIte, encodedStoreLength,
          List.flatMap_cons, List.length_append]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add_left ih
            (Entry.encode (storedAddress, storedValue)).length

private theorem encodedStoreLength_stepInstr_le (instruction : Instr)
    (snapshot : Snapshot) :
    encodedStoreLength (Snapshot.stepInstr instruction snapshot).store ≤
      encodedStoreLength snapshot.store +
        4 * (RegisterStore.Instr.staticWidth instruction +
          instruction.logCost snapshot.decode + 1) := by
  cases instruction with
  | imm destination value =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.store
        destination value
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost]
      omega
  | add destination source₀ source₁ =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.store
        destination
        (read snapshot.store source₀ + read snapshot.store source₁)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, RegisterStore.decode]
      omega
  | sub destination source₀ source₁ =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.store
        destination
        (read snapshot.store source₀ - read snapshot.store source₁)
      have hsub : bitlen
          (read snapshot.store source₀ - read snapshot.store source₁) ≤
          bitlen (read snapshot.store source₀) :=
        Nat.size_le_size (Nat.sub_le _ _)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, RegisterStore.decode]
      omega
  | mul destination source₀ source₁ =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.store
        destination
        (read snapshot.store source₀ * read snapshot.store source₁)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, RegisterStore.decode]
      omega
  | load destination addressRegister =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.store
        destination (read snapshot.store (read snapshot.store addressRegister))
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, RegisterStore.decode]
      omega
  | store addressRegister source =>
      have hwrite := encodedStoreLength_write_le_internal snapshot.store
        (read snapshot.store addressRegister) (read snapshot.store source)
      apply le_trans hwrite
      rw [Entry.encode_length_internal]
      simp only [RegisterStore.Instr.staticWidth, Instr.logCost,
        Snapshot.decode, RegisterStore.decode]
      omega
  | jz source target =>
      simp only [Snapshot.stepInstr]
      split <;> simp [encodedStoreLength]
  | jmp target => simp [Snapshot.stepInstr]
  | halt => simp [Snapshot.stepInstr]

private theorem encodedStoreLength_step_le (program : Program)
    (snapshot : Snapshot) :
    encodedStoreLength (snapshot.step program).store ≤
      encodedStoreLength snapshot.store +
        4 * (programStaticWidth program +
          RAM.stepLogCost program snapshot.decode + 1) := by
  have hstep := encodedStoreLength_stepInstr_le
    (snapshot.curInstr program) snapshot
  have hstatic : RegisterStore.Instr.staticWidth
      (snapshot.curInstr program) ≤ programStaticWidth program := by
    simpa only [Snapshot.curInstr] using
      staticWidth_curInstr_le program snapshot.pc
  apply le_trans hstep
  apply Nat.add_le_add_left
  have hcost : (snapshot.curInstr program).logCost snapshot.decode =
      RAM.stepLogCost program snapshot.decode := rfl
  rw [hcost]
  exact Nat.mul_le_mul_left 4
    (Nat.add_le_add_right
      (Nat.add_le_add_right hstatic _) 1)

theorem Snapshot.encodedStoreLength_run_le_internal (program : Program)
    (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    encodedStoreLength (snapshot.run program fuel).store ≤
      encodedStoreLength snapshot.store +
        4 * (RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) := by
  induction fuel generalizing snapshot with
  | zero => simp [Snapshot.run, RAM.unitTimeUpto, RAM.logTimeUpto]
  | succ fuel ih =>
      rw [Snapshot.run]
      by_cases hhalt : snapshot.Halted program
      · have hramHalted :=
          (Snapshot.halted_decode_iff_internal program snapshot).mpr hhalt
        simp only [hhalt, hramHalted, if_true, RAM.unitTimeUpto,
          RAM.logTimeUpto]
        simp
      · have hramNotHalted : ¬RAM.Halted program snapshot.decode :=
          mt (Snapshot.halted_decode_iff_internal program snapshot).mp hhalt
        rw [ite_eq_right hhalt]
        simp only [RAM.unitTimeUpto, RAM.logTimeUpto, hramNotHalted,
          ite_false]
        have hstep := encodedStoreLength_step_le program snapshot
        have hnextCanonical :=
          Snapshot.step_canonical_internal program snapshot hcanonical
        have htail := ih (snapshot.step program) hnextCanonical
        have hdecode := Snapshot.decode_step_internal program snapshot hcanonical
        rw [hdecode] at htail
        calc
          encodedStoreLength
                (Snapshot.run program fuel (snapshot.step program)).store ≤
              encodedStoreLength (snapshot.step program).store +
                4 * (RAM.unitTimeUpto program fuel
                    (RAM.step program snapshot.decode) *
                    (programStaticWidth program + 1) +
                  RAM.logTimeUpto program fuel
                    (RAM.step program snapshot.decode)) := htail
          _ ≤ (encodedStoreLength snapshot.store +
                4 * (programStaticWidth program +
                  RAM.stepLogCost program snapshot.decode + 1)) +
              4 * (RAM.unitTimeUpto program fuel
                    (RAM.step program snapshot.decode) *
                    (programStaticWidth program + 1) +
                  RAM.logTimeUpto program fuel
                    (RAM.step program snapshot.decode)) :=
            Nat.add_le_add_right hstep _
          _ = encodedStoreLength snapshot.store +
              4 * ((1 + RAM.unitTimeUpto program fuel
                    (RAM.step program snapshot.decode)) *
                    (programStaticWidth program + 1) +
                  (RAM.stepLogCost program snapshot.decode +
                    RAM.logTimeUpto program fuel
                      (RAM.step program snapshot.decode))) := by ring

private theorem entries_encode_length_le (store : Store) (width : ℕ)
    (hwidth : ∀ entry ∈ store,
      bitlen entry.1 ≤ width ∧ bitlen entry.2 ≤ width) :
    (store.flatMap Entry.encode).length ≤ store.length * (4 * width + 2) := by
  induction store with
  | nil => simp
  | cons entry rest ih =>
    have hentry := hwidth entry (by simp)
    have hrest : ∀ current ∈ rest,
        bitlen current.1 ≤ width ∧ bitlen current.2 ≤ width := by
      intro current hmem
      exact hwidth current (by simp [hmem])
    have hhead : (Entry.encode entry).length ≤ 4 * width + 2 := by
      rw [Entry.encode_length_internal]
      omega
    have htail := ih hrest
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem decodeEntries?_encode_append_internal (store : Store) (suffix : List Bool) :
    decodeEntries? store.length (store.flatMap Entry.encode ++ suffix) =
      some (store, suffix) := by
  induction store with
  | nil => rfl
  | cons entry rest ih =>
    simp [List.flatMap_cons, decodeEntries?, List.append_assoc,
      Entry.decodePrefix?_encode_append_internal, ih]

theorem Snapshot.decodePrefix?_encode_append_internal (snapshot : Snapshot)
    (suffix : List Bool) :
    Snapshot.decodePrefix? (snapshot.encode ++ suffix) = some (snapshot, suffix) := by
  rcases snapshot with ⟨pc, store⟩
  simp [Snapshot.encode, Snapshot.decodePrefix?, List.append_assoc,
    WordCode.decodePrefix?_encode_append_internal,
    decodeEntries?_encode_append_internal]

theorem Snapshot.decodePrefix?_encode_internal (snapshot : Snapshot) :
    Snapshot.decodePrefix? snapshot.encode = some (snapshot, []) := by
  simpa using Snapshot.decodePrefix?_encode_append_internal snapshot []

theorem Snapshot.decode?_encode_internal (snapshot : Snapshot) :
    Snapshot.decode? snapshot.encode = some snapshot := by
  rw [Snapshot.decode?, Snapshot.decodePrefix?_encode_internal]
  rfl

theorem Snapshot.encode_length_le_internal (snapshot : Snapshot) (width : ℕ)
    (hpc : bitlen snapshot.pc ≤ width)
    (hcount : bitlen snapshot.store.length ≤ width)
    (hstore : ∀ entry ∈ snapshot.store,
      bitlen entry.1 ≤ width ∧ bitlen entry.2 ≤ width) :
    snapshot.encode.length ≤ (snapshot.store.length + 1) * (4 * width + 2) := by
  have hentries := entries_encode_length_le snapshot.store width hstore
  have hpcCode : (WordCode.encode snapshot.pc).length ≤ 2 * width + 1 := by
    rw [WordCode.encode_length_internal]
    omega
  have hcountCode : (WordCode.encode snapshot.store.length).length ≤ 2 * width + 1 := by
    rw [WordCode.encode_length_internal]
    omega
  simp only [Snapshot.encode, List.length_append]
  rw [Nat.add_mul]
  omega

private theorem bitlen_le_maxWidth (store : Store) (entry : Entry)
    (hentry : entry ∈ store) :
    bitlen entry.1 ≤ maxWidth store ∧ bitlen entry.2 ≤ maxWidth store := by
  induction store with
  | nil => simp at hentry
  | cons head rest ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · simp [maxWidth]
    · have hrest := ih hentry
      simp only [maxWidth]
      have htail : maxWidth rest ≤
          max (bitlen head.1) (max (bitlen head.2) (maxWidth rest)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact ⟨le_trans hrest.1 htail, le_trans hrest.2 htail⟩

theorem encodedStoreLength_initial_le_internal (input : List Bool) :
    encodedStoreLength (initialStore input) ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) := by
  have hlength := initialStore_length_le_internal input
  have hsnapshotWidth := Snapshot.initial_width_le_internal input
  have hstoreWidth : ∀ entry ∈ initialStore input,
      bitlen entry.1 ≤ bitlen (input.length + 1) ∧
        bitlen entry.2 ≤ bitlen (input.length + 1) := by
    intro entry hentry
    have hentryWidth := bitlen_le_maxWidth (initialStore input) entry hentry
    have hmaxWidth : maxWidth (initialStore input) ≤
        (Snapshot.initial input).width := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact ⟨le_trans hentryWidth.1 (le_trans hmaxWidth hsnapshotWidth),
      le_trans hentryWidth.2 (le_trans hmaxWidth hsnapshotWidth)⟩
  have hentries := entries_encode_length_le (initialStore input)
    (bitlen (input.length + 1)) hstoreWidth
  unfold encodedStoreLength
  exact le_trans hentries
    (Nat.mul_le_mul_right (4 * bitlen (input.length + 1) + 2) hlength)

theorem Snapshot.encode_length_le_sizeBound_internal (snapshot : Snapshot) :
    snapshot.encode.length ≤ snapshot.sizeBound := by
  apply Snapshot.encode_length_le_internal snapshot snapshot.width
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro entry hentry
    have hwidth := bitlen_le_maxWidth snapshot.store entry hentry
    exact ⟨le_trans hwidth.1 (le_trans (le_max_right _ _) (le_max_right _ _)),
      le_trans hwidth.2 (le_trans (le_max_right _ _) (le_max_right _ _))⟩

theorem Snapshot.encode_length_le_encodedStore_internal (snapshot : Snapshot) :
    snapshot.encode.length ≤
      encodedStoreLength snapshot.store + 4 * snapshot.width + 2 := by
  have hpc : bitlen snapshot.pc ≤ snapshot.width := le_max_left _ _
  have hcount : bitlen snapshot.store.length ≤ snapshot.width :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  simp only [Snapshot.encode, List.length_append, encodedStoreLength]
  rw [WordCode.encode_length_internal, WordCode.encode_length_internal]
  omega

theorem Snapshot.encode_run_length_le_amortized_internal
    (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      encodedStoreLength snapshot.store + 4 * snapshot.width +
        8 * (RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2 := by
  let growth := RAM.unitTimeUpto program fuel snapshot.decode *
      (programStaticWidth program + 1) +
      RAM.logTimeUpto program fuel snapshot.decode
  have hcode := Snapshot.encode_length_le_encodedStore_internal
    (snapshot.run program fuel)
  have hentries := Snapshot.encodedStoreLength_run_le_internal
    program fuel snapshot hcanonical
  have hwidth := Snapshot.width_run_le_internal
    program fuel snapshot hcanonical
  calc
    (snapshot.run program fuel).encode.length ≤
        encodedStoreLength (snapshot.run program fuel).store +
          4 * (snapshot.run program fuel).width + 2 := hcode
    _ ≤ (encodedStoreLength snapshot.store + 4 * growth) +
          4 * (snapshot.width + growth) + 2 := by
      simpa only [growth, Nat.add_assoc] using Nat.add_le_add_right
        (Nat.add_le_add hentries (Nat.mul_le_mul_left 4 hwidth)) 2
    _ = encodedStoreLength snapshot.store + 4 * snapshot.width +
          8 * growth + 2 := by ring

theorem Snapshot.encode_initial_run_length_le_amortized_internal
    (program : Program) (fuel : ℕ) (input : List Bool) :
    ((Snapshot.initial input).run program fuel).encode.length ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) +
        4 * bitlen (input.length + 1) +
        8 * (RAM.logTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 2)) + 2 := by
  have hinitial := Snapshot.initial_represents_internal input
  have hrun := Snapshot.encode_run_length_le_amortized_internal
    program fuel (Snapshot.initial input) hinitial.1
  rw [hinitial.2] at hrun
  have hentries := encodedStoreLength_initial_le_internal input
  have hentries' : encodedStoreLength (Snapshot.initial input).store ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) := by
    simpa only [Snapshot.initial] using hentries
  have hwidth := Snapshot.initial_width_le_internal input
  have hunit := RAM.unitTimeUpto_le_logTimeUpto program fuel
    (RAM.initCfg input)
  have hgrowth :
      RAM.unitTimeUpto program fuel (RAM.initCfg input) *
            (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input) ≤
        RAM.logTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 2) := by
    calc
      RAM.unitTimeUpto program fuel (RAM.initCfg input) *
              (programStaticWidth program + 1) +
            RAM.logTimeUpto program fuel (RAM.initCfg input) ≤
          RAM.logTimeUpto program fuel (RAM.initCfg input) *
              (programStaticWidth program + 1) +
            RAM.logTimeUpto program fuel (RAM.initCfg input) :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (programStaticWidth program + 1) hunit) _
      _ = RAM.logTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 2) := by ring
  have hentriesWidth := Nat.add_le_add hentries'
    (Nat.mul_le_mul_left 4 hwidth)
  have hgrowth' := Nat.mul_le_mul_left 8 hgrowth
  exact le_trans hrun
    (Nat.add_le_add_right (Nat.add_le_add hentriesWidth hgrowth') 2)

theorem Snapshot.encode_run_length_le_internal (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      (snapshot.store.length + RAM.unitTimeUpto program fuel snapshot.decode + 1) *
        (4 * (snapshot.width + RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2) := by
  have hcode := Snapshot.encode_length_le_sizeBound_internal
    (snapshot.run program fuel)
  have hlength := Snapshot.length_run_le_internal program fuel snapshot hcanonical
  have hwidth := Snapshot.width_run_le_internal program fuel snapshot hcanonical
  apply le_trans hcode
  unfold Snapshot.sizeBound
  apply Nat.mul_le_mul
  · omega
  · omega

theorem Snapshot.encode_run_length_le_logTime_internal
    (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      (snapshot.store.length + RAM.logTimeUpto program fuel snapshot.decode + 1) *
        (4 * (snapshot.width + RAM.logTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2) := by
  have hcode := Snapshot.encode_run_length_le_internal
    program fuel snapshot hcanonical
  have hunit := RAM.unitTimeUpto_le_logTimeUpto program fuel snapshot.decode
  apply le_trans hcode
  apply Nat.mul_le_mul
  · omega
  · have hmul := Nat.mul_le_mul_right (programStaticWidth program + 1) hunit
    omega

theorem Snapshot.encode_initial_run_length_le_logTime_internal
    (program : Program) (fuel : ℕ) (input : List Bool) :
    ((Snapshot.initial input).run program fuel).encode.length ≤
      (input.length + 1 + RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) *
        (4 * (bitlen (input.length + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input) *
            (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input)) + 2) := by
  have hrepresents := Snapshot.initial_represents_internal input
  have hcode := Snapshot.encode_run_length_le_logTime_internal program fuel
    (Snapshot.initial input) hrepresents.1
  rw [hrepresents.2] at hcode
  have hlength := initialStore_length_le_internal input
  have hlength' : (Snapshot.initial input).store.length ≤ input.length + 1 := by
    simpa only [Snapshot.initial] using hlength
  have hwidth := Snapshot.initial_width_le_internal input
  apply le_trans hcode
  apply Nat.mul_le_mul <;> omega

end RegisterStore

end RAM

end Complexity

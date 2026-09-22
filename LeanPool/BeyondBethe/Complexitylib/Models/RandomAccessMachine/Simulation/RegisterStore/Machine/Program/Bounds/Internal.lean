/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Bounds.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Decision.Defs
import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Internal

/-!
# Sparse RAM decision-machine resource-bound proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem size_le_self (value : ℕ) : value.size ≤ value := by
  rw [Nat.size_le]
  exact Nat.lt_pow_self (by decide)

private theorem bitlen_le_succ (value : ℕ) : bitlen value ≤ value + 1 := by
  unfold bitlen
  exact le_trans (size_le_self value) (Nat.le_succ value)

private theorem instructionStaticWidth_le_resourceMagnitude
    (instruction : Instr) :
    RegisterStore.Instr.staticWidth instruction ≤
      instructionResourceMagnitude instruction := by
  cases instruction with
  | imm destination value =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ destination) (by omega))
        (le_trans (bitlen_le_succ value) (by omega))
  | add destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ destination) (by omega))
        (max_le (le_trans (bitlen_le_succ source₀) (by omega))
          (le_trans (bitlen_le_succ source₁) (by omega)))
  | sub destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ destination) (by omega))
        (max_le (le_trans (bitlen_le_succ source₀) (by omega))
          (le_trans (bitlen_le_succ source₁) (by omega)))
  | mul destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ destination) (by omega))
        (max_le (le_trans (bitlen_le_succ source₀) (by omega))
          (le_trans (bitlen_le_succ source₁) (by omega)))
  | load destination addressRegister =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ destination) (by omega))
        (le_trans (bitlen_le_succ addressRegister) (by omega))
  | store destination addressRegister =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ destination) (by omega))
        (le_trans (bitlen_le_succ addressRegister) (by omega))
  | jz source target =>
      simp only [RegisterStore.Instr.staticWidth,
        instructionResourceMagnitude]
      exact max_le (le_trans (bitlen_le_succ source) (by omega))
        (le_trans (bitlen_le_succ target) (by omega))
  | jmp target =>
      exact le_trans (bitlen_le_succ target) (by
        simp [instructionResourceMagnitude])
  | halt => simp [RegisterStore.Instr.staticWidth,
      instructionResourceMagnitude]

theorem programResourceMagnitude_pos_internal (program : Program) :
    1 ≤ programResourceMagnitude program := by
  simp [programResourceMagnitude]

theorem program_length_le_resourceMagnitude_internal (program : Program) :
    program.length ≤ programResourceMagnitude program := by
  unfold programResourceMagnitude
  omega

theorem programStaticWidth_le_resourceMagnitude_internal (program : Program) :
    programStaticWidth program ≤ programResourceMagnitude program := by
  induction program with
  | nil => simp [programStaticWidth, programResourceMagnitude]
  | cons instruction rest ih =>
      have hinstruction :=
        instructionStaticWidth_le_resourceMagnitude instruction
      simp only [programStaticWidth, programResourceMagnitude,
        List.length_cons, List.map_cons, List.sum_cons]
      apply max_le
      · omega
      · unfold programResourceMagnitude at ih
        omega

theorem programDecisionScale_pos_internal (program : Program)
    (inputLength cost : ℕ) :
    1 ≤ programDecisionScale program inputLength cost := by
  simp [programDecisionScale]

private theorem binarySuccTime_le_width (value width : ℕ)
    (hvalue : value.size ≤ width) :
    TM.binarySuccTime value ≤ 2 * width + 2 := by
  exact le_trans (TM.binarySuccTime_le value) (by omega)

private theorem binaryPredTime_le_width (value width : ℕ)
    (hvalue : (value + 1).size ≤ width) :
    TM.binaryPredTime value ≤ 2 * width + 2 := by
  exact le_trans (TM.binaryPredTime_le value) (by omega)

private theorem binaryCopyTime_le_width (srcValue dstValue width : ℕ)
    (hsrc : srcValue.size ≤ width) (hdst : dstValue.size ≤ width) :
    TM.binaryCopyTime srcValue dstValue ≤ 5 * width + 20 := by
  exact le_trans (TM.binaryCopyTime_le srcValue dstValue) (by omega)

private theorem binaryAddConstTime_zero_le (fixedValue : ℕ) :
    TM.binaryAddConstTime fixedValue 0 ≤ 4 * (fixedValue + 1) ^ 2 := by
  induction fixedValue with
  | zero => simp [TM.binaryAddConstTime]
  | succ fixedValue ih =>
      rw [TM.binaryAddConstTime]
      have hsucc := TM.binarySuccTime_le fixedValue
      have hsize := size_le_self fixedValue
      calc
        TM.binaryAddConstTime fixedValue 0 + 1 +
            TM.binarySuccTime (0 + fixedValue) ≤
            4 * (fixedValue + 1) ^ 2 + 1 + (2 * fixedValue + 2) := by
          simp only [Nat.zero_add]
          exact Nat.add_le_add (Nat.add_le_add ih le_rfl)
            (le_trans hsucc (by omega))
        _ ≤ 4 * (fixedValue + 1 + 1) ^ 2 := by nlinarith

private theorem binaryAddConstTime_zero_le_width (fixedValue width : ℕ)
    (hconstant : fixedValue ≤ width) :
    TM.binaryAddConstTime fixedValue 0 ≤ 5 * (width + 1) ^ 2 := by
  have htime := binaryAddConstTime_zero_le fixedValue
  nlinarith [Nat.mul_le_mul (Nat.add_le_add_right hconstant 1)
    (Nat.add_le_add_right hconstant 1)]

private theorem forWorkOnesLoopTime_succ_le
    (limit value count : ℕ) (hsum : value + count ≤ limit) :
    TM.forWorkOnesLoopTime TM.binarySuccTime value count ≤
      1 + count * (2 * limit + 4) := by
  induction count generalizing value with
  | zero => simp [TM.forWorkOnesLoopTime]
  | succ count ih =>
      rw [TM.forWorkOnesLoopTime]
      have hvalue : value ≤ limit := by omega
      have hsize : value.size ≤ limit :=
        le_trans (size_le_self value) hvalue
      have hsucc := binarySuccTime_le_width value limit hsize
      have htail := ih (value + 1) (by omega)
      rw [Nat.succ_mul]
      omega

private theorem wordWidthTime_le (width : ℕ) :
    wordWidthTime width ≤ 4 * (width + 1) ^ 2 := by
  have hloop := forWorkOnesLoopTime_succ_le width 0 width (by omega)
  unfold wordWidthTime
  nlinarith

private theorem binaryForLoopTime_one_le
    (limit value count : ℕ) (hsum : value + count ≤ limit) :
    TM.binaryForLoopTime (fun _ => 1) limit value count ≤
      (count + 1) * (4 * limit + 8) := by
  induction count generalizing value with
  | zero =>
      simp only [TM.binaryForLoopTime, TM.binaryForCompareTime]
      have hsize := size_le_self limit
      omega
  | succ count ih =>
      rw [TM.binaryForLoopTime]
      have hvalue : value ≤ limit := by omega
      have hsize : value.size ≤ limit :=
        le_trans (size_le_self value) hvalue
      have hsucc := binarySuccTime_le_width value limit hsize
      have hlimitSize := size_le_self limit
      have htail := ih (value + 1) (by omega)
      simp only [TM.binaryForCompareTime, TM.binaryForIterationTime]
      nlinarith

private theorem wordPayloadTime_le (width : ℕ) :
    wordPayloadTime width ≤ 8 * (width + 1) ^ 2 := by
  have hloop := binaryForLoopTime_one_le width 0 width (by omega)
  unfold wordPayloadTime
  nlinarith

private theorem wordDecodeTime_le (width bound : ℕ)
    (hwidth : width ≤ bound) :
    wordDecodeTime width ≤ 20 * (bound + 1) ^ 2 := by
  have hprefix := wordWidthTime_le width
  have hpayload := wordPayloadTime_le width
  unfold wordDecodeTime
  nlinarith [Nat.mul_le_mul hwidth hwidth]

private theorem entryMatchReadTime_le (entry : Entry)
    (queryBits : List Bool) (bound : ℕ)
    (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound)
    (hquery : queryBits.length ≤ bound) :
    entryMatchReadTime entry queryBits ≤ 100 * (bound + 1) ^ 2 := by
  have hlinear := entryMatchReadTime_le_linear entry queryBits
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  omega

private theorem entryMissBits_length_le {m : ℕ}
    (tapes : EntryMatchTapes m) (entry : Entry)
    (queryBits : List Bool) (bound : ℕ)
    (hbound : 1 ≤ bound)
    (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound) (i : Fin m) :
    (entryMissBits tapes entry queryBits i).length ≤ bound := by
  have haddressWidth : bitlen entry.1 ≤ bound := by
    simpa only [bitlen, Nat.size_eq_bits_len] using! haddress
  have hvalueWidth : bitlen entry.2 ≤ bound := by
    simpa only [bitlen, Nat.size_eq_bits_len] using! hvalue
  unfold entryMissBits
  split_ifs <;>
    (try simp only [List.length_nil, List.length_replicate,
      List.length_singleton]) <;> omega

private theorem entryMissCleanupTime_canonical_le {m : ℕ}
    (tapes : EntryMatchTapes m) (entry : Entry)
    (queryBits : List Bool) (bound : ℕ)
    (hbound : 1 ≤ bound)
    (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound)
    (hquery : queryBits.length ≤ bound) :
    entryMissCleanupTime tapes entry queryBits
        (entryScanCanonicalWork (n := m)) ≤
      1000 * (bound + 1) ^ 2 := by
  let matchTime := entryMatchReadTime entry queryBits
  have hmatch : matchTime ≤ 100 * (bound + 1) ^ 2 :=
    entryMatchReadTime_le entry queryBits bound haddress hvalue hquery
  have hreset := TM.resetBinaryWorkManyTime_le
    (entryMissTargets tapes) (entryMissBits tapes entry queryBits)
    (entryMissHeadBound entry queryBits (entryScanCanonicalWork (n := m)))
    (1 + matchTime) bound
    (fun i _ => by
      unfold entryMissHeadBound entryScanCanonicalWork
      simp only [Function.const_apply]
      dsimp only [matchTime]
      simp [TM.resetBinaryBlank, Tape.move, Tape.init])
    (fun i _ => entryMissBits_length_le tapes entry queryBits bound hbound
      haddress hvalue i)
  have htargets : (entryMissTargets tapes).length = 7 := by
    simp [entryMissTargets]
  rw [htargets] at hreset
  dsimp only [matchTime] at hmatch hreset
  have hreset' :
      TM.resetBinaryWorkManyTime (entryMissBits tapes entry queryBits)
          (fun _ => 1 + entryMatchReadTime entry queryBits)
          (entryMissTargets tapes) ≤
        7 * (1 + entryMatchReadTime entry queryBits + 2 * bound + 9) + 1 := by
    simpa [entryMissHeadBound, entryScanCanonicalWork,
      TM.resetBinaryBlank, Tape.move, Tape.init] using! hreset
  unfold entryMissCleanupTime entryMissHeadBound entryScanCanonicalWork
  simp only [Function.const_apply]
  simp only [TM.resetBinaryBlank, Tape.move, Tape.init]
  simp only [Nat.zero_add]
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  omega

private theorem entryScanOneTime_le {m : ℕ}
    (tapes : EntryScanTapes m) (entry : Entry)
    (queryBits : List Bool) (bound : ℕ)
    (hbound : 1 ≤ bound)
    (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound)
    (hquery : queryBits.length ≤ bound) :
    entryScanOneTime tapes entry queryBits ≤
      1200 * (bound + 1) ^ 2 := by
  have hmatch := entryMatchReadTime_le entry queryBits bound
    haddress hvalue hquery
  have hcleanup := entryMissCleanupTime_canonical_le tapes.entry entry
    queryBits bound hbound haddress hvalue hquery
  unfold entryScanOneTime entryScanStepTime entryScanBranchTime
    TM.branchWorkSymbolTime
  have hbranch : 1 + max 1
      (entryMissCleanupTime tapes.entry entry queryBits
        (entryScanCanonicalWork (n := m))) ≤
      1 + 1000 * (bound + 1) ^ 2 := by
    apply Nat.add_le_add_left
    apply max_le
    · have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
      omega
    · exact hcleanup
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  omega

private theorem entryScanTime_le {m : ℕ} (tapes : EntryScanTapes m)
    (queryBits : List Bool) (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hquery : queryBits.length ≤ bound) :
    entryScanTime tapes queryBits store ≤
      1300 * (store.length + 1) * (bound + 1) ^ 2 := by
  induction store with
  | nil =>
      simp [entryScanTime]
      nlinarith
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      have hrestEntries : ∀ current ∈ rest,
          current.1.bits.length ≤ bound ∧
            current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      have hrestLength : rest.length ≤ bound := by
        simp only [List.length_cons] at hstoreLength
        omega
      have hone := entryScanOneTime_le tapes entry queryBits bound hbound
        hentry.1 hentry.2 hquery
      have hpred := TM.binaryPredTime_le rest.length
      have hpredSize : (rest.length + 1).size ≤ bound := by
        exact le_trans (size_le_self (rest.length + 1)) (by simp_all)
      have hpred' : TM.binaryPredTime rest.length ≤ 2 * bound + 2 :=
        le_trans hpred (by omega)
      have htail := ih hrestLength hrestEntries
      simp only [entryScanTime, List.length_cons]
      have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
      have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
      nlinarith

private theorem entryScanTime_le_cube {m : ℕ}
    (tapes : EntryScanTapes m) (queryBits : List Bool)
    (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hquery : queryBits.length ≤ bound) :
    entryScanTime tapes queryBits store ≤ 1300 * (bound + 1) ^ 3 := by
  have htime := entryScanTime_le tapes queryBits store bound hbound
    hstoreLength hentries hquery
  have hfactor : store.length + 1 ≤ bound + 1 := by omega
  calc
    entryScanTime tapes queryBits store ≤
        1300 * (store.length + 1) * (bound + 1) ^ 2 := htime
    _ ≤ 1300 * (bound + 1) * (bound + 1) ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1300 hfactor)
    _ = 1300 * (bound + 1) ^ 3 := by ring

private theorem encodedStoreLength_le_uniform (store : Store) (bound : ℕ)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    encodedStoreLength store ≤ store.length * (4 * bound + 2) := by
  induction store with
  | nil => simp [encodedStoreLength]
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      have hrest : ∀ current ∈ rest,
          current.1.bits.length ≤ bound ∧
            current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      have htail := ih hrest
      have hhead : (Entry.encode entry).length ≤ 4 * bound + 2 := by
        rw [Entry.encode_length]
        have haddressWidth : bitlen entry.1 ≤ bound := by
          simpa only [bitlen, Nat.size_eq_bits_len] using! hentry.1
        have hvalueWidth : bitlen entry.2 ≤ bound := by
          simpa only [bitlen, Nat.size_eq_bits_len] using! hentry.2
        omega
      unfold encodedStoreLength at htail ⊢
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        Nat.succ_mul]
      ring_nf at htail ⊢
      omega

private theorem entryScanTime_le_square {m : ℕ}
    (tapes : EntryScanTapes m) (queryBits : List Bool)
    (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hquery : queryBits.length ≤ bound) :
    entryScanTime tapes queryBits store ≤ 7000 * (bound + 1) ^ 2 := by
  have hscan := entryScanTime_le_encoded tapes queryBits store
  have hencoded := encodedStoreLength_le_uniform store bound hentries
  have hcount : bitlen store.length ≤ bound := by
    unfold bitlen
    exact le_trans (size_le_self store.length) hstoreLength
  have hfactor : queryBits.length + bitlen store.length + 2 ≤
      2 * bound + 2 := by omega
  have hencoded' : encodedStoreLength store ≤
      bound * (4 * bound + 2) :=
    le_trans hencoded (Nat.mul_le_mul_right _ hstoreLength)
  have hqueryTerm : store.length *
      (queryBits.length + bitlen store.length + 2) ≤
      bound * (2 * bound + 2) :=
    Nat.mul_le_mul hstoreLength hfactor
  have hinside : encodedStoreLength store +
        store.length * (queryBits.length + bitlen store.length + 2) + 1 ≤
      7 * (bound + 1) ^ 2 := by
    nlinarith
  exact le_trans hscan (by
    calc
      1000 * (encodedStoreLength store +
            store.length *
              (queryBits.length + bitlen store.length + 2) + 1)
          ≤ 1000 * (7 * (bound + 1) ^ 2) :=
        Nat.mul_le_mul_left 1000 hinside
      _ = 7000 * (bound + 1) ^ 2 := by ring)

private theorem read_bits_length_le (store : Store) (address bound : ℕ)
    (hentries : ∀ entry ∈ store, entry.2.bits.length ≤ bound) :
    (RegisterStore.read store address).bits.length ≤ bound := by
  induction store with
  | nil => simp [RegisterStore.read]
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      have hrest : ∀ current ∈ rest,
          current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      simp only [RegisterStore.read]
      split
      · exact hentry
      · exact ih hrest

private theorem entryLookupEntryWidth_le (entry : Entry)
    (address bound : ℕ) (hbound : 1 ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hentryAddress : entry.1.bits.length ≤ bound)
    (hentryValue : entry.2.bits.length ≤ bound) :
    entryLookupEntryWidth entry address ≤ bound := by
  have haddressWidth : bitlen entry.1 ≤ bound := by
    simpa only [bitlen, Nat.size_eq_bits_len] using! hentryAddress
  have hvalueWidth : bitlen entry.2 ≤ bound := by
    simpa only [bitlen, Nat.size_eq_bits_len] using! hentryValue
  unfold entryLookupEntryWidth
  omega

private theorem entryLookupStoreWidth_le (store : Store)
    (address bound : ℕ) (hbound : 1 ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    entryLookupStoreWidth address store ≤ bound := by
  induction store with
  | nil => simpa [entryLookupStoreWidth] using! haddress
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      have hrest : ∀ current ∈ rest,
          current.1.bits.length ≤ bound ∧
            current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      simp only [entryLookupStoreWidth]
      exact max_le
        (entryLookupEntryWidth_le entry address bound hbound haddress
          hentry.1 hentry.2)
        (ih hrest)

private theorem entryLookupResetWidth_le (store : Store)
    (address bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    entryLookupResetWidth store address ≤ bound := by
  have hlengthBits : store.length.bits.length ≤ bound := by
    rw [Nat.size_eq_bits_len store.length]
    exact le_trans (size_le_self store.length) hstoreLength
  unfold entryLookupResetWidth
  exact max_le hlengthBits
    (entryLookupStoreWidth_le store address bound hbound haddress hentries)

private theorem entryLookupLoadedTime_le {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (store : Store)
    (address bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    entryLookupLoadedTime tapes store address ≤
      20000 * (bound + 1) ^ 3 := by
  have hscan := entryScanTime_le_cube tapes.scan address.bits store bound
    hbound hstoreLength hentries haddress
  have hlookup : entryLookupTime tapes.scan address store ≤
      1300 * (bound + 1) ^ 3 := hscan
  have hwidth := entryLookupResetWidth_le store address bound hbound
    hstoreLength haddress hentries
  have hread := read_bits_length_le store address bound
    (fun entry hentry => (hentries entry hentry).2)
  have hcopyAddress := binaryCopyTime_le_width address 0 bound
    (by simpa [Nat.size_eq_bits_len] using! haddress) (by simp)
  have hcopyRead := binaryCopyTime_le_width
    (RegisterStore.read store address) 0 bound
    (by simpa [Nat.size_eq_bits_len] using! hread) (by simp)
  have hcopyCount := binaryCopyTime_le_width store.length 0 bound
    (le_trans (size_le_self store.length) hstoreLength) (by simp)
  unfold entryLookupLoadedTime entryLookupCopyRestoreTime
    entryLookupRestoreTailTime entryLookupResetTime
    entryLookupRestoreHeadBound
  have hboundCube : bound ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega) hboundCube
  omega

private theorem entryLookupStaticTime_le {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (store : Store)
    (address bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (haddressValue : address ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    entryLookupStaticTime tapes store address ≤
      21000 * (bound + 1) ^ 3 := by
  have haddress : address.bits.length ≤ bound := by
    rw [Nat.size_eq_bits_len address]
    exact le_trans (size_le_self address) haddressValue
  have hloaded := entryLookupLoadedTime_le tapes store address bound hbound
    hstoreLength haddress hentries
  have hadd := binaryAddConstTime_zero_le_width address bound haddressValue
  unfold entryLookupStaticTime
  have hreset : TM.resetBinaryWorkTime 1 address.bits.length ≤
      2 * bound + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    omega
  have hboundCube : bound ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega) hboundCube
  have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
    calc
      (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
      _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (bound + 1) ^ 3 := by ring
  omega

private theorem rewindEntryEncodeTime_le (entry : Entry)
    (addressHead valueHead bound : ℕ)
    (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound)
    (haddressHead : addressHead ≤ bound)
    (hvalueHead : valueHead ≤ bound) :
    rewindEntryEncodeTime entry addressHead valueHead ≤ 10 * bound + 21 := by
  unfold rewindEntryEncodeTime rewindWordEncodeTime wordEncodeTime
  omega

private theorem entryUpdatePostEmitHead_le {m : ℕ}
    (tapes : EntryUpdateTapes m) (entry : Entry) (i : Fin m)
    (bound : ℕ) (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound) :
    entryUpdatePostEmitHead tapes entry i ≤ bound + 1 := by
  have haddressWidth : bitlen entry.1 ≤ bound := by
    simpa only [bitlen, Nat.size_eq_bits_len] using! haddress
  have hvalueWidth : bitlen entry.2 ≤ bound := by
    simpa only [bitlen, Nat.size_eq_bits_len] using! hvalue
  unfold entryUpdatePostEmitHead
  split_ifs <;> omega

private theorem entryUpdateReadyCleanupTime_le {m : ℕ}
    (tapes : EntryUpdateTapes m) (entry : Entry) (address bound : ℕ)
    (hbound : 1 ≤ bound)
    (hentryAddress : entry.1.bits.length ≤ bound)
    (hentryValue : entry.2.bits.length ≤ bound)
    (haddress : address.bits.length ≤ bound) :
    entryUpdateReadyCleanupTime tapes entry address ≤
      1000 * (bound + 1) ^ 2 := by
  let matchTime := entryMatchReadTime entry address.bits
  have hmatch : matchTime ≤ 100 * (bound + 1) ^ 2 :=
    entryMatchReadTime_le entry address.bits bound hentryAddress hentryValue
      haddress
  have hreset := TM.resetBinaryWorkManyTime_le
    (entryMissTargets tapes.entry) (entryMissBits tapes.entry entry address.bits)
    (fun _ => 1 + matchTime) (1 + matchTime) bound
    (fun _ _ => le_rfl)
    (fun i _ => entryMissBits_length_le tapes.entry entry address.bits bound
      hbound hentryAddress hentryValue i)
  have htargets : (entryMissTargets tapes.entry).length = 7 := by
    simp [entryMissTargets]
  rw [htargets] at hreset
  unfold entryUpdateReadyCleanupTime
  dsimp only [matchTime] at hmatch hreset ⊢
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  omega

private theorem entryUpdatePostEmitCleanupTime_le {m : ℕ}
    (tapes : EntryUpdateTapes m) (entry : Entry) (address bound : ℕ)
    (hbound : 1 ≤ bound)
    (hentryAddress : entry.1.bits.length ≤ bound)
    (hentryValue : entry.2.bits.length ≤ bound)
    (haddress : address.bits.length ≤ bound) :
    entryUpdatePostEmitCleanupTime tapes entry address ≤
      2000 * (bound + 1) ^ 2 := by
  let matchTime := entryMatchReadTime entry address.bits
  have hmatch : matchTime ≤ 100 * (bound + 1) ^ 2 :=
    entryMatchReadTime_le entry address.bits bound hentryAddress hentryValue
      haddress
  have hreset := TM.resetBinaryWorkManyTime_le
    (entryMissTargets tapes.entry) (entryMissBits tapes.entry entry address.bits)
    (fun i => entryUpdatePostEmitHead tapes entry i + matchTime)
    (bound + 1 + matchTime) bound
    (fun i _ => Nat.add_le_add_right
      (entryUpdatePostEmitHead_le tapes entry i bound hentryAddress hentryValue)
      matchTime)
    (fun i _ => entryMissBits_length_le tapes.entry entry address.bits bound
      hbound hentryAddress hentryValue i)
  have htargets : (entryMissTargets tapes.entry).length = 7 := by
    simp [entryMissTargets]
  rw [htargets] at hreset
  unfold entryUpdatePostEmitCleanupTime
  dsimp only [matchTime] at hmatch hreset ⊢
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  omega

private theorem entryUpdateBranchTime_le {m : ℕ}
    (tapes : EntryUpdateTapes m) (entry : Entry)
    (address newValue total bound : ℕ) (hbound : 1 ≤ bound)
    (hentryAddress : entry.1.bits.length ≤ bound)
    (hentryValue : entry.2.bits.length ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hnewValue : newValue.bits.length ≤ bound)
    (htotal : total ≤ bound) :
    entryUpdateBranchTime tapes entry address newValue total ≤
      4000 * (bound + 1) ^ 2 := by
  let matchTime := entryMatchReadTime entry address.bits
  have hmatch : matchTime ≤ 100 * (bound + 1) ^ 2 :=
    entryMatchReadTime_le entry address.bits bound hentryAddress hentryValue
      haddress
  have hpost := entryUpdatePostEmitCleanupTime_le tapes entry address bound
    hbound hentryAddress hentryValue haddress
  have hready := entryUpdateReadyCleanupTime_le tapes entry address bound
    hbound hentryAddress hentryValue haddress
  have hrewindMiss := rewindEntryEncodeTime_le entry (1 + matchTime)
    (1 + matchTime) (1 + 100 * (bound + 1) ^ 2)
    (le_trans hentryAddress (by nlinarith))
    (le_trans hentryValue (by nlinarith)) (by omega) (by omega)
  have hrewindReplace := rewindEntryEncodeTime_le (entry.1, newValue)
    (1 + matchTime) 1 (1 + 100 * (bound + 1) ^ 2)
    (le_trans hentryAddress (by nlinarith))
    (le_trans hnewValue (by nlinarith)) (by omega) (by omega)
  have hcount : entryUpdateCountTime total ≤ 2 * bound + 2 := by
    unfold entryUpdateCountTime
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 (le_trans (size_le_self total) htotal)) 2
  unfold entryUpdateBranchTime entryUpdateMissTime entryUpdateReplaceTime
  dsimp only [matchTime] at hmatch hpost hready hrewindMiss hrewindReplace ⊢
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  apply max_le
  · omega
  · apply max_le <;> omega

private theorem entryUpdateTime_le {m : ℕ} (tapes : EntryUpdateTapes m)
    (store : Store) (address newValue bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hnewValue : newValue.bits.length ≤ bound) :
    entryUpdateTime tapes store address newValue ≤
      5000 * (bound + 1) ^ 3 := by
  have hloop : ∀ remaining : Store, remaining.length ≤ bound →
      (∀ entry ∈ remaining,
        entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) →
      entryUpdateLoopTime tapes address newValue store.length remaining ≤
        5000 * (remaining.length + 1) * (bound + 1) ^ 2 := by
    intro remaining
    induction remaining with
    | nil =>
        intro _ _
        have hrewind := rewindEntryEncodeTime_le (address, newValue) 1 1
          bound haddress hnewValue hbound hbound
        have hcount : entryUpdateCountTime store.length ≤ 2 * bound + 2 := by
          unfold entryUpdateCountTime
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 2
              (le_trans (size_le_self store.length) hstoreLength)) 2
        unfold entryUpdateLoopTime entryAppendRestoreTime
        simp only [List.length_nil, Nat.zero_add, Nat.mul_one]
        have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
        have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
        omega
    | cons entry rest ih =>
        intro hremainingLength hremainingEntries
        have hentry := hremainingEntries entry (by simp)
        have hrestEntries : ∀ current ∈ rest,
            current.1.bits.length ≤ bound ∧
              current.2.bits.length ≤ bound := by
          intro current hcurrent
          exact hremainingEntries current (by simp [hcurrent])
        have hrestLength : rest.length ≤ bound := by
          simp only [List.length_cons] at hremainingLength
          omega
        have hmatch := entryMatchReadTime_le entry address.bits bound
          hentry.1 hentry.2 haddress
        have hbranch := entryUpdateBranchTime_le tapes entry address newValue
          store.length bound hbound hentry.1 hentry.2 haddress hnewValue
          hstoreLength
        have hpred := TM.binaryPredTime_le rest.length
        have hpredSize : (rest.length + 1).size ≤ bound :=
          le_trans (size_le_self (rest.length + 1)) (by
            simp only [List.length_cons] at hremainingLength
            omega)
        have hpred' : TM.binaryPredTime rest.length ≤ 2 * bound + 2 :=
          le_trans hpred (by omega)
        have htail := ih hrestLength hrestEntries
        unfold entryUpdateLoopTime entryUpdateIterationTime
        have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
        have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
        simp only [List.length_cons]
        nlinarith
  unfold entryUpdateTime
  have htime := hloop store hstoreLength hentries
  have hfactor : store.length + 1 ≤ bound + 1 := by omega
  calc
    entryUpdateLoopTime tapes address newValue store.length store ≤
        5000 * (store.length + 1) * (bound + 1) ^ 2 := htime
    _ ≤ 5000 * (bound + 1) * (bound + 1) ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5000 hfactor)
    _ = 5000 * (bound + 1) ^ 3 := by ring

private theorem entriesEncode_length_le (store : Store) (bound : ℕ)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    (store.flatMap Entry.encode).length ≤ store.length * (4 * bound + 2) := by
  induction store with
  | nil => simp
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      have hrest : ∀ current ∈ rest,
          current.1.bits.length ≤ bound ∧
            current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      have htail := ih hrest
      have hhead : (Entry.encode entry).length ≤ 4 * bound + 2 := by
        rw [Entry.encode_length]
        simpa [bitlen, Nat.size_eq_bits_len] using!
          (show 2 * entry.1.bits.length + 2 * entry.2.bits.length + 2 ≤
              4 * bound + 2 by omega)
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

private theorem binaryInstructionArithmeticTime_le
    (op : BinaryInstrOp) (lhs rhs bound : ℕ)
    (hlhs : lhs.bits.length ≤ bound)
    (hrhs : rhs.bits.length ≤ bound) :
    binaryInstructionArithmeticTime op lhs rhs ≤
      1000 * (bound + 1) ^ 2 := by
  have hlhsSize : lhs.size ≤ bound := by
    simpa [Nat.size_eq_bits_len] using! hlhs
  have hrhsSize : rhs.size ≤ bound := by
    simpa [Nat.size_eq_bits_len] using! hrhs
  cases op with
  | add =>
      have htime := TM.binaryRippleAddTime_le lhs rhs
      have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
      have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
      change TM.binaryRippleAddTime lhs rhs ≤ 1000 * (bound + 1) ^ 2
      omega
  | sub =>
      have htime := TM.binaryRippleSubTime_le lhs rhs
      have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
      have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
      change TM.binaryRippleSubTime lhs rhs ≤ 1000 * (bound + 1) ^ 2
      omega
  | mul =>
      change TM.binaryShiftMulTime lhs rhs ≤ 1000 * (bound + 1) ^ 2
      unfold TM.binaryShiftMulTime TM.binaryShiftMulWidth
      nlinarith

private theorem binaryInstrResult_bits_length_le
    (op : BinaryInstrOp) (lhs rhs bound : ℕ)
    (hlhs : lhs.bits.length ≤ bound)
    (hrhs : rhs.bits.length ≤ bound) :
    (op.eval lhs rhs).bits.length ≤ 2 * bound + 1 := by
  have hlhsSize : lhs.size ≤ bound := by
    simpa [Nat.size_eq_bits_len] using! hlhs
  have hrhsSize : rhs.size ≤ bound := by
    simpa [Nat.size_eq_bits_len] using! hrhs
  rw [Nat.size_eq_bits_len (op.eval lhs rhs)]
  cases op with
  | add =>
      exact le_trans (TM.binaryRippleAdd_sum_size_le lhs rhs) (by omega)
  | sub =>
      exact le_trans (Nat.size_le_size (Nat.sub_le lhs rhs)) (by omega)
  | mul =>
      exact le_trans (BinaryShiftMul.size_mul_le_add lhs rhs) (by omega)

private theorem directBinaryInstructionTime_le {m : ℕ}
    (tapes : BinaryInstructionTapes m) (op : BinaryInstrOp)
    (store : Store) (destination source₀ source₁ bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hdestination : destination ≤ bound)
    (hsource₀ : source₀ ≤ bound) (hsource₁ : source₁ ≤ bound) :
    directBinaryInstructionTime tapes op store destination source₀ source₁ ≤
      100000 * (bound + 1) ^ 3 := by
  let lhs := RegisterStore.read store source₀
  let rhs := RegisterStore.read store source₁
  have hlhs : lhs.bits.length ≤ bound := read_bits_length_le store source₀ bound
    (fun entry hentry => (hentries entry hentry).2)
  have hrhs : rhs.bits.length ≤ bound := read_bits_length_le store source₁ bound
    (fun entry hentry => (hentries entry hentry).2)
  have hlookup₀ := entryLookupStaticTime_le tapes.lhsLookup store source₀
    bound hbound hstoreLength hsource₀ hentries
  have hlookup₁ := entryLookupStaticTime_le tapes.rhsLookup store source₁
    bound hbound hstoreLength hsource₁ hentries
  have hadd := binaryAddConstTime_zero_le_width destination bound hdestination
  have harithmetic := binaryInstructionArithmeticTime_le op lhs rhs bound hlhs hrhs
  let wide := 2 * bound + 1
  have hwide : 1 ≤ wide := by omega
  have hresult : (op.eval lhs rhs).bits.length ≤ wide :=
    binaryInstrResult_bits_length_le op lhs rhs bound hlhs hrhs
  have hdestinationBitsWide : destination.bits.length ≤ wide := by
    rw [Nat.size_eq_bits_len destination]
    exact le_trans (size_le_self destination) (by omega)
  have hupdate := entryUpdateTime_le tapes.update store destination
    (op.eval lhs rhs) wide hwide (by omega)
    (fun entry hentry => ⟨le_trans (hentries entry hentry).1 (by omega),
      le_trans (hentries entry hentry).2 (by omega)⟩)
    hdestinationBitsWide hresult
  have hwideCube : (wide + 1) ^ 3 = 8 * (bound + 1) ^ 3 := by
    simp only [wide]
    ring
  rw [hwideCube] at hupdate
  dsimp only [lhs, rhs] at hlhs hrhs harithmetic hupdate ⊢
  unfold directBinaryInstructionTime binaryInstructionUpdateTime
  have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
    calc
      (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
      _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (bound + 1) ^ 3 := by ring
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  omega

private theorem immediateInstructionTime_le {m : ℕ}
    (tapes : BinaryInstructionTapes m) (store : Store)
    (destination value bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hdestination : destination ≤ bound) (hvalue : value ≤ bound) :
    immediateInstructionTime tapes store destination value ≤
      30000 * (bound + 1) ^ 3 := by
  have hvalueBits : value.bits.length ≤ bound := by
    rw [Nat.size_eq_bits_len value]
    exact le_trans (size_le_self value) hvalue
  have hdestinationBits : destination.bits.length ≤ bound := by
    rw [Nat.size_eq_bits_len destination]
    exact le_trans (size_le_self destination) hdestination
  have hupdate := entryUpdateTime_le tapes.update store destination value bound
    hbound hstoreLength hentries hdestinationBits hvalueBits
  have hvalueAdd := binaryAddConstTime_zero_le_width value bound hvalue
  have hdestinationAdd := binaryAddConstTime_zero_le_width destination bound
    hdestination
  unfold immediateInstructionTime
  have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
    calc
      (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
      _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (bound + 1) ^ 3 := by ring
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  omega

private theorem indirectLoadInstructionTime_le {m : ℕ}
    (tapes : BinaryInstructionTapes m) (store : Store)
    (destination addressRegister bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hdestination : destination ≤ bound)
    (haddressRegister : addressRegister ≤ bound) :
    indirectLoadInstructionTime tapes store destination addressRegister ≤
      80000 * (bound + 1) ^ 3 := by
  let address := RegisterStore.read store addressRegister
  let value := RegisterStore.read store address
  have haddress : address.bits.length ≤ bound := read_bits_length_le store
    addressRegister bound (fun entry hentry => (hentries entry hentry).2)
  have hvalue : value.bits.length ≤ bound := read_bits_length_le store address
    bound (fun entry hentry => (hentries entry hentry).2)
  have hlookup := entryLookupStaticTime_le tapes.lhsLookup store addressRegister
    bound hbound hstoreLength haddressRegister hentries
  have hloaded := entryLookupLoadedTime_le tapes.indirectLoadLookup store address
    bound hbound hstoreLength haddress hentries
  have hadd := binaryAddConstTime_zero_le_width destination bound hdestination
  have hdestinationBits : destination.bits.length ≤ bound := by
    rw [Nat.size_eq_bits_len destination]
    exact le_trans (size_le_self destination) hdestination
  have hupdate := entryUpdateTime_le tapes.update store destination value bound
    hbound hstoreLength hentries hdestinationBits hvalue
  dsimp only [address, value] at hloaded hupdate ⊢
  unfold indirectLoadInstructionTime
  have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
    calc
      (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
      _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (bound + 1) ^ 3 := by ring
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  omega

private theorem indirectStoreInstructionTime_le {m : ℕ}
    (tapes : BinaryInstructionTapes m) (store : Store)
    (addressRegister source bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (haddressRegister : addressRegister ≤ bound) (hsource : source ≤ bound) :
    indirectStoreInstructionTime tapes store addressRegister source ≤
      80000 * (bound + 1) ^ 3 := by
  let address := RegisterStore.read store addressRegister
  let value := RegisterStore.read store source
  have haddress : address.bits.length ≤ bound := read_bits_length_le store
    addressRegister bound (fun entry hentry => (hentries entry hentry).2)
  have hvalue : value.bits.length ≤ bound := read_bits_length_le store source
    bound (fun entry hentry => (hentries entry hentry).2)
  have hlookupAddress := entryLookupStaticTime_le tapes.lhsLookup store
    addressRegister bound hbound hstoreLength haddressRegister hentries
  have hlookupValue := entryLookupStaticTime_le tapes.rhsLookup store source
    bound hbound hstoreLength hsource hentries
  have hcopyAddress := binaryCopyTime_le_width address 0 bound
    (by simpa [Nat.size_eq_bits_len] using! haddress) (by simp)
  have hcopyValue := binaryCopyTime_le_width value 0 bound
    (by simpa [Nat.size_eq_bits_len] using! hvalue) (by simp)
  have hupdate := entryUpdateTime_le tapes.update store address value bound
    hbound hstoreLength hentries haddress hvalue
  dsimp only [address, value] at hcopyAddress hcopyValue hupdate ⊢
  unfold indirectStoreInstructionTime
  have hboundCube : bound ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega) hboundCube
  omega

private theorem executeInstructionTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound)
    (hinstruction : instructionResourceMagnitude instruction ≤ bound) :
    executeInstructionTime tapes instruction pcValue store ≤
      200000 * (bound + 1) ^ 3 := by
  have hpcSucc : TM.binarySuccTime pcValue ≤ 2 * bound + 2 :=
    binarySuccTime_le_width pcValue bound (by
      simpa [Nat.size_eq_bits_len] using! hpc)
  have hencoded := entriesEncode_length_le store bound hentries
  have hencodedCube : (store.flatMap Entry.encode).length ≤
      6 * (bound + 1) ^ 3 := by
    have hproduct := Nat.mul_le_mul hstoreLength (show 4 * bound + 2 ≤
      6 * (bound + 1) by omega)
    have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
      calc
        (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
        _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (bound + 1) ^ 3 := by ring
    calc
      (store.flatMap Entry.encode).length ≤ store.length * (4 * bound + 2) :=
        hencoded
      _ ≤ bound * (6 * (bound + 1)) := hproduct
      _ ≤ 6 * (bound + 1) ^ 2 := by nlinarith
      _ ≤ 6 * (bound + 1) ^ 3 := Nat.mul_le_mul_left 6 hsqCube
  have hresetPC : TM.resetBinaryWorkTime 1 pcValue.bits.length ≤
      2 * bound + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    omega
  have hboundCube : bound ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega) hboundCube
  cases instruction with
  | imm destination value =>
      simp only [instructionResourceMagnitude] at hinstruction
      have htime := immediateInstructionTime_le tapes.data store destination value
        bound hbound hstoreLength hentries (by omega) (by omega)
      simp only [executeInstructionTime]
      omega
  | add destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have htime := directBinaryInstructionTime_le tapes.data .add store
        destination source₀ source₁ bound hbound hstoreLength hentries
        (by omega) (by omega) (by omega)
      simp only [executeInstructionTime]
      omega
  | sub destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have htime := directBinaryInstructionTime_le tapes.data .sub store
        destination source₀ source₁ bound hbound hstoreLength hentries
        (by omega) (by omega) (by omega)
      simp only [executeInstructionTime]
      omega
  | mul destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have htime := directBinaryInstructionTime_le tapes.data .mul store
        destination source₀ source₁ bound hbound hstoreLength hentries
        (by omega) (by omega) (by omega)
      simp only [executeInstructionTime]
      omega
  | load destination addressRegister =>
      simp only [instructionResourceMagnitude] at hinstruction
      have htime := indirectLoadInstructionTime_le tapes.data store destination
        addressRegister bound hbound hstoreLength hentries (by omega) (by omega)
      simp only [executeInstructionTime]
      omega
  | store addressRegister source =>
      simp only [instructionResourceMagnitude] at hinstruction
      have htime := indirectStoreInstructionTime_le tapes.data store
        addressRegister source bound hbound hstoreLength hentries (by omega)
        (by omega)
      simp only [executeInstructionTime]
      omega
  | jz source target =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hlookup := entryLookupStaticTime_le tapes.lifted.data.lhsLookup store
        source bound hbound hstoreLength (by omega) hentries
      have hadd := binaryAddConstTime_zero_le_width target bound (by omega)
      have hread := read_bits_length_le store source bound
        (fun entry hentry => (hentries entry hentry).2)
      have hresetRead : TM.resetBinaryWorkTime 1
          (RegisterStore.read store source).bits.length ≤ 2 * bound + 9 := by
        unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
        omega
      change zeroJumpInstructionTime tapes.lifted store pcValue source target + 1 +
          (store.flatMap Entry.encode).length + 1 ≤
        200000 * (bound + 1) ^ 3
      unfold zeroJumpInstructionTime setProgramCounterTime
        TM.branchWorkBlankTime
      have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
        calc
          (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
          _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = (bound + 1) ^ 3 := by ring
      omega
  | jmp target =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hadd := binaryAddConstTime_zero_le_width target bound (by omega)
      change jumpInstructionTime pcValue target + 1 +
          (store.flatMap Entry.encode).length + 1 ≤
        200000 * (bound + 1) ^ 3
      unfold jumpInstructionTime setProgramCounterTime
      have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
        calc
          (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
          _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = (bound + 1) ^ 3 := by ring
      omega
  | halt =>
      change haltInstructionTime + 1 + (store.flatMap Entry.encode).length + 1 ≤
        200000 * (bound + 1) ^ 3
      unfold haltInstructionTime
      omega

private theorem instructionResourceMagnitude_le_program
    (instruction : Instr) (program : Program) (hinstruction : instruction ∈ program) :
    instructionResourceMagnitude instruction ≤ programResourceMagnitude program := by
  induction program with
  | nil => simp at hinstruction
  | cons head rest ih =>
      simp only [List.mem_cons] at hinstruction
      unfold programResourceMagnitude
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rcases hinstruction with rfl | hinstruction
      · omega
      · have htail := ih hinstruction
        unfold programResourceMagnitude at htail
        omega

private theorem dispatchProgramTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (store : Store) (pcValue : ℕ)
    (program : Program) (selector bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound) (hselector : selector ≤ pcValue)
    (hprogram : ∀ instruction ∈ program,
      instructionResourceMagnitude instruction ≤ bound) :
    dispatchProgramTime tapes store pcValue program selector ≤
      210000 * (program.length + 1) * (bound + 1) ^ 3 := by
  induction program generalizing selector with
  | nil =>
      have hselectorBits : selector.bits.length ≤ bound := by
        rw [Nat.size_eq_bits_len selector]
        have hsize := Nat.size_le_size hselector
        simpa [Nat.size_eq_bits_len] using! le_trans hsize (by
          simpa [Nat.size_eq_bits_len] using! hpc)
      have hreset : TM.resetBinaryWorkTime 1 selector.bits.length ≤
          2 * bound + 9 := by
        unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
        omega
      have hexecute := executeInstructionTime_le tapes .halt pcValue store bound
        hbound hstoreLength hentries hpc (by
          simpa [instructionResourceMagnitude] using! hbound)
      simp only [dispatchProgramTime, List.length_nil, Nat.zero_add]
      have hboundCube : bound ≤ (bound + 1) ^ 3 := by
        exact le_trans (by omega)
          (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
      have honeCube : 1 ≤ (bound + 1) ^ 3 := by
        exact le_trans (by omega) hboundCube
      omega
  | cons instruction rest ih =>
      have hinstruction := hprogram instruction (by simp)
      have hrest : ∀ current ∈ rest,
          instructionResourceMagnitude current ≤ bound := by
        intro current hcurrent
        exact hprogram current (by simp [hcurrent])
      have hexecute := executeInstructionTime_le tapes instruction pcValue store
        bound hbound hstoreLength hentries hpc hinstruction
      have hrecursive := ih (selector - 1) (Nat.sub_le selector 1 |>.trans hselector)
        hrest
      have hpred := TM.binaryPredTime_le (selector - 1)
      have hpredSize : (selector - 1 + 1).size ≤ bound + 1 := by
        have hvalue : selector - 1 + 1 ≤ pcValue + 1 := by omega
        have hsize := Nat.size_le_size hvalue
        have hpcSize : pcValue.size ≤ bound := by
          simpa [Nat.size_eq_bits_len] using! hpc
        have hpcSucc : (pcValue + 1).size ≤ bound + 1 := by
          rw [Nat.size_le]
          have hlt := Nat.lt_size_self pcValue
          have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hpcSize
          rw [pow_succ]
          omega
        exact le_trans hsize hpcSucc
      have hpred' : TM.binaryPredTime (selector - 1) ≤
          2 * (bound + 1) + 2 := le_trans hpred (by omega)
      simp only [dispatchProgramTime, TM.branchWorkBlankTime,
        List.length_cons]
      have hboundCube : bound ≤ (bound + 1) ^ 3 := by
        exact le_trans (by omega)
          (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
      have honeCube : 1 ≤ (bound + 1) ^ 3 := by
        exact le_trans (by omega) hboundCube
      have hmax : max (executeInstructionTime tapes instruction pcValue store)
          (TM.binaryPredTime (selector - 1) + 1 +
            dispatchProgramTime tapes store pcValue rest (selector - 1)) ≤
          200000 * (bound + 1) ^ 3 + 1 +
            210000 * (rest.length + 1) * (bound + 1) ^ 3 := by
        apply max_le
        · omega
        · omega
      nlinarith

private theorem programInstructionTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (pcValue : ℕ) (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound)
    (hprogram : programResourceMagnitude program ≤ bound) :
    programInstructionTime tapes program pcValue store ≤
      220000 * (program.length + 1) * (bound + 1) ^ 3 := by
  have hdispatch := dispatchProgramTime_le tapes store pcValue program pcValue
    bound hbound hstoreLength hentries hpc le_rfl
    (fun instruction hinstruction => le_trans
      (instructionResourceMagnitude_le_program instruction program hinstruction)
      hprogram)
  have hcopy := binaryCopyTime_le_width pcValue 0 bound
    (by simpa [Nat.size_eq_bits_len] using! hpc) (by simp)
  unfold programInstructionTime
  have hboundCube : bound ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega)
      (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega) hboundCube
  nlinarith

private theorem bits_length_le_of_value_le (value bound : ℕ)
    (hvalue : value ≤ bound) : value.bits.length ≤ bound := by
  rw [Nat.size_eq_bits_len value]
  exact le_trans (size_le_self value) hvalue

private theorem maxWidth_le_of_entries (store : Store) (bound : ℕ)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    maxWidth store ≤ bound := by
  induction store with
  | nil => simp [maxWidth]
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      have hrest : ∀ current ∈ rest,
          current.1.bits.length ≤ bound ∧ current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      simpa [maxWidth, bitlen, Nat.size_eq_bits_len] using!
        (max_le hentry.1 (max_le hentry.2 (ih hrest)))

private theorem snapshotWidth_le_of_bounds (pcValue : ℕ) (store : Store)
    (bound : ℕ) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound) :
    Snapshot.width { pc := pcValue, store := store } ≤ bound := by
  have hcount : store.length.bits.length ≤ bound :=
    bits_length_le_of_value_le store.length bound hstoreLength
  have hwidth := maxWidth_le_of_entries store bound hentries
  simpa [Snapshot.width, bitlen, Nat.size_eq_bits_len] using!
    (max_le hpc (max_le hcount hwidth))

private theorem entryBitlen_le_maxWidth (store : Store) (entry : Entry)
    (hentry : entry ∈ store) :
    max (bitlen entry.1) (bitlen entry.2) ≤ maxWidth store := by
  induction store with
  | nil => simp at hentry
  | cons head rest ih =>
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp only [maxWidth]
        exact max_le (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (ih hentry)
          (le_trans (le_max_right _ _) (le_max_right _ _))

private theorem snapshotEntryBits_le_width (snapshot : Snapshot)
    (entry : Entry) (hentry : entry ∈ snapshot.store) :
    entry.1.bits.length ≤ snapshot.width ∧
      entry.2.bits.length ≤ snapshot.width := by
  have hstore : maxWidth snapshot.store ≤ snapshot.width :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hmember : max (bitlen entry.1) (bitlen entry.2) ≤
      maxWidth snapshot.store :=
    entryBitlen_le_maxWidth snapshot.store entry hentry
  have hboth := le_trans hmember hstore
  simpa [bitlen, Nat.size_eq_bits_len] using!
    (show bitlen entry.1 ≤ snapshot.width ∧
        bitlen entry.2 ≤ snapshot.width from
      ⟨le_trans (le_max_left _ _) hboth,
        le_trans (le_max_right _ _) hboth⟩)

private theorem instructionLogCost_le (instruction : Instr)
    (pcValue : ℕ) (store : Store) (bound : ℕ)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hinstruction : instructionResourceMagnitude instruction ≤ bound) :
    instruction.logCost
        (Snapshot.decode { pc := pcValue, store := store }) ≤
      6 * (bound + 1) := by
  have hread (address : ℕ) :
      (RegisterStore.read store address).bits.length ≤ bound :=
    read_bits_length_le store address bound
      (fun entry hentry => (hentries entry hentry).2)
  cases instruction with
  | imm destination value =>
      simp only [instructionResourceMagnitude] at hinstruction
      simp only [Instr.logCost]
      have hvalue := bits_length_le_of_value_le value bound (by omega)
      simpa [bitlen, Nat.size_eq_bits_len] using!
        (show value.bits.length + 1 ≤ 6 * (bound + 1) by omega)
  | add destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hlhs := hread source₀
      have hrhs := hread source₁
      have hresult := binaryInstrResult_bits_length_le .add
        (RegisterStore.read store source₀)
        (RegisterStore.read store source₁) bound hlhs hrhs
      have hresult' : (RegisterStore.read store source₀ +
          RegisterStore.read store source₁).bits.length ≤ 2 * bound + 1 := by
        simpa [BinaryInstrOp.eval] using! hresult
      simpa [Instr.logCost, Snapshot.decode, RegisterStore.decode, bitlen,
        Nat.size_eq_bits_len, BinaryInstrOp.eval] using!
        (show (RegisterStore.read store source₀).bits.length +
            (RegisterStore.read store source₁).bits.length +
            (RegisterStore.read store source₀ +
              RegisterStore.read store source₁).bits.length + 1 ≤
            6 * (bound + 1) by omega)
  | sub destination source₀ source₁ =>
      have hlhs := hread source₀
      have hrhs := hread source₁
      simpa [Instr.logCost, Snapshot.decode, RegisterStore.decode, bitlen,
        Nat.size_eq_bits_len] using!
        (show (RegisterStore.read store source₀).bits.length +
            (RegisterStore.read store source₁).bits.length + 1 ≤
            6 * (bound + 1) by omega)
  | mul destination source₀ source₁ =>
      have hlhs := hread source₀
      have hrhs := hread source₁
      have hresult := binaryInstrResult_bits_length_le .mul
        (RegisterStore.read store source₀)
        (RegisterStore.read store source₁) bound hlhs hrhs
      have hresult' : (RegisterStore.read store source₀ *
          RegisterStore.read store source₁).bits.length ≤ 2 * bound + 1 := by
        simpa [BinaryInstrOp.eval] using! hresult
      simpa [Instr.logCost, Snapshot.decode, RegisterStore.decode, bitlen,
        Nat.size_eq_bits_len, BinaryInstrOp.eval] using!
        (show (RegisterStore.read store source₀).bits.length +
            (RegisterStore.read store source₁).bits.length +
            (RegisterStore.read store source₀ *
              RegisterStore.read store source₁).bits.length + 1 ≤
            6 * (bound + 1) by omega)
  | load destination addressRegister =>
      have haddress := hread addressRegister
      have hvalue := hread (RegisterStore.read store addressRegister)
      simpa [Instr.logCost, Snapshot.decode, RegisterStore.decode, bitlen,
        Nat.size_eq_bits_len] using!
        (show (RegisterStore.read store addressRegister).bits.length +
            (RegisterStore.read store
              (RegisterStore.read store addressRegister)).bits.length + 1 ≤
            6 * (bound + 1) by omega)
  | store addressRegister source =>
      have haddress := hread addressRegister
      have hvalue := hread source
      simpa [Instr.logCost, Snapshot.decode, RegisterStore.decode, bitlen,
        Nat.size_eq_bits_len] using!
        (show (RegisterStore.read store addressRegister).bits.length +
            (RegisterStore.read store source).bits.length + 1 ≤
            6 * (bound + 1) by omega)
  | jz source target =>
      have hvalue := hread source
      simpa [Instr.logCost, Snapshot.decode, RegisterStore.decode, bitlen,
        Nat.size_eq_bits_len] using!
        (show (RegisterStore.read store source).bits.length + 1 ≤
            6 * (bound + 1) by omega)
  | jmp target => simp only [Instr.logCost]; omega
  | halt => simp only [Instr.logCost]; omega

private theorem write_length_le (store : Store) (address value : ℕ) :
    (RegisterStore.write store address value).length ≤ store.length + 1 := by
  induction store with
  | nil =>
      by_cases hvalue : value = 0 <;>
        simp [RegisterStore.write, hvalue]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedValue⟩
      by_cases haddress : address = storedAddress
      · subst address
        by_cases hvalue : value = 0
        · simp [RegisterStore.write, hvalue]
          omega
        · simp [RegisterStore.write, hvalue]
      · simp only [RegisterStore.write, haddress, ↓reduceIte,
          List.length_cons]
        omega

private theorem instructionStoreBounds (instruction : Instr)
    (pcValue : ℕ) (store : Store) (bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound)
    (hinstruction : instructionResourceMagnitude instruction ≤ bound) :
    (instructionStore instruction pcValue store).length ≤ bound + 1 ∧
      ∀ entry ∈ instructionStore instruction pcValue store,
        entry.1.bits.length ≤ 6 * (bound + 1) ∧
          entry.2.bits.length ≤ 6 * (bound + 1) := by
  let snapshot : Snapshot := { pc := pcValue, store := store }
  let next := Snapshot.stepInstr instruction snapshot
  have hsnapshot : snapshot.width ≤ bound :=
    snapshotWidth_le_of_bounds pcValue store bound hstoreLength hentries hpc
  have hstatic := instructionStaticWidth_le_resourceMagnitude instruction
  have hcost := instructionLogCost_le instruction pcValue store bound hentries
    hinstruction
  have hnextWidth : next.width ≤ 6 * (bound + 1) := by
    exact le_trans (Snapshot.width_stepInstr_le instruction snapshot) (by
      unfold Snapshot.stepWidthBound
      exact max_le (by omega)
        (max_le (le_trans (le_trans hstatic hinstruction) (by omega)) hcost))
  have hnextLength : next.store.length ≤ bound + 1 := by
    cases instruction with
    | imm destination value =>
        exact le_trans (write_length_le store destination value) (by omega)
    | add destination source₀ source₁ =>
        exact le_trans (write_length_le store destination _) (by omega)
    | sub destination source₀ source₁ =>
        exact le_trans (write_length_le store destination _) (by omega)
    | mul destination source₀ source₁ =>
        exact le_trans (write_length_le store destination _) (by omega)
    | load destination addressRegister =>
        exact le_trans (write_length_le store destination _) (by omega)
    | store addressRegister source =>
        exact le_trans (write_length_le store _ _) (by omega)
    | jz source target =>
        simp only [next, snapshot, Snapshot.stepInstr]
        split <;> simp_all <;> omega
    | jmp target => simp [next, snapshot, Snapshot.stepInstr]; omega
    | halt => simp [next, snapshot, Snapshot.stepInstr]; omega
  constructor
  · simpa [next, snapshot, instructionStore] using! hnextLength
  · intro entry hentry
    have := snapshotEntryBits_le_width next entry (by
      simpa [next, snapshot, instructionStore] using! hentry)
    exact ⟨le_trans this.1 hnextWidth, le_trans this.2 hnextWidth⟩

private theorem instructionCleanupResetBits_le
    (instruction : Instr) (store : Store) (bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hinstruction : instructionResourceMagnitude instruction ≤ bound)
    (slot : Fin 7) :
    (instructionCleanupResetBits instruction store slot).length ≤
      6 * (bound + 1) ^ 2 := by
  have hread (address : ℕ) :
      (RegisterStore.read store address).bits.length ≤ bound :=
    read_bits_length_le store address bound
      (fun entry hentry => (hentries entry hentry).2)
  have hencoded := entriesEncode_length_le store bound hentries
  have hencodedWide : (store.flatMap Entry.encode).length ≤
      6 * (bound + 1) ^ 2 := by
    have hproduct := Nat.mul_le_mul hstoreLength (show 4 * bound + 2 ≤
      6 * (bound + 1) by omega)
    exact le_trans hencoded (le_trans hproduct (by nlinarith))
  have hencodedWide' : (store.map (fun entry => entry.encode.length)).sum ≤
      6 * (bound + 1) ^ 2 := by
    simpa only [List.length_flatMap] using! hencodedWide
  have hboundWide : bound ≤ 6 * (bound + 1) ^ 2 := by nlinarith
  have hstoreLengthBitsWide : store.length.bits.length ≤
      6 * (bound + 1) ^ 2 := by
    exact le_trans (by
      rw [Nat.size_eq_bits_len store.length]
      exact le_trans (size_le_self store.length) hstoreLength) hboundWide
  have hsmall (width : ℕ) (hwidth : width ≤ 2 * bound + 1) :
      width ≤ 6 * (bound + 1) ^ 2 := by nlinarith
  cases instruction with
  | imm destination value =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hdestination := bits_length_le_of_value_le destination bound (by omega)
      have hvalue := bits_length_le_of_value_le value bound (by omega)
      have hdestinationWide := le_trans hdestination hboundWide
      have hvalueWide := le_trans hvalue hboundWide
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;>
        (try split_ifs) <;> simp_all
  | add destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hdestination := bits_length_le_of_value_le destination bound (by omega)
      have hlhs := hread source₀
      have hrhs := hread source₁
      have hresult := binaryInstrResult_bits_length_le .add
        (RegisterStore.read store source₀) (RegisterStore.read store source₁)
        bound hlhs hrhs
      have hdestinationWide := le_trans hdestination hboundWide
      have hlhsWide := le_trans hlhs hboundWide
      have hrhsWide := le_trans hrhs hboundWide
      have hresultWide :
          (RegisterStore.read store source₀ +
            RegisterStore.read store source₁).bits.length ≤
            6 * (bound + 1) ^ 2 := by
        simpa [BinaryInstrOp.eval] using! hsmall _ hresult
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;>
        (try split_ifs) <;> simp_all
  | sub destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hdestination := bits_length_le_of_value_le destination bound (by omega)
      have hlhs := hread source₀
      have hrhs := hread source₁
      have hresult := binaryInstrResult_bits_length_le .sub
        (RegisterStore.read store source₀) (RegisterStore.read store source₁)
        bound hlhs hrhs
      have hdestinationWide := le_trans hdestination hboundWide
      have hlhsWide := le_trans hlhs hboundWide
      have hrhsWide := le_trans hrhs hboundWide
      have hresultWide :
          (RegisterStore.read store source₀ -
            RegisterStore.read store source₁).bits.length ≤
            6 * (bound + 1) ^ 2 := by
        simpa [BinaryInstrOp.eval] using! hsmall _ hresult
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;>
        (try split_ifs) <;> simp_all
  | mul destination source₀ source₁ =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hdestination := bits_length_le_of_value_le destination bound (by omega)
      have hlhs := hread source₀
      have hrhs := hread source₁
      have hresult := binaryInstrResult_bits_length_le .mul
        (RegisterStore.read store source₀) (RegisterStore.read store source₁)
        bound hlhs hrhs
      have hdestinationWide := le_trans hdestination hboundWide
      have hlhsWide := le_trans hlhs hboundWide
      have hrhsWide := le_trans hrhs hboundWide
      have hresultWide :
          (RegisterStore.read store source₀ *
            RegisterStore.read store source₁).bits.length ≤
            6 * (bound + 1) ^ 2 := by
        simpa [BinaryInstrOp.eval] using! hsmall _ hresult
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;>
        (try split_ifs) <;> simp_all
  | load destination addressRegister =>
      simp only [instructionResourceMagnitude] at hinstruction
      have hdestination := bits_length_le_of_value_le destination bound (by omega)
      have haddress := hread addressRegister
      have hvalue := hread (RegisterStore.read store addressRegister)
      have hdestinationWide := le_trans hdestination hboundWide
      have haddressWide := le_trans haddress hboundWide
      have hvalueWide := le_trans hvalue hboundWide
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;>
        (try split_ifs) <;> simp_all
  | store addressRegister source =>
      simp only [instructionResourceMagnitude] at hinstruction
      have haddress := hread addressRegister
      have hvalue := hread source
      have haddressWide := le_trans haddress hboundWide
      have hvalueWide := le_trans hvalue hboundWide
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;>
        (try split_ifs) <;> simp_all
  | jz source target =>
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;> try nlinarith
  | jmp target =>
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;> try nlinarith
  | halt =>
      fin_cases slot <;>
        simp [instructionCleanupResetBits, instructionCleanupValue,
          instructionRemainingValue] <;> try nlinarith

private theorem instructionCleanupTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (sourceHeadBound bound : ℕ)
    (hbound : 1 ≤ bound) (hsourceHead : 1 ≤ sourceHeadBound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound)
    (hinstruction : instructionResourceMagnitude instruction ≤ bound) :
    instructionCleanupTime tapes instruction pcValue store sourceHeadBound ≤
      1000 * (sourceHeadBound + (bound + 1) ^ 2 + 1) := by
  let nextStore := instructionStore instruction pcValue store
  let nextBits := nextStore.flatMap Entry.encode
  have hnext := instructionStoreBounds instruction pcValue store bound hbound
    hstoreLength hentries hpc hinstruction
  have hnextLength : nextStore.length ≤ bound + 1 := by
    simpa only [nextStore] using! hnext.1
  have hnextEntries : ∀ entry ∈ nextStore,
      entry.1.bits.length ≤ 6 * (bound + 1) ∧
        entry.2.bits.length ≤ 6 * (bound + 1) := by
    simpa only [nextStore] using! hnext.2
  have hnextEncoded := entriesEncode_length_le nextStore (6 * (bound + 1))
    hnextEntries
  have hnextBits : nextBits.length ≤ 26 * (bound + 1) ^ 2 := by
    dsimp only [nextBits]
    exact le_trans hnextEncoded (by
      have hfactor : 4 * (6 * (bound + 1)) + 2 ≤ 26 * (bound + 1) := by
        omega
      have hproduct := Nat.mul_le_mul hnextLength hfactor
      nlinarith)
  have hreset := TM.resetBinaryWorkManyTime_le
    (instructionCleanupResetTargets tapes)
    (instructionCleanupResetBitsAt tapes instruction store)
    (instructionCleanupResetHeadBoundAt tapes sourceHeadBound)
    sourceHeadBound (6 * (bound + 1) ^ 2)
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      rw [instructionCleanupResetHeadBoundAt,
        (instructionCleanupResetTape_injective tapes).extend_apply]
      fin_cases slot <;>
        simp [instructionCleanupResetHeadBound, hsourceHead])
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      rw [instructionCleanupResetBitsAt,
        (instructionCleanupResetTape_injective tapes).extend_apply]
      exact instructionCleanupResetBits_le instruction store bound hbound
        hstoreLength hentries hinstruction slot)
  have htargets : (instructionCleanupResetTargets tapes).length = 7 := by
    simp [instructionCleanupResetTargets]
  rw [htargets] at hreset
  have hcopy := TM.binaryCopyTime_le nextStore.length 0
  have hcopy' : TM.binaryCopyTime nextStore.length 0 ≤
      3 * (bound + 1) + 20 := by
    exact le_trans hcopy (by
      have hsize := le_trans (size_le_self nextStore.length) hnextLength
      simp only [Nat.size_zero]
      omega)
  have hresetNext : TM.resetBinaryWorkTime (nextBits.length + 1)
      nextBits.length ≤ 3 * (26 * (bound + 1) ^ 2) + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    omega
  unfold instructionCleanupTime
  dsimp only [nextStore, nextBits] at hnextBits hcopy' hresetNext ⊢
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  nlinarith

private theorem selectedInstructionResourceMagnitude_le
    (program : Program) (pcValue : ℕ) :
    instructionResourceMagnitude (selectedInstruction program pcValue) ≤
      programResourceMagnitude program := by
  induction program generalizing pcValue with
  | nil => simp [selectedInstruction, instructionResourceMagnitude,
      programResourceMagnitude]
  | cons instruction rest ih =>
      cases pcValue with
      | zero =>
          simp only [selectedInstruction, programResourceMagnitude,
            List.length_cons, List.map_cons, List.sum_cons]
          omega
      | succ pcValue =>
          have htail := ih pcValue
          simp only [selectedInstruction, programResourceMagnitude,
            List.length_cons, List.map_cons, List.sum_cons]
          unfold programResourceMagnitude at htail
          omega

private theorem programStepTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (pcValue : ℕ) (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hpc : pcValue.bits.length ≤ bound)
    (hprogram : programResourceMagnitude program ≤ bound) :
    programStepTime tapes program pcValue store ≤
      300000000 * (program.length + 1) * (bound + 1) ^ 3 := by
  let instruction := selectedInstruction program pcValue
  let instructionTime := programInstructionTime tapes program pcValue store
  have hinstruction : instructionResourceMagnitude instruction ≤ bound :=
    le_trans (selectedInstructionResourceMagnitude_le program pcValue) hprogram
  have hinstructionTime : instructionTime ≤
      220000 * (program.length + 1) * (bound + 1) ^ 3 := by
    exact programInstructionTime_le tapes program pcValue store bound hbound
      hstoreLength hentries hpc hprogram
  have hcleanup := instructionCleanupTime_le tapes instruction pcValue store
    (1 + instructionTime) bound hbound (by omega) hstoreLength hentries hpc
    hinstruction
  have hsqCube : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := by
    calc
      (bound + 1) ^ 2 = (bound + 1) ^ 2 * 1 := by simp
      _ ≤ (bound + 1) ^ 2 * (bound + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (bound + 1) ^ 3 := by ring
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega : 1 ≤ bound + 1) (Nat.le_self_pow
      (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  unfold programStepTime programStepSourceHeadBound
  dsimp only [instruction, instructionTime] at hinstructionTime hcleanup ⊢
  nlinarith

private theorem dispatchHaltTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (selector bound : ℕ) (hbound : 1 ≤ bound)
    (hselector : selector.bits.length ≤ bound) :
    dispatchHaltTime tapes program selector ≤
      20 * (program.length + 1) * (bound + 1) := by
  induction program generalizing selector with
  | nil =>
      have hreset : TM.resetBinaryWorkTime 1 selector.bits.length ≤
          2 * bound + 9 := by
        unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
        omega
      simp only [dispatchHaltTime, List.length_nil, Nat.zero_add,
        Nat.mul_one]
      omega
  | cons instruction rest ih =>
      have hselectorPred : (selector - 1).bits.length ≤ bound := by
        simpa only [Nat.size_eq_bits_len] using!
          (le_trans (Nat.size_le_size (Nat.sub_le selector 1)) (by
            simpa [Nat.size_eq_bits_len] using! hselector))
      have htail := ih (selector - 1) hselectorPred
      have hpred := TM.binaryPredTime_le (selector - 1)
      have hpredSize : (selector - 1 + 1).size ≤ bound + 1 := by
        have hvalue : selector - 1 + 1 ≤ selector + 1 := by omega
        have hsize := Nat.size_le_size hvalue
        have hselectorSize : selector.size ≤ bound := by
          simpa [Nat.size_eq_bits_len] using! hselector
        have hsucc : (selector + 1).size ≤ bound + 1 := by
          rw [Nat.size_le]
          have hlt := Nat.lt_size_self selector
          have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hselectorSize
          rw [pow_succ]
          omega
        exact le_trans hsize hsucc
      have hpred' : TM.binaryPredTime (selector - 1) ≤
          2 * (bound + 1) + 2 := le_trans hpred (by omega)
      simp only [dispatchHaltTime, TM.branchWorkBlankTime, List.length_cons]
      have hmax : max 1
          (TM.binaryPredTime (selector - 1) + 1 +
            dispatchHaltTime tapes rest (selector - 1)) ≤
          2 * (bound + 1) + 3 +
            20 * (rest.length + 1) * (bound + 1) := by
        apply max_le <;> omega
      nlinarith

private theorem programHaltTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (pcValue bound : ℕ) (hbound : 1 ≤ bound)
    (hpc : pcValue.bits.length ≤ bound) :
    programHaltTime tapes program pcValue ≤
      40 * (program.length + 1) * (bound + 1) := by
  have hdispatch := dispatchHaltTime_le tapes program pcValue bound hbound hpc
  have hcopy := binaryCopyTime_le_width pcValue 0 bound
    (by simpa [Nat.size_eq_bits_len] using! hpc) (by simp)
  unfold programHaltTime
  nlinarith

private theorem programOutputTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (store : Store) (bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    programOutputTime tapes store ≤ 22000 * (bound + 1) ^ 3 := by
  have hlookup := entryLookupStaticTime_le tapes.lifted.data.lhsLookup store
    0 bound hbound hstoreLength (by omega) hentries
  unfold programOutputTime
  have honeCube : 1 ≤ (bound + 1) ^ 3 := by
    exact le_trans (by omega : 1 ≤ bound + 1) (Nat.le_self_pow
      (by decide : (3 : ℕ) ≠ 0) (bound + 1))
  omega

private def SnapshotBounded (snapshot : Snapshot) (bound : ℕ) : Prop :=
  snapshot.store.length ≤ bound ∧
    (∀ entry ∈ snapshot.store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) ∧
    snapshot.pc.bits.length ≤ bound

private theorem snapshotSteps_eq_run (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) :
    snapshotSteps program fuel snapshot = snapshot.run program fuel := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      rw [snapshotSteps, ih]
      by_cases hhalted : snapshot.Halted program
      · rw [snapshot_step_eq_self_of_halted_internal program snapshot hhalted,
          snapshot_run_halted_internal program snapshot hhalted]
        simp [Snapshot.run, hhalted]
      · simp [Snapshot.run, hhalted]

private theorem programLoopIterationTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (snapshot : Snapshot) (bound : ℕ) (hbound : 1 ≤ bound)
    (hcurrent : SnapshotBounded snapshot bound)
    (hnext : SnapshotBounded (snapshot.step program) bound)
    (hprogram : programResourceMagnitude program ≤ bound) :
    programLoopIterationTime tapes program snapshot ≤
      301000000 * (program.length + 1) * (bound + 1) ^ 3 := by
  have hstep := programStepTime_le tapes program snapshot.pc snapshot.store
    bound hbound hcurrent.1 hcurrent.2.1 hcurrent.2.2 hprogram
  have hhalt := programHaltTime_le tapes program (snapshot.step program).pc
    bound hbound hnext.2.2
  unfold programLoopIterationTime
  have hlinearCube : bound + 1 ≤ (bound + 1) ^ 3 := by
    exact Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (bound + 1)
  have honeCube : 1 ≤ (bound + 1) ^ 3 :=
    le_trans (by omega) hlinearCube
  nlinarith

private theorem programLoopTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (fuel : ℕ) (snapshot : Snapshot) (bound : ℕ)
    (hbound : 1 ≤ bound)
    (hall : ∀ k, k ≤ fuel →
      SnapshotBounded (snapshotSteps program k snapshot) bound)
    (hprogram : programResourceMagnitude program ≤ bound) :
    programLoopTime tapes program fuel snapshot ≤
      fuel * (301000000 * (program.length + 1) * (bound + 1) ^ 3) := by
  induction fuel generalizing snapshot with
  | zero => simp [programLoopTime]
  | succ fuel ih =>
      have hcurrent : SnapshotBounded snapshot bound := by
        simpa [snapshotSteps] using! hall 0 (by omega)
      have hnext : SnapshotBounded (snapshot.step program) bound := by
        simpa [snapshotSteps] using! hall 1 (by omega)
      have hiteration := programLoopIterationTime_le tapes program snapshot
        bound hbound hcurrent hnext hprogram
      have htail := ih (snapshot.step program) (by
        intro k hk
        simpa [snapshotSteps] using! hall (k + 1) (by omega))
      simp only [programLoopTime]
      rw [Nat.succ_mul]
      omega

private theorem write_entries_le (store : Store) (address value bound : ℕ)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (haddress : address.bits.length ≤ bound)
    (hvalue : value.bits.length ≤ bound) :
    ∀ entry ∈ RegisterStore.write store address value,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound := by
  intro entry hentry
  induction store with
  | nil =>
      by_cases hvalueZero : value = 0
      · simp [RegisterStore.write, hvalueZero] at hentry
      · simp [RegisterStore.write, hvalueZero] at hentry
        subst entry
        exact ⟨haddress, hvalue⟩
  | cons head rest ih =>
      rcases head with ⟨storedAddress, storedValue⟩
      have hhead := hentries (storedAddress, storedValue) (by simp)
      have hrest : ∀ current ∈ rest,
          current.1.bits.length ≤ bound ∧
            current.2.bits.length ≤ bound := by
        intro current hcurrent
        exact hentries current (by simp [hcurrent])
      by_cases haddressEq : address = storedAddress
      · subst address
        by_cases hvalueZero : value = 0
        · simp [RegisterStore.write, hvalueZero] at hentry
          exact hrest entry hentry
        · simp [RegisterStore.write, hvalueZero] at hentry
          rcases hentry with rfl | hentry
          · exact ⟨haddress, hvalue⟩
          · exact hrest entry hentry
      · simp only [RegisterStore.write, haddressEq, ↓reduceIte,
          List.mem_cons] at hentry
        rcases hentry with rfl | hentry
        · exact hhead
        · exact ih hrest hentry

private theorem inputBitStoreFrom_bounds (address : ℕ) (input : List Bool)
    (bound : ℕ) (hsum : address + input.length ≤ bound) :
    (inputBitStoreFrom address input).length ≤ input.length ∧
      ∀ entry ∈ inputBitStoreFrom address input,
        entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound := by
  induction input generalizing address with
  | nil => simp [inputBitStoreFrom]
  | cons bit rest ih =>
      have htail := ih (address + 1) (by simp only [List.length_cons] at hsum; omega)
      have haddress : address.bits.length ≤ bound :=
        bits_length_le_of_value_le address bound (by
          simp only [List.length_cons] at hsum
          omega)
      have hone : (1 : ℕ).bits.length ≤ bound := by
        simpa using! (show 1 ≤ bound by
          simp only [List.length_cons] at hsum
          omega)
      cases bit with
      | false =>
          change (inputBitStoreFrom (address + 1) rest).length ≤
              rest.length + 1 ∧
            ∀ entry ∈ inputBitStoreFrom (address + 1) rest,
              entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound
          exact ⟨by omega, htail.2⟩
      | true =>
          change ((address, 1) :: inputBitStoreFrom (address + 1) rest).length ≤
              rest.length + 1 ∧
            ∀ entry ∈ (address, 1) :: inputBitStoreFrom (address + 1) rest,
              entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound
          constructor
          · simp only [List.length_cons]
            omega
          · intro entry hentry
            simp only [List.mem_cons] at hentry
            rcases hentry with rfl | hentry
            · exact ⟨haddress, hone⟩
            · exact htail.2 entry hentry

private theorem programInitialSnapshot_bounded (input : List Bool) :
    SnapshotBounded (programInitialSnapshot input) (input.length + 1) := by
  have hprefix := inputBitStoreFrom_bounds 1 input (input.length + 1) (by omega)
  have hlength := write_length_le (inputBitStoreFrom 1 input) 0 input.length
  have hentries := write_entries_le (inputBitStoreFrom 1 input) 0 input.length
    (input.length + 1) hprefix.2 (by simp) (by
      exact bits_length_le_of_value_le input.length (input.length + 1) (by omega))
  refine ⟨?_, ?_, by simp [programInitialSnapshot]⟩
  · change (RegisterStore.write (inputBitStoreFrom 1 input) 0
        input.length).length ≤ input.length + 1
    omega
  · simpa [programInitialSnapshot, programInitialStore] using! hentries

private theorem rewindEntryEncodeRestoreTime_bound (entry : Entry) (bound : ℕ)
    (hbound : 1 ≤ bound) (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound) :
    rewindEntryEncodeRestoreTime entry ≤ 30 * (bound + 1) := by
  have hrewind := rewindEntryEncodeTime_le entry 1 1 bound haddress hvalue
    hbound hbound
  unfold Machine.rewindEntryEncodeRestoreTime
  omega

private theorem inputTrueCount_le_length (input : List Bool) :
    inputTrueCount input ≤ input.length := by
  induction input with
  | nil => simp [inputTrueCount]
  | cons bit rest ih =>
      cases bit <;> simp [inputTrueCount] <;> omega

private theorem initialInputLoopTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (address count : ℕ)
    (input : List Bool) (bound : ℕ) (hbound : 1 ≤ bound)
    (haddress : address + input.length ≤ bound)
    (hcount : count + input.length ≤ bound) :
    initialInputLoopTime tapes address count input ≤
      (input.length + 1) * (100 * (bound + 1) ^ 2) := by
  induction input generalizing address count with
  | nil =>
      simp only [initialInputLoopTime, List.length_nil, Nat.zero_add,
        Nat.one_mul]
      nlinarith
  | cons bit rest ih =>
      have haddressValue : address.bits.length ≤ bound :=
        bits_length_le_of_value_le address bound (by
          simp only [List.length_cons] at haddress
          omega)
      have hone : (1 : ℕ).bits.length ≤ bound := by simp [hbound]
      have hrewind := rewindEntryEncodeRestoreTime_bound (address, 1) bound
        hbound haddressValue hone
      have hsuccAddress := binarySuccTime_le_width address bound (by
        simpa [Nat.size_eq_bits_len] using! haddressValue)
      have hsuccCount := binarySuccTime_le_width count bound (by
        exact le_trans (size_le_self count) (by omega))
      cases bit with
      | false =>
          have htail := ih (address + 1) count (by
            simp only [List.length_cons] at haddress ⊢
            omega) (by
              simp only [List.length_cons] at hcount
              omega)
          simp [initialInputLoopTime]
          have hbody : 1 + TM.binarySuccTime address + 1 ≤
              100 * (bound + 1) ^ 2 := by nlinarith
          nlinarith
      | true =>
          have htail := ih (address + 1) (count + 1) (by
            simp only [List.length_cons] at haddress ⊢
            omega) (by
              simp only [List.length_cons] at hcount
              omega)
          simp [initialInputLoopTime]
          have hbody : 1 +
              (rewindEntryEncodeRestoreTime (address, 1) + 1 +
                TM.binarySuccTime count + 1 + TM.binarySuccTime address) + 1 ≤
              100 * (bound + 1) ^ 2 := by nlinarith
          nlinarith

private theorem initialLengthTime_le (length count : ℕ)
    (hcount : count ≤ length) :
    initialLengthTime length count ≤ 100 * (length + 2) ^ 2 := by
  have hbound : 1 ≤ length + 1 := by omega
  have hlength : length.bits.length ≤ length + 1 :=
    bits_length_le_of_value_le length (length + 1) (by omega)
  have hzero : (0 : ℕ).bits.length ≤ length + 1 := by simp
  have hrewind := rewindEntryEncodeRestoreTime_bound (0, length)
    (length + 1) hbound hzero hlength
  have hsucc := binarySuccTime_le_width count (length + 1) (by
    exact le_trans (size_le_self count) (by omega))
  unfold initialLengthTime
  split <;> nlinarith

private theorem initialCleanupBits_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (length bound : ℕ)
    (hlength : length.bits.length ≤ bound) (hbound : 1 ≤ bound)
    (i : Fin (m + 1)) :
    (initialCleanupBits tapes length i).length ≤ bound := by
  unfold initialCleanupBits
  split
  · exact hlength
  · split
    · simpa using! hbound
    · simp

private theorem initialAbiInstallTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (store : Store) (length bound : ℕ)
    (hbound : 1 ≤ bound) (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hlength : length.bits.length ≤ bound) :
    initialAbiInstallTime tapes store length ≤ 100 * (bound + 1) ^ 2 := by
  let encoded := store.flatMap Entry.encode
  have hencodedBase := entriesEncode_length_le store bound hentries
  have hencoded : encoded.length ≤ 6 * (bound + 1) ^ 2 := by
    dsimp only [encoded]
    have hfactor : 4 * bound + 2 ≤ 6 * (bound + 1) := by omega
    have hproduct := Nat.mul_le_mul hstoreLength hfactor
    exact le_trans hencodedBase (by nlinarith)
  have hcopy := binaryCopyTime_le_width store.length 0 bound
    (le_trans (size_le_self store.length) hstoreLength) (by simp)
  have hresetEncoded : TM.resetBinaryWorkTime (encoded.length + 1)
      encoded.length ≤ 3 * (6 * (bound + 1) ^ 2) + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    omega
  have hresetMany := TM.resetBinaryWorkManyTime_le
    (initialCleanupTargets tapes) (initialCleanupBits tapes length)
    (fun _ => 1) 1 bound (fun _ _ => le_rfl)
    (fun i _ => initialCleanupBits_le tapes length bound hlength hbound i)
  have htargets : (initialCleanupTargets tapes).length = 2 := by
    simp [initialCleanupTargets]
  rw [htargets] at hresetMany
  unfold initialAbiInstallTime
  dsimp only [encoded] at hencoded hresetEncoded ⊢
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  nlinarith

private theorem programInitTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (input : List Bool) :
    programInitTime tapes input ≤ 1000 * (input.length + 2) ^ 3 := by
  let bound := input.length + 1
  have hbound : 1 ≤ bound := by simp [bound]
  have hloop := initialInputLoopTime_le tapes 1 0 input bound hbound
    (by dsimp only [bound]; omega) (by dsimp only [bound]; omega)
  have htrueCount := inputTrueCount_le_length input
  have hlengthTime := initialLengthTime_le input.length (inputTrueCount input)
    htrueCount
  have hinitial := programInitialSnapshot_bounded input
  have hlengthBits : input.length.bits.length ≤ bound :=
    bits_length_le_of_value_le input.length bound (by simp [bound])
  have habi := initialAbiInstallTime_le tapes (programInitialStore input)
    input.length bound hbound hinitial.1 hinitial.2.1 hlengthBits
  have hpred := TM.binaryPredTime_le input.length
  have hpred' : TM.binaryPredTime input.length ≤
      2 * (input.length + 1) + 2 := by
    exact le_trans hpred (by
      have hsize := size_le_self (input.length + 1)
      omega)
  have hsuccZero := TM.binarySuccTime_le 0
  have hsuccZero' : TM.binarySuccTime 0 ≤ 2 := by
    simpa using! hsuccZero
  unfold programInitTime
  dsimp only [bound] at hloop habi hlengthBits hbound ⊢
  have hsqCube : (input.length + 2) ^ 2 ≤
      (input.length + 2) ^ 3 := by
    calc
      (input.length + 2) ^ 2 = (input.length + 2) ^ 2 * 1 := by simp
      _ ≤ (input.length + 2) ^ 2 * (input.length + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (input.length + 2) ^ 3 := by ring
  have honeCube : 1 ≤ (input.length + 2) ^ 3 := by nlinarith
  have hloopCube : initialInputLoopTime tapes 1 0 input ≤
      100 * (input.length + 2) ^ 3 := by
    calc
      initialInputLoopTime tapes 1 0 input ≤
          (input.length + 1) * (100 * (input.length + 2) ^ 2) := by
        simpa only [Nat.add_assoc] using! hloop
      _ ≤ (input.length + 2) * (100 * (input.length + 2) ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 100 * (input.length + 2) ^ 3 := by ring
  have habi' : initialAbiInstallTime tapes (programInitialStore input)
      input.length ≤ 100 * (input.length + 2) ^ 2 := by
    simpa only [Nat.add_assoc] using! habi
  nlinarith

theorem programDecisionTime_le_envelope_internal {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input)))
    (hfuel : fuel ≤
      RAM.logTimeUpto program fuel (RAM.initCfg input)) :
    programDecisionTime tapes program input fuel ≤
      programDecisionEnvelope program input.length
        (RAM.logTimeUpto program fuel (RAM.initCfg input)) := by
  let initial := programInitialSnapshot input
  let cost := RAM.logTimeUpto program fuel (RAM.initCfg input)
  let scale := programDecisionScale program input.length cost
  let magnitude := programResourceMagnitude program
  have hmagnitude : 1 ≤ magnitude := by
    exact programResourceMagnitude_pos_internal program
  have hprogramLength : program.length ≤ magnitude := by
    exact program_length_le_resourceMagnitude_internal program
  have hstatic : programStaticWidth program ≤ magnitude := by
    exact programStaticWidth_le_resourceMagnitude_internal program
  have hscale : 1 ≤ scale := by
    exact programDecisionScale_pos_internal program input.length cost
  have hinitial := programInitialSnapshot_bounded input
  have hinitialRep : initial.Represents (RAM.initCfg input) := by
    simpa only [initial] using! programInitialSnapshot_represents_internal input
  have hinitialWidth : initial.width ≤ input.length + 1 := by
    exact snapshotWidth_le_of_bounds initial.pc initial.store
      (input.length + 1) hinitial.1 hinitial.2.1 hinitial.2.2
  have hhaltedInitial : RAM.Halted program
      (RAM.run program fuel initial.decode) := by
    rw [hinitialRep.2]
    exact hhalted
  have hcostSucc : RAM.logTimeUpto program (fuel + 1) initial.decode = cost := by
    have hsame := RAM.logTimeUpto_eq_of_halted_le program
      (Nat.le_succ fuel) hhaltedInitial
    calc
      RAM.logTimeUpto program (fuel + 1) initial.decode =
          RAM.logTimeUpto program fuel initial.decode := by
        simpa only [Nat.succ_eq_add_one] using! hsame
      _ = cost := by rw [hinitialRep.2]
  have hcanonical : Canonical initial.store := hinitialRep.1
  have hall : ∀ k, k ≤ fuel + 1 →
      SnapshotBounded (snapshotSteps program k initial) scale := by
    intro k hk
    let current := initial.run program k
    have hlog := RAM.logTimeUpto_mono program (c := initial.decode) hk
    rw [hcostSucc] at hlog
    have hunit := RAM.unitTimeUpto_le_logTimeUpto program k initial.decode
    have hunitCost : RAM.unitTimeUpto program k initial.decode ≤ cost :=
      le_trans hunit hlog
    have hlength := Snapshot.length_run_le_internal program k initial hcanonical
    have hwidth := Snapshot.width_run_le_internal program k initial hcanonical
    have hstaticMagnitude : programStaticWidth program + 1 ≤ magnitude + 1 :=
      Nat.add_le_add_right hstatic 1
    have hwidthProduct :
        RAM.unitTimeUpto program k initial.decode *
            (programStaticWidth program + 1) ≤
          cost * (magnitude + 1) :=
      Nat.mul_le_mul hunitCost hstaticMagnitude
    have hlengthScale : current.store.length ≤ scale := by
      have hinitialLength : initial.store.length ≤ input.length + 1 := by
        simpa only [initial] using! hinitial.1
      have hlengthBase : current.store.length ≤
          input.length + 1 + RAM.unitTimeUpto program k initial.decode := by
        dsimp only [current]
        exact le_trans hlength
          (Nat.add_le_add_right hinitialLength _)
      have hcostFactor : cost ≤ cost * (magnitude + 2) := by
        calc
          cost = cost * 1 := by simp
          _ ≤ cost * (magnitude + 2) :=
            Nat.mul_le_mul_left cost (by omega)
      change current.store.length ≤
        input.length + cost * (magnitude + 2) + magnitude + 3
      omega
    have hwidthScale : current.width ≤ scale := by
      have hwidthBase : current.width ≤
          input.length + 1 + cost * (magnitude + 1) + cost := by
        dsimp only [current]
        exact le_trans hwidth (by omega)
      have hcostSplit : cost * (magnitude + 1) + cost =
          cost * (magnitude + 2) := by ring
      calc
        current.width ≤ input.length + 1 +
            (cost * (magnitude + 1) + cost) := by omega
        _ = input.length + 1 + cost * (magnitude + 2) := by rw [hcostSplit]
        _ ≤ scale := by
          change input.length + 1 + cost * (magnitude + 2) ≤
            input.length + cost * (magnitude + 2) + magnitude + 3
          omega
    have hentriesScale : ∀ entry ∈ current.store,
        entry.1.bits.length ≤ scale ∧
          entry.2.bits.length ≤ scale := by
      intro entry hentry
      have hentryWidth := snapshotEntryBits_le_width current entry hentry
      exact ⟨le_trans hentryWidth.1 hwidthScale,
        le_trans hentryWidth.2 hwidthScale⟩
    have hpcWidth : current.pc.bits.length ≤ current.width := by
      have hpc : bitlen current.pc ≤ current.width :=
        le_max_left (bitlen current.pc)
          (max (bitlen current.store.length) (maxWidth current.store))
      unfold bitlen at hpc
      rw [← Nat.size_eq_bits_len] at hpc
      exact hpc
    rw [snapshotSteps_eq_run]
    exact ⟨hlengthScale, hentriesScale, le_trans hpcWidth hwidthScale⟩
  have hprogramScale : magnitude ≤ scale := by
    unfold scale programDecisionScale
    omega
  have hloop := programLoopTime_le tapes program (fuel + 1) initial scale
    hscale hall hprogramScale
  have hfinalBound : SnapshotBounded (initial.run program fuel) scale := by
    rw [← snapshotSteps_eq_run]
    exact hall fuel (by omega)
  have houtput := programOutputTime_le tapes (initial.run program fuel).store
    scale hscale hfinalBound.1 hfinalBound.2.1
  have hinit := programInitTime_le tapes input
  have hinputScale : input.length + 2 ≤ scale + 1 := by
    unfold scale programDecisionScale
    omega
  have hinit' : programInitTime tapes input ≤
      1000 * (scale + 1) ^ 3 :=
    le_trans hinit (Nat.mul_le_mul_left 1000
      (Nat.pow_le_pow_left hinputScale 3))
  have hfuelScale : fuel + 1 ≤ scale + 1 := by
    have hfuelCost : fuel ≤ cost := by simpa only [cost] using! hfuel
    have hcostScale : cost ≤ scale := by
      change cost ≤ input.length + cost * (magnitude + 2) + magnitude + 3
      have hfactor : cost * 1 ≤ cost * (magnitude + 2) :=
        Nat.mul_le_mul_left cost (by omega)
      omega
    omega
  have hlengthMagnitude : program.length + 1 ≤ 2 * magnitude := by omega
  have hloopProduct : (fuel + 1) * (program.length + 1) ≤
      (scale + 1) * (2 * magnitude) :=
    Nat.mul_le_mul hfuelScale hlengthMagnitude
  have hloop' : programLoopTime tapes program (fuel + 1) initial ≤
      602000000 * magnitude * (scale + 1) ^ 4 := by
    calc
      programLoopTime tapes program (fuel + 1) initial ≤
          (fuel + 1) *
            (301000000 * (program.length + 1) * (scale + 1) ^ 3) := hloop
      _ = 301000000 * ((fuel + 1) * (program.length + 1)) *
          (scale + 1) ^ 3 := by ring
      _ ≤ 301000000 * ((scale + 1) * (2 * magnitude)) *
          (scale + 1) ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 301000000 hloopProduct)
      _ = 602000000 * magnitude * (scale + 1) ^ 4 := by ring
  have hcubeFourth : (scale + 1) ^ 3 ≤ (scale + 1) ^ 4 := by
    calc
      (scale + 1) ^ 3 = (scale + 1) ^ 3 * 1 := by simp
      _ ≤ (scale + 1) ^ 3 * (scale + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (scale + 1) ^ 4 := by ring
  have hinitEnvelope : programInitTime tapes input ≤
      1000 * magnitude * (scale + 1) ^ 4 := by
    exact le_trans hinit' (by
      have hmultiply := Nat.mul_le_mul hmagnitude hcubeFourth
      nlinarith)
  have houtputEnvelope : programOutputTime tapes
      (initial.run program fuel).store ≤
      22000 * magnitude * (scale + 1) ^ 4 := by
    exact le_trans houtput (by
      have hmultiply := Nat.mul_le_mul hmagnitude hcubeFourth
      nlinarith)
  let envelopeUnit := magnitude * (scale + 1) ^ 4
  have hunitPos : 1 ≤ envelopeUnit := by
    dsimp only [envelopeUnit]
    exact Nat.mul_pos hmagnitude (pow_pos (by omega) 4)
  have hinitUnit : programInitTime tapes input ≤ 1000 * envelopeUnit := by
    simpa only [envelopeUnit, Nat.mul_assoc] using! hinitEnvelope
  have hloopUnit : programLoopTime tapes program (fuel + 1) initial ≤
      602000000 * envelopeUnit := by
    simpa only [envelopeUnit, Nat.mul_assoc] using! hloop'
  have houtputUnit : programOutputTime tapes
      (initial.run program fuel).store ≤ 22000 * envelopeUnit := by
    simpa only [envelopeUnit, Nat.mul_assoc] using! houtputEnvelope
  have hloopUnit' : programLoopTime tapes program (fuel + 1)
      (programInitialSnapshot input) ≤ 602000000 * envelopeUnit := by
    simpa only [initial] using! hloopUnit
  have houtputUnit' : programOutputTime tapes
      ((programInitialSnapshot input).run program fuel).store ≤
      22000 * envelopeUnit := by
    simpa only [initial] using! houtputUnit
  have htotal : programDecisionTime tapes program input fuel ≤
      602023002 * envelopeUnit := by
    unfold programDecisionTime
    dsimp only
    omega
  apply le_trans htotal
  unfold programDecisionEnvelope
  change 602023002 * envelopeUnit ≤
    1000000000 * magnitude * (scale + 1) ^ 4
  simpa only [envelopeUnit, Nat.mul_assoc] using!
    (Nat.mul_le_mul_right envelopeUnit
      (show 602023002 ≤ 1000000000 by decide))

theorem programDecisionEnvelope_mono_cost_internal (program : Program)
    (inputLength left right : ℕ) (hle : left ≤ right) :
    programDecisionEnvelope program inputLength left ≤
      programDecisionEnvelope program inputLength right := by
  have hscale : programDecisionScale program inputLength left ≤
      programDecisionScale program inputLength right := by
    unfold programDecisionScale
    exact Nat.add_le_add_right
      (Nat.add_le_add_left
        (Nat.mul_le_mul_right (programResourceMagnitude program + 2) hle)
        inputLength)
      (programResourceMagnitude program + 3)
  unfold programDecisionEnvelope
  exact Nat.mul_le_mul_left
    (1000000000 * programResourceMagnitude program)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hscale 1) 4)

end Machine

end RegisterStore

end RAM

end Complexity

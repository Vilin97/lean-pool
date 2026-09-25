/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBoundsDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Bounds
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecisionDefs

/-!
# Dense-overlay RAM decision-machine resource-bound proof internals
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

private theorem encodedStoreLength_eq_sums (store : Store) :
    encodedStoreLength store =
      2 * (store.map fun entry => bitlen entry.1).sum +
        2 * (store.map fun entry => bitlen entry.2).sum +
        2 * store.length := by
  induction store with
  | nil => simp [encodedStoreLength]
  | cons entry rest ih =>
      rw [encodedStoreLength, List.flatMap_cons, List.length_append,
        Entry.encode_length]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ih' : (rest.flatMap Entry.encode).length =
          2 * (rest.map fun entry => bitlen entry.1).sum +
            2 * (rest.map fun entry => bitlen entry.2).sum +
            2 * rest.length := by
        simpa only [encodedStoreLength] using! ih
      rw [ih']
      omega

private theorem address_count_width_le_encodedStoreLength
    (store : Store) (hcanonical : Canonical store) :
    store.length * bitlen store.length ≤ encodedStoreLength store := by
  let addresses := store.map Prod.fst
  let addressWidths := addresses.map bitlen
  have hnodup : addresses.Nodup := hcanonical.1
  have hlength : addresses.length = store.length := by
    simp [addresses]
  have hsum : addressWidths.sum =
      (store.map fun entry => bitlen entry.1).sum := by
    simp [addressWidths, addresses, Function.comp_def]
  have hencoded :
      2 * addressWidths.sum + 2 * store.length ≤
        encodedStoreLength store := by
    rw [encodedStoreLength_eq_sums]
    rw [hsum]
    omega
  generalize hsize : store.length.size = width
  cases width with
  | zero =>
      have hzero : store.length = 0 := by
        have := Nat.size_pos.not.mp (by omega : ¬0 < store.length.size)
        omega
      simp [hzero]
  | succ width =>
      cases width with
      | zero =>
          have hsmall : store.length ≤ 1 := by
            have hlt := Nat.lt_size_self store.length
            rw [hsize] at hlt
            norm_num at hlt
            omega
          have hbits : bitlen store.length = 1 := by
            simpa [bitlen] using! hsize
          rw [hbits]
          omega
      | succ width =>
          let addressSet := addresses.toFinset
          let threshold := 2 ^ width
          let low := addressSet.filter fun address => address < threshold
          let high := addressSet.filter fun address => threshold ≤ address
          have hcard : addressSet.card = store.length := by
            rw [List.toFinset_card_of_nodup hnodup, hlength]
          have hlowSubset : low ⊆ Finset.range threshold := by
            intro address haddress
            have := (Finset.mem_filter.mp haddress).2
            simpa [Finset.mem_range] using! this
          have hlow : low.card ≤ threshold := by
            exact le_trans (Finset.card_le_card hlowSubset) (by simp)
          have hpartition : low.card + high.card = store.length := by
            have hparts := Finset.card_filter_add_card_filter_not
              (s := addressSet) (p := fun address => address < threshold)
            simpa [low, high, Nat.not_lt, hcard] using! hparts
          have hthresholdTwice : 2 * threshold ≤ store.length := by
            have hpow : 2 ^ (width + 1) ≤ store.length := by
              rw [← Nat.lt_size]
              omega
            simpa [threshold, pow_succ, Nat.mul_comm] using! hpow
          have hmanyHigh : store.length ≤ 2 * high.card := by omega
          have hhighWidth : ∀ address ∈ high, width + 1 ≤ bitlen address := by
            intro address haddress
            have hge := (Finset.mem_filter.mp haddress).2
            unfold bitlen
            have hlt : width < address.size := Nat.lt_size.mpr (by
              simpa [threshold] using! hge)
            omega
          have hhighSum : high.card * (width + 1) ≤
              ∑ address ∈ high, bitlen address := by
            exact Finset.card_nsmul_le_sum high (fun address => bitlen address)
              (width + 1) hhighWidth
          have hhighSubset : high ⊆ addressSet := Finset.filter_subset _ _
          have hsumSubset : (∑ address ∈ high, bitlen address) ≤
              ∑ address ∈ addressSet, bitlen address := by
            exact Finset.sum_le_sum_of_subset hhighSubset
          have hsetSum : (∑ address ∈ addressSet, bitlen address) =
              addressWidths.sum := by
            rw [← List.sum_toFinset (fun address => bitlen address) hnodup]
          have hwidth : bitlen store.length = width + 2 := by
            simpa [bitlen] using! hsize
          rw [hwidth]
          have hmain : store.length * (width + 2) ≤
              2 * addressWidths.sum + store.length := by
            rw [show store.length * (width + 2) =
              store.length * (width + 1) + store.length by ring]
            have hproduct : store.length * (width + 1) ≤
                2 * (high.card * (width + 1)) :=
              by simpa [Nat.mul_assoc] using!
                Nat.mul_le_mul_right (width + 1) hmanyHigh
            omega
          omega

private theorem store_length_le_encodedStoreLength (store : Store) :
    store.length ≤ encodedStoreLength store := by
  rw [encodedStoreLength_eq_sums]
  omega

private theorem entry_bits_le_encodedStoreLength (store : Store)
    (entry : Entry) (hentry : entry ∈ store) :
    entry.1.bits.length ≤ encodedStoreLength store ∧
      entry.2.bits.length ≤ encodedStoreLength store := by
  induction store with
  | nil => simp at hentry
  | cons head rest ih =>
      simp only [List.mem_cons] at hentry
      have hcode : (Entry.encode head).length + encodedStoreLength rest =
          encodedStoreLength (head :: rest) := by
        simp [encodedStoreLength]
      rcases hentry with rfl | hentry
      · rw [Entry.encode_length] at hcode
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
        unfold bitlen at hcode
        omega
      · have htail := ih hentry
        omega

private theorem read_bits_le_encodedStoreLength (store : Store)
    (address : ℕ) :
    (RegisterStore.read store address).bits.length ≤ encodedStoreLength store := by
  induction store with
  | nil => simp [RegisterStore.read, encodedStoreLength]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedValue⟩
      by_cases haddress : address = storedAddress
      · subst address
        simp only [RegisterStore.read, ↓reduceIte]
        exact (entry_bits_le_encodedStoreLength
          ((storedAddress, storedValue) :: rest) (storedAddress, storedValue)
            (by simp)).2
      · simp only [RegisterStore.read, haddress, ↓reduceIte]
        exact le_trans ih (by
          simp [encodedStoreLength])

private theorem count_bits_le_encodedStoreLength (store : Store)
    (hcanonical : Canonical store) :
    store.length.bits.length ≤ encodedStoreLength store := by
  rw [Nat.size_eq_bits_len]
  change bitlen store.length ≤ encodedStoreLength store
  have hproduct :=
    address_count_width_le_encodedStoreLength store hcanonical
  by_cases hzero : store.length = 0
  · simp [hzero, bitlen]
  · have hpos : 1 ≤ store.length := Nat.one_le_iff_ne_zero.mpr hzero
    have hle : bitlen store.length ≤ store.length * bitlen store.length := by
      simpa only [one_mul] using!
        Nat.mul_le_mul_right (bitlen store.length) hpos
    exact le_trans hle hproduct

private theorem entryLookupStoreWidth_le_encoded (store : Store)
    (address : ℕ) :
    entryLookupStoreWidth address store ≤
      encodedStoreLength store + address.bits.length := by
  induction store with
  | nil => simp [entryLookupStoreWidth, encodedStoreLength]
  | cons entry rest ih =>
      have hentry := entry_bits_le_encodedStoreLength (entry :: rest)
        entry (by simp)
      have hrestEncoded : encodedStoreLength rest ≤
          encodedStoreLength (entry :: rest) := by
        simp [encodedStoreLength]
      simp only [entryLookupStoreWidth]
      apply max_le
      · unfold entryLookupEntryWidth
        apply max_le
        · exact Nat.le_add_left _ _
        · apply max_le
          · exact le_trans hentry.1 (Nat.le_add_right _ _)
          · apply max_le
            · exact le_trans hentry.2 (Nat.le_add_right _ _)
            · apply max_le
              · simpa [bitlen, Nat.size_eq_bits_len] using!
                  le_trans hentry.1 (Nat.le_add_right
                    (encodedStoreLength (entry :: rest)) address.bits.length)
              · apply max_le
                · simpa [bitlen, Nat.size_eq_bits_len] using!
                    le_trans hentry.2 (Nat.le_add_right
                      (encodedStoreLength (entry :: rest)) address.bits.length)
                · have hpositive : 1 ≤ encodedStoreLength (entry :: rest) := by
                    rw [encodedStoreLength_eq_sums]
                    simp only [List.map_cons, List.sum_cons, List.length_cons]
                    omega
                  exact le_trans hpositive (Nat.le_add_right _ _)
      · exact le_trans ih (Nat.add_le_add_right hrestEncoded _)

private theorem entryLookupResetWidth_le_encoded
    (store : Store) (address : ℕ) (hcanonical : Canonical store) :
    entryLookupResetWidth store address ≤
      encodedStoreLength store + address.bits.length := by
  unfold entryLookupResetWidth
  exact max_le (le_trans (count_bits_le_encodedStoreLength store hcanonical)
    (Nat.le_add_right _ _))
    (entryLookupStoreWidth_le_encoded store address)

private def denseLookupVolume (inputLength : ℕ) (store : Store)
    (address : ℕ) : ℕ :=
  encodedStoreLength store +
    store.length * (bitlen address + 1) +
    inputLength * (bitlen address + 1) + bitlen address + 1

private theorem denseLookupVolume_pos (inputLength : ℕ)
    (store : Store) (address : ℕ) :
    1 ≤ denseLookupVolume inputLength store address := by
  simp [denseLookupVolume]

private theorem entryLookupTime_le_volume {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (inputLength : ℕ)
    (store : Store) (address : ℕ) (hcanonical : Canonical store) :
    entryLookupTime tapes.scan address store ≤
      3000 * denseLookupVolume inputLength store address := by
  have hscan := entryScanTime_le_encoded tapes.scan address.bits store
  have hcount := address_count_width_le_encodedStoreLength store hcanonical
  have hlength := store_length_le_encodedStoreLength store
  have haddress : address.bits.length = bitlen address := by
    simp [bitlen, Nat.size_eq_bits_len]
  rw [haddress] at hscan
  unfold denseLookupVolume
  nlinarith

private theorem entryLookupLoadedTime_le_volume {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (inputLength : ℕ)
    (store : Store) (address : ℕ) (hcanonical : Canonical store) :
    entryLookupLoadedTime tapes store address ≤
      100000 * denseLookupVolume inputLength store address := by
  let volume := denseLookupVolume inputLength store address
  have hvolume : 1 ≤ volume := denseLookupVolume_pos inputLength store address
  have hencoded : encodedStoreLength store ≤ volume := by
    dsimp only [volume]
    unfold denseLookupVolume
    omega
  have haddressWidth : bitlen address ≤ volume := by
    dsimp only [volume]
    unfold denseLookupVolume
    omega
  have hlookup := entryLookupTime_le_volume tapes inputLength store address
    hcanonical
  have hresetWidth := entryLookupResetWidth_le_encoded store address hcanonical
  have hread := read_bits_le_encodedStoreLength store address
  have hcount := count_bits_le_encodedStoreLength store hcanonical
  have hcopyAddress := TM.binaryCopyTime_le address 0
  have hcopyRead := TM.binaryCopyTime_le
    (RegisterStore.read store address) 0
  have hcopyCount := TM.binaryCopyTime_le store.length 0
  have haddress : address.size = bitlen address := rfl
  have hreadSize : (RegisterStore.read store address).size =
      (RegisterStore.read store address).bits.length :=
    (Nat.size_eq_bits_len _).symm
  have hcountSize : store.length.size = store.length.bits.length :=
    (Nat.size_eq_bits_len _).symm
  rw [haddress, Nat.size_zero] at hcopyAddress
  rw [hreadSize, Nat.size_zero] at hcopyRead
  rw [hcountSize, Nat.size_zero] at hcopyCount
  have hhead : entryLookupRestoreHeadBound tapes store address ≤
      3000 * volume + 1 := by
    unfold entryLookupRestoreHeadBound
    omega
  have hreset : entryLookupResetTime tapes store address ≤
      30000 * volume := by
    unfold entryLookupResetTime
    have haddressBits : address.bits.length = bitlen address := by
      simp [bitlen, Nat.size_eq_bits_len]
    rw [haddressBits] at hresetWidth
    have hresetWidth' : entryLookupResetWidth store address ≤
        2 * volume := le_trans hresetWidth (by omega)
    omega
  have htail : entryLookupRestoreTailTime tapes store address ≤
      40000 * volume := by
    unfold entryLookupRestoreTailTime
    omega
  have hcopyRestore : entryLookupCopyRestoreTime tapes store address ≤
      70000 * volume := by
    unfold entryLookupCopyRestoreTime
    omega
  unfold entryLookupLoadedTime
  omega

private theorem denseInputLookupTime_le_volume
    (inputLength address : ℕ) :
    denseInputLookupTime inputLength address ≤
      50 * (inputLength * (bitlen address + 1) + bitlen address + 1) := by
  have hscan := denseInputScanTime_le_width inputLength address
  have hcopy := TM.binaryCopyTime_le address 0
  have hsubSize : (address - inputLength).bits.length ≤ bitlen address := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (Nat.sub_le address inputLength)
  rw [show address.size = bitlen address from rfl] at hscan
  rw [show address.size = bitlen address from rfl, Nat.size_zero] at hcopy
  unfold denseInputLookupTime TM.resetBinaryWorkTime TM.clearWorkTimeBound
  nlinarith

private theorem denseOverlayLookupTime_le_volume {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (inputLength : ℕ)
    (overlay : Store) (address : ℕ)
    (hvalid : DenseOverlay.Valid overlay) :
    denseOverlayLookupTime tapes inputLength overlay address ≤
      200000 * denseLookupVolume inputLength overlay address := by
  have hvolume := denseLookupVolume_pos inputLength overlay address
  have hloaded := entryLookupLoadedTime_le_volume tapes inputLength overlay
    address hvalid.1
  have hfallback := denseInputLookupTime_le_volume inputLength address
  have htag := read_bits_le_encodedStoreLength overlay address
  have hpred := TM.binaryPredTime_le
    (RegisterStore.read overlay address - 1)
  have hpredSize :
      (RegisterStore.read overlay address - 1 + 1).size ≤
        encodedStoreLength overlay + 1 := by
    have hreadSize : (RegisterStore.read overlay address).size ≤
        encodedStoreLength overlay := by
      simpa [Nat.size_eq_bits_len] using! htag
    have hvalue : RegisterStore.read overlay address - 1 + 1 ≤
        RegisterStore.read overlay address + 1 := by omega
    have hsize := Nat.size_le_size hvalue
    have hsucc : (RegisterStore.read overlay address + 1).size ≤
        (RegisterStore.read overlay address).size + 1 := by
      rw [Nat.size_le]
      have hlt := Nat.lt_size_self (RegisterStore.read overlay address)
      have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by
        simpa [Nat.size_eq_bits_len] using! htag)
      rw [pow_succ]
      omega
    exact le_trans hsize (le_trans hsucc (by omega))
  have hpred' : TM.binaryPredTime
      (RegisterStore.read overlay address - 1) ≤
      2 * (encodedStoreLength overlay + 1) + 2 := by
    exact le_trans hpred (by omega)
  have hbranch : max (denseInputLookupTime inputLength address)
      (TM.binaryPredTime (RegisterStore.read overlay address - 1)) ≤
      90000 * denseLookupVolume inputLength overlay address := by
    apply max_le
    · unfold denseLookupVolume at hvolume ⊢
      omega
    · unfold denseLookupVolume at hvolume ⊢
      omega
  unfold denseOverlayLookupTime TM.branchWorkBlankTime
  omega

private theorem size_le_self (value : ℕ) : value.size ≤ value := by
  rw [Nat.size_le]
  exact Nat.lt_pow_self (by decide)

private theorem bitlen_le_succ (value : ℕ) : bitlen value ≤ value + 1 := by
  unfold bitlen
  exact le_trans (size_le_self value) (Nat.le_succ value)

private theorem bitlen_succ_le (value : ℕ) :
    bitlen (value + 1) ≤ bitlen value + 1 := by
  rw [bitlen, bitlen, Nat.size_le]
  have hvalue := Nat.lt_size_self value
  have hpowPos : 0 < 2 ^ value.size := pow_pos (by omega) _
  rw [pow_succ]
  omega

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

private theorem binaryInstructionArithmeticTime_le_width
    (op : BinaryInstrOp) (lhs rhs width : ℕ)
    (hlhs : bitlen lhs ≤ width) (hrhs : bitlen rhs ≤ width) :
    binaryInstructionArithmeticTime op lhs rhs ≤
      1000 * (width + 1) ^ 2 := by
  have hlhsSize : lhs.size ≤ width := by simpa [bitlen] using! hlhs
  have hrhsSize : rhs.size ≤ width := by simpa [bitlen] using! hrhs
  cases op with
  | add =>
      have htime := TM.binaryRippleAddTime_le lhs rhs
      have honeSq : 1 ≤ (width + 1) ^ 2 := by nlinarith
      have hwidthSq : width ≤ (width + 1) ^ 2 := by nlinarith
      change TM.binaryRippleAddTime lhs rhs ≤ 1000 * (width + 1) ^ 2
      omega
  | sub =>
      have htime := TM.binaryRippleSubTime_le lhs rhs
      have honeSq : 1 ≤ (width + 1) ^ 2 := by nlinarith
      have hwidthSq : width ≤ (width + 1) ^ 2 := by nlinarith
      change TM.binaryRippleSubTime lhs rhs ≤ 1000 * (width + 1) ^ 2
      omega
  | mul =>
      change TM.binaryShiftMulTime lhs rhs ≤ 1000 * (width + 1) ^ 2
      unfold TM.binaryShiftMulTime TM.binaryShiftMulWidth
      nlinarith

private theorem binaryInstrResult_bitlen_le
    (op : BinaryInstrOp) (lhs rhs : ℕ) :
    bitlen (op.eval lhs rhs) ≤ bitlen lhs + bitlen rhs + 1 := by
  unfold bitlen
  cases op with
  | add =>
      exact le_trans (TM.binaryRippleAdd_sum_size_le lhs rhs) (by omega)
  | sub =>
      exact le_trans (Nat.size_le_size (Nat.sub_le lhs rhs)) (by omega)
  | mul =>
      exact le_trans (BinaryShiftMul.size_mul_le_add lhs rhs) (by omega)

private theorem denseLookupVolume_le_product
    (inputLength : ℕ) (store : Store) (address width : ℕ)
    (haddress : bitlen address ≤ width) :
    denseLookupVolume inputLength store address ≤
      4 * (encodedStoreLength store + inputLength + width + 1) *
        (width + 1) := by
  have hlength := store_length_le_encodedStoreLength store
  have hstoreProduct : store.length * (bitlen address + 1) ≤
      encodedStoreLength store * (width + 1) :=
    Nat.mul_le_mul hlength (Nat.add_le_add_right haddress 1)
  have hinputProduct : inputLength * (bitlen address + 1) ≤
      inputLength * (width + 1) :=
    Nat.mul_le_mul_left inputLength (Nat.add_le_add_right haddress 1)
  unfold denseLookupVolume
  nlinarith

private theorem denseOverlayLookupTime_le_product {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (inputLength : ℕ)
    (overlay : Store) (address width : ℕ)
    (hvalid : DenseOverlay.Valid overlay) (haddress : bitlen address ≤ width) :
    denseOverlayLookupTime tapes inputLength overlay address ≤
      800000 * (encodedStoreLength overlay + inputLength + width + 1) *
        (width + 1) := by
  have hlookup := denseOverlayLookupTime_le_volume tapes inputLength overlay
    address hvalid
  have hvolume := denseLookupVolume_le_product inputLength overlay address width
    haddress
  calc
    denseOverlayLookupTime tapes inputLength overlay address ≤
        200000 * denseLookupVolume inputLength overlay address := hlookup
    _ ≤ 200000 *
        (4 * (encodedStoreLength overlay + inputLength + width + 1) *
          (width + 1)) := Nat.mul_le_mul_left 200000 hvolume
    _ = 800000 * (encodedStoreLength overlay + inputLength + width + 1) *
        (width + 1) := by ring

private theorem denseOverlayLookupStaticTime_le_product {m : ℕ}
    (tapes : EntryLookupRestoreTapes m) (inputLength : ℕ)
    (overlay : Store) (address width magnitude : ℕ)
    (hvalid : DenseOverlay.Valid overlay) (haddress : bitlen address ≤ width)
    (hfixed : address ≤ magnitude) :
    denseOverlayLookupStaticTime tapes inputLength overlay address ≤
      1000000 * (magnitude + 1) ^ 2 *
        (encodedStoreLength overlay + inputLength + width + 1) *
        (width + 1) := by
  let volume := encodedStoreLength overlay + inputLength + width + 1
  let unit := (magnitude + 1) ^ 2 * volume * (width + 1)
  have hvolume : 1 ≤ volume := by
    dsimp only [volume]
    omega
  have hmagnitudeSq : 1 ≤ (magnitude + 1) ^ 2 := by nlinarith
  have hunitPos : 0 < unit := by
    dsimp only [unit]
    positivity
  have hunit : 1 ≤ unit := hunitPos
  have hadd := binaryAddConstTime_zero_le address
  have hadd' : TM.binaryAddConstTime address 0 ≤ 4 * unit := by
    have hfixedSq : (address + 1) ^ 2 ≤ (magnitude + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hfixed 1) 2
    have hfactor : (magnitude + 1) ^ 2 ≤ unit := by
      dsimp only [unit]
      calc
        (magnitude + 1) ^ 2 = (magnitude + 1) ^ 2 * 1 * 1 := by ring
        _ ≤ (magnitude + 1) ^ 2 * volume * (width + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hvolume) (by omega)
    exact le_trans hadd (by nlinarith)
  have hlookup := denseOverlayLookupTime_le_product tapes inputLength overlay
    address width hvalid haddress
  have hlookup' : denseOverlayLookupTime tapes inputLength overlay address ≤
      800000 * unit := by
    have hbase : volume * (width + 1) ≤ unit := by
      dsimp only [unit]
      calc
        volume * (width + 1) = (1 * volume) * (width + 1) := by simp
        _ ≤ ((magnitude + 1) ^ 2 * volume) * (width + 1) :=
          Nat.mul_le_mul_right (width + 1)
            (Nat.mul_le_mul_right volume hmagnitudeSq)
    calc
      denseOverlayLookupTime tapes inputLength overlay address ≤
          800000 * (volume * (width + 1)) := by
        simpa only [volume, Nat.mul_assoc] using! hlookup
      _ ≤ 800000 * unit := Nat.mul_le_mul_left 800000 hbase
  have hreset : TM.resetBinaryWorkTime 1 address.bits.length ≤
      2 * width + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    simpa [bitlen, Nat.size_eq_bits_len] using!
      (show 1 + 2 + 1 + (2 * bitlen address + 5) ≤
          2 * width + 9 by omega)
  have hwidthUnit : width + 1 ≤ unit := by
    dsimp only [unit]
    calc
      width + 1 = (1 * 1) * (width + 1) := by simp
      _ ≤ ((magnitude + 1) ^ 2 * volume) * (width + 1) :=
        Nat.mul_le_mul_right (width + 1) (Nat.mul_le_mul hmagnitudeSq hvolume)
  have hreset' : TM.resetBinaryWorkTime 1 address.bits.length ≤
      11 * unit := le_trans hreset (by nlinarith)
  unfold denseOverlayLookupStaticTime
  calc
    TM.binaryAddConstTime address 0 + 1 +
        (denseOverlayLookupTime tapes inputLength overlay address + 1 +
          TM.resetBinaryWorkTime 1 address.bits.length) ≤
        1000000 * unit := by omega
    _ = 1000000 * (magnitude + 1) ^ 2 *
        (encodedStoreLength overlay + inputLength + width + 1) *
        (width + 1) := by
      dsimp only [unit, volume]
      ring

private theorem taggedEntryUpdateTime_le_product {m : ℕ}
    (tapes : EntryUpdateTapes m) (inputLength : ℕ)
    (overlay : Store) (address value width : ℕ)
    (hcanonical : Canonical overlay) (haddress : bitlen address ≤ width)
    (hvalue : bitlen value ≤ width) :
    taggedEntryUpdateTime tapes overlay address value ≤
      20000 * (encodedStoreLength overlay + inputLength + width + 1) *
        (width + 1) := by
  let volume := encodedStoreLength overlay + inputLength + width + 1
  have hvolume : 1 ≤ volume := by
    dsimp only [volume]
    omega
  have hencoded : encodedStoreLength overlay ≤ volume := by
    dsimp only [volume]
    omega
  have hwidthVolume : width + 1 ≤ volume := by
    dsimp only [volume]
    omega
  have hvolumeFactor : volume ≤ volume * (width + 1) := by
    calc
      volume = volume * 1 := by simp
      _ ≤ volume * (width + 1) := Nat.mul_le_mul_left volume (by omega)
  have hlengthEncoded := store_length_le_encodedStoreLength overlay
  have hlength : overlay.length ≤ volume := le_trans hlengthEncoded hencoded
  have hcountBits := count_bits_le_encodedStoreLength overlay hcanonical
  have hcount : bitlen overlay.length ≤ encodedStoreLength overlay := by
    simpa [bitlen, Nat.size_eq_bits_len] using! hcountBits
  have hcountProduct :=
    address_count_width_le_encodedStoreLength overlay hcanonical
  have htag : bitlen (value + 1) ≤ width + 1 :=
    le_trans (bitlen_succ_le value) (Nat.add_le_add_right hvalue 1)
  have hlengthAddress : overlay.length * bitlen address ≤
      volume * width := Nat.mul_le_mul hlength haddress
  have hlengthTag : overlay.length * bitlen (value + 1) ≤
      volume * (width + 1) := Nat.mul_le_mul hlength htag
  have hupdate := entryUpdateTime_le_encoded tapes overlay address (value + 1)
  have hupdateVolume : entryUpdateTime tapes overlay address (value + 1) ≤
      12000 * volume * (width + 1) := by
    calc
      entryUpdateTime tapes overlay address (value + 1) ≤
          1000 * (encodedStoreLength overlay +
            (overlay.length + 1) *
              (bitlen address + bitlen (value + 1) +
                bitlen overlay.length + 1) + 1) := hupdate
      _ ≤ 1000 * (12 * volume * (width + 1)) := by
        apply Nat.mul_le_mul_left 1000
        rw [show (overlay.length + 1) *
            (bitlen address + bitlen (value + 1) + bitlen overlay.length + 1) =
            overlay.length * bitlen address +
              overlay.length * bitlen (value + 1) +
              overlay.length * bitlen overlay.length + overlay.length +
              bitlen address + bitlen (value + 1) +
              bitlen overlay.length + 1 by ring]
        dsimp only [volume] at hvolumeFactor ⊢
        nlinarith
      _ = 12000 * volume * (width + 1) := by ring
  have hsucc := TM.binarySuccTime_le value
  have hsucc' : TM.binarySuccTime value ≤
      3 * volume * (width + 1) := by
    have hsize : value.size ≤ width := by simpa [bitlen] using! hvalue
    exact le_trans hsucc (by nlinarith)
  unfold taggedEntryUpdateTime
  dsimp only [volume] at hupdateVolume hsucc' ⊢
  nlinarith

private def denseResourceUnit (magnitude inputLength : ℕ)
    (overlay : Store) (width : ℕ) : ℕ :=
  (magnitude + 1) ^ 2 *
    (encodedStoreLength overlay + inputLength + width + 1) * (width + 1)

private theorem denseResourceUnit_pos (magnitude inputLength : ℕ)
    (overlay : Store) (width : ℕ) :
    1 ≤ denseResourceUnit magnitude inputLength overlay width := by
  have hpos : 0 < denseResourceUnit magnitude inputLength overlay width := by
    unfold denseResourceUnit
    positivity
  omega

private theorem denseResourceBase_le_unit (magnitude inputLength : ℕ)
    (overlay : Store) (width : ℕ) :
    (encodedStoreLength overlay + inputLength + width + 1) * (width + 1) ≤
      denseResourceUnit magnitude inputLength overlay width := by
  unfold denseResourceUnit
  have hmagnitudePos : 0 < (magnitude + 1) ^ 2 := pow_pos (by omega) _
  have hmagnitude : 1 ≤ (magnitude + 1) ^ 2 := by omega
  calc
    (encodedStoreLength overlay + inputLength + width + 1) * (width + 1) =
        (1 * (encodedStoreLength overlay + inputLength + width + 1)) *
          (width + 1) := by simp
    _ ≤ ((magnitude + 1) ^ 2 *
        (encodedStoreLength overlay + inputLength + width + 1)) *
          (width + 1) := Nat.mul_le_mul_right (width + 1)
      (Nat.mul_le_mul_right _ hmagnitude)

private theorem denseResourceVolume_le_unit (magnitude inputLength : ℕ)
    (overlay : Store) (width : ℕ) :
    encodedStoreLength overlay + inputLength + width + 1 ≤
      denseResourceUnit magnitude inputLength overlay width := by
  exact le_trans (by
    have := Nat.mul_le_mul_left
      (encodedStoreLength overlay + inputLength + width + 1)
      (show 1 ≤ width + 1 by omega)
    simpa only [Nat.mul_one] using! this)
    (denseResourceBase_le_unit magnitude inputLength overlay width)

private theorem denseResourceWidthSq_le_unit (magnitude inputLength : ℕ)
    (overlay : Store) (width : ℕ) :
    (width + 1) ^ 2 ≤
      denseResourceUnit magnitude inputLength overlay width := by
  apply le_trans _ (denseResourceBase_le_unit magnitude inputLength overlay width)
  calc
    (width + 1) ^ 2 = (width + 1) * (width + 1) := by ring
    _ ≤ (encodedStoreLength overlay + inputLength + width + 1) *
        (width + 1) := Nat.mul_le_mul_right (width + 1) (by omega)

private theorem denseResourceMagnitudeSq_le_unit
    (magnitude inputLength : ℕ) (overlay : Store) (width : ℕ) :
    (magnitude + 1) ^ 2 ≤
      denseResourceUnit magnitude inputLength overlay width := by
  unfold denseResourceUnit
  calc
    (magnitude + 1) ^ 2 = (magnitude + 1) ^ 2 * 1 * 1 := by ring
    _ ≤ (magnitude + 1) ^ 2 *
        (encodedStoreLength overlay + inputLength + width + 1) *
          (width + 1) := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ (by omega)) (by omega)
private theorem denseExecuteInstructionTime_le_product {m : ℕ}
    (tapes : ControlInstructionTapes m) (input : List Bool)
    (instruction : Instr) (pcValue : ℕ) (overlay : Store)
    (width magnitude : ℕ) (hvalid : DenseOverlay.Valid overlay)
    (hstatic : RegisterStore.Instr.staticWidth instruction ≤ width)
    (hcost : instruction.logCost
      (DenseOverlay.Snapshot.decode input { pc := pcValue, overlay }) ≤ width)
    (hfixed : instructionResourceMagnitude instruction ≤ magnitude)
    (hpc : pcValue ≤ magnitude) :
    denseExecuteInstructionTime tapes input instruction pcValue overlay ≤
      6000000 * denseResourceUnit magnitude input.length overlay width := by
  let unit := denseResourceUnit magnitude input.length overlay width
  have hunit : 1 ≤ unit := denseResourceUnit_pos magnitude input.length
    overlay width
  have hbase : (encodedStoreLength overlay + input.length + width + 1) *
      (width + 1) ≤ unit := denseResourceBase_le_unit magnitude input.length
    overlay width
  have hvolume : encodedStoreLength overlay + input.length + width + 1 ≤
      unit := denseResourceVolume_le_unit magnitude input.length overlay width
  have hwidthSq : (width + 1) ^ 2 ≤ unit :=
    denseResourceWidthSq_le_unit magnitude input.length overlay width
  have hmagnitudeSq : (magnitude + 1) ^ 2 ≤ unit :=
    denseResourceMagnitudeSq_le_unit magnitude input.length overlay width
  have hencoded : encodedStoreLength overlay ≤ unit := by
    exact le_trans (by omega) hvolume
  have hencodedBits : (overlay.flatMap Entry.encode).length ≤ unit := by
    simpa only [encodedStoreLength] using! hencoded
  have hfixedAdd : ∀ fixedValue, fixedValue ≤ magnitude →
      TM.binaryAddConstTime fixedValue 0 ≤ 4 * unit := by
    intro fixedValue hconstant
    have hadd := binaryAddConstTime_zero_le fixedValue
    have hsquare : (fixedValue + 1) ^ 2 ≤ (magnitude + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hconstant 1) 2
    exact le_trans hadd (by nlinarith)
  have hstaticLookup : ∀ address, bitlen address ≤ width →
      address ≤ magnitude →
      denseOverlayLookupStaticTime tapes.data.lhsLookup input.length overlay
        address ≤ 1000000 * unit := by
    intro address haddress haddressFixed
    have hlookup := denseOverlayLookupStaticTime_le_product
      tapes.data.lhsLookup input.length overlay address width magnitude hvalid
      haddress haddressFixed
    calc
      denseOverlayLookupStaticTime tapes.data.lhsLookup input.length overlay
          address ≤ 1000000 * (magnitude + 1) ^ 2 *
            (encodedStoreLength overlay + input.length + width + 1) *
            (width + 1) := hlookup
      _ = 1000000 * unit := by
        dsimp only [unit, denseResourceUnit]
        ring
  have hstaticLookupRhs : ∀ address, bitlen address ≤ width →
      address ≤ magnitude →
      denseOverlayLookupStaticTime tapes.data.rhsLookup input.length overlay
        address ≤ 1000000 * unit := by
    intro address haddress haddressFixed
    have hlookup := denseOverlayLookupStaticTime_le_product
      tapes.data.rhsLookup input.length overlay address width magnitude hvalid
      haddress haddressFixed
    calc
      denseOverlayLookupStaticTime tapes.data.rhsLookup input.length overlay
          address ≤ 1000000 * (magnitude + 1) ^ 2 *
            (encodedStoreLength overlay + input.length + width + 1) *
            (width + 1) := hlookup
      _ = 1000000 * unit := by
        dsimp only [unit, denseResourceUnit]
        ring
  have hdynamicLookup : ∀ address, bitlen address ≤ width →
      denseOverlayLookupTime tapes.data.indirectLoadLookup input.length overlay
        address ≤ 800000 * unit := by
    intro address haddress
    have hlookup := denseOverlayLookupTime_le_product
      tapes.data.indirectLoadLookup input.length overlay address width hvalid
      haddress
    calc
      denseOverlayLookupTime tapes.data.indirectLoadLookup input.length overlay
          address ≤ 800000 *
            ((encodedStoreLength overlay + input.length + width + 1) *
              (width + 1)) := by simpa only [Nat.mul_assoc] using! hlookup
      _ ≤ 800000 * unit := Nat.mul_le_mul_left 800000 hbase
  have htaggedUpdate : ∀ address value,
      bitlen address ≤ width → bitlen value ≤ width →
      taggedEntryUpdateTime tapes.data.update overlay address value ≤
        20000 * unit := by
    intro address value haddress hvalue
    have hupdate := taggedEntryUpdateTime_le_product tapes.data.update
      input.length overlay address value width hvalid.1 haddress hvalue
    calc
      taggedEntryUpdateTime tapes.data.update overlay address value ≤
          20000 * ((encodedStoreLength overlay + input.length + width + 1) *
            (width + 1)) := by simpa only [Nat.mul_assoc] using! hupdate
      _ ≤ 20000 * unit := Nat.mul_le_mul_left 20000 hbase
  have harithmetic : ∀ op lhs rhs, bitlen lhs ≤ width →
      bitlen rhs ≤ width →
      binaryInstructionArithmeticTime op lhs rhs ≤ 1000 * unit := by
    intro op lhs rhs hlhs hrhs
    exact le_trans (binaryInstructionArithmeticTime_le_width op lhs rhs width
      hlhs hrhs) (Nat.mul_le_mul_left 1000 hwidthSq)
  have hcopy : ∀ value, bitlen value ≤ width →
      TM.binaryCopyTime value 0 ≤ 23 * unit := by
    intro value hvalue
    have htime := TM.binaryCopyTime_le value 0
    have hsize : value.size ≤ width := by simpa [bitlen] using! hvalue
    rw [Nat.size_zero] at htime
    exact le_trans htime (by nlinarith)
  have hreset : ∀ value, bitlen value ≤ width →
      TM.resetBinaryWorkTime 1 value.bits.length ≤ 11 * unit := by
    intro value hvalue
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    have hbits : value.bits.length ≤ width := by
      simpa [bitlen, Nat.size_eq_bits_len] using! hvalue
    nlinarith
  have hpcSize : pcValue.size ≤ magnitude :=
    le_trans (size_le_self pcValue) hpc
  have hpcSucc := TM.binarySuccTime_le pcValue
  have hpcSucc' : TM.binarySuccTime pcValue ≤ 4 * unit :=
    le_trans hpcSucc (by nlinarith)
  have hpcReset : TM.resetBinaryWorkTime 1 pcValue.bits.length ≤
      11 * unit := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    have hbits : pcValue.bits.length ≤ magnitude := by
      simpa [Nat.size_eq_bits_len] using! hpcSize
    nlinarith
  cases instruction with
  | imm destination value =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost] at hcost
      have hdestinationWidth : bitlen destination ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hvalueWidth : bitlen value ≤ width := by omega
      have hvalueAdd := hfixedAdd value (by omega)
      have hdestinationAdd := hfixedAdd destination (by omega)
      have hupdate := htaggedUpdate destination value hdestinationWidth hvalueWidth
      simp only [denseExecuteInstructionTime, denseImmediateInstructionTime]
      omega
  | add destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      have hdestinationWidth : bitlen destination ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hsource₀Width : bitlen source₀ ≤ width :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hstatic)
      have hsource₁Width : bitlen source₁ ≤ width :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hstatic)
      have hlhs : bitlen (DenseOverlay.read input overlay source₀) ≤ width :=
        by omega
      have hrhs : bitlen (DenseOverlay.read input overlay source₁) ≤ width :=
        by omega
      have hresult : bitlen (DenseOverlay.read input overlay source₀ +
          DenseOverlay.read input overlay source₁) ≤ width := by omega
      have hlookup₀ := hstaticLookup source₀ hsource₀Width (by omega)
      have hlookup₁ := hstaticLookupRhs source₁ hsource₁Width (by omega)
      have hadd := hfixedAdd destination (by omega)
      have hop := harithmetic .add (DenseOverlay.read input overlay source₀)
        (DenseOverlay.read input overlay source₁) hlhs hrhs
      have hupdate := htaggedUpdate destination
        (DenseOverlay.read input overlay source₀ +
          DenseOverlay.read input overlay source₁)
        hdestinationWidth hresult
      simp only [denseExecuteInstructionTime, denseDirectBinaryInstructionTime,
        denseBinaryInstructionUpdateTime, BinaryInstrOp.eval]
      omega
  | sub destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      have hdestinationWidth : bitlen destination ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hsource₀Width : bitlen source₀ ≤ width :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hstatic)
      have hsource₁Width : bitlen source₁ ≤ width :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hstatic)
      have hlhs : bitlen (DenseOverlay.read input overlay source₀) ≤ width :=
        by omega
      have hrhs : bitlen (DenseOverlay.read input overlay source₁) ≤ width :=
        by omega
      have hresultRaw := binaryInstrResult_bitlen_le .sub
        (DenseOverlay.read input overlay source₀)
        (DenseOverlay.read input overlay source₁)
      have hresult : bitlen (DenseOverlay.read input overlay source₀ -
          DenseOverlay.read input overlay source₁) ≤ width :=
        le_trans hresultRaw (by omega)
      have hlookup₀ := hstaticLookup source₀ hsource₀Width (by omega)
      have hlookup₁ := hstaticLookupRhs source₁ hsource₁Width (by omega)
      have hadd := hfixedAdd destination (by omega)
      have hop := harithmetic .sub (DenseOverlay.read input overlay source₀)
        (DenseOverlay.read input overlay source₁) hlhs hrhs
      have hupdate := htaggedUpdate destination
        (DenseOverlay.read input overlay source₀ -
          DenseOverlay.read input overlay source₁)
        hdestinationWidth hresult
      simp only [denseExecuteInstructionTime, denseDirectBinaryInstructionTime,
        denseBinaryInstructionUpdateTime, BinaryInstrOp.eval]
      omega
  | mul destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      have hdestinationWidth : bitlen destination ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hsource₀Width : bitlen source₀ ≤ width :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hstatic)
      have hsource₁Width : bitlen source₁ ≤ width :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hstatic)
      have hlhs : bitlen (DenseOverlay.read input overlay source₀) ≤ width :=
        by omega
      have hrhs : bitlen (DenseOverlay.read input overlay source₁) ≤ width :=
        by omega
      have hresult : bitlen (DenseOverlay.read input overlay source₀ *
          DenseOverlay.read input overlay source₁) ≤ width := by omega
      have hlookup₀ := hstaticLookup source₀ hsource₀Width (by omega)
      have hlookup₁ := hstaticLookupRhs source₁ hsource₁Width (by omega)
      have hadd := hfixedAdd destination (by omega)
      have hop := harithmetic .mul (DenseOverlay.read input overlay source₀)
        (DenseOverlay.read input overlay source₁) hlhs hrhs
      have hupdate := htaggedUpdate destination
        (DenseOverlay.read input overlay source₀ *
          DenseOverlay.read input overlay source₁)
        hdestinationWidth hresult
      simp only [denseExecuteInstructionTime, denseDirectBinaryInstructionTime,
        denseBinaryInstructionUpdateTime, BinaryInstrOp.eval]
      omega
  | load destination addressRegister =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      have hdestinationWidth : bitlen destination ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hregisterWidth : bitlen addressRegister ≤ width :=
        le_trans (le_max_right _ _) hstatic
      have haddress : bitlen
          (DenseOverlay.read input overlay addressRegister) ≤ width := by omega
      have hvalue : bitlen (DenseOverlay.read input overlay
          (DenseOverlay.read input overlay addressRegister)) ≤ width := by omega
      have hlookup := hstaticLookup addressRegister hregisterWidth (by omega)
      have hindirect := hdynamicLookup
        (DenseOverlay.read input overlay addressRegister) haddress
      have hadd := hfixedAdd destination (by omega)
      have hupdate := htaggedUpdate destination
        (DenseOverlay.read input overlay
          (DenseOverlay.read input overlay addressRegister))
        hdestinationWidth hvalue
      simp only [denseExecuteInstructionTime, denseIndirectLoadInstructionTime]
      omega
  | store addressRegister source =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      have hregisterWidth : bitlen addressRegister ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hsourceWidth : bitlen source ≤ width :=
        le_trans (le_max_right _ _) hstatic
      have haddress : bitlen
          (DenseOverlay.read input overlay addressRegister) ≤ width := by omega
      have hvalue : bitlen (DenseOverlay.read input overlay source) ≤ width :=
        by omega
      have hlookupAddress := hstaticLookup addressRegister hregisterWidth
        (by omega)
      have hlookupValue := hstaticLookupRhs source hsourceWidth (by omega)
      have hcopyAddress := hcopy
        (DenseOverlay.read input overlay addressRegister) haddress
      have hcopyValue := hcopy (DenseOverlay.read input overlay source) hvalue
      have hupdate := htaggedUpdate
        (DenseOverlay.read input overlay addressRegister)
        (DenseOverlay.read input overlay source) haddress hvalue
      simp only [denseExecuteInstructionTime, denseIndirectStoreInstructionTime]
      omega
  | jz source target =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [instructionResourceMagnitude] at hfixed
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      have hsourceWidth : bitlen source ≤ width :=
        le_trans (le_max_left _ _) hstatic
      have hvalue : bitlen (DenseOverlay.read input overlay source) ≤ width :=
        by omega
      have hlookupRaw := denseOverlayLookupStaticTime_le_product
        tapes.lifted.data.lhsLookup input.length overlay source width magnitude
        hvalid hsourceWidth (by omega)
      have hlookup : denseOverlayLookupStaticTime
          tapes.lifted.data.lhsLookup input.length overlay source ≤
          1000000 * unit := by
        calc
          denseOverlayLookupStaticTime tapes.lifted.data.lhsLookup input.length
              overlay source ≤ 1000000 * (magnitude + 1) ^ 2 *
                (encodedStoreLength overlay + input.length + width + 1) *
                (width + 1) := hlookupRaw
          _ = 1000000 * unit := by
            dsimp only [unit, denseResourceUnit]
            ring
      have htargetAdd := hfixedAdd target (by omega)
      have hset : setProgramCounterTime pcValue target ≤ 16 * unit := by
        unfold setProgramCounterTime
        omega
      have hbranch : max (setProgramCounterTime pcValue target)
          (TM.binarySuccTime pcValue) ≤ 16 * unit :=
        max_le hset (by omega)
      have hresetValue := hreset (DenseOverlay.read input overlay source) hvalue
      simp only [denseExecuteInstructionTime, denseZeroJumpInstructionTime,
        TM.branchWorkBlankTime]
      omega
  | jmp target =>
      simp only [instructionResourceMagnitude] at hfixed
      have htargetAdd := hfixedAdd target (by omega)
      have hset : setProgramCounterTime pcValue target ≤ 16 * unit := by
        unfold setProgramCounterTime
        omega
      simp only [denseExecuteInstructionTime, jumpInstructionTime]
      omega
  | halt =>
      simp only [denseExecuteInstructionTime, haltInstructionTime]
      omega

private theorem dispatchWithTime_le_selected {m : ℕ}
    (tapes : ControlInstructionTapes m) (executeTime : Instr → ℕ)
    (program : Program) (selector : ℕ) :
    dispatchWithTime tapes executeTime program selector ≤
      executeTime (selectedInstruction program selector) +
        20 * (selector + 1) ^ 2 + 20 := by
  induction program generalizing selector with
  | nil =>
      have hsize := size_le_self selector
      simp only [dispatchWithTime, selectedInstruction]
      unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
      rw [Nat.size_eq_bits_len]
      nlinarith
  | cons instruction rest ih =>
      cases selector with
      | zero =>
          simp [dispatchWithTime, selectedInstruction]
      | succ selector =>
          have htail := ih selector
          have hpred := TM.binaryPredTime_le selector
          have hsize := size_le_self (selector + 1)
          simp only [dispatchWithTime, selectedInstruction]
          nlinarith

private theorem selectedInstructionResourceMagnitude_le
    (program : Program) (selector : ℕ) :
    instructionResourceMagnitude (selectedInstruction program selector) ≤
      programResourceMagnitude program := by
  induction program generalizing selector with
  | nil => simp [selectedInstruction, instructionResourceMagnitude,
      programResourceMagnitude]
  | cons instruction rest ih =>
      cases selector with
      | zero =>
          simp only [selectedInstruction, programResourceMagnitude,
            List.length_cons, List.map_cons, List.sum_cons]
          omega
      | succ selector =>
          have htail := ih selector
          simp only [selectedInstruction, programResourceMagnitude,
            List.length_cons, List.map_cons, List.sum_cons]
          unfold programResourceMagnitude at htail
          omega

private theorem selectedInstructionStaticWidth_le
    (program : Program) (selector : ℕ) :
    RegisterStore.Instr.staticWidth (selectedInstruction program selector) ≤
      programStaticWidth program := by
  induction program generalizing selector with
  | nil => simp [selectedInstruction, RegisterStore.Instr.staticWidth,
      programStaticWidth]
  | cons instruction rest ih =>
      cases selector with
      | zero => simp [selectedInstruction, programStaticWidth]
      | succ selector =>
          exact le_trans (ih selector) (by
            simp [programStaticWidth])
private theorem denseProgramInstructionTime_le_product {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    denseProgramInstructionTime tapes program input snapshot.pc
        snapshot.overlay ≤
      7000000 * denseResourceUnit (programResourceMagnitude program)
        input.length snapshot.overlay (denseStepWidth program input snapshot) := by
  let width := denseStepWidth program input snapshot
  let magnitude := programResourceMagnitude program
  let unit := denseResourceUnit magnitude input.length snapshot.overlay width
  let instruction := selectedInstruction program snapshot.pc
  have hunit : 1 ≤ unit := denseResourceUnit_pos magnitude input.length
    snapshot.overlay width
  have hmagnitudeSq : (magnitude + 1) ^ 2 ≤ unit :=
    denseResourceMagnitudeSq_le_unit magnitude input.length snapshot.overlay width
  have hstatic : RegisterStore.Instr.staticWidth instruction ≤ width := by
    exact le_trans (selectedInstructionStaticWidth_le program snapshot.pc) (by
      unfold width denseStepWidth
      omega)
  have hselectedCost : instruction.logCost (snapshot.decode input) =
      RAM.stepLogCost program (snapshot.decode input) := by
    unfold instruction RAM.stepLogCost RAM.curInstr
    rw [selectedInstruction_eq_getElem?_getD]
    simp [DenseOverlay.Snapshot.decode]
  have hcost : instruction.logCost (snapshot.decode input) ≤ width := by
    rw [hselectedCost]
    unfold width denseStepWidth
    omega
  have hfixed : instructionResourceMagnitude instruction ≤ magnitude := by
    exact selectedInstructionResourceMagnitude_le program snapshot.pc
  have hexecute := denseExecuteInstructionTime_le_product tapes input instruction
    snapshot.pc snapshot.overlay width magnitude hvalid hstatic hcost hfixed (by
      simpa only [magnitude] using! hpc)
  have hdispatchRaw := dispatchWithTime_le_selected tapes
    (fun current => denseExecuteInstructionTime tapes input current snapshot.pc
      snapshot.overlay) program snapshot.pc
  have hselectorSquare : (snapshot.pc + 1) ^ 2 ≤
      (magnitude + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (by
      simpa only [magnitude] using! hpc) 1) 2
  have hdispatch : denseDispatchProgramTime tapes input snapshot.overlay
      snapshot.pc program snapshot.pc ≤ 6100000 * unit := by
    unfold denseDispatchProgramTime
    apply le_trans hdispatchRaw
    dsimp only [instruction] at hexecute ⊢
    nlinarith
  have hcopyRaw := TM.binaryCopyTime_le snapshot.pc 0
  have hpcSize : snapshot.pc.size ≤ magnitude :=
    le_trans (size_le_self snapshot.pc) (by simpa only [magnitude] using! hpc)
  have hcopy : TM.binaryCopyTime snapshot.pc 0 ≤ 23 * unit := by
    rw [Nat.size_zero] at hcopyRaw
    exact le_trans hcopyRaw (by nlinarith)
  unfold denseProgramInstructionTime
  dsimp only [unit, width, magnitude] at hdispatch hcopy hunit ⊢
  omega

private theorem bufferedCleanupTime_le_linear {m : ℕ}
    (tapes : ControlInstructionTapes m) (oldStore nextStore : Store)
    (cleanupValues : Fin 5 → ℕ) (remainingValue sourceHeadBound bound : ℕ)
    (hsource : 1 ≤ sourceHeadBound)
    (hcleanup : ∀ slot, (cleanupValues slot).bits.length ≤ bound)
    (hremaining : remainingValue.bits.length ≤ bound)
    (hold : encodedStoreLength oldStore ≤ bound)
    (hnext : encodedStoreLength nextStore ≤ bound) :
    bufferedCleanupTime tapes oldStore nextStore cleanupValues remainingValue
        sourceHeadBound ≤
      100 * (sourceHeadBound + bound + 1) := by
  let nextBits := nextStore.flatMap Entry.encode
  have hreset := TM.resetBinaryWorkManyTime_le
    (instructionCleanupResetTargets tapes)
    (bufferedCleanupResetBitsAt tapes cleanupValues remainingValue oldStore)
    (instructionCleanupResetHeadBoundAt tapes sourceHeadBound)
    sourceHeadBound bound
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      rw [instructionCleanupResetHeadBoundAt,
        (instructionCleanupResetTape_injective tapes).extend_apply]
      fin_cases slot <;>
        simp [instructionCleanupResetHeadBound, hsource])
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      rw [bufferedCleanupResetBitsAt,
        (instructionCleanupResetTape_injective tapes).extend_apply]
      fin_cases slot
      · simpa [bufferedCleanupResetBits] using! hcleanup 0
      · simpa [bufferedCleanupResetBits] using! hcleanup 1
      · simpa [bufferedCleanupResetBits] using! hcleanup 2
      · simpa [bufferedCleanupResetBits] using! hcleanup 3
      · simpa [bufferedCleanupResetBits] using! hcleanup 4
      · simpa [bufferedCleanupResetBits] using! hremaining
      · simpa [bufferedCleanupResetBits, encodedStoreLength] using! hold)
  have htargets : (instructionCleanupResetTargets tapes).length = 7 := by
    simp [instructionCleanupResetTargets]
  rw [htargets] at hreset
  have hnextBits : nextBits.length ≤ bound := by
    simpa only [nextBits, encodedStoreLength] using! hnext
  have hnextLength : nextStore.length ≤ bound :=
    le_trans (store_length_le_encodedStoreLength nextStore) hnext
  have hresetNext : TM.resetBinaryWorkTime (nextBits.length + 1)
      nextBits.length ≤ 3 * bound + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    omega
  have hcopyRaw := TM.binaryCopyTime_le nextStore.length 0
  have hcopy : TM.binaryCopyTime nextStore.length 0 ≤ 3 * bound + 20 := by
    rw [Nat.size_zero] at hcopyRaw
    exact le_trans hcopyRaw (by
      have hsize := le_trans (size_le_self nextStore.length) hnextLength
      omega)
  unfold bufferedCleanupTime
  dsimp only [nextBits] at hnextBits hresetNext ⊢
  omega

private theorem denseInstructionCleanupValue_bits_le
    (input : List Bool) (instruction : Instr) (pcValue : ℕ)
    (overlay : Store) (width : ℕ)
    (hstatic : RegisterStore.Instr.staticWidth instruction ≤ width)
    (hcost : instruction.logCost
      (DenseOverlay.Snapshot.decode input { pc := pcValue, overlay }) ≤ width) :
    ∀ slot, (denseInstructionCleanupValue input instruction overlay slot).bits.length
      ≤ width + 1 := by
  have hbits (value : ℕ) (hvalue : bitlen value ≤ width + 1) :
      value.bits.length ≤ width + 1 := by
    simpa [bitlen, Nat.size_eq_bits_len] using! hvalue
  cases instruction with
  | imm destination value =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [Instr.logCost] at hcost
      have hdestination : bitlen destination ≤ width + 1 := by omega
      have htag : bitlen (value + 1) ≤ width + 1 :=
        le_trans (bitlen_succ_le value) (by omega)
      intro slot
      fin_cases slot
      · exact hbits destination hdestination
      · exact hbits (value + 1) htag
      · simp only [denseInstructionCleanupValue]
        split <;> simp_all [Fin.ext_iff]
        split <;> simp [Nat.bits]
      · simp [denseInstructionCleanupValue]
      · simp [denseInstructionCleanupValue]
  | add destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      let lhs := DenseOverlay.read input overlay source₀
      let rhs := DenseOverlay.read input overlay source₁
      have hdestination : bitlen destination ≤ width + 1 := by omega
      have hlhs : bitlen lhs ≤ width + 1 := by
        dsimp only [lhs]
        omega
      have hrhs : bitlen rhs ≤ width + 1 := by
        dsimp only [rhs]
        omega
      have htag : bitlen (lhs + rhs + 1) ≤ width + 1 := by
        exact le_trans (bitlen_succ_le (lhs + rhs)) (by
          dsimp only [lhs, rhs]
          omega)
      intro slot
      fin_cases slot
      · exact hbits destination hdestination
      · simpa only [lhs, rhs] using! hbits (lhs + rhs + 1) htag
      · simp only [denseInstructionCleanupValue]
        split <;> simp_all [Fin.ext_iff]
        split <;> simp [Nat.bits]
      · simpa only [lhs] using! hbits lhs hlhs
      · simpa only [rhs] using! hbits rhs hrhs
  | sub destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      let lhs := DenseOverlay.read input overlay source₀
      let rhs := DenseOverlay.read input overlay source₁
      have hdestination : bitlen destination ≤ width + 1 := by omega
      have hlhs : bitlen lhs ≤ width := by
        dsimp only [lhs]
        omega
      have hrhs : bitlen rhs ≤ width := by
        dsimp only [rhs]
        omega
      have hresult := binaryInstrResult_bitlen_le .sub lhs rhs
      have hresult' : bitlen (lhs - rhs) ≤ bitlen lhs + bitlen rhs + 1 := by
        simpa [BinaryInstrOp.eval] using! hresult
      have hresultWidth : bitlen (lhs - rhs) ≤ width := by
        apply le_trans hresult'
        dsimp only [lhs, rhs] at hcost ⊢
        exact hcost
      have htag : bitlen (lhs - rhs + 1) ≤ width + 1 :=
        le_trans (bitlen_succ_le (lhs - rhs))
          (Nat.add_le_add_right hresultWidth 1)
      intro slot
      fin_cases slot
      · exact hbits destination hdestination
      · simpa only [lhs, rhs] using! hbits (lhs - rhs + 1) htag
      · simp only [denseInstructionCleanupValue]
        split <;> simp_all [Fin.ext_iff]
        split <;> simp [Nat.bits]
      · exact hbits lhs (by omega)
      · exact hbits rhs (by omega)
  | mul destination source₀ source₁ =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      let lhs := DenseOverlay.read input overlay source₀
      let rhs := DenseOverlay.read input overlay source₁
      have hdestination : bitlen destination ≤ width + 1 := by omega
      have hlhs : bitlen lhs ≤ width + 1 := by
        dsimp only [lhs]
        omega
      have hrhs : bitlen rhs ≤ width + 1 := by
        dsimp only [rhs]
        omega
      have htag : bitlen (lhs * rhs + 1) ≤ width + 1 :=
        le_trans (bitlen_succ_le (lhs * rhs)) (by
          dsimp only [lhs, rhs]
          omega)
      intro slot
      fin_cases slot
      · exact hbits destination hdestination
      · simpa only [lhs, rhs] using! hbits (lhs * rhs + 1) htag
      · simp only [denseInstructionCleanupValue]
        split <;> simp_all [Fin.ext_iff]
        split <;> simp [Nat.bits]
      · simpa only [lhs] using! hbits lhs hlhs
      · simpa only [rhs] using! hbits rhs hrhs
  | load destination addressRegister =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      let address := DenseOverlay.read input overlay addressRegister
      let value := DenseOverlay.read input overlay address
      have hdestination : bitlen destination ≤ width + 1 := by omega
      have haddress : bitlen address ≤ width + 1 := by
        dsimp only [address]
        omega
      have htag : bitlen (value + 1) ≤ width + 1 :=
        le_trans (bitlen_succ_le value) (by
          dsimp only [address, value]
          omega)
      intro slot
      fin_cases slot
      · exact hbits destination hdestination
      · simpa only [address, value] using! hbits (value + 1) htag
      · simp only [denseInstructionCleanupValue]
        split <;> simp_all [Fin.ext_iff]
        split <;> simp [Nat.bits]
      · simpa only [address] using! hbits address haddress
      · simp [denseInstructionCleanupValue]
  | store addressRegister source =>
      simp only [RegisterStore.Instr.staticWidth] at hstatic
      simp only [Instr.logCost, DenseOverlay.Snapshot.decode,
        DenseOverlay.decode] at hcost
      let address := DenseOverlay.read input overlay addressRegister
      let value := DenseOverlay.read input overlay source
      have haddress : bitlen address ≤ width + 1 := by
        dsimp only [address]
        omega
      have hvalue : bitlen value ≤ width := by
        dsimp only [value]
        omega
      have htag : bitlen (value + 1) ≤ width + 1 :=
        le_trans (bitlen_succ_le value) (by omega)
      intro slot
      fin_cases slot
      · simpa only [address] using! hbits address haddress
      · simpa only [value] using! hbits (value + 1) htag
      · simp only [denseInstructionCleanupValue]
        split <;> simp_all [Fin.ext_iff]
        split <;> simp [Nat.bits]
      · simpa only [address] using! hbits address haddress
      · simpa only [value] using! hbits value (by omega)
  | jz source target =>
      intro slot
      fin_cases slot <;> simp [denseInstructionCleanupValue]
  | jmp target =>
      intro slot
      fin_cases slot <;> simp [denseInstructionCleanupValue]
  | halt =>
      intro slot
      fin_cases slot <;> simp [denseInstructionCleanupValue]

private theorem denseInstructionRemainingValue_bits_le
    (instruction : Instr) (overlay : Store) (hcanonical : Canonical overlay) :
    (denseInstructionRemainingValue instruction overlay).bits.length ≤
      encodedStoreLength overlay := by
  have hcount := count_bits_le_encodedStoreLength overlay hcanonical
  cases instruction <;>
    simp only [denseInstructionRemainingValue] <;> simp_all
theorem denseProgramStepTime_le_envelope_internal {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    denseProgramStepTime tapes program input snapshot.pc snapshot.overlay ≤
      denseStepEnvelope program input snapshot := by
  let width := denseStepWidth program input snapshot
  let magnitude := programResourceMagnitude program
  let unit := denseResourceUnit magnitude input.length snapshot.overlay width
  let instruction := selectedInstruction program snapshot.pc
  let nextStore := denseInstructionStore input instruction snapshot.pc
    snapshot.overlay
  let instructionTime := denseProgramInstructionTime tapes program input
    snapshot.pc snapshot.overlay
  let cleanupBound := encodedStoreLength snapshot.overlay + 2 * width + 2
  have hunit : 1 ≤ unit := denseResourceUnit_pos magnitude input.length
    snapshot.overlay width
  have hvolume : encodedStoreLength snapshot.overlay + input.length + width + 1 ≤
      unit := denseResourceVolume_le_unit magnitude input.length snapshot.overlay
    width
  have hinstruction : instructionTime ≤ 7000000 * unit := by
    have htime := denseProgramInstructionTime_le_product tapes program input
      snapshot hvalid hpc
    simpa only [instructionTime, unit, width, magnitude] using! htime
  have hstatic : RegisterStore.Instr.staticWidth instruction ≤ width := by
    exact le_trans (selectedInstructionStaticWidth_le program snapshot.pc) (by
      unfold width denseStepWidth
      omega)
  have hselectedCost : instruction.logCost (snapshot.decode input) =
      RAM.stepLogCost program (snapshot.decode input) := by
    unfold instruction RAM.stepLogCost RAM.curInstr
    rw [selectedInstruction_eq_getElem?_getD]
    simp [DenseOverlay.Snapshot.decode]
  have hcost : instruction.logCost (snapshot.decode input) ≤ width := by
    rw [hselectedCost]
    unfold width denseStepWidth
    omega
  have hcleanupValues : ∀ slot,
      (denseInstructionCleanupValue input instruction snapshot.overlay slot).bits.length
        ≤ cleanupBound := by
    intro slot
    apply le_trans (denseInstructionCleanupValue_bits_le input instruction
      snapshot.pc snapshot.overlay width hstatic hcost slot)
    unfold cleanupBound
    omega
  have hremaining :
      (denseInstructionRemainingValue instruction snapshot.overlay).bits.length ≤
        cleanupBound := by
    apply le_trans (denseInstructionRemainingValue_bits_le instruction
      snapshot.overlay hvalid.1)
    unfold cleanupBound
    omega
  have hold : encodedStoreLength snapshot.overlay ≤ cleanupBound := by
    unfold cleanupBound
    omega
  have hnextRaw := DenseOverlay.Snapshot.encodedStoreLength_stepInstr_le input
    instruction snapshot
  have hnext : encodedStoreLength nextStore ≤ cleanupBound := by
    have hincrement : RegisterStore.Instr.staticWidth instruction +
        instruction.logCost (snapshot.decode input) + 1 ≤ width := by
      rw [hselectedCost]
      unfold width denseStepWidth
      have hselectedStatic := selectedInstructionStaticWidth_le program snapshot.pc
      change RegisterStore.Instr.staticWidth instruction ≤
        programStaticWidth program at hselectedStatic
      omega
    dsimp only [nextStore]
    unfold denseInstructionStore
    exact le_trans hnextRaw (by
      unfold cleanupBound
      omega)
  have hcleanup := bufferedCleanupTime_le_linear tapes snapshot.overlay nextStore
    (denseInstructionCleanupValue input instruction snapshot.overlay)
    (denseInstructionRemainingValue instruction snapshot.overlay)
    (denseProgramStepSourceHeadBound tapes program input snapshot.pc
      snapshot.overlay)
    cleanupBound (by
      unfold denseProgramStepSourceHeadBound
      omega)
    hcleanupValues hremaining hold hnext
  have hcleanupBoundUnit : cleanupBound ≤ 3 * unit := by
    unfold cleanupBound
    nlinarith
  have hcleanup' : bufferedCleanupTime tapes snapshot.overlay nextStore
      (denseInstructionCleanupValue input instruction snapshot.overlay)
      (denseInstructionRemainingValue instruction snapshot.overlay)
      (denseProgramStepSourceHeadBound tapes program input snapshot.pc
        snapshot.overlay) ≤
      800000000 * unit := by
    apply le_trans hcleanup
    unfold denseProgramStepSourceHeadBound
    dsimp only [instructionTime] at hinstruction ⊢
    nlinarith
  unfold denseProgramStepTime
  dsimp only [instruction, nextStore, instructionTime]
  apply le_trans (by omega : instructionTime + 1 +
      bufferedCleanupTime tapes snapshot.overlay nextStore
        (denseInstructionCleanupValue input instruction snapshot.overlay)
        (denseInstructionRemainingValue instruction snapshot.overlay)
        (denseProgramStepSourceHeadBound tapes program input snapshot.pc
          snapshot.overlay) ≤ 1000000000 * unit)
  apply le_of_eq
  dsimp only [unit, width, magnitude, denseResourceUnit, denseStepEnvelope,
    denseStepVolume]
  ring

private theorem denseSnapshot_step_pc_le_resourceMagnitude
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    (snapshot.step program input).pc ≤ programResourceMagnitude program := by
  by_cases hinRange : snapshot.pc < program.length
  · have hfallthrough : snapshot.pc + 1 ≤
        programResourceMagnitude program := by
      exact le_trans (by omega) (program_length_le_resourceMagnitude program)
    have hselected := selectedInstructionResourceMagnitude_le program snapshot.pc
    unfold DenseOverlay.Snapshot.step DenseOverlay.Snapshot.curInstr
    rw [← selectedInstruction_eq_getElem?_getD]
    generalize hinstruction : selectedInstruction program snapshot.pc = instruction
    rw [hinstruction] at hselected
    cases instruction <;>
      simp only [DenseOverlay.Snapshot.stepInstr,
        instructionResourceMagnitude] at hselected ⊢
    · exact hfallthrough
    · exact hfallthrough
    · exact hfallthrough
    · exact hfallthrough
    · exact hfallthrough
    · exact hfallthrough
    · split <;> dsimp only <;> omega
    · omega
    · exact hpc
  · have houtOfRange : program[snapshot.pc]? = none :=
      List.getElem?_eq_none (by omega)
    unfold DenseOverlay.Snapshot.step DenseOverlay.Snapshot.curInstr
    rw [houtOfRange]
    simpa [DenseOverlay.Snapshot.stepInstr] using! hpc

private theorem denseStepVolume_le_runScale_succ
    (program : Program) (input : List Bool) (fuel : ℕ)
    (snapshot : DenseOverlay.Snapshot) :
    denseStepVolume program input snapshot ≤
      denseRunScale program input (fuel + 1) snapshot := by
  have hhalted : snapshot.Halted program ↔
      RAM.Halted program (snapshot.decode input) := Iff.rfl
  by_cases hhalt : snapshot.Halted program
  · have hramHalt := hhalted.mp hhalt
    have hcost : RAM.stepLogCost program (snapshot.decode input) = 1 := by
      unfold RAM.stepLogCost RAM.curInstr
      change (snapshot.curInstr program).logCost (snapshot.decode input) = 1
      rw [hhalt]
      rfl
    unfold denseStepVolume denseStepWidth denseRunScale
    rw [RAM.unitTimeUpto_succ, ite_eq_left hramHalt,
      RAM.logTimeUpto_succ, ite_eq_left hramHalt]
    rw [hcost]
    nlinarith
  · have hramNotHalt : ¬RAM.Halted program (snapshot.decode input) :=
      fun h => hhalt (hhalted.mpr h)
    unfold denseStepVolume denseStepWidth denseRunScale
    rw [RAM.unitTimeUpto_succ, ite_eq_right hramNotHalt,
      RAM.logTimeUpto_succ, ite_eq_right hramNotHalt]
    nlinarith

private theorem denseRunScale_step_add_width_le
    (program : Program) (input : List Bool) (fuel : ℕ)
    (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay) :
    denseRunScale program input fuel (snapshot.step program input) +
        (denseStepWidth program input snapshot + 1) ≤
      denseRunScale program input (fuel + 1) snapshot := by
  have hhalted : snapshot.Halted program ↔
      RAM.Halted program (snapshot.decode input) := Iff.rfl
  by_cases hhalt : snapshot.Halted program
  · have hramHalt := hhalted.mp hhalt
    have hstep : snapshot.step program input = snapshot := by
      change snapshot.stepInstr input (snapshot.curInstr program) = snapshot
      rw [hhalt]
      rfl
    have hcost : RAM.stepLogCost program (snapshot.decode input) = 1 := by
      unfold RAM.stepLogCost RAM.curInstr
      change (snapshot.curInstr program).logCost (snapshot.decode input) = 1
      rw [hhalt]
      rfl
    rw [hstep]
    unfold denseRunScale denseStepWidth
    rw [RAM.unitTimeUpto_halted program hramHalt,
      RAM.logTimeUpto_halted program hramHalt]
    rw [hcost]
    nlinarith
  · have hramNotHalt : ¬RAM.Halted program (snapshot.decode input) :=
      fun h => hhalt (hhalted.mpr h)
    have hstore := DenseOverlay.Snapshot.encodedStoreLength_step_le
      program input snapshot
    have hdecode := DenseOverlay.Snapshot.decode_step program input snapshot
      hvalid.1
    unfold denseRunScale denseStepWidth
    rw [RAM.unitTimeUpto_succ, ite_eq_right hramNotHalt,
      RAM.logTimeUpto_succ, ite_eq_right hramNotHalt, hdecode]
    nlinarith

private theorem denseDispatchHaltTime_le_width {m : ℕ}
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

private theorem denseProgramHaltTime_le_magnitude {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (pcValue : ℕ) (hpc : pcValue ≤ programResourceMagnitude program) :
    programHaltTime tapes program pcValue ≤
      40 * (programResourceMagnitude program + 1) ^ 2 := by
  let magnitude := programResourceMagnitude program
  have hmagnitude : 1 ≤ magnitude := programResourceMagnitude_pos program
  have hpcSize : pcValue.size ≤ magnitude :=
    le_trans (size_le_self pcValue) hpc
  have hpcBits : pcValue.bits.length ≤ magnitude := by
    simpa only [Nat.size_eq_bits_len] using! hpcSize
  have hdispatch := denseDispatchHaltTime_le_width tapes program pcValue
    magnitude hmagnitude hpcBits
  have hcopyRaw := TM.binaryCopyTime_le pcValue 0
  have hcopy : TM.binaryCopyTime pcValue 0 ≤ 3 * magnitude + 20 := by
    apply le_trans hcopyRaw
    simp only [Nat.size_zero, Nat.mul_zero]
    omega
  have hlength := program_length_le_resourceMagnitude program
  unfold programHaltTime
  dsimp only [magnitude] at hmagnitude hdispatch hcopy ⊢
  nlinarith

private theorem denseProgramLoopIterationTime_le_product {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    denseProgramLoopIterationTime tapes program input snapshot ≤
      2000000000 * (programResourceMagnitude program + 1) ^ 2 *
        denseStepVolume program input snapshot *
        (denseStepWidth program input snapshot + 1) := by
  let magnitude := programResourceMagnitude program
  let volume := denseStepVolume program input snapshot
  let width := denseStepWidth program input snapshot
  let unit := (magnitude + 1) ^ 2 * volume * (width + 1)
  have hstep := denseProgramStepTime_le_envelope_internal tapes program input
    snapshot hvalid hpc
  have hnextPc := denseSnapshot_step_pc_le_resourceMagnitude program input
    snapshot hpc
  have hhalt := denseProgramHaltTime_le_magnitude tapes program
    (snapshot.step program input).pc hnextPc
  have hvolume : 1 ≤ volume := by
    unfold volume denseStepVolume
    omega
  have hwidth : 1 ≤ width + 1 := by omega
  have hfixed : (magnitude + 1) ^ 2 ≤ unit := by
    calc
      (magnitude + 1) ^ 2 = (magnitude + 1) ^ 2 * 1 * 1 := by ring
      _ ≤ (magnitude + 1) ^ 2 * volume * (width + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hvolume) hwidth
  unfold denseProgramLoopIterationTime
  dsimp only [magnitude, volume, width, unit] at hstep hhalt hfixed ⊢
  unfold denseStepEnvelope at hstep
  nlinarith
theorem denseProgramLoopTime_le_envelope_internal {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    denseProgramLoopTime tapes program input fuel snapshot ≤
      denseProgramLoopEnvelope program input fuel snapshot := by
  induction fuel generalizing snapshot with
  | zero =>
      simp [denseProgramLoopTime, denseProgramLoopEnvelope]
  | succ fuel ih =>
      let next := snapshot.step program input
      let fixed := 2000000000 * (programResourceMagnitude program + 1) ^ 2
      let volume := denseStepVolume program input snapshot
      let width := denseStepWidth program input snapshot
      let currentScale := denseRunScale program input (fuel + 1) snapshot
      let nextScale := denseRunScale program input fuel next
      have hiteration := denseProgramLoopIterationTime_le_product tapes program
        input snapshot hvalid hpc
      have hnextValid : DenseOverlay.Valid next.overlay := by
        dsimp only [next]
        exact DenseOverlay.Snapshot.step_valid program input snapshot hvalid
      have hnextPc : next.pc ≤ programResourceMagnitude program := by
        dsimp only [next]
        exact denseSnapshot_step_pc_le_resourceMagnitude program input snapshot hpc
      have htail := ih next hnextValid hnextPc
      have hvolume : volume ≤ currentScale := by
        dsimp only [volume, currentScale]
        exact denseStepVolume_le_runScale_succ program input fuel snapshot
      have hdrop : nextScale + (width + 1) ≤ currentScale := by
        dsimp only [nextScale, next, width, currentScale]
        exact denseRunScale_step_add_width_le program input fuel snapshot hvalid
      have hnextCurrent : nextScale ≤ currentScale := by omega
      have hvolumeProduct : volume * (width + 1) ≤
          currentScale * (width + 1) :=
        Nat.mul_le_mul_right (width + 1) hvolume
      have hnextSquare : nextScale * nextScale ≤
          currentScale * nextScale :=
        Nat.mul_le_mul_right nextScale hnextCurrent
      have hcurrentProduct :
          currentScale * (nextScale + (width + 1)) ≤
            currentScale * currentScale :=
        Nat.mul_le_mul_left currentScale hdrop
      have hquadratic : volume * (width + 1) + nextScale ^ 2 ≤
          currentScale ^ 2 := by
        nlinarith
      have hiteration' :
          denseProgramLoopIterationTime tapes program input snapshot ≤
            fixed * volume * (width + 1) := by
        simpa only [fixed, volume, width] using! hiteration
      have htail' : denseProgramLoopTime tapes program input fuel next ≤
          fixed * nextScale ^ 2 := by
        simpa only [denseProgramLoopEnvelope, fixed, nextScale] using! htail
      rw [denseProgramLoopTime]
      unfold denseProgramLoopEnvelope
      dsimp only [next, fixed, currentScale] at hiteration' htail' ⊢
      calc
        denseProgramLoopIterationTime tapes program input snapshot +
              denseProgramLoopTime tapes program input fuel
                (snapshot.step program input) ≤
            (2000000000 * (programResourceMagnitude program + 1) ^ 2) *
                volume * (width + 1) +
              (2000000000 * (programResourceMagnitude program + 1) ^ 2) *
                nextScale ^ 2 := Nat.add_le_add hiteration' htail'
        _ = (2000000000 * (programResourceMagnitude program + 1) ^ 2) *
              (volume * (width + 1) + nextScale ^ 2) := by ring
        _ ≤ (2000000000 * (programResourceMagnitude program + 1) ^ 2) *
              currentScale ^ 2 :=
            Nat.mul_le_mul_left _ hquadratic

private theorem denseInitialLengthLoopTime_le
    (address : ℕ) (input : List Bool) (bound : ℕ)
    (haddress : address + input.length ≤ bound) :
    denseInitialLengthLoopTime address input ≤
      (input.length + 1) * (2 * bound + 5) := by
  induction input generalizing address with
  | nil =>
      simp [denseInitialLengthLoopTime]
  | cons bit rest ih =>
      have haddressLe : address ≤ bound := by
        simp only [List.length_cons] at haddress
        omega
      have hsuccRaw := TM.binarySuccTime_le address
      have hsucc : TM.binarySuccTime address ≤ 2 * bound + 2 := by
        exact le_trans hsuccRaw (by
          have hsize := le_trans (size_le_self address) haddressLe
          omega)
      have htail := ih (address + 1) (by
        simp only [List.length_cons] at haddress
        omega)
      simp only [denseInitialLengthLoopTime, List.length_cons]
      rw [Nat.succ_add, Nat.succ_mul]
      omega

private theorem denseEntriesEncode_length_le (store : Store) (bound : ℕ)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound) :
    (store.flatMap Entry.encode).length ≤
      store.length * (4 * bound + 2) := by
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

private theorem denseInitialCleanupBits_le {m : ℕ}
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

private theorem denseInitialAbiInstallTime_le {m : ℕ}
    (tapes : ControlInstructionTapes m) (store : Store)
    (length bound : ℕ) (hbound : 1 ≤ bound)
    (hstoreLength : store.length ≤ bound)
    (hentries : ∀ entry ∈ store,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound)
    (hlength : length.bits.length ≤ bound) :
    initialAbiInstallTime tapes store length ≤ 100 * (bound + 1) ^ 2 := by
  let encoded := store.flatMap Entry.encode
  have hencodedBase := denseEntriesEncode_length_le store bound hentries
  have hencoded : encoded.length ≤ 6 * (bound + 1) ^ 2 := by
    dsimp only [encoded]
    have hfactor : 4 * bound + 2 ≤ 6 * (bound + 1) := by omega
    have hproduct := Nat.mul_le_mul hstoreLength hfactor
    exact le_trans hencodedBase (by nlinarith)
  have hcopyRaw := TM.binaryCopyTime_le store.length 0
  have hcopy : TM.binaryCopyTime store.length 0 ≤ 3 * bound + 20 := by
    apply le_trans hcopyRaw
    simp only [Nat.size_zero, Nat.mul_zero]
    have hsize := le_trans (size_le_self store.length) hstoreLength
    omega
  have hresetEncoded : TM.resetBinaryWorkTime (encoded.length + 1)
      encoded.length ≤ 3 * (6 * (bound + 1) ^ 2) + 9 := by
    unfold TM.resetBinaryWorkTime TM.clearWorkTimeBound
    omega
  have hresetMany := TM.resetBinaryWorkManyTime_le
    (initialCleanupTargets tapes) (initialCleanupBits tapes length)
    (fun _ => 1) 1 bound (fun _ _ => le_rfl)
    (fun i _ => denseInitialCleanupBits_le tapes length bound hlength hbound i)
  have htargets : (initialCleanupTargets tapes).length = 2 := by
    simp [initialCleanupTargets]
  rw [htargets] at hresetMany
  unfold initialAbiInstallTime
  dsimp only [encoded] at hencoded hresetEncoded ⊢
  have hboundSq : bound ≤ (bound + 1) ^ 2 := by nlinarith
  have honeSq : 1 ≤ (bound + 1) ^ 2 := by nlinarith
  nlinarith

private theorem denseRewindEntryEncodeRestoreTime_bound
    (entry : Entry) (bound : ℕ)
    (hbound : 1 ≤ bound) (haddress : entry.1.bits.length ≤ bound)
    (hvalue : entry.2.bits.length ≤ bound) :
    rewindEntryEncodeRestoreTime entry ≤ 30 * (bound + 1) := by
  unfold rewindEntryEncodeRestoreTime rewindEntryEncodeTime
    rewindWordEncodeTime wordEncodeTime
  have haddressSize : entry.1.size = entry.1.bits.length :=
    (Nat.size_eq_bits_len entry.1).symm
  have hvalueSize : entry.2.size = entry.2.bits.length :=
    (Nat.size_eq_bits_len entry.2).symm
  omega

private theorem denseProgramInitTime_le_quadratic {m : ℕ}
    (tapes : ControlInstructionTapes m) (input : List Bool) :
    denseProgramInitTime tapes input ≤ 1000 * (input.length + 3) ^ 2 := by
  let bound := input.length + 2
  have hbound : 1 ≤ bound := by simp [bound]
  have hloop := denseInitialLengthLoopTime_le 1 input (input.length + 1)
    (by omega)
  have htagBits : (input.length + 1).bits.length ≤ bound := by
    simpa only [Nat.size_eq_bits_len] using!
      (le_trans (size_le_self (input.length + 1)) (by
        dsimp only [bound]
        omega))
  have hrewind := denseRewindEntryEncodeRestoreTime_bound
    (0, input.length + 1) bound hbound (by simp) htagBits
  have hstoreLength : (denseProgramInitialStore input).length ≤ bound := by
    simp [denseProgramInitialStore, DenseOverlay.Snapshot.initial,
      DenseOverlay.write, RegisterStore.write, bound]
  have hentries : ∀ entry ∈ denseProgramInitialStore input,
      entry.1.bits.length ≤ bound ∧ entry.2.bits.length ≤ bound := by
    intro entry hentry
    simp [denseProgramInitialStore, DenseOverlay.Snapshot.initial,
      DenseOverlay.write, RegisterStore.write] at hentry
    subst entry
    exact ⟨by simp, htagBits⟩
  have habi := denseInitialAbiInstallTime_le tapes
    (denseProgramInitialStore input) (input.length + 1) bound hbound
    hstoreLength hentries htagBits
  have hsuccZero := TM.binarySuccTime_le 0
  have hsuccZero' : TM.binarySuccTime 0 ≤ 2 := by
    simpa using! hsuccZero
  unfold denseProgramInitTime
  dsimp only [bound] at hrewind habi htagBits hbound ⊢
  nlinarith

private theorem denseProgramOutputTime_le_encoded {m : ℕ}
    (tapes : ControlInstructionTapes m) (input : List Bool)
    (overlay : Store) (hvalid : DenseOverlay.Valid overlay) :
    denseProgramOutputTime tapes input overlay ≤
      2000000 * (encodedStoreLength overlay + input.length + 1) := by
  have hlookup := denseOverlayLookupStaticTime_le_product
    tapes.lifted.data.lhsLookup input.length overlay 0 0 0 hvalid
    (by simp [bitlen]) (by simp)
  unfold denseProgramOutputTime
  nlinarith

private theorem denseRunScale_initial_succ_le
    (program : Program) (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input)))
    (hfuel : fuel ≤
      RAM.logTimeUpto program fuel (RAM.initCfg input)) :
    denseRunScale program input (fuel + 1)
        (DenseOverlay.Snapshot.initial input) ≤
      10 * (programResourceMagnitude program + 1) *
        (input.length +
          RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) := by
  let initial := DenseOverlay.Snapshot.initial input
  let cost := RAM.logTimeUpto program fuel (RAM.initCfg input)
  let magnitude := programResourceMagnitude program
  have hdecode : initial.decode input = RAM.initCfg input := by
    simpa only [initial] using! DenseOverlay.Snapshot.initial_decode input
  have hhaltedInitial : RAM.Halted program
      (RAM.run program fuel (initial.decode input)) := by
    rw [hdecode]
    exact hhalted
  have hcostSucc :
      RAM.logTimeUpto program (fuel + 1) (initial.decode input) = cost := by
    have hsame := RAM.logTimeUpto_eq_of_halted_le program
      (Nat.le_succ fuel) hhaltedInitial
    calc
      RAM.logTimeUpto program (fuel + 1) (initial.decode input) =
          RAM.logTimeUpto program fuel (initial.decode input) := by
        simpa only [Nat.succ_eq_add_one] using! hsame
      _ = cost := by rw [hdecode]
  have hunit := RAM.unitTimeUpto_le_logTimeUpto program (fuel + 1)
    (initial.decode input)
  rw [hcostSucc] at hunit
  have hstatic := programStaticWidth_le_resourceMagnitude program
  have hmagnitude : 1 ≤ magnitude := by
    simpa only [magnitude] using! programResourceMagnitude_pos program
  have hencodedRaw := DenseOverlay.Snapshot.initial_encodedStoreLength_run_le
    program input 0
  have hencoded : encodedStoreLength initial.overlay ≤
      2 * bitlen (input.length + 1) + 2 := by
    simpa only [initial, DenseOverlay.Snapshot.run,
      RAM.unitTimeUpto_zero, RAM.logTimeUpto_zero, Nat.zero_mul,
      Nat.zero_add, Nat.mul_zero, Nat.add_zero] using! hencodedRaw
  have hbitlen : bitlen (input.length + 1) ≤ input.length + 1 :=
    size_le_self (input.length + 1)
  have htime : fuel + 1 +
      RAM.unitTimeUpto program (fuel + 1) (initial.decode input) ≤
        2 * cost + 1 := by
    dsimp only [cost] at hfuel ⊢
    omega
  have hstatic' : programStaticWidth program + 1 ≤ magnitude + 1 := by
    dsimp only [magnitude]
    omega
  have hproduct := Nat.mul_le_mul hstatic' htime
  unfold denseRunScale
  dsimp only [initial, cost, magnitude] at hcostSucc hencoded hbitlen hmagnitude hproduct ⊢
  rw [hcostSucc]
  nlinarith

private theorem denseFinalEncodedStoreLength_le
    (program : Program) (input : List Bool) (fuel : ℕ) :
    encodedStoreLength
        ((DenseOverlay.Snapshot.initial input).run program input fuel).overlay ≤
      6 * (programResourceMagnitude program + 1) *
        (input.length +
          RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) := by
  let cost := RAM.logTimeUpto program fuel (RAM.initCfg input)
  let magnitude := programResourceMagnitude program
  have hencoded := DenseOverlay.Snapshot.initial_encodedStoreLength_run_le
    program input fuel
  have hunit := RAM.unitTimeUpto_le_logTimeUpto program fuel
    (RAM.initCfg input)
  have hstatic := programStaticWidth_le_resourceMagnitude program
  have hbitlen : bitlen (input.length + 1) ≤ input.length + 1 :=
    size_le_self (input.length + 1)
  have hproduct :
      RAM.unitTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 1) ≤
        cost * (magnitude + 1) := by
    exact Nat.mul_le_mul hunit (by
      dsimp only [magnitude]
      omega)
  dsimp only [cost, magnitude] at hproduct ⊢
  nlinarith
theorem denseProgramDecisionTime_le_envelope_internal {m : ℕ}
    (tapes : ControlInstructionTapes m) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input)))
    (hfuel : fuel ≤
      RAM.logTimeUpto program fuel (RAM.initCfg input)) :
    denseProgramDecisionTime tapes program input fuel ≤
      denseProgramDecisionEnvelope program input.length
        (RAM.logTimeUpto program fuel (RAM.initCfg input)) := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  let cost := RAM.logTimeUpto program fuel (RAM.initCfg input)
  let magnitude := programResourceMagnitude program
  let scale := input.length + cost + 1
  let fixed := (magnitude + 1) ^ 4 * scale ^ 2
  have hmagnitude : 1 ≤ magnitude := by
    simpa only [magnitude] using! programResourceMagnitude_pos program
  have hscale : 1 ≤ scale := by
    dsimp only [scale]
    omega
  have hinitialValid : DenseOverlay.Valid initial.overlay := by
    simpa only [initial] using! DenseOverlay.Snapshot.initial_valid input
  have hinitialPc : initial.pc ≤ magnitude := by
    dsimp only [initial, DenseOverlay.Snapshot.initial, magnitude]
    omega
  have hloopRaw := denseProgramLoopTime_le_envelope_internal tapes program
    input (fuel + 1) initial hinitialValid hinitialPc
  have hrunScale := denseRunScale_initial_succ_le program input fuel
    hhalted hfuel
  have hloop : denseProgramLoopTime tapes program input (fuel + 1) initial ≤
      200000000000 * fixed := by
    apply le_trans hloopRaw
    unfold denseProgramLoopEnvelope
    have hsquare := Nat.pow_le_pow_left hrunScale 2
    dsimp only [initial, cost, magnitude, scale, fixed] at hsquare ⊢
    nlinarith
  have hinitRaw := denseProgramInitTime_le_quadratic tapes input
  have hinit : denseProgramInitTime tapes input ≤ 9000 * fixed := by
    apply le_trans hinitRaw
    have hlength : input.length + 3 ≤ 3 * scale := by
      dsimp only [scale]
      omega
    have hsquare := Nat.pow_le_pow_left hlength 2
    have hfixedOne : scale ^ 2 ≤ fixed := by
      dsimp only [fixed]
      have honePos : 0 < (magnitude + 1) ^ 4 := by positivity
      have hone : 1 ≤ (magnitude + 1) ^ 4 := by omega
      calc
        scale ^ 2 = 1 * scale ^ 2 := by simp
        _ ≤ (magnitude + 1) ^ 4 * scale ^ 2 :=
          Nat.mul_le_mul_right _ hone
    nlinarith
  have hfinalValid : DenseOverlay.Valid final.overlay := by
    dsimp only [final, initial]
    exact DenseOverlay.Snapshot.run_valid program input fuel
      (DenseOverlay.Snapshot.initial input)
        (DenseOverlay.Snapshot.initial_valid input)
  have houtputRaw := denseProgramOutputTime_le_encoded tapes input
    final.overlay hfinalValid
  have hfinalEncoded := denseFinalEncodedStoreLength_le program input fuel
  have houtput : denseProgramOutputTime tapes input final.overlay ≤
      20000000 * fixed := by
    apply le_trans houtputRaw
    have hvolume : encodedStoreLength final.overlay + input.length + 1 ≤
        7 * (magnitude + 1) * scale := by
      dsimp only [final, initial, cost, magnitude, scale] at hfinalEncoded ⊢
      nlinarith
    have hlinearFixed : (magnitude + 1) * scale ≤ fixed := by
      dsimp only [fixed]
      have hmagnitudePow : magnitude + 1 ≤ (magnitude + 1) ^ 4 := by
        exact Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) (magnitude + 1)
      have hscaleSq : scale ≤ scale ^ 2 := by
        exact Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) scale
      exact Nat.mul_le_mul hmagnitudePow hscaleSq
    nlinarith
  unfold denseProgramDecisionTime denseProgramDecisionEnvelope
  dsimp only [initial, final, cost, magnitude, scale, fixed] at hloop hinit houtput ⊢
  have hfixedPos : 1 ≤
      (programResourceMagnitude program + 1) ^ 4 *
        (input.length +
          RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) ^ 2 := by
    have hpos : 0 <
        (programResourceMagnitude program + 1) ^ 4 *
          (input.length +
            RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) ^ 2 := by
      positivity
    omega
  nlinarith
end Machine
end RegisterStore
end RAM
end Complexity

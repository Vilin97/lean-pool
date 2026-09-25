/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineGreedyRowMatching
public import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateAssembly

/-!
# Counting the selected pairs and assembling the fixed matching gain

The matching machine returns a self-delimiting list of ordered endpoint pairs.
This module counts that list with a verified binary counter and multiplies the
count by the fixed rational gain.  The counter iterates for the bit-length of
the input word and stutters after the encoded list is exhausted, so it is a
total polynomial-time string function even on malformed inputs.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Encodes a list-count state as remaining list, binary counter, and source word. -/
def machineListCountPack
    (remaining counter source : List Bool) : List Bool :=
  pair remaining (pair counter source)

/-- Extracts the unprocessed list suffix from the counting state. -/
def machineListCountRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the binary count from the list-count state. -/
def machineListCountCounter (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the original encoded list from the counting state. -/
def machineListCountSource (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

/-- Pairs a false bit with the source list to provide a count-state width bound. -/
def machineListCountInputBound (word : List Bool) : List Bool :=
  pair [false] word

/-- Reads the count-state bound derived from the original list. -/
def machineListCountBound (state : List Bool) : List Bool :=
  machineListCountInputBound (machineListCountSource state)

/-- Increments the binary count and truncates it to the source-derived width bound. -/
def machineListCountNextCounter (state : List Bool) : List Bool :=
  (machineBinaryAddBits
      (pair (machineListCountCounter state) [true])).take
    (machineListCountBound state).length

/-- Consumes one encoded list entry and updates the bounded count. -/
def machineListCountProcess (state : List Bool) : List Bool :=
  machineListCountPack
    (machineListTail (machineListCountRemaining state))
    (machineListCountNextCounter state)
    (machineListCountSource state)

/-- Counts the next entry, leaving an exhausted list-count state fixed. -/
def machineListCountStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineListCountRemaining state) state
    (machineListCountProcess state)

/-- Initializes list counting with the entire input list and a zero counter. -/
def machineListCountInit (word : List Bool) : List Bool :=
  machineListCountPack word [] word

/-- Packs three copies of the source-derived bound to bound the full counting state. -/
def machineListCountWidth (word : List Bool) : List Bool :=
  let bound := machineListCountInputBound word
  machineListCountPack bound bound bound

/-- Counts encoded list entries using at most one step per input bit and returns the binary
count. -/
def machineEncodedListLengthBits (word : List Bool) : List Bool :=
  machineListCountCounter
    ((machineListCountStep)^[word.length] (machineListCountInit word))

theorem machineListCountRemaining_mem_FP :
    machineListCountRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineListCountCounter_mem_FP :
    machineListCountCounter ∈ FP := by
  simpa only [machineListCountCounter] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineListCountSource_mem_FP :
    machineListCountSource ∈ FP := by
  simpa only [machineListCountSource] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineListCountInputBound_mem_FP :
    machineListCountInputBound ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP

theorem machineListCountBound_mem_FP :
    machineListCountBound ∈ FP := by
  simpa only [machineListCountBound] using! machineCompose_mem_FP
    machineListCountSource_mem_FP machineListCountInputBound_mem_FP

theorem machineListCountNextCounter_mem_FP :
    machineListCountNextCounter ∈ FP := by
  have hinput := machinePair_mem_FP machineListCountCounter_mem_FP
    (machineConst_mem_FP [true])
  have hadd := machineCompose_mem_FP hinput machineBinaryAddBits_mem_FP
  simpa only [machineListCountNextCounter] using!
    machineTake_mem_FP machineListCountBound_mem_FP hadd

theorem machineListCountProcess_mem_FP :
    machineListCountProcess ∈ FP := by
  have htail := machineCompose_mem_FP machineListCountRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineListCountNextCounter_mem_FP
      machineListCountSource_mem_FP)

theorem machineListCountStep_mem_FP :
    machineListCountStep ∈ FP := by
  simpa only [machineListCountStep] using! machineIfEmpty_mem_FP
    machineListCountRemaining_mem_FP id_mem_FP machineListCountProcess_mem_FP

theorem machineListCountInit_mem_FP :
    machineListCountInit ∈ FP :=
  machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP []) id_mem_FP)

theorem machineListCountWidth_mem_FP :
    machineListCountWidth ∈ FP :=
  machinePair_mem_FP machineListCountInputBound_mem_FP
    (machinePair_mem_FP machineListCountInputBound_mem_FP
      machineListCountInputBound_mem_FP)

@[simp] theorem machineListCountRemaining_pack (remaining counter source) :
    machineListCountRemaining
        (machineListCountPack remaining counter source) = remaining := by
  simp [machineListCountRemaining, machineListCountPack]

@[simp] theorem machineListCountCounter_pack (remaining counter source) :
    machineListCountCounter
        (machineListCountPack remaining counter source) = counter := by
  simp [machineListCountCounter, machineListCountPack]

@[simp] theorem machineListCountSource_pack (remaining counter source) :
    machineListCountSource
        (machineListCountPack remaining counter source) = source := by
  simp [machineListCountSource, machineListCountPack]

/-- Bounds the remaining-list and counter lengths while preserving the original encoded list. -/
def MachineListCountStateBound (word state : List Bool) : Prop :=
  let B := (machineListCountInputBound word).length
  state = machineListCountPack (machineListCountRemaining state)
      (machineListCountCounter state) (machineListCountSource state) ∧
    (machineListCountRemaining state).length ≤ B ∧
    (machineListCountCounter state).length ≤ B ∧
    machineListCountSource state = word

theorem machineListCount_word_le_bound (word : List Bool) :
    word.length ≤ (machineListCountInputBound word).length := by
  simp [machineListCountInputBound, pair_length]

theorem machineListCountInit_bound (word : List Bool) :
    MachineListCountStateBound word (machineListCountInit word) := by
  simp only [MachineListCountStateBound, machineListCountInit,
    machineListCountRemaining_pack, machineListCountCounter_pack,
    machineListCountSource_pack, List.length_nil]
  exact ⟨trivial, machineListCount_word_le_bound word,
    Nat.zero_le _, trivial⟩

theorem machineListCountStep_bound {word state : List Bool}
    (hstate : MachineListCountStateBound word state) :
    MachineListCountStateBound word (machineListCountStep state) := by
  rcases hstate with ⟨hpack, hremaining, hcounter, hsource⟩
  by_cases hrem : machineListCountRemaining state = []
  · rw [machineListCountStep, hrem, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hcounter, hsource⟩
  · rw [machineListCountStep]
    cases hcode : machineListCountRemaining state with
    | nil => exact False.elim (hrem hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineListCountProcess]
        simp only [MachineListCountStateBound,
          machineListCountRemaining_pack, machineListCountCounter_pack,
          machineListCountSource_pack]
        refine ⟨trivial, ?_, ?_, hsource⟩
        · exact (machinePairSecond_length_le
            (machineListCountRemaining state)).trans hremaining
        · simp only [machineListCountNextCounter, List.length_take,
            machineListCountBound, hsource]
          exact Nat.min_le_left _ _

theorem machineListCountIterate_bound (word : List Bool) : ∀ k,
    MachineListCountStateBound word
      ((machineListCountStep)^[k] (machineListCountInit word)) := by
  intro k
  induction k with
  | zero => exact machineListCountInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineListCountStep_bound ih

theorem machineListCountIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineListCountStep)^[iterations]
        (machineListCountInit word)).length ≤
      (machineListCountWidth word).length := by
  rcases machineListCountIterate_bound word iterations with
    ⟨hpack, hremaining, hcounter, hsource⟩
  have hsourceLength : (machineListCountSource
      ((machineListCountStep)^[iterations]
        (machineListCountInit word))).length ≤
      (machineListCountInputBound word).length := by
    rw [hsource]
    exact machineListCount_word_le_bound word
  rw [hpack]
  simp only [machineListCountPack, machineListCountWidth, pair_length]
  omega

theorem machineEncodedListLengthBits_mem_FP :
    machineEncodedListLengthBits ∈ FP := by
  have hfinal : (fun word =>
      (machineListCountStep)^[word.length]
        (machineListCountInit word)) ∈ FP :=
    Cobham.iterate_mem_FP machineListCountStep_mem_FP
      machineListCountInit_mem_FP id_mem_FP machineListCountWidth_mem_FP
      machineListCountIterate_length_le_width
  simpa only [machineEncodedListLengthBits] using! machineCompose_mem_FP
    hfinal machineListCountCounter_mem_FP

/-! ## Exact counting semantics -/

/-- Encodes a counting state with suffix `xs.drop k`, counter `k`, and the original list. -/
def machineListCountSemanticState {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha) (k : ℕ) : List Bool :=
  machineListCountPack (binaryListCode encode (xs.drop k)) k.bits
    (binaryListCode encode xs)

@[simp] theorem machineListCountSemanticState_zero {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha) :
    machineListCountSemanticState encode xs 0 =
      machineListCountInit (binaryListCode encode xs) := by
  simp [machineListCountSemanticState, machineListCountInit,
    binaryListCode]

theorem nat_succ_bits_length_le_succ (k : ℕ) :
    (k + 1).bits.length ≤ k + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact Nat.lt_two_pow_self

theorem machineListCountSemanticState_step {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha)
    (k : ℕ) (hk : k < xs.length) :
    machineListCountStep (machineListCountSemanticState encode xs k) =
      machineListCountSemanticState encode xs (k + 1) := by
  rw [machineListCountSemanticState, List.drop_eq_getElem_cons hk,
    machineListCountStep]
  simp only [machineListCountRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil encode xs[k] (xs.drop (k + 1))),
    machineListCountProcess]
  simp only [machineListCountRemaining_pack, machineListTail_cons,
    machineListCountSource_pack, machineListCountNextCounter,
    machineListCountCounter_pack]
  have hadd : machineBinaryAddBits (pair k.bits [true]) = (k + 1).bits := by
    simpa using! machineBinaryAddBits_pair_natBits k 1
  rw [hadd]
  have hbits : (k + 1).bits.length ≤
      (machineListCountInputBound (binaryListCode encode xs)).length := by
    calc
      _ ≤ k + 1 := nat_succ_bits_length_le_succ k
      _ ≤ xs.length := by omega
      _ ≤ (binaryListCode encode xs).length :=
        binaryListCode_listLength_le encode xs
      _ ≤ _ := machineListCount_word_le_bound _
  rw [machineListCountBound, machineListCountSource_pack,
    (List.take_eq_self_iff _).2 hbits]
  rw [machineListCountSemanticState]

theorem machineListCountIterate_semantics {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha) : ∀ k ≤ xs.length,
    (machineListCountStep)^[k]
        (machineListCountInit (binaryListCode encode xs)) =
      machineListCountSemanticState encode xs k := by
  intro k hk
  induction k with
  | zero => exact (machineListCountSemanticState_zero encode xs).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineListCountSemanticState_step encode xs k (by omega)

theorem machineListCount_done_iterate
    (extra : ℕ) (counter source : List Bool) :
    (machineListCountStep)^[extra]
        (machineListCountPack [] counter source) =
      machineListCountPack [] counter source := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineListCountStep]

@[simp] theorem machineEncodedListLengthBits_encode {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha) :
    machineEncodedListLengthBits (binaryListCode encode xs) = xs.length.bits := by
  rw [machineEncodedListLengthBits]
  let word := binaryListCode encode xs
  have hle : xs.length ≤ word.length :=
    binaryListCode_listLength_le encode xs
  have hsplit : word.length = (word.length - xs.length) + xs.length := by
    omega
  rw [hsplit, Function.iterate_add_apply,
    machineListCountIterate_semantics encode xs xs.length le_rfl]
  simp only [machineListCountSemanticState, List.drop_length]
  change machineListCountCounter
      ((machineListCountStep)^[word.length - xs.length]
        (machineListCountPack [] xs.length.bits
          (binaryListCode encode xs))) = xs.length.bits
  rw [machineListCount_done_iterate]
  simp only [machineListCountCounter_pack]

/-! ## Fixed-gain assembly -/

/-- Encodes the computed list length as a nonnegative raw rational with denominator one. -/
def machineListCountRawNatCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode (machineEncodedListLengthBits word)) [true]

/-- The raw-rational representation of the fixed matching-gain coefficient `explicitGamma`. -/
def rawExplicitGamma : RawRat := rawRatOfRat explicitGamma

/-- Multiplies the selected-pair count by `explicitGamma` and normalizes the resulting rational
entry. -/
def machineMatchingGainFromSelected (selectedWord : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRawRatMulCode
      (pair (rawRatBinaryCode rawExplicitGamma)
        (machineListCountRawNatCode selectedWord)))

/-- Computes the explicit matching gain from the greedy selection in the input's second
component. -/
def machineExplicitMatchingGainRawCode (word : List Bool) : List Bool :=
  machineMatchingGainFromSelected
    (machineGreedyMatchingSelected (machinePairSecond word))

theorem machineListCountRawNatCode_mem_FP :
    machineListCountRawNatCode ∈ FP := by
  have hnum := machineCompose_mem_FP machineEncodedListLengthBits_mem_FP
    machineNaturalIntegerCode_mem_FP
  exact machinePair_mem_FP hnum (machineConst_mem_FP [true])

theorem machineMatchingGainFromSelected_mem_FP :
    machineMatchingGainFromSelected ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawExplicitGamma))
    machineListCountRawNatCode_mem_FP
  have hmul := machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP
  simpa only [machineMatchingGainFromSelected] using!
    machineCompose_mem_FP hmul machineNormalizeRawRatEntryCode_mem_FP

theorem machineExplicitMatchingGainRawCode_mem_FP :
    machineExplicitMatchingGainRawCode ∈ FP := by
  have hselected := machineCompose_mem_FP machinePairSecond_mem_FP
    machineGreedyMatchingSelected_mem_FP
  simpa only [machineExplicitMatchingGainRawCode] using! machineCompose_mem_FP
    hselected machineMatchingGainFromSelected_mem_FP

@[simp] theorem machineListCountRawNatCode_encode {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha) :
    machineListCountRawNatCode (binaryListCode encode xs) =
      rawRatBinaryCode (RawRat.ofNat xs.length) := by
  rw [machineListCountRawNatCode,
    machineEncodedListLengthBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [rawRatBinaryCode, RawRat.ofNat]

@[simp] theorem machineMatchingGainFromSelected_encode {alpha : Type*}
    (encode : alpha → List Bool) (xs : List alpha) :
    machineMatchingGainFromSelected (binaryListCode encode xs) =
      rawRatBinaryCode (rawRatOfRat
        (explicitGamma * (xs.length : ℚ))) := by
  rw [machineMatchingGainFromSelected,
    machineListCountRawNatCode_encode, machineRawRatMulCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    ← rawRatBinaryCode_rawRatOfRat]
  apply congrArg rawRatBinaryCode
  apply congrArg rawRatOfRat
  rw [binaryNormalizeRawRat_eq_value, RawRat.value_mul,
    rawExplicitGamma, rawRatOfRat_value, RawRat.value_ofNat]

theorem explicitCertifiedMatchingGain_eq_typed_length {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    explicitCertifiedMatchingGain X =
      explicitGamma *
        (certifiedGreedyTypedOuterScan X []
          (List.finRange n).reverse).length := by
  let selected := certifiedGreedyTypedOuterScan X []
    (List.finRange n).reverse
  have hfin := certifiedGreedyTypedOuterScan_toFinset X
  have hnodup := certifiedGreedyTypedOuterScan_full_nodup X
  rw [explicitCertifiedMatchingGain, greedyCertifiedMatchingGain]
  rw [← hfin]
  have hweight : ∀ q ∈ selected.toFinset,
      explicitCertifiedRowWeight X q = explicitGamma := by
    intro q hq
    have hqmatching : q ∈ greedyThresholdRowMatching
        (explicitCertifiedRowWeight X) explicitGamma := by
      rw [← hfin]
      exact hq
    have hmax := greedyThresholdRowMatching_isMaximal
      (explicitCertifiedRowWeight X) explicitGamma
    have hthreshold : explicitGamma ≤ explicitCertifiedRowWeight X q := by
      have hmem := hmax.subset hqmatching
      simpa only [List.mem_toFinset, mem_thresholdRowPairsList_iff] using! hmem
    exact certifiedConstantRowWeight_eq_gamma_of_threshold
      (explicitRegularizationScale n) X explicitKappa explicitGamma
      (directedPairCostPrecision n) q explicitGamma_pos hthreshold
  calc
    ∑ q ∈ selected.toFinset, explicitCertifiedRowWeight X q =
        ∑ _q ∈ selected.toFinset, explicitGamma := by
          exact Finset.sum_congr rfl hweight
    _ = selected.toFinset.card * explicitGamma := by simp
    _ = explicitGamma * selected.length := by
      rw [List.toFinset_card_of_nodup hnodup]
      ring

@[simp] theorem machineExplicitMatchingGainRawCode_encode
    (source : List Bool) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineExplicitMatchingGainRawCode
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode (rawRatOfRat (explicitCertifiedMatchingGain X)) := by
  rw [machineExplicitMatchingGainRawCode, machinePairSecond_pair,
    machineGreedyMatchingSelected_typed_encode,
    machineMatchingGainFromSelected_encode]
  simp only [List.length_map]
  rw [explicitCertifiedMatchingGain_eq_typed_length]

theorem machineExplicitMatchingGainRawCode_realizes :
    OptimizerMatchingGainStringRealizes machineExplicitMatchingGainRawCode := by
  intro m B
  simpa only [explicitLargeOptimizerOutput] using!
    machineExplicitMatchingGainRawCode_encode
      (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
      (explicitBetheOptimizerMatrix (m := m + 1) B)
      (explicitBetheOptimizerRowPotential (m := m + 1) B)
      (explicitBetheOptimizerColumnPotential (m := m + 1) B)

end BeyondBethe

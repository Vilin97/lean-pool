/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryAddSemantics
public import LeanPool.BeyondBethe.BeyondBethe.MachineRAMBridge

/-!
# Assembling a polynomial number of queried output bits

This file turns any one-bit `FP` query routine into a full output routine.  At
iteration `k`, the state stores `k.bits`, the first `k` queried bits, and the
unchanged original input.  A verified binary addition increments the counter.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Query bit `k`, represented by the canonical paired input
`pair k.bits word`.  Truncating to `machineHeadBit` guarantees one output bit
even on malformed inputs or for a total query function with arbitrary output. -/
def machineQueriedBit (query : List Bool → List Bool)
    (counter word : List Bool) : List Bool :=
  machineHeadBit (query (pair counter word))

/-- Package the binary query counter, accumulated output bits, and immutable input word. -/
def machineBitAssemblyPack
    (counter acc word : List Bool) : List Bool :=
  pair counter (pair acc word)

/-- Extract the binary query-position counter from the assembly state. -/
def machineBitAssemblyCounter (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extract the output bits already assembled. -/
def machineBitAssemblyAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extract the immutable input supplied to each output-bit query. -/
def machineBitAssemblyInput (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

/-- Increment the assembly state's binary query counter by one. -/
def machineBitAssemblyNextCounter (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineBitAssemblyCounter state) [true])

/-- Append the queried output bit at the current counter, increment the counter, and retain the
original input. -/
def machineBitAssemblyStep (query : List Bool → List Bool)
    (state : List Bool) : List Bool :=
  machineBitAssemblyPack
    (machineBitAssemblyNextCounter state)
    (machineBitAssemblyAcc state ++
      machineQueriedBit query (machineBitAssemblyCounter state)
        (machineBitAssemblyInput state))
    (machineBitAssemblyInput state)

/-- Initialize bit assembly at counter zero with an empty output accumulator. -/
def machineBitAssemblyInit (word : List Bool) : List Bool :=
  machineBitAssemblyPack [] [] word

/-- A state with two ruler-sized fields is an exact length envelope for every
semantic assembly state before the ruler is exhausted. -/
def machineBitAssemblyWidth (ruler : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineBitAssemblyPack (ruler word) (ruler word) word

/-- Run bit assembly for the number of positions specified by the ruler's length. -/
def machineBitAssemblyFinalState
    (query ruler : List Bool → List Bool) (word : List Bool) : List Bool :=
  (machineBitAssemblyStep query)^[(ruler word).length]
    (machineBitAssemblyInit word)

/-- Return the accumulated output bits after all ruler-bounded queries. -/
def machineAssembleBits
    (query ruler : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineBitAssemblyAcc (machineBitAssemblyFinalState query ruler word)

theorem machineBitAssemblyCounter_mem_FP :
    machineBitAssemblyCounter ∈ Complexity.FP := by
  simpa only [machineBitAssemblyCounter] using! machinePairFirst_mem_FP

theorem machineBitAssemblyAcc_mem_FP :
    machineBitAssemblyAcc ∈ Complexity.FP := by
  simpa only [machineBitAssemblyAcc] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBitAssemblyInput_mem_FP :
    machineBitAssemblyInput ∈ Complexity.FP := by
  simpa only [machineBitAssemblyInput] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineQueriedBit_mem_FP
    {query counter word : List Bool → List Bool}
    (hquery : query ∈ Complexity.FP)
    (hcounter : counter ∈ Complexity.FP)
    (hword : word ∈ Complexity.FP) :
    (fun input => machineQueriedBit query (counter input) (word input)) ∈
      Complexity.FP := by
  have hpayload :
      (fun input => pair (counter input) (word input)) ∈ Complexity.FP :=
    machinePair_mem_FP hcounter hword
  exact machineCompose_mem_FP
    (machineCompose_mem_FP hpayload hquery) machineHeadBit_mem_FP

theorem machineBitAssemblyNextCounter_mem_FP :
    machineBitAssemblyNextCounter ∈ Complexity.FP := by
  have hpayload :
      (fun state => pair (machineBitAssemblyCounter state) [true]) ∈
        Complexity.FP :=
    machinePair_mem_FP machineBitAssemblyCounter_mem_FP
      (machineConst_mem_FP [true])
  simpa only [machineBitAssemblyNextCounter] using!
    machineCompose_mem_FP hpayload machineBinaryAddBits_mem_FP

theorem machineBitAssemblyStep_mem_FP
    {query : List Bool → List Bool} (hquery : query ∈ Complexity.FP) :
    machineBitAssemblyStep query ∈ Complexity.FP := by
  have hbit :
      (fun state => machineQueriedBit query
        (machineBitAssemblyCounter state)
        (machineBitAssemblyInput state)) ∈ Complexity.FP :=
    machineQueriedBit_mem_FP hquery machineBitAssemblyCounter_mem_FP
      machineBitAssemblyInput_mem_FP
  have hacc :
      (fun state => machineBitAssemblyAcc state ++
        machineQueriedBit query (machineBitAssemblyCounter state)
          (machineBitAssemblyInput state)) ∈ Complexity.FP :=
    machineAppend_mem_FP machineBitAssemblyAcc_mem_FP hbit
  exact machinePair_mem_FP machineBitAssemblyNextCounter_mem_FP
    (machinePair_mem_FP hacc machineBitAssemblyInput_mem_FP)

theorem machineBitAssemblyInit_mem_FP :
    machineBitAssemblyInit ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP (machineConst_mem_FP []) id_mem_FP)

theorem machineBitAssemblyWidth_mem_FP
    {ruler : List Bool → List Bool} (hruler : ruler ∈ Complexity.FP) :
    machineBitAssemblyWidth ruler ∈ Complexity.FP := by
  exact machinePair_mem_FP hruler (machinePair_mem_FP hruler id_mem_FP)

@[simp] theorem machineBitAssemblyCounter_pack (counter acc word) :
    machineBitAssemblyCounter (machineBitAssemblyPack counter acc word) =
      counter := by
  simp [machineBitAssemblyCounter, machineBitAssemblyPack]

@[simp] theorem machineBitAssemblyAcc_pack (counter acc word) :
    machineBitAssemblyAcc (machineBitAssemblyPack counter acc word) = acc := by
  simp [machineBitAssemblyAcc, machineBitAssemblyPack]

@[simp] theorem machineBitAssemblyInput_pack (counter acc word) :
    machineBitAssemblyInput (machineBitAssemblyPack counter acc word) = word := by
  simp [machineBitAssemblyInput, machineBitAssemblyPack]

/-- The semantic list of the first `iterations` queried bits. -/
def assembledQueryBits (query : List Bool → List Bool)
    (word : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => assembledQueryBits query word k ++
      machineHeadBit (query (pair k.bits word))

@[simp] theorem assembledQueryBits_length
    (query : List Bool → List Bool) (word : List Bool) :
    ∀ k, (assembledQueryBits query word k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [assembledQueryBits, ih]

theorem natBits_length_le_self (k : ℕ) : k.bits.length ≤ k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr k.lt_two_pow_self

@[simp] theorem machineBitAssemblyStep_semantics
    (query : List Bool → List Bool) (word : List Bool) (k : ℕ) :
    machineBitAssemblyStep query
        (machineBitAssemblyPack k.bits
          (assembledQueryBits query word k) word) =
      machineBitAssemblyPack (k + 1).bits
        (assembledQueryBits query word (k + 1)) word := by
  simp only [machineBitAssemblyStep, machineBitAssemblyNextCounter,
    machineBitAssemblyCounter_pack, machineBitAssemblyAcc_pack,
    machineQueriedBit, machineBitAssemblyInput_pack, assembledQueryBits]
  rw [show ([true] : List Bool) = (1 : ℕ).bits by decide,
    machineBinaryAddBits_pair_natBits]

theorem machineBitAssemblyIterate_semantics
    (query : List Bool → List Bool) (word : List Bool) :
    ∀ k,
      (machineBitAssemblyStep query)^[k] (machineBitAssemblyInit word) =
        machineBitAssemblyPack k.bits
          (assembledQueryBits query word k) word := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        machineBitAssemblyStep_semantics]

theorem machineBitAssemblyIterate_length_le_width
    (query ruler : List Bool → List Bool) (word : List Bool)
    (iterations : ℕ) (hiterations : iterations ≤ (ruler word).length) :
    ((machineBitAssemblyStep query)^[iterations]
      (machineBitAssemblyInit word)).length ≤
        (machineBitAssemblyWidth ruler word).length := by
  rw [machineBitAssemblyIterate_semantics]
  simp only [machineBitAssemblyPack, pair_length]
  have hcounter := natBits_length_le_self iterations
  have hacc := assembledQueryBits_length query word iterations
  simp only [machineBitAssemblyWidth, machineBitAssemblyPack, pair_length]
  omega

theorem machineBitAssemblyFinalState_mem_FP
    {query ruler : List Bool → List Bool}
    (hquery : query ∈ Complexity.FP) (hruler : ruler ∈ Complexity.FP) :
    machineBitAssemblyFinalState query ruler ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP (machineBitAssemblyStep_mem_FP hquery)
    machineBitAssemblyInit_mem_FP hruler
    (machineBitAssemblyWidth_mem_FP hruler)
    (machineBitAssemblyIterate_length_le_width query ruler)

theorem machineAssembleBits_mem_FP
    {query ruler : List Bool → List Bool}
    (hquery : query ∈ Complexity.FP) (hruler : ruler ∈ Complexity.FP) :
    machineAssembleBits query ruler ∈ Complexity.FP := by
  simpa only [machineAssembleBits] using!
    machineCompose_mem_FP
      (machineBitAssemblyFinalState_mem_FP hquery hruler)
      machineBitAssemblyAcc_mem_FP

theorem machineAssembleBits_eq
    (query ruler : List Bool → List Bool) (word : List Bool) :
    machineAssembleBits query ruler word =
      assembledQueryBits query word (ruler word).length := by
  simp [machineAssembleBits, machineBitAssemblyFinalState,
    machineBitAssemblyIterate_semantics]

theorem assembledQueryBits_eq_take
    (query target : List Bool → List Bool)
    (hquery : ∀ word k, k < (target word).length →
      query (pair k.bits word) = [(target word)[k]?.getD false]) :
    ∀ word k, k ≤ (target word).length →
      assembledQueryBits query word k = (target word).take k := by
  intro word k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      have hklt : k < (target word).length := by omega
      rw [assembledQueryBits, ih (by omega), hquery word k hklt]
      simp only [machineHeadBit_cons]
      rw [List.getElem?_eq_getElem hklt]
      simp only [Option.getD_some]
      exact (List.take_succ_eq_append_getElem hklt).symm

/-- Exact bit queries assembled for exactly the target length reproduce the
target word, including internal and trailing zero bits. -/
theorem machineAssembleBits_realizes
    (query ruler target : List Bool → List Bool)
    (hruler : ∀ word, (ruler word).length = (target word).length)
    (hquery : ∀ word k, k < (target word).length →
      query (pair k.bits word) = [(target word)[k]?.getD false]) :
    machineAssembleBits query ruler = target := by
  funext word
  rw [machineAssembleBits_eq, hruler,
    assembledQueryBits_eq_take query target hquery word
      (target word).length le_rfl,
    List.take_length]

/-- The bit graph of a total string function, expressed using canonical
pairing and little-endian natural indices. -/
def outputBitLanguage (target : List Bool → List Bool) : Language :=
  {payload | (target (machinePairSecond payload))[
      Nat.fromBitsLE (machinePairFirst payload)]?.getD false = true}

instance outputBitLanguage_decidable (target : List Bool → List Bool) :
    DecidablePred (fun word => word ∈ outputBitLanguage target) := by
  intro word
  change Decidable
    ((target (machinePairSecond word))[
      Nat.fromBitsLE (machinePairFirst word)]?.getD false = true)
  infer_instance

theorem outputBitLanguage_flag_pair_all
    (target : List Bool → List Bool) (word : List Bool) (k : ℕ) :
    MachineRAMBridge.languageFlag (outputBitLanguage target)
        (pair k.bits word) = [(target word)[k]?.getD false] := by
  simp only [MachineRAMBridge.languageFlag, outputBitLanguage,
    machinePairFirst_pair, machinePairSecond_pair, Nat.fromBitsLE_bits,
    Set.mem_setOf_eq]
  cases hbit : (target word)[k]? with
  | none => simp [hbit]
  | some bit => cases bit <;> simp [hbit]

theorem outputBitLanguage_flag_pair
    (target : List Bool → List Bool) (word : List Bool) (k : ℕ)
    (_hk : k < (target word).length) :
    MachineRAMBridge.languageFlag (outputBitLanguage target)
        (pair k.bits word) = [(target word)[k]?.getD false] :=
  outputBitLanguage_flag_pair_all target word k

/-- A polynomial-time RAM decider for the bit graph, together with an `FP`
ruler of the exact output length, yields an unconditional `FP` implementation
of the whole string function. -/
theorem target_mem_FP_of_ramBitProgram
    (target ruler : List Bool → List Bool)
    (program : RAM.Program) (p : Polynomial ℕ)
    (hdecides : program.DecidesInTime (outputBitLanguage target) p.eval)
    (hrulerFP : ruler ∈ Complexity.FP)
    (hrulerLength : ∀ word,
      (ruler word).length = (target word).length) :
    target ∈ Complexity.FP := by
  let query := MachineRAMBridge.languageFlag (outputBitLanguage target)
  have hqueryFP : query ∈ Complexity.FP :=
    MachineRAMBridge.languageFlag_mem_FP_of_ramProgram program p hdecides
  have hassembly : machineAssembleBits query ruler ∈ Complexity.FP :=
    machineAssembleBits_mem_FP hqueryFP hrulerFP
  have heq : machineAssembleBits query ruler = target :=
    machineAssembleBits_realizes query ruler target hrulerLength
      (outputBitLanguage_flag_pair target)
  rwa [heq] at hassembly

end BeyondBethe

/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorCutEntry
public import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryGridGenerator
public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryListSnoc

/-!
# Finite-word Bethe floor-cut vectors

The floor scan identifies a recovered matrix coordinate `(i,j)`.  This file
uses the common row-major grid generator to construct all `m^2` coefficients
of its affine pullback, then appends the zero epigraph-height coefficient.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Adapter from grid-entry inputs to floor-cut-entry inputs -/

/-- Extract the unary base-row index from a floor-cut grid-generator request. -/
def machineBetheFloorCutGridBaseRow (word : List Bool) : List Bool :=
  machinePairFirst word

/-- The grid-generator payload following the base-row word. -/
def machineBetheFloorCutGridRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the unary base-column index from a floor-cut grid-generator request. -/
def machineBetheFloorCutGridBaseColumn (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFloorCutGridRest word)

/-- Extract the original floor-cut vector request carried by the grid generator. -/
def machineBetheFloorCutGridPayload (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheFloorCutGridRest word)

/-- Extract the unary base dimension from a request for the complete floor-cut vector. -/
def machineBetheFloorCutVectorDimension (word : List Bool) : List Bool :=
  machinePairFirst word

/-- The floor-cut vector request after removing its dimension word. -/
def machineBetheFloorCutVectorRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the queried recovered-entry row from the floor-cut vector request. -/
def machineBetheFloorCutVectorQueryRow (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFloorCutVectorRest word)

/-- Extract the queried recovered-entry column from the floor-cut vector request. -/
def machineBetheFloorCutVectorQueryColumn (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheFloorCutVectorRest word)

/-- Combine the stored recovered-entry query with the generator's base-row and base-column
indices, setting the height flag to false. -/
def machineBetheFloorCutGridEntryInput (word : List Bool) : List Bool :=
  let payload := machineBetheFloorCutGridPayload word
  pair (machineBetheFloorCutVectorDimension payload)
    (pair (machineBetheFloorCutVectorQueryRow payload)
      (pair (machineBetheFloorCutVectorQueryColumn payload)
        (pair (machineBetheFloorCutGridBaseRow word)
          (pair (machineBetheFloorCutGridBaseColumn word) [false]))))

/-- Evaluate the encoded floor-cut coefficient at the current grid coordinate. -/
def machineBetheFloorCutGridEntryCode (word : List Bool) : List Bool :=
  machineBetheFloorCutEntryCode (machineBetheFloorCutGridEntryInput word)

theorem machineBetheFloorCutGridBaseRow_mem_FP :
    machineBetheFloorCutGridBaseRow ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFloorCutGridRest_mem_FP :
    machineBetheFloorCutGridRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFloorCutGridBaseColumn_mem_FP :
    machineBetheFloorCutGridBaseColumn ∈ FP := by
  simpa only [machineBetheFloorCutGridBaseColumn] using!
    machineCompose_mem_FP machineBetheFloorCutGridRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFloorCutGridPayload_mem_FP :
    machineBetheFloorCutGridPayload ∈ FP := by
  simpa only [machineBetheFloorCutGridPayload] using!
    machineCompose_mem_FP machineBetheFloorCutGridRest_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFloorCutVectorDimension_mem_FP :
    machineBetheFloorCutVectorDimension ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFloorCutVectorRest_mem_FP :
    machineBetheFloorCutVectorRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFloorCutVectorQueryRow_mem_FP :
    machineBetheFloorCutVectorQueryRow ∈ FP := by
  simpa only [machineBetheFloorCutVectorQueryRow] using!
    machineCompose_mem_FP machineBetheFloorCutVectorRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFloorCutVectorQueryColumn_mem_FP :
    machineBetheFloorCutVectorQueryColumn ∈ FP := by
  simpa only [machineBetheFloorCutVectorQueryColumn] using!
    machineCompose_mem_FP machineBetheFloorCutVectorRest_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFloorCutGridEntryInput_mem_FP :
    machineBetheFloorCutGridEntryInput ∈ FP := by
  have hdimension := machineCompose_mem_FP
    machineBetheFloorCutGridPayload_mem_FP
    machineBetheFloorCutVectorDimension_mem_FP
  have hqueryRow := machineCompose_mem_FP
    machineBetheFloorCutGridPayload_mem_FP
    machineBetheFloorCutVectorQueryRow_mem_FP
  have hqueryColumn := machineCompose_mem_FP
    machineBetheFloorCutGridPayload_mem_FP
    machineBetheFloorCutVectorQueryColumn_mem_FP
  exact machinePair_mem_FP hdimension
    (machinePair_mem_FP hqueryRow
      (machinePair_mem_FP hqueryColumn
        (machinePair_mem_FP machineBetheFloorCutGridBaseRow_mem_FP
          (machinePair_mem_FP machineBetheFloorCutGridBaseColumn_mem_FP
            (machineConst_mem_FP [false])))))

theorem machineBetheFloorCutGridEntryCode_mem_FP :
    machineBetheFloorCutGridEntryCode ∈ FP := by
  simpa only [machineBetheFloorCutGridEntryCode] using!
    machineCompose_mem_FP machineBetheFloorCutGridEntryInput_mem_FP
      machineBetheFloorCutEntryCode_mem_FP

/-! ## Complete vector machine -/

/-- The twice-iterated binary-width ruler used to bound generated floor-cut entries. -/
def machineBetheFloorCutVectorBound (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 2 word

/-- Package the unary grid dimension, entry-width ruler, and original floor-cut vector request
for grid generation. -/
def machineBetheFloorCutVectorGeneratorInput
    (word : List Bool) : List Bool :=
  pair (machineBetheFloorCutVectorDimension word)
    (pair (machineBetheFloorCutVectorBound word) word)

/-- Generate the encoded floor-cut coefficients over the square grid of base coordinates. -/
def machineBetheFloorCutVectorBaseCode (word : List Bool) : List Bool :=
  machineUnaryGridGeneratorCode machineBetheFloorCutGridEntryCode
    (machineBetheFloorCutVectorGeneratorInput word)

/-- Package a zero rational entry for appending to the generated base-coordinate vector. -/
def machineBetheFloorCutVectorSnocInput (word : List Bool) : List Bool :=
  pair (rationalEntryBinaryCode 0)
    (machineBetheFloorCutVectorBaseCode word)

/-- Append the zero height coefficient to the generated base-coordinate floor-cut vector. -/
def machineBetheFloorCutVectorCode (word : List Bool) : List Bool :=
  machineBinaryListSnoc (machineBetheFloorCutVectorSnocInput word)

theorem machineBetheFloorCutVectorBound_mem_FP :
    machineBetheFloorCutVectorBound ∈ FP :=
  machineIteratedBinaryWidth_mem_FP 2

theorem machineBetheFloorCutVectorGeneratorInput_mem_FP :
    machineBetheFloorCutVectorGeneratorInput ∈ FP :=
  machinePair_mem_FP machineBetheFloorCutVectorDimension_mem_FP
    (machinePair_mem_FP machineBetheFloorCutVectorBound_mem_FP id_mem_FP)

theorem machineBetheFloorCutVectorBaseCode_mem_FP :
    machineBetheFloorCutVectorBaseCode ∈ FP := by
  have hgenerator := machineUnaryGridGeneratorCode_mem_FP
    machineBetheFloorCutGridEntryCode_mem_FP
  simpa only [machineBetheFloorCutVectorBaseCode] using!
    machineCompose_mem_FP machineBetheFloorCutVectorGeneratorInput_mem_FP
      hgenerator

theorem machineBetheFloorCutVectorSnocInput_mem_FP :
    machineBetheFloorCutVectorSnocInput ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP (rationalEntryBinaryCode 0))
    machineBetheFloorCutVectorBaseCode_mem_FP

theorem machineBetheFloorCutVectorCode_mem_FP :
    machineBetheFloorCutVectorCode ∈ FP := by
  simpa only [machineBetheFloorCutVectorCode] using!
    machineCompose_mem_FP machineBetheFloorCutVectorSnocInput_mem_FP
      machineBinaryListSnoc_mem_FP

/-- Encode a floor-cut vector request with unary base dimension and recovered-entry row and
column indices. -/
def machineBetheFloorCutVectorCanonicalWord {m : ℕ}
    (i j : Fin (m + 1)) : List Bool :=
  pair (List.replicate m true)
    (pair (List.replicate i.1 true) (List.replicate j.1 true))

@[simp] theorem machineBetheFloorCutGridEntryInput_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) :
    machineBetheFloorCutGridEntryInput
        (pair (List.replicate a.1 true)
          (pair (List.replicate b.1 true)
            (machineBetheFloorCutVectorCanonicalWord i j))) =
      machineBetheFloorCutEntryCanonicalWord i j a b false := by
  simp [machineBetheFloorCutGridEntryInput,
    machineBetheFloorCutGridPayload, machineBetheFloorCutGridRest,
    machineBetheFloorCutGridBaseRow,
    machineBetheFloorCutGridBaseColumn,
    machineBetheFloorCutVectorDimension,
    machineBetheFloorCutVectorQueryRow,
    machineBetheFloorCutVectorQueryColumn,
    machineBetheFloorCutVectorRest,
    machineBetheFloorCutVectorCanonicalWord,
    machineBetheFloorCutEntryCanonicalWord]

@[simp] theorem machineBetheFloorCutGridEntryCode_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) :
    machineBetheFloorCutGridEntryCode
        (pair (List.replicate a.1 true)
          (pair (List.replicate b.1 true)
            (machineBetheFloorCutVectorCanonicalWord i j))) =
      rationalEntryBinaryCode (explicitBetheFloorCutBaseEntry i j a b) := by
  rw [machineBetheFloorCutGridEntryCode,
    machineBetheFloorCutGridEntryInput_encode,
    machineBetheFloorCutEntryCode_encode]
  simp

theorem betheFloorCut_entry_code_length_le {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) :
    (rationalEntryBinaryCode
      (explicitBetheFloorCutBaseEntry i j a b)).length ≤ 16 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · norm_num [rationalEntryBinaryCode, integerBinaryCode] <;> decide
  · by_cases hb : b = j <;>
      simp [hb, rationalEntryBinaryCode, integerBinaryCode] <;> decide
  · by_cases ha : a = i <;>
      simp [ha, rationalEntryBinaryCode, integerBinaryCode] <;> decide
  · by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [ha, hb, rationalEntryBinaryCode, integerBinaryCode] <;> decide

theorem betheFloorCut_base_code_length_le_bound {m : ℕ}
    (i j : Fin (m + 1)) :
    (binaryListCode rationalEntryBinaryCode
      (unaryGridValues (explicitBetheFloorCutBaseEntry i j))).length ≤
      (machineBetheFloorCutVectorBound
        (machineBetheFloorCutVectorCanonicalWord i j)).length := by
  let word := machineBetheFloorCutVectorCanonicalWord i j
  let L := word.length
  let T := L + 16
  have hmL : m ≤ L := by
    simp only [L, word, machineBetheFloorCutVectorCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have heach : ∀ q ∈
      unaryGridValues (explicitBetheFloorCutBaseEntry i j),
      (rationalEntryBinaryCode q).length ≤ 16 := by
    intro q hq
    rw [unaryGridValues] at hq
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
    exact betheFloorCut_entry_code_length_le i j _ _
  have hsum := List.sum_le_card_nsmul
    ((unaryGridValues (explicitBetheFloorCutBaseEntry i j)).map
      fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2)
    34 (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      have hq' := heach q hq
      omega)
  have hmT : m ≤ T := hmL.trans (by simp [T])
  have hmm := Nat.mul_le_mul hmT hmT
  have hbase : 16 ≤ T := by simp [T]
  have hcoefficient : 34 ≤ T ^ 2 := by
    have hpow := Nat.pow_le_pow_left hbase 2
    exact (by norm_num : 34 ≤ 16 ^ 2).trans hpow
  have hmul := Nat.mul_le_mul hmm hcoefficient
  have hcode :
      (binaryListCode rationalEntryBinaryCode
        (unaryGridValues (explicitBetheFloorCutBaseEntry i j))).length ≤
        T ^ 4 := by
    rw [binaryListCode_length_eq_sum]
    simp only [List.length_map, unaryGridValues_length,
      Nat.nsmul_eq_mul] at hsum
    calc
      _ ≤ m * m * 34 := hsum
      _ ≤ T * T * T ^ 2 := hmul
      _ = T ^ 4 := by ring
  rw [machineBetheFloorCutVectorBound,
    machineIteratedBinaryWidth_length]
  exact hcode.trans (by
    simpa only [T, L, word] using!
      certificateExpGuardWidth_pow_lower 1
        (machineBetheFloorCutVectorCanonicalWord i j).length)

@[simp] theorem machineBetheFloorCutVectorGeneratorInput_encode {m : ℕ}
    (i j : Fin (m + 1)) :
    machineBetheFloorCutVectorGeneratorInput
        (machineBetheFloorCutVectorCanonicalWord i j) =
      machineUnaryGridGeneratorCanonicalWord m
        (machineBetheFloorCutVectorBound
          (machineBetheFloorCutVectorCanonicalWord i j))
        (machineBetheFloorCutVectorCanonicalWord i j) := by
  simp [machineBetheFloorCutVectorGeneratorInput,
    machineBetheFloorCutVectorDimension,
    machineBetheFloorCutVectorCanonicalWord,
    machineUnaryGridGeneratorCanonicalWord]

@[simp] theorem machineBetheFloorCutVectorBaseCode_encode {m : ℕ}
    (i j : Fin (m + 1)) :
    machineBetheFloorCutVectorBaseCode
        (machineBetheFloorCutVectorCanonicalWord i j) =
      binaryListCode rationalEntryBinaryCode
        (unaryGridValues (explicitBetheFloorCutBaseEntry i j)) := by
  rw [machineBetheFloorCutVectorBaseCode,
    machineBetheFloorCutVectorGeneratorInput_encode]
  exact machineUnaryGridGeneratorCode_encode_of_bound
    machineBetheFloorCutGridEntryCode
    (explicitBetheFloorCutBaseEntry i j)
    (machineBetheFloorCutVectorBound
      (machineBetheFloorCutVectorCanonicalWord i j))
    (machineBetheFloorCutVectorCanonicalWord i j)
    (machineBetheFloorCutGridEntryCode_encode i j)
    (betheFloorCut_base_code_length_le_bound i j)

theorem ofFn_explicitBetheFloorCutNormal {m : ℕ}
    (i j : Fin (m + 1)) :
    List.ofFn (explicitBetheFloorCutNormal i j) =
      unaryGridValues (explicitBetheFloorCutBaseEntry i j) ++ [0] := by
  rw [List.ofFn_succ']
  simp only [explicitBetheFloorCutNormal, Fin.snoc_castSucc,
    Fin.snoc_last, List.concat_eq_append, unaryGridValues]

@[simp] theorem machineBetheFloorCutVectorCode_encode {m : ℕ}
    (i j : Fin (m + 1)) :
    machineBetheFloorCutVectorCode
        (machineBetheFloorCutVectorCanonicalWord i j) =
      rationalFiniteVectorCode (explicitBetheFloorCutNormal i j) := by
  rw [machineBetheFloorCutVectorCode,
    machineBetheFloorCutVectorSnocInput,
    machineBetheFloorCutVectorBaseCode_encode,
    machineBinaryListSnoc_encode,
    rationalFiniteVectorCode, ofFn_explicitBetheFloorCutNormal]

@[simp] theorem machineBetheFloorCutVectorCode_encode_oracleNormal {m : ℕ}
    (i j : Fin (m + 1)) :
    machineBetheFloorCutVectorCode
        (machineBetheFloorCutVectorCanonicalWord i j) =
      rationalFiniteVectorCode (betheFloorCutNormal i j) := by
  rw [machineBetheFloorCutVectorCode_encode,
    explicitBetheFloorCutNormal_eq]

end BeyondBethe

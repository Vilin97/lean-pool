/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorCutVector

/-!
# Finite-word height-cap normals

The upper-height constraint has normal `(0,...,0,1)`.  We construct its
`m^2` zero base coordinates with the common grid generator and append the
single positive height coordinate with the verified list-snoc machine.
-/

namespace BeyondBethe

open Complexity

def machineBetheHeightNormalEntryCode (_word : List Bool) : List Bool :=
  rationalEntryBinaryCode 0

def machineBetheHeightNormalBound (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 2 word

def machineBetheHeightNormalGeneratorInput
    (word : List Bool) : List Bool :=
  pair word (pair (machineBetheHeightNormalBound word) word)

def machineBetheHeightNormalBaseCode (word : List Bool) : List Bool :=
  machineUnaryGridGeneratorCode machineBetheHeightNormalEntryCode
    (machineBetheHeightNormalGeneratorInput word)

def machineBetheHeightNormalSnocInput (word : List Bool) : List Bool :=
  pair (rationalEntryBinaryCode 1)
    (machineBetheHeightNormalBaseCode word)

def machineBetheHeightNormalVectorCode (word : List Bool) : List Bool :=
  machineBinaryListSnoc (machineBetheHeightNormalSnocInput word)

theorem machineBetheHeightNormalEntryCode_mem_FP :
    machineBetheHeightNormalEntryCode ∈ FP :=
  machineConst_mem_FP (rationalEntryBinaryCode 0)

theorem machineBetheHeightNormalBound_mem_FP :
    machineBetheHeightNormalBound ∈ FP :=
  machineIteratedBinaryWidth_mem_FP 2

theorem machineBetheHeightNormalGeneratorInput_mem_FP :
    machineBetheHeightNormalGeneratorInput ∈ FP :=
  machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineBetheHeightNormalBound_mem_FP id_mem_FP)

theorem machineBetheHeightNormalBaseCode_mem_FP :
    machineBetheHeightNormalBaseCode ∈ FP := by
  have hgenerator := machineUnaryGridGeneratorCode_mem_FP
    machineBetheHeightNormalEntryCode_mem_FP
  simpa only [machineBetheHeightNormalBaseCode] using!
    machineCompose_mem_FP machineBetheHeightNormalGeneratorInput_mem_FP
      hgenerator

theorem machineBetheHeightNormalSnocInput_mem_FP :
    machineBetheHeightNormalSnocInput ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP (rationalEntryBinaryCode 1))
    machineBetheHeightNormalBaseCode_mem_FP

theorem machineBetheHeightNormalVectorCode_mem_FP :
    machineBetheHeightNormalVectorCode ∈ FP := by
  simpa only [machineBetheHeightNormalVectorCode] using!
    machineCompose_mem_FP machineBetheHeightNormalSnocInput_mem_FP
      machineBinaryListSnoc_mem_FP

theorem rationalEntryBinaryCode_zero_length_le :
    (rationalEntryBinaryCode 0).length ≤ 16 := by
  norm_num [rationalEntryBinaryCode, integerBinaryCode]

theorem betheHeightNormal_base_code_length_le_bound (m : ℕ) :
    (binaryListCode rationalEntryBinaryCode
      (unaryGridValues (fun _ _ : Fin m ↦ (0 : ℚ)))).length ≤
      (machineBetheHeightNormalBound
        (List.replicate m true)).length := by
  let word := List.replicate m true
  let L := word.length
  let T := L + 16
  have hmL : m ≤ L := by simp [L, word]
  have hsum := List.sum_le_card_nsmul
    ((unaryGridValues (fun _ _ : Fin m ↦ (0 : ℚ))).map
      fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2)
    34 (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      rw [unaryGridValues] at hq
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
      have hzero := rationalEntryBinaryCode_zero_length_le
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
        (unaryGridValues (fun _ _ : Fin m ↦ (0 : ℚ)))).length ≤
        T ^ 4 := by
    rw [binaryListCode_length_eq_sum]
    simp only [List.length_map, unaryGridValues_length,
      Nat.nsmul_eq_mul] at hsum
    calc
      _ ≤ m * m * 34 := hsum
      _ ≤ T * T * T ^ 2 := hmul
      _ = T ^ 4 := by ring
  rw [machineBetheHeightNormalBound,
    machineIteratedBinaryWidth_length]
  exact hcode.trans (by
    simpa only [T, L, word] using!
      certificateExpGuardWidth_pow_lower 1
        (List.replicate m true).length)

@[simp] theorem machineBetheHeightNormalGeneratorInput_encode (m : ℕ) :
    machineBetheHeightNormalGeneratorInput (List.replicate m true) =
      machineUnaryGridGeneratorCanonicalWord m
        (machineBetheHeightNormalBound (List.replicate m true))
        (List.replicate m true) := by
  simp [machineBetheHeightNormalGeneratorInput,
    machineUnaryGridGeneratorCanonicalWord]

@[simp] theorem machineBetheHeightNormalBaseCode_encode (m : ℕ) :
    machineBetheHeightNormalBaseCode (List.replicate m true) =
      binaryListCode rationalEntryBinaryCode
        (unaryGridValues (fun _ _ : Fin m ↦ (0 : ℚ))) := by
  rw [machineBetheHeightNormalBaseCode,
    machineBetheHeightNormalGeneratorInput_encode]
  exact machineUnaryGridGeneratorCode_encode_of_bound
    machineBetheHeightNormalEntryCode (fun _ _ : Fin m ↦ (0 : ℚ))
    (machineBetheHeightNormalBound (List.replicate m true))
    (List.replicate m true) (by intro i j; rfl)
    (betheHeightNormal_base_code_length_le_bound m)

theorem ofFn_epigraphUpperNormal_square (m : ℕ) :
    List.ofFn (epigraphUpperNormal (m * m)) =
      unaryGridValues (fun _ _ : Fin m ↦ (0 : ℚ)) ++ [1] := by
  rw [List.ofFn_succ']
  simp [epigraphUpperNormal, unaryGridValues]

@[simp] theorem machineBetheHeightNormalVectorCode_encode (m : ℕ) :
    machineBetheHeightNormalVectorCode (List.replicate m true) =
      rationalFiniteVectorCode (epigraphUpperNormal (m * m)) := by
  rw [machineBetheHeightNormalVectorCode,
    machineBetheHeightNormalSnocInput,
    machineBetheHeightNormalBaseCode_encode,
    machineBinaryListSnoc_encode,
    rationalFiniteVectorCode, ofFn_epigraphUpperNormal_square]

end BeyondBethe

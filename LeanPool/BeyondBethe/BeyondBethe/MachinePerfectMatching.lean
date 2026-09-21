/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMateAllSome
import Mathlib.Tactic

/-!
# A finite-word perfect-matching decision procedure

This module composes the complete Kuhn runner with the exact mate-table scan.
The result is an actual polynomial-time function on bitstrings.  On the
canonical encoding of a square rational matrix it returns `[true]` exactly
when the positive support contains a perfect matching.
-/

namespace BeyondBethe

open Complexity

/-! ## The finite-word program -/

def machineKuhnFinalMate (matrix : List Bool) : List Bool :=
  machineKuhnDoneMate (machineKuhnControl (machineKuhnFinalState matrix))

def machineKuhnPerfectMatchingInput (matrix : List Bool) : List Bool :=
  pair (machineKuhnInitDimension matrix) (machineKuhnFinalMate matrix)

def machineKuhnPerfectMatchingBit (matrix : List Bool) : List Bool :=
  machineMateAllSomeBit (machineKuhnPerfectMatchingInput matrix)

theorem machineKuhnFinalMate_mem_FP :
    machineKuhnFinalMate ∈ Complexity.FP := by
  have hcontrol := machineCompose_mem_FP machineKuhnFinalState_mem_FP
    machineKuhnControl_mem_FP
  simpa only [machineKuhnFinalMate] using
    machineCompose_mem_FP hcontrol machineKuhnDoneMate_mem_FP

theorem machineKuhnPerfectMatchingInput_mem_FP :
    machineKuhnPerfectMatchingInput ∈ Complexity.FP := by
  exact machinePair_mem_FP machineKuhnInitDimension_mem_FP
    machineKuhnFinalMate_mem_FP

theorem machineKuhnPerfectMatchingBit_mem_FP :
    machineKuhnPerfectMatchingBit ∈ Complexity.FP := by
  simpa only [machineKuhnPerfectMatchingBit] using
    machineCompose_mem_FP machineKuhnPerfectMatchingInput_mem_FP
      machineMateAllSomeBit_mem_FP

/-! ## The column-totality criterion -/

def AllColumnsMatched {n : ℕ} (mate : ColumnMate n) : Prop :=
  ∀ col, ∃ row, mate col = some row

theorem hasPerfectMatching_of_all_columns_matched {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (mate : ColumnMate n)
    (hsupport : IsSupportColumnMate A mate)
    (hallColumns : AllColumnsMatched mate) :
    Matrix.HasPerfectMatching A := by
  classical
  let rowOfColumn : Fin n → Fin n :=
    fun col ↦ Classical.choose (hallColumns col)
  have rowOfColumn_spec (col : Fin n) :
      mate col = some (rowOfColumn col) :=
    Classical.choose_spec (hallColumns col)
  have rowOfColumn_injective : Function.Injective rowOfColumn := by
    intro col col' hrows
    apply hsupport.injective (rowOfColumn_spec col)
    simpa only [hrows] using rowOfColumn_spec col'
  have rowOfColumn_bijective : Function.Bijective rowOfColumn :=
    (Fintype.bijective_iff_injective_and_card rowOfColumn).2
      ⟨rowOfColumn_injective, rfl⟩
  let matching : Fin n ≃ Fin n :=
    Equiv.ofBijective rowOfColumn rowOfColumn_bijective
  refine ⟨matching, ?_⟩
  intro col
  exact hsupport.support (rowOfColumn_spec col)

theorem all_columns_matched_of_all_rows_matched {n : ℕ}
    (mate : ColumnMate n)
    (hallRows : ∀ row, MatchesRow mate row) :
    AllColumnsMatched mate := by
  classical
  let colOfRow : Fin n → Fin n :=
    fun row ↦ Classical.choose (hallRows row)
  have colOfRow_spec (row : Fin n) : mate (colOfRow row) = some row :=
    Classical.choose_spec (hallRows row)
  have colOfRow_injective : Function.Injective colOfRow := by
    intro row row' hcols
    have hrow := colOfRow_spec row
    have hrow' := colOfRow_spec row'
    rw [hcols, hrow'] at hrow
    exact Option.some.inj hrow.symm
  have colOfRow_surjective : Function.Surjective colOfRow :=
    ((Fintype.bijective_iff_injective_and_card colOfRow).2
      ⟨colOfRow_injective, rfl⟩).2
  intro col
  obtain ⟨row, hrow⟩ := colOfRow_surjective col
  refine ⟨row, ?_⟩
  simpa only [hrow] using colOfRow_spec row

theorem columnMateList_all_isSome_eq_true_iff {n : ℕ}
    (mate : ColumnMate n) :
    (columnMateList mate).all Option.isSome = true ↔
      AllColumnsMatched mate := by
  constructor
  · intro hall col
    have hi : col.1 < (columnMateList mate).length := by simp
    have hvalue := (List.all_eq_true.mp hall)
      (columnMateList mate)[col.1] (List.getElem_mem hi)
    rw [columnMateList_getElem] at hvalue
    cases hmate : mate col with
    | none => simp [hmate] at hvalue
    | some row => exact ⟨row, rfl⟩
  · intro hall
    apply List.all_eq_true.mpr
    intro value hvalue
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvalue
    have hin : i < n := by simpa using hi
    obtain ⟨row, hrow⟩ := hall ⟨i, hin⟩
    rw [columnMateList_getElem, hrow]
    rfl

theorem kuhnColumnMate_all_isSome_eq_true_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (columnMateList (kuhnColumnMate A)).all Option.isSome = true ↔
      Matrix.HasPerfectMatching A := by
  rw [columnMateList_all_isSome_eq_true_iff]
  constructor
  · exact hasPerfectMatching_of_all_columns_matched A (kuhnColumnMate A)
      (kuhnColumnMate_support A)
  · intro hperfect
    exact all_columns_matched_of_all_rows_matched (kuhnColumnMate A)
      (kuhnColumnMate_all_rows_of_hasPerfectMatching A hperfect)

/-! ## Exact machine semantics -/

@[simp] theorem machineKuhnFinalMate_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnFinalMate (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      mateVectorCode (columnMateList (kuhnColumnMate A)) := by
  simp [machineKuhnFinalMate, kuhnControlCode]

@[simp] theorem machineKuhnPerfectMatchingInput_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnPerfectMatchingInput
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      pair (List.replicate n true)
        (mateVectorCode (columnMateList (kuhnColumnMate A))) := by
  simp [machineKuhnPerfectMatchingInput]

@[simp] theorem machineKuhnPerfectMatchingBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnPerfectMatchingBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [(columnMateList (kuhnColumnMate A)).all Option.isSome] := by
  rw [machineKuhnPerfectMatchingBit,
    machineKuhnPerfectMatchingInput_encode]
  simpa only [columnMateList_length] using
    machineMateAllSomeBit_encode (columnMateList (kuhnColumnMate A))

theorem machineKuhnPerfectMatchingBit_eq_true_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnPerfectMatchingBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) = [true] ↔
      Matrix.HasPerfectMatching A := by
  rw [machineKuhnPerfectMatchingBit_encode, List.cons.injEq,
    and_iff_left rfl, kuhnColumnMate_all_isSome_eq_true_iff]

theorem machineKuhnPerfectMatchingBit_eq_false_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnPerfectMatchingBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) = [false] ↔
      ¬Matrix.HasPerfectMatching A := by
  rw [machineKuhnPerfectMatchingBit_encode, List.cons.injEq,
    and_iff_left rfl, ← kuhnColumnMate_all_isSome_eq_true_iff]
  exact Bool.eq_false_iff

end BeyondBethe

/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExplicitBetheOptimizer
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixDimension
import LeanPool.BeyondBethe.BeyondBethe.RationalEncodingBounds
import LeanPool.BeyondBethe.BeyondBethe.SourceStableReindex
import Mathlib.Tactic

/-! # Certificate Magnitude -/

open scoped BigOperators

namespace BeyondBethe

open Complexity

/-!
# A polynomial magnitude bound for the final certificate logarithm

The rational exponential routine necessarily has running time proportional to
the bit length of its answer.  This file proves that, on the positive
normalized matrices on which the optimizer is used, the logarithm passed to
that routine has polynomial numerical magnitude.  The proof avoids inspecting
the optimizer's rational arithmetic: the certified permanent sandwich and the
elementary input-size bounds on the permanent already give both sides.
-/

def explicitCertificateMagnitudeBudget {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  n * (rationalMatrixEntryBitBound B + n + 1)

def rationalListDataCost (xs : List ℚ) : ℕ :=
  (xs.map fun q ↦ encodedBitLength ℚ q).sum

def rationalRowsDataCost (rows : List (List ℚ)) : ℕ :=
  (rows.map rationalListDataCost).sum

theorem rational_encodedBitLength_le_entryCode (q : ℚ) :
    encodedBitLength ℚ q ≤ 12 + 8 * (rationalEntryBinaryCode q).length := by
  have h := rational_encodedBitLength_le q
  have hnum := integerNatAbs_size_le_binaryCode_length q.num
  have hnumCode : (integerBinaryCode q.num).length ≤
      (rationalEntryBinaryCode q).length := by
    rw [rationalEntryBinaryCode, pair_length]
    omega
  have hden : q.den.size ≤ (rationalEntryBinaryCode q).length := by
    rw [rationalEntryBinaryCode, pair_length, Nat.size_eq_bits_len]
    omega
  omega

theorem rationalListDataCost_le (xs : List ℚ) :
    rationalListDataCost xs ≤
      12 * xs.length + 8 * (binaryListCode rationalEntryBinaryCode xs).length := by
  induction xs with
  | nil => simp [rationalListDataCost, binaryListCode]
  | cons q qs ih =>
      rw [rationalListDataCost, List.map_cons, List.sum_cons,
        List.length_cons, binaryListCode, pair_length]
      have hq := rational_encodedBitLength_le_entryCode q
      have ih' : (qs.map fun q ↦ encodedBitLength ℚ q).sum ≤
          12 * qs.length +
            8 * (binaryListCode rationalEntryBinaryCode qs).length := by
        simpa only [rationalListDataCost] using ih
      omega

theorem rationalRowsDataCost_le (rows : List (List ℚ)) :
    rationalRowsDataCost rows ≤
      12 * (rows.map List.length).sum +
        8 * (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
  induction rows with
  | nil => simp [rationalRowsDataCost, binaryListCode]
  | cons row rows ih =>
      rw [rationalRowsDataCost, List.map_cons, List.sum_cons,
        binaryListCode, pair_length]
      simp only [List.map_cons, List.sum_cons]
      have hrow := rationalListDataCost_le row
      have ih' : (rows.map rationalListDataCost).sum ≤
          12 * (rows.map List.length).sum +
            8 * (binaryListCode
              (binaryListCode rationalEntryBinaryCode) rows).length := by
        simpa only [rationalRowsDataCost] using ih
      omega

theorem rationalRowsEntryCount_le_codeLength (rows : List (List ℚ)) :
    (rows.map List.length).sum ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
  induction rows with
  | nil => simp [binaryListCode]
  | cons row rows ih =>
      rw [List.map_cons, List.sum_cons, binaryListCode, pair_length]
      have hrow := list_length_le_binaryListCode_length
        rationalEntryBinaryCode row
      omega

theorem rationalMatrixEntryBitBound_le_machineCode
    {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixEntryBitBound B ≤
      32 * (rationalMatrixBinaryEncoding.encode ⟨n, B⟩).length := by
  let rows := rationalMatrixRows B
  let rowsCode := binaryListCode
    (binaryListCode rationalEntryBinaryCode) rows
  let word := rationalMatrixBinaryEncoding.encode ⟨n, B⟩
  have hrowsCode : rowsCode.length ≤ word.length := by
    change rowsCode.length ≤ (pair n.bits rowsCode).length
    simpa using machinePairSecond_length_le (pair n.bits rowsCode)
  have hcount : n ^ 2 = (rows.map List.length).sum := by
    simp only [rows, rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply, List.length_ofFn]
    simp
    ring
  have hnSq : n ^ 2 ≤ word.length := by
    rw [hcount]
    exact (rationalRowsEntryCount_le_codeLength rows).trans hrowsCode
  have hcost :
      (∑ i, ∑ j, encodedBitLength ℚ (B i j)) = rationalRowsDataCost rows := by
    simp only [rationalRowsDataCost, rationalListDataCost, rows,
      rationalMatrixRows, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  have hdata := rationalRowsDataCost_le rows
  rw [← hcost, ← hcount] at hdata
  have hwordPos : 1 ≤ word.length := hn.trans (matrix_dimension_le_code_length B)
  rw [rationalMatrixEntryBitBound]
  nlinarith

theorem positive_normalized_log_permanent_bounds
    {n : ℕ} (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    -(n * rationalMatrixEntryBitBound B : ℝ) ≤
        Real.log (Matrix.permanent (fun i j ↦ (B i j : ℝ))) ∧
      Real.log (Matrix.permanent (fun i j ↦ (B i j : ℝ))) ≤
        (n : ℝ) ^ 2 := by
  classical
  let Br : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ (B i j : ℝ)
  let J : Matrix (Fin n) (Fin n) ℝ := fun _ _ ↦ 1
  let L := rationalMatrixEntryBitBound B
  let d : ℚ := (1 / 2 : ℚ) ^ L
  have hBrpos : Matrix.Positive Br := by
    intro i j
    exact Rat.cast_pos.mpr (hBpos i j)
  have hBr0 : Matrix.Nonnegative Br := fun i j ↦ (hBrpos i j).le
  have hperpos : 0 < Matrix.permanent Br :=
    permanent_pos_of_positive Br hBrpos
  have hdQ : 0 < d := by positivity
  have hdR : 0 < (d : ℝ) := Rat.cast_pos.mpr hdQ
  have hmin : ∀ i j, (d : ℝ) ≤ Br i j := by
    intro i j
    have hq := (matrix_dyadic_bitBound_lt_entry hBpos i j).le
    have hr : (((1 / 2 : ℚ) ^ rationalMatrixEntryBitBound B : ℚ) : ℝ) ≤
        (B i j : ℝ) := by exact_mod_cast hq
    simpa only [d, L, Br] using hr
  have hlowerPermanent : (d : ℝ) ^ n ≤ Matrix.permanent Br := by
    simpa using
      (Matrix.pow_card_le_permanent_of_hasPerfectMatching Br hdR.le hBr0
        (fun i j _ ↦ hmin i j) (positiveMatrix_hasPerfectMatching hBrpos))
  have hlogLower := Real.log_le_log (pow_pos hdR n) hlowerPermanent
  have hlogTwoUpper : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hscaleNonneg : 0 ≤ (n : ℝ) * L := by positivity
  have hscaledLog : (n : ℝ) * L * Real.log 2 ≤ (n : ℝ) * L := by
    simpa using mul_le_mul_of_nonneg_left hlogTwoUpper hscaleNonneg
  have hlower : -(n * L : ℝ) ≤ Real.log (Matrix.permanent Br) := by
    rw [Real.log_pow] at hlogLower
    have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hdcast : (d : ℝ) = (1 / 2 : ℝ) ^ L := by
      norm_num [d]
    rw [hdcast, Real.log_pow] at hlogLower
    rw [hlogHalf] at hlogLower
    push_cast
    nlinarith
  have hBJ : ∀ i j, Br i j ≤ J i j := by
    intro i j
    have hr : (B i j : ℝ) ≤ 1 := by exact_mod_cast hBupper i j
    simpa only [Br, J] using hr
  have hperJ : Matrix.permanent J = (Nat.factorial n : ℝ) := by
    simp [J, Matrix.permanent, Fintype.card_perm]
  have hupperPermanent : Matrix.permanent Br ≤ (n : ℝ) ^ n := by
    calc
      Matrix.permanent Br ≤ Matrix.permanent J :=
        Matrix.permanent_mono_real hBr0 hBJ
      _ = (Nat.factorial n : ℝ) := hperJ
      _ ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow n
      _ = (n : ℝ) ^ n := by norm_num
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpowpos : 0 < (n : ℝ) ^ n := pow_pos hnR n
  have hlogUpper := Real.log_le_log hperpos hupperPermanent
  rw [Real.log_pow] at hlogUpper
  have hlogn : Real.log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos hnR
    linarith
  have hnnonneg : 0 ≤ (n : ℝ) := hnR.le
  have hscaledN := mul_le_mul_of_nonneg_left hlogn hnnonneg
  have hupper : Real.log (Matrix.permanent Br) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  simpa only [Br, L] using And.intro hlower hupper

theorem preSmoothingBase_explicit_le_exp_one :
    preSmoothingBase (explicitCertifiedEpsilon : ℝ) ≤ Real.exp 1 := by
  have hε : 0 ≤ (explicitCertifiedEpsilon : ℝ) := by
    exact_mod_cast explicitCertifiedEpsilon_pos.le
  have hexpNonpos : Real.exp
      (-(explicitCertifiedEpsilon : ℝ) +
        (explicitCertifiedEpsilon : ℝ) / 4) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hbaseTwo : preSmoothingBase (explicitCertifiedEpsilon : ℝ) ≤ 2 := by
    rw [preSmoothingBase]
    calc
      Real.sqrt 2 * Real.exp
          (-(explicitCertifiedEpsilon : ℝ) +
            (explicitCertifiedEpsilon : ℝ) / 4) ≤
          Real.sqrt 2 * 1 :=
        mul_le_mul_of_nonneg_left hexpNonpos (Real.sqrt_nonneg 2)
      _ ≤ 2 := by simpa using hsqrt
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  exact hbaseTwo.trans htwoExp

theorem explicitExpEvaluationLoss_le_one :
    (explicitExpEvaluationLoss : ℝ) ≤ 1 := by
  have hq : explicitExpEvaluationLoss ≤ (1 : ℚ) := by
    rw [explicitExpEvaluationLoss, explicitCertifiedEpsilon,
      explicitCertifiedEpsilon_eq]
    norm_num [explicitXi, explicitDelta, explicitEta, explicitRowRatio]
  exact_mod_cast hq

/-- The magnitude argument depends only on the certified matrix and KKT
relations, not on how the optimizer breaks ties.  This form is used by the
row-major executable optimizer. -/
theorem certificateLog_abs_le_of_feasibleApproximateKKT
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (X : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (R C : Fin (m + 2) → ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1)
    (hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)))
    (hXpos : ∀ i j, 0 < (X i j : ℝ))
    (happrox : HasApproximateLogKKT (explicitKKTError : ℝ)
      (explicitRegularizationScale (m + 2) : ℝ)
      (fun i j ↦ (B i j : ℝ))
      (fun i j ↦ ((X i j : ℚ) : ℝ))
      (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ))) :
    abs ((explicitDirectedCertificateLog X R C : ℚ) : ℝ) ≤
      explicitCertificateMagnitudeBudget B := by
  let n := m + 2
  let qlog : ℝ := (explicitDirectedCertificateLog X R C : ℚ)
  let qvalue : ℝ := (explicitDirectedCertificateValue X R C : ℚ)
  let P : ℝ := Matrix.permanent (fun i j ↦ (B i j : ℝ))
  change abs qlog ≤ explicitCertificateMagnitudeBudget B
  have hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)) := by
    intro i
    refine ⟨hX.row_probability i, fun j ↦ ⟨hXpos i j, ?_⟩⟩
    exact hX.entry_lt_one_of_positive hXpos (by simp) i j
  have hBR : Matrix.Positive (fun i j ↦ (B i j : ℝ)) := fun i j ↦
    Rat.cast_pos.mpr (hBpos i j)
  have hcert := explicitDirectedCertificate_twoSided
    anariOveisGharanStableCoefficient (n := m + 2) (by omega)
    hBR hX hXint happrox
  have hlossQ : 0 < explicitExpEvaluationLoss * (m + 2) :=
    mul_pos explicitExpEvaluationLoss_pos (by positivity)
  have hexp := rationalExpLower_bounds
    (s := explicitDirectedCertificateLog X R C) hlossQ
  have hexp' : Real.exp
        (qlog - (explicitExpEvaluationLoss : ℝ) * n) ≤ qvalue ∧
      qvalue ≤ Real.exp qlog := by
    have hdim : m + 1 + 1 = m + 2 := by omega
    simpa [qlog, qvalue, n, explicitDirectedCertificateValue, hdim] using hexp
  have hperbounds := positive_normalized_log_permanent_bounds
    (n := m + 2) (by omega) B hBpos hBupper
  have hPpos : 0 < P := permanent_pos_of_positive _ hBR
  have hqvaluePos : 0 < qvalue := by
    simpa only [qvalue] using explicitDirectedCertificateValue_pos
      (n := m + 2) (by omega) X R C
  have hqUpperLog : qlog - (explicitExpEvaluationLoss : ℝ) * n ≤
      Real.log P := by
    have h := Real.log_le_log (Real.exp_pos _)
      (hexp'.1.trans (by simpa only [qvalue, P] using hcert.1))
    simpa using h
  have hlossScaled : (explicitExpEvaluationLoss : ℝ) * n ≤ n := by
    exact mul_le_of_le_one_left (by positivity) explicitExpEvaluationLoss_le_one
  have hqUpper : qlog ≤ (n : ℝ) ^ 2 + n := by
    have hp := hperbounds.2
    simp only [P, n] at hqUpperLog hp hlossScaled ⊢
    linarith
  have hbasePow :
      (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n ≤
        Real.exp (n : ℝ) := by
    calc
      (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n ≤
          (Real.exp 1) ^ n :=
        pow_le_pow_left₀ (preSmoothingBase_pos _).le
          preSmoothingBase_explicit_le_exp_one n
      _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul]; norm_num
  have hPExp : P ≤ Real.exp ((n : ℝ) + qlog) := by
    calc
      P ≤ (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n * qvalue := by
        simpa only [P, qvalue] using hcert.2
      _ ≤ Real.exp (n : ℝ) * Real.exp qlog :=
        mul_le_mul hbasePow hexp'.2 hqvaluePos.le (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) + qlog) := by rw [Real.exp_add]
  have hqLowerLog : Real.log P ≤ (n : ℝ) + qlog := by
    have h := Real.log_le_log hPpos hPExp
    simpa using h
  have hqLower : -((n : ℝ) * rationalMatrixEntryBitBound B + n) ≤ qlog := by
    have hp := hperbounds.1
    simp only [P, n] at hqLowerLog hp ⊢
    linarith
  have hbudget : (n : ℝ) * rationalMatrixEntryBitBound B + n ≤
      (explicitCertificateMagnitudeBudget B : ℕ) := by
    simp only [explicitCertificateMagnitudeBudget, n]
    push_cast
    nlinarith
  have hupperBudget : (n : ℝ) ^ 2 + n ≤
      (explicitCertificateMagnitudeBudget B : ℕ) := by
    have hL : 1 ≤ rationalMatrixEntryBitBound B := by
      rw [rationalMatrixEntryBitBound]
      omega
    simp only [explicitCertificateMagnitudeBudget, n]
    push_cast
    nlinarith
  rw [abs_le]
  exact ⟨(neg_le_neg hbudget).trans hqLower,
    hqUpper.trans hupperBudget⟩

theorem explicitOptimizerCertificateLog_abs_le
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    abs ((explicitDirectedCertificateLog
        (explicitBetheOptimizerMatrix (m := m + 1) B)
        (explicitBetheOptimizerRowPotential (m := m + 1) B)
        (explicitBetheOptimizerColumnPotential (m := m + 1) B) : ℚ) : ℝ) ≤
      explicitCertificateMagnitudeBudget B := by
  let n := m + 2
  let X := explicitBetheOptimizerMatrix (m := m + 1) B
  let R := explicitBetheOptimizerRowPotential (m := m + 1) B
  let C := explicitBetheOptimizerColumnPotential (m := m + 1) B
  let qlog : ℝ := (explicitDirectedCertificateLog X R C : ℚ)
  let qvalue : ℝ := (explicitDirectedCertificateValue X R C : ℚ)
  let P : ℝ := Matrix.permanent (fun i j ↦ (B i j : ℝ))
  change abs qlog ≤ explicitCertificateMagnitudeBudget B
  have hpoint := explicitBetheOptimizerPoint_spec (m := m + 1)
    (by omega) B hBpos hBupper
  have hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)) := by
    simpa only [X] using hpoint.2.1
  have hXlo : ∀ i j, (explicitOptimizerFloor B : ℝ) ≤ (X i j : ℝ) := by
    simpa only [X] using hpoint.2.2.1
  have hfloor : 0 < (explicitOptimizerFloor B : ℝ) :=
    Rat.cast_pos.mpr (explicitOptimizerFloor_pos B)
  have hXpos : ∀ i j, 0 < (X i j : ℝ) := fun i j ↦
    hfloor.trans_le (hXlo i j)
  have hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)) := by
    intro i
    refine ⟨hX.row_probability i, fun j ↦ ⟨hXpos i j, ?_⟩⟩
    exact hX.entry_lt_one_of_positive hXpos (by simp) i j
  have happrox := explicitBetheOptimizer_hasApproximateLogKKT
    (m := m + 1) (by omega) B hBpos hBupper
  have hBR : Matrix.Positive (fun i j ↦ (B i j : ℝ)) := fun i j ↦
    Rat.cast_pos.mpr (hBpos i j)
  have hcert := explicitDirectedCertificate_twoSided
    anariOveisGharanStableCoefficient (n := m + 2) (by omega)
    hBR hX hXint (by simpa only [X, R, C] using happrox)
  have hlossQ : 0 < explicitExpEvaluationLoss * (m + 2) :=
    mul_pos explicitExpEvaluationLoss_pos (by positivity)
  have hexp := rationalExpLower_bounds
    (s := explicitDirectedCertificateLog X R C) hlossQ
  have hexp' : Real.exp
        (qlog - (explicitExpEvaluationLoss : ℝ) * n) ≤ qvalue ∧
      qvalue ≤ Real.exp qlog := by
    have hdim : m + 1 + 1 = m + 2 := by omega
    simpa [qlog, qvalue, n, explicitDirectedCertificateValue, hdim] using hexp
  have hperbounds := positive_normalized_log_permanent_bounds
    (n := m + 2) (by omega) B hBpos hBupper
  have hPpos : 0 < P := permanent_pos_of_positive _ hBR
  have hqvaluePos : 0 < qvalue := by
    simpa only [qvalue, R, C] using explicitDirectedCertificateValue_pos
      (n := m + 2) (by omega) X R C
  have hqUpperLog : qlog - (explicitExpEvaluationLoss : ℝ) * n ≤
      Real.log P := by
    have h := Real.log_le_log (Real.exp_pos _)
      (hexp'.1.trans (by simpa only [qvalue, P] using hcert.1))
    simpa using h
  have hlossScaled : (explicitExpEvaluationLoss : ℝ) * n ≤ n := by
    exact mul_le_of_le_one_left (by positivity) explicitExpEvaluationLoss_le_one
  have hqUpper : qlog ≤ (n : ℝ) ^ 2 + n := by
    have hp := hperbounds.2
    simp only [P, n] at hqUpperLog hp hlossScaled ⊢
    linarith
  have hbasePow :
      (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n ≤
        Real.exp (n : ℝ) := by
    calc
      (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n ≤
          (Real.exp 1) ^ n :=
        pow_le_pow_left₀ (preSmoothingBase_pos _).le
          preSmoothingBase_explicit_le_exp_one n
      _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul]; norm_num
  have hPExp : P ≤ Real.exp ((n : ℝ) + qlog) := by
    calc
      P ≤ (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n * qvalue := by
        simpa only [P, qvalue] using hcert.2
      _ ≤ Real.exp (n : ℝ) * Real.exp qlog :=
        mul_le_mul hbasePow hexp'.2 hqvaluePos.le (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) + qlog) := by rw [Real.exp_add]
  have hqLowerLog : Real.log P ≤ (n : ℝ) + qlog := by
    have h := Real.log_le_log hPpos hPExp
    simpa using h
  have hqLower : -((n : ℝ) * rationalMatrixEntryBitBound B + n) ≤ qlog := by
    have hp := hperbounds.1
    simp only [P, n] at hqLowerLog hp ⊢
    linarith
  have hbudget : (n : ℝ) * rationalMatrixEntryBitBound B + n ≤
      (explicitCertificateMagnitudeBudget B : ℕ) := by
    simp only [explicitCertificateMagnitudeBudget, n]
    push_cast
    nlinarith
  have hupperBudget : (n : ℝ) ^ 2 + n ≤
      (explicitCertificateMagnitudeBudget B : ℕ) := by
    have hL : 1 ≤ rationalMatrixEntryBitBound B := by
      rw [rationalMatrixEntryBitBound]
      omega
    simp only [explicitCertificateMagnitudeBudget, n]
    push_cast
    nlinarith
  rw [abs_le]
  constructor
  · exact (neg_le_neg hbudget).trans hqLower
  · exact hqUpper.trans hupperBudget

end BeyondBethe

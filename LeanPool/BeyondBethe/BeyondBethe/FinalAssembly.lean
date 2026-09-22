/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.NumericalScales
import LeanPool.BeyondBethe.BeyondBethe.AlgorithmicSpec
import LeanPool.BeyondBethe.BeyondBethe.Smoothing
import LeanPool.BeyondBethe.BeyondBethe.KuhnMatching

/-! # Final Assembly -/

open scoped BigOperators

namespace BeyondBethe

/-- A rational scaling factor that is positive on every nonnegative matrix
and dominates each entry.  Using `1 + sum A` avoids a special case for the
largest entry while retaining polynomial bit complexity. -/
def rationalNormalizationScale {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  1 + ∑ i, ∑ j, A i j

/-- Entrywise normalization used before smoothing. -/
def normalizedRationalMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ A i j / rationalNormalizationScale A

/-- The factor assigned to one matrix coordinate when forming the support
floor. -/
def rationalSupportFactor {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (p : Fin n × Fin n) : ℚ :=
  if B p.1 p.2 = 0 then 1 else B p.1 p.2

/-- A rational lower bound for every nonzero entry of a normalized matrix.
Zero entries contribute the neutral factor. -/
def rationalSupportFloor {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  ∏ p ∈ (Finset.univ.product Finset.univ),
    rationalSupportFactor B p

/-- The paper's rational smoothing level, applied after normalization. -/
def rationalSmoothingDelta {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (χ : ℚ) : ℚ :=
  min (1 / (2 * n))
    (χ * rationalSupportFloor B ^ n / (4 * Nat.factorial n))

/-- The canonical positive rational perturbation used by the final
algorithm. -/
def smoothedRationalMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let B := normalizedRationalMatrix A
  let δ := rationalSmoothingDelta B χ
  fun i j ↦ B i j + δ

/-- What the certified finite-precision routine must provide on positive
rational matrices.  Its numerical loss is exactly the allowance in Lemma 24
of the paper. -/
structure CertifiedPositiveRoutine (ε : ℝ) where
  alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ
  positiveOutput : ∀ {n : ℕ}, 2 ≤ n →
    ∀ A : Matrix (Fin n) (Fin n) ℚ,
      Matrix.Positive (fun i j ↦ (A i j : ℝ)) →
      0 < ((alg n A : ℚ) : ℝ)
  lower : ∀ {n : ℕ}, 2 ≤ n →
    ∀ A : Matrix (Fin n) (Fin n) ℚ,
      Matrix.Positive (fun i j ↦ (A i j : ℝ)) →
      ((alg n A : ℚ) : ℝ) ≤ ((Matrix.permanent A : ℚ) : ℝ)
  upper : ∀ {n : ℕ}, 2 ≤ n →
    ∀ A : Matrix (Fin n) (Fin n) ℚ,
      Matrix.Positive (fun i j ↦ (A i j : ℝ)) →
      ((Matrix.permanent A : ℚ) : ℝ) ≤
        (preSmoothingBase ε) ^ n * ((alg n A : ℚ) : ℝ)

/-- Executable entrywise nonnegativity test.  The outer algorithm uses this
guard to remain a polynomial-time total function on all rational matrices,
including inputs outside the approximation theorem's domain. -/
def rationalMatrixNonnegativeDecision {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : Bool := by
  letI : ∀ i j : Fin n, Decidable (0 ≤ A i j) := fun i j => inferInstance
  letI : ∀ i : Fin n, Decidable (∀ j : Fin n, 0 ≤ A i j) :=
    fun i => Fintype.decidableForallFintype
  exact @decide (∀ i : Fin n, ∀ j : Fin n, 0 ≤ A i j)
    Fintype.decidableForallFintype

theorem rationalMatrixNonnegativeDecision_eq_true_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixNonnegativeDecision A = true ↔ Matrix.Nonnegative A := by
  simp [rationalMatrixNonnegativeDecision, Matrix.Nonnegative]

/-- Rational wrapper around the positive-matrix routine.  Matrices of order
zero or one are evaluated exactly; a matrix with no support matching returns
zero; otherwise we normalize, smooth, call the positive routine, and undo the
normalization and smoothing factor. -/
def completedAlgorithm
    {ε : ℝ} (routine : CertifiedPositiveRoutine ε) (χ : ℚ) :
    ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ := by
  exact fun n A ↦
    if rationalMatrixNonnegativeDecision A then
      if n < 2 then Matrix.permanent A
      else if kuhnSupportMatchingDecision A then
        let scale := rationalNormalizationScale A
        let lowerSmooth := routine.alg n (smoothedRationalMatrix A χ)
        scale ^ n * lowerSmooth / (1 + χ * n / 2)
      else 0
    else 0

theorem rationalNormalizationScale_pos
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) :
    0 < rationalNormalizationScale A := by
  have hsum : 0 ≤ ∑ i, ∑ j, A i j :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hA i j
  simp only [rationalNormalizationScale]
  linarith

theorem entry_le_rationalNormalizationScale
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) (i j : Fin n) :
    A i j ≤ rationalNormalizationScale A := by
  have hrow : A i j ≤ ∑ k, A i k :=
    Finset.single_le_sum (fun k _ ↦ hA i k) (Finset.mem_univ j)
  have htotal : (∑ k, A i k) ≤ ∑ r, ∑ k, A r k :=
    Finset.single_le_sum
      (fun r _ ↦ Finset.sum_nonneg fun k _ ↦ hA r k)
      (Finset.mem_univ i)
  simp only [rationalNormalizationScale]
  linarith

theorem normalizedRationalMatrix_nonnegative
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) :
    Matrix.Nonnegative (normalizedRationalMatrix A) := by
  intro i j
  exact div_nonneg (hA i j) (rationalNormalizationScale_pos hA).le

theorem normalizedRationalMatrix_le_one
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) (i j : Fin n) :
    normalizedRationalMatrix A i j ≤ 1 := by
  rw [normalizedRationalMatrix, div_le_one
    (rationalNormalizationScale_pos hA)]
  exact entry_le_rationalNormalizationScale hA i j

theorem normalizedRationalMatrix_ne_zero_iff
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) (i j : Fin n) :
    normalizedRationalMatrix A i j ≠ 0 ↔ A i j ≠ 0 := by
  rw [normalizedRationalMatrix, div_ne_zero_iff]
  simp [ne_of_gt (rationalNormalizationScale_pos hA)]

theorem normalizedRationalMatrix_hasPerfectMatching
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A)
    (hmatch : Matrix.HasPerfectMatching A) :
    Matrix.HasPerfectMatching (normalizedRationalMatrix A) := by
  obtain ⟨σ, hσ⟩ := hmatch
  exact ⟨σ, fun i ↦ (normalizedRationalMatrix_ne_zero_iff hA _ _).2 (hσ i)⟩

theorem rationalSupportFactor_pos
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : Matrix.Nonnegative B) (p : Fin n × Fin n) :
    0 < rationalSupportFactor B p := by
  rw [rationalSupportFactor]
  split_ifs with hp
  · norm_num
  · exact lt_of_le_of_ne (hB p.1 p.2) (Ne.symm hp)

theorem rationalSupportFactor_le_one
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB1 : ∀ i j, B i j ≤ 1) (p : Fin n × Fin n) :
    rationalSupportFactor B p ≤ 1 := by
  rw [rationalSupportFactor]
  split_ifs
  · rfl
  · exact hB1 p.1 p.2

theorem finset_prod_le_factor
    {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → ℚ} {p : α}
    (hp : p ∈ s) (hpos : ∀ q ∈ s, 0 ≤ f q)
    (hone : ∀ q ∈ s, f q ≤ 1) :
    ∏ q ∈ s, f q ≤ f p := by
  rw [← Finset.prod_erase_mul s f hp]
  have herase : ∏ q ∈ s.erase p, f q ≤ 1 :=
    Finset.prod_le_one₀
      (fun q hq ↦ hpos q (Finset.mem_of_mem_erase hq))
      (fun q hq ↦ hone q (Finset.mem_of_mem_erase hq))
  exact (mul_le_mul_of_nonneg_right herase (hpos p hp)).trans_eq (one_mul _)

theorem rationalSupportFloor_pos
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : Matrix.Nonnegative B) :
    0 < rationalSupportFloor B := by
  rw [rationalSupportFloor]
  exact Finset.prod_pos fun p _ ↦ rationalSupportFactor_pos hB p

theorem rationalSupportFloor_le_entry
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : Matrix.Nonnegative B) (hB1 : ∀ i j, B i j ≤ 1)
    (i j : Fin n) (hij : B i j ≠ 0) :
    rationalSupportFloor B ≤ B i j := by
  let s : Finset (Fin n × Fin n) := Finset.univ.product Finset.univ
  have hp : (i, j) ∈ s := by simp [s]
  have hprod := finset_prod_le_factor hp
    (fun p _ ↦ (rationalSupportFactor_pos hB p).le)
    (fun p _ ↦ rationalSupportFactor_le_one hB1 p)
  simpa [rationalSupportFloor, rationalSupportFactor, hij, s] using hprod

theorem cast_rationalNormalizationScale
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    ((rationalNormalizationScale A : ℚ) : ℝ) =
      1 + ∑ i, ∑ j, (A i j : ℝ) := by
  simp [rationalNormalizationScale]

theorem cast_normalizedRationalMatrix
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    ((normalizedRationalMatrix A i j : ℚ) : ℝ) =
      (A i j : ℝ) / (1 + ∑ r, ∑ k, (A r k : ℝ)) := by
  simp [normalizedRationalMatrix, cast_rationalNormalizationScale]

theorem cast_rationalSupportFloor
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    ((rationalSupportFloor B : ℚ) : ℝ) =
      ∏ p ∈ (Finset.univ.product Finset.univ),
        if B p.1 p.2 = 0 then 1 else (B p.1 p.2 : ℝ) := by
  classical
  rw [rationalSupportFloor]
  push_cast
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases h : B p.1 p.2 = 0 <;>
    simp [rationalSupportFactor, h]

theorem cast_rationalSmoothingDelta
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (χ : ℚ) :
    ((rationalSmoothingDelta B χ : ℚ) : ℝ) =
      smoothingDelta n (rationalSupportFloor B : ℝ) (χ : ℝ) := by
  simp [rationalSmoothingDelta, smoothingDelta]

theorem cast_smoothedRationalMatrix
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (χ : ℚ)
    (i j : Fin n) :
    ((smoothedRationalMatrix A χ i j : ℚ) : ℝ) =
      (normalizedRationalMatrix A i j : ℝ) +
        smoothingDelta n (rationalSupportFloor (normalizedRationalMatrix A) : ℝ)
          (χ : ℝ) := by
  simp [smoothedRationalMatrix, cast_rationalSmoothingDelta]

theorem cast_normalizedRationalMatrix_nonnegative
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) :
    Matrix.Nonnegative
      (fun i j ↦ ((normalizedRationalMatrix A i j : ℚ) : ℝ)) := by
  intro i j
  change 0 ≤ ((normalizedRationalMatrix A i j : ℚ) : ℝ)
  exact_mod_cast normalizedRationalMatrix_nonnegative hA i j

theorem cast_normalizedRationalMatrix_le_one
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A) (i j : Fin n) :
    ((normalizedRationalMatrix A i j : ℚ) : ℝ) ≤ 1 := by
  exact_mod_cast normalizedRationalMatrix_le_one hA i j

theorem cast_rationalSupportFloor_pos
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : Matrix.Nonnegative B) :
    0 < ((rationalSupportFloor B : ℚ) : ℝ) := by
  exact_mod_cast rationalSupportFloor_pos hB

theorem cast_rationalSupportFloor_le_entry
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : Matrix.Nonnegative B) (hB1 : ∀ i j, B i j ≤ 1)
    (i j : Fin n)
    (hij : ((B i j : ℚ) : ℝ) ≠ 0) :
    ((rationalSupportFloor B : ℚ) : ℝ) ≤ (B i j : ℝ) := by
  have hijq : B i j ≠ 0 := by exact_mod_cast hij
  exact_mod_cast rationalSupportFloor_le_entry hB hB1 i j hijq

theorem cast_normalizedRationalMatrix_hasPerfectMatching
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Nonnegative A)
    (hmatch : Matrix.HasPerfectMatching A) :
    Matrix.HasPerfectMatching
      (fun i j ↦ ((normalizedRationalMatrix A i j : ℚ) : ℝ)) := by
  obtain ⟨σ, hσ⟩ := normalizedRationalMatrix_hasPerfectMatching hA hmatch
  refine ⟨σ, ?_⟩
  intro i
  change ((normalizedRationalMatrix A (σ i) i : ℚ) : ℝ) ≠ 0
  exact_mod_cast hσ i

/-- The explicit rational perturbation satisfies the real smoothing lemma.
This closes the zero-entry reduction independently of numerical convex
optimization. -/
theorem canonical_smoothing_comparison
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : Matrix.Nonnegative A)
    (hmatch : Matrix.HasPerfectMatching A)
    (χ : ℚ) (hχ : 0 < (χ : ℝ)) :
    let B : Matrix (Fin n) (Fin n) ℝ :=
      fun i j ↦ ((normalizedRationalMatrix A i j : ℚ) : ℝ)
    let Atilde : Matrix (Fin n) (Fin n) ℝ :=
      fun i j ↦ ((smoothedRationalMatrix A χ i j : ℚ) : ℝ)
    Matrix.permanent B ≤ Matrix.permanent Atilde ∧
      Matrix.permanent Atilde ≤
        (1 + (χ : ℝ) * n / 2) * Matrix.permanent B := by
  dsimp only
  let Bq := normalizedRationalMatrix A
  let m : ℝ := (rationalSupportFloor Bq : ℚ)
  have hBq0 : Matrix.Nonnegative Bq := normalizedRationalMatrix_nonnegative hA
  have hBq1 : ∀ i j, Bq i j ≤ 1 := normalizedRationalMatrix_le_one hA
  have hm : 0 < m := cast_rationalSupportFloor_pos hBq0
  have hcomparison := smoothing_comparison_explicit
    (fun i j ↦ ((Bq i j : ℚ) : ℝ))
    (m := m) (χ := (χ : ℝ)) (by simpa using hn) hm hχ
    (cast_normalizedRationalMatrix_nonnegative hA)
    (cast_normalizedRationalMatrix_le_one hA)
    (fun i j hij ↦ cast_rationalSupportFloor_le_entry hBq0 hBq1 i j hij)
    (cast_normalizedRationalMatrix_hasPerfectMatching hA hmatch)
  simpa [Bq, m, cast_smoothedRationalMatrix] using hcomparison

theorem cast_smoothedRationalMatrix_positive
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : Matrix.Nonnegative A)
    (χ : ℚ) (hχ : 0 < (χ : ℝ)) :
    Matrix.Positive
      (fun i j ↦ ((smoothedRationalMatrix A χ i j : ℚ) : ℝ)) := by
  let Bq := normalizedRationalMatrix A
  have hBq0 : Matrix.Nonnegative Bq := normalizedRationalMatrix_nonnegative hA
  have hm : 0 < ((rationalSupportFloor Bq : ℚ) : ℝ) :=
    cast_rationalSupportFloor_pos hBq0
  have hδ : 0 < smoothingDelta n
      ((rationalSupportFloor Bq : ℚ) : ℝ) (χ : ℝ) :=
    smoothingDelta_pos hn hm hχ
  intro i j
  change 0 < ((smoothedRationalMatrix A χ i j : ℚ) : ℝ)
  rw [cast_smoothedRationalMatrix]
  exact add_pos_of_nonneg_of_pos
    (cast_normalizedRationalMatrix_nonnegative hA i j) hδ

theorem cast_permanent_eq_scale_pow_mul_normalized
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : Matrix.Nonnegative A) :
    ((Matrix.permanent A : ℚ) : ℝ) =
      ((rationalNormalizationScale A : ℚ) : ℝ) ^ n *
        Matrix.permanent
          (fun i j ↦ ((normalizedRationalMatrix A i j : ℚ) : ℝ)) := by
  let scale : ℝ := (rationalNormalizationScale A : ℚ)
  let B : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ ((normalizedRationalMatrix A i j : ℚ) : ℝ)
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact_mod_cast rationalNormalizationScale_pos hA
  have hmatrix : (fun i j ↦ ((A i j : ℚ) : ℝ)) = scale • B := by
    ext i j
    change (A i j : ℝ) = scale * B i j
    dsimp only [B, scale]
    rw [cast_normalizedRationalMatrix]
    rw [cast_rationalNormalizationScale]
    have hden : 1 + ∑ r, ∑ k, (A r k : ℝ) ≠ 0 := by
      simpa [scale, cast_rationalNormalizationScale] using hscale.ne'
    field_simp [hden]
  rw [Matrix.cast_permanent_rat, hmatrix, Matrix.permanent_scale_real]
  simp [scale, B]

theorem cast_completedAlgorithm_of_large_matching
    {ε : ℝ} (routine : CertifiedPositiveRoutine ε) (χ : ℚ)
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : Matrix.Nonnegative A)
    (hmatch : Matrix.HasPerfectMatching A) :
    (((completedAlgorithm routine χ n A : ℚ) : ℝ)) =
      ((rationalNormalizationScale A : ℚ) : ℝ) ^ n *
        ((routine.alg n (smoothedRationalMatrix A χ) : ℚ) : ℝ) /
          (1 + (χ : ℝ) * n / 2) := by
  have hnot : ¬n < 2 := not_lt.mpr hn
  have hdecision : kuhnSupportMatchingDecision A = true :=
    (kuhnSupportMatchingDecision_eq_true_iff A).2 hmatch
  have hnonnegative : rationalMatrixNonnegativeDecision A = true :=
    (rationalMatrixNonnegativeDecision_eq_true_iff A).2 hA
  simp [completedAlgorithm, hnonnegative, hnot, hdecision]

/-- The explicit rational wrapper inherits the desired two-sided estimate on
the support-matching branch. -/
theorem completedAlgorithm_guarantee_of_matching
    {ε : ℝ} (hε : 0 < ε)
    (routine : CertifiedPositiveRoutine ε) (χ : ℚ)
    (hχ : 0 < (χ : ℝ)) (hχsmall : (χ : ℝ) ≤ ε / 2)
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : Matrix.Nonnegative A)
    (hmatch : Matrix.HasPerfectMatching A) :
    ((completedAlgorithm routine χ n A : ℚ) : ℝ) ≤
        ((Matrix.permanent A : ℚ) : ℝ) ∧
      ((Matrix.permanent A : ℚ) : ℝ) ≤
        (finalBase ε) ^ n *
          ((completedAlgorithm routine χ n A : ℚ) : ℝ) := by
  let Bq := normalizedRationalMatrix A
  let Aq := smoothedRationalMatrix A χ
  let lower : ℝ := (routine.alg n Aq : ℚ)
  have hnpos : 0 < n := by omega
  have hAqpos : Matrix.Positive (fun i j ↦ ((Aq i j : ℚ) : ℝ)) := by
    simpa only [Aq] using cast_smoothedRationalMatrix_positive hnpos A hA χ hχ
  have hlowerPos : 0 < lower := routine.positiveOutput hn Aq hAqpos
  have hcertLower : lower ≤ Matrix.permanent
      (fun i j ↦ ((Aq i j : ℚ) : ℝ)) := by
    rw [← Matrix.cast_permanent_rat]
    exact routine.lower hn Aq hAqpos
  have hcertUpper : Matrix.permanent
      (fun i j ↦ ((Aq i j : ℚ) : ℝ)) ≤
        (preSmoothingBase ε) ^ n * lower := by
    rw [← Matrix.cast_permanent_rat]
    exact routine.upper hn Aq hAqpos
  obtain ⟨hsmoothLower, hsmoothUpper⟩ :=
    canonical_smoothing_comparison hnpos A hA hmatch χ hχ
  have hassembly := assemble_smoothing_and_numerics hε hχ.le hχsmall
    hlowerPos hsmoothLower hsmoothUpper hcertLower hcertUpper
  have hscale : 0 < ((rationalNormalizationScale A : ℚ) : ℝ) := by
    exact_mod_cast rationalNormalizationScale_pos hA
  have houtput := cast_completedAlgorithm_of_large_matching routine χ hn A hA hmatch
  have hper := cast_permanent_eq_scale_pow_mul_normalized A hA
  constructor
  · rw [houtput, hper]
    have hmul := mul_le_mul_of_nonneg_left hassembly.1
      (pow_nonneg hscale.le n)
    simpa [lower, Aq, div_eq_mul_inv, mul_assoc] using hmul
  · rw [houtput, hper]
    have hmul := mul_le_mul_of_nonneg_left hassembly.2
      (pow_nonneg hscale.le n)
    simpa [lower, Aq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem exactPositiveCertificate_mono
    {ε ε' : ℝ} (hε : ε' ≤ ε)
    (hcert : ExactPositiveCertificate ε) :
    ExactPositiveCertificate ε' := by
  intro n hn A hA
  obtain ⟨X, hX, hlower, hgap⟩ := hcert hn A hA
  refine ⟨X, hX, hlower, hgap.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

theorem one_lt_finalBase_of_le_log_two_half
    {ε : ℝ} (hε : 0 < ε) (hbound : ε ≤ Real.log 2 / 2) :
    1 < finalBase ε := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [finalBase, ← Real.exp_log hsqrt, ← Real.exp_add,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.one_lt_exp_iff]
  nlinarith

theorem cast_permanent_nonnegative
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : Matrix.Nonnegative A) :
    0 ≤ ((Matrix.permanent A : ℚ) : ℝ) := by
  rw [Matrix.cast_permanent_rat]
  apply Matrix.permanent_nonneg_real
  intro i j
  change 0 ≤ ((A i j : ℚ) : ℝ)
  exact_mod_cast hA i j

/-- All nonnumerical branches of Theorem 1: exact treatment of orders zero
and one, the zero-support case, normalization, smoothing, and rescaling. -/
theorem completedAlgorithm_guarantee
    {ε : ℝ} (hε : 0 < ε) (hεbound : ε ≤ Real.log 2 / 2)
    (routine : CertifiedPositiveRoutine ε) (χ : ℚ)
    (hχ : 0 < (χ : ℝ)) (hχsmall : (χ : ℝ) ≤ ε / 2) :
    ∀ n (A : Matrix (Fin n) (Fin n) ℚ),
      Matrix.Nonnegative A →
      ((completedAlgorithm routine χ n A : ℚ) : ℝ) ≤
          ((Matrix.permanent A : ℚ) : ℝ) ∧
        ((Matrix.permanent A : ℚ) : ℝ) ≤
          (finalBase ε) ^ n *
            ((completedAlgorithm routine χ n A : ℚ) : ℝ) := by
  intro n A hA
  have hnonnegative : rationalMatrixNonnegativeDecision A = true :=
    (rationalMatrixNonnegativeDecision_eq_true_iff A).2 hA
  by_cases hn : n < 2
  · have hout : completedAlgorithm routine χ n A = Matrix.permanent A := by
      simp [completedAlgorithm, hnonnegative, hn]
    rw [hout]
    refine ⟨le_rfl, ?_⟩
    have hbase : 1 ≤ finalBase ε :=
      (one_lt_finalBase_of_le_log_two_half hε hεbound).le
    have hpow : 1 ≤ (finalBase ε) ^ n := one_le_pow₀ hbase
    simpa using mul_le_mul_of_nonneg_right hpow
      (cast_permanent_nonnegative A hA)
  · have hnlarge : 2 ≤ n := by omega
    by_cases hmatch : Matrix.HasPerfectMatching A
    · exact completedAlgorithm_guarantee_of_matching hε routine χ hχ
        hχsmall hnlarge A hA hmatch
    · have hper : Matrix.permanent A = 0 :=
        Matrix.permanent_eq_zero_of_noPerfectMatching A hmatch
      have hdecision : kuhnSupportMatchingDecision A = false :=
        (kuhnSupportMatchingDecision_eq_false_iff A).2 hmatch
      simp [completedAlgorithm, hnonnegative, hn, hdecision, hper]

/-- The smoothing budget is a fixed rational function of the requested
improvement and is therefore explicit algorithmic data. -/
def canonicalSmoothingParameter (ε : ℚ) : ℚ := ε / 4

theorem canonicalSmoothingParameter_pos {ε : ℚ} (hε : 0 < ε) :
    0 < (canonicalSmoothingParameter ε : ℝ) := by
  rw [canonicalSmoothingParameter]
  exact_mod_cast div_pos hε (by norm_num : (0 : ℚ) < 4)

theorem canonicalSmoothingParameter_le_half {ε : ℚ} (hε : 0 < ε) :
    (canonicalSmoothingParameter ε : ℝ) ≤ (ε : ℝ) / 2 := by
  norm_num [canonicalSmoothingParameter]
  have hεreal : 0 ≤ (ε : ℝ) := by exact_mod_cast hε.le
  linarith

end BeyondBethe

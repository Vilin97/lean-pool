/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.RootEdge
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# The crossed root--edge `(1,2)` obstruction

This file excludes the crossed term in the root--edge minimax.  The proof uses the positive
separator with weights `1, 1, 2`.  Three scalar norm tangents reduce it to one fixed rational
Gram certificate; radial secants use only the sibling separation and the unit-ball bounds.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

/-- Failure slack of the crossed `(1,2)` term for a red root--second-child edge. -/
def redRootEdgeType12Slack
    (c M r₂ b₁ b₂ rootToBlueFirst secondCross : ℝ) : ℝ :=
  r₂ + rootToBlueFirst + secondCross + M -
    2 * c * (r₂ + (b₁ + b₂ + M) / 2)

private abbrev Five := Fin 5

private abbrev Three := Fin 3

private def redSeparationMultiplier : ℝ := 4713 / 20000

private def blueSeparationMultiplier : ℝ := 7587 / 20000

private def factorRow : Three → Five → ℝ
  | 0 => ![590 / 10000, 4584 / 10000, -1112 / 10000, -3575 / 10000, 2862 / 10000]
  | 1 => ![3933 / 10000, 3465 / 10000, 8248 / 10000, -821 / 10000, -4181 / 10000]
  | 2 => ![7438 / 10000, 205 / 10000, 417 / 10000, 6703 / 10000, 6674 / 10000]

private def factorGram : Matrix Five Five ℝ :=
  ∑ k, Matrix.vecMulVec (factorRow k) (factorRow k)

private def factorGramValues : Matrix Five Five ℝ :=
  !![71140433 / 100000000, 3571439 / 20000000, 697699 / 2000000,
        44518671 / 100000000, 34885919 / 100000000;
      3571439 / 20000000, 16530653 / 50000000, 23567397 / 100000000,
        -357169 / 2000000, 413 / 100000000;
      697699 / 2000000, 23567397 / 100000000, 69439937 / 100000000,
        -1057 / 100000000, -17442187 / 50000000;
      44518671 / 100000000, -357169 / 2000000, -1057 / 100000000,
        467079 / 800000, 37936773 / 100000000;
      34885919 / 100000000, 413 / 100000000, -17442187 / 50000000,
        37936773 / 100000000, 70214081 / 100000000]

private theorem factorGram_eq_values : factorGram = factorGramValues := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorGram, factorGramValues, factorRow, Matrix.vecMulVec,
      Fin.sum_univ_three]

private def targetOffDiagonal : Matrix Five Five ℝ :=
  !![0, 5 / 28, 15 / 43, 5 / 28 + 4 / 15, 15 / 43;
      5 / 28, 0, redSeparationMultiplier, -5 / 28, 0;
      15 / 43, redSeparationMultiplier, 0, 0, -15 / 43;
      5 / 28 + 4 / 15, -5 / 28, 0, 0, blueSeparationMultiplier;
      15 / 43, 0, -15 / 43, blueSeparationMultiplier, 0]

private def pairSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

private def pairVector (r : ℝ) (i j : Five) : Five → ℝ :=
  fun k ↦ if k = i then 1 else if k = j then pairSign r else 0

private def pairCorrection (r : ℝ) (i j : Five) : Matrix Five Five ℝ :=
  |r| • Matrix.vecMulVec (pairVector r i j) (pairVector r i j)

private def residual (i j : Five) : ℝ :=
  targetOffDiagonal i j - factorGram i j

private def certificateMatrix : Matrix Five Five ℝ :=
  factorGram + (1 / 10000000 : ℝ) • 1 +
    pairCorrection (residual 0 1) 0 1 +
    pairCorrection (residual 0 2) 0 2 +
    pairCorrection (residual 0 3) 0 3 +
    pairCorrection (residual 0 4) 0 4 +
    pairCorrection (residual 1 2) 1 2 +
    pairCorrection (residual 1 3) 1 3 +
    pairCorrection (residual 1 4) 1 4 +
    pairCorrection (residual 2 3) 2 3 +
    pairCorrection (residual 2 4) 2 4 +
    pairCorrection (residual 3 4) 3 4

private theorem pairCorrection_posSemidef (r : ℝ) (i j : Five) :
    (pairCorrection r i j).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (pairVector r i j)).smul (abs_nonneg r)

private theorem certificateMatrix_posSemidef : certificateMatrix.PosSemidef := by
  have hfactor : factorGram.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact Matrix.posSemidef_vecMulVec_self_star (factorRow i)
  have hepsilon : ((1 / 10000000 : ℝ) • (1 : Matrix Five Five ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by norm_num)
  have h := hfactor.add hepsilon
  have h := h.add (pairCorrection_posSemidef (residual 0 1) 0 1)
  have h := h.add (pairCorrection_posSemidef (residual 0 2) 0 2)
  have h := h.add (pairCorrection_posSemidef (residual 0 3) 0 3)
  have h := h.add (pairCorrection_posSemidef (residual 0 4) 0 4)
  have h := h.add (pairCorrection_posSemidef (residual 1 2) 1 2)
  have h := h.add (pairCorrection_posSemidef (residual 1 3) 1 3)
  have h := h.add (pairCorrection_posSemidef (residual 1 4) 1 4)
  have h := h.add (pairCorrection_posSemidef (residual 2 3) 2 3)
  have h := h.add (pairCorrection_posSemidef (residual 2 4) 2 4)
  exact h.add (pairCorrection_posSemidef (residual 3 4) 3 4)

private theorem abs_mul_pairSign (r : ℝ) : |r| * pairSign r = r := by
  by_cases hr : 0 ≤ r
  · simp [pairSign, hr, abs_of_nonneg hr]
  · simp [pairSign, hr, abs_of_neg (lt_of_not_ge hr)]

@[simp]
private theorem pairCorrection_apply_pair (r : ℝ) {i j : Five} (hij : i ≠ j) :
    pairCorrection r i j i j = r := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hij.symm, abs_mul_pairSign]

@[simp]
private theorem pairCorrection_apply_pair_rev (r : ℝ) {i j : Five} (hij : i ≠ j) :
    pairCorrection r i j j i = r := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hij.symm, abs_mul_pairSign, mul_comm]

@[simp]
private theorem pairCorrection_apply_left_left (r : ℝ) {i j : Five} (_hij : i ≠ j) :
    pairCorrection r i j i i = |r| := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector]

@[simp]
private theorem pairCorrection_apply_right_right (r : ℝ) {i j : Five} (hij : i ≠ j) :
    pairCorrection r i j j j = |r| := by
  by_cases hr : 0 ≤ r <;>
    simp [pairCorrection, Matrix.vecMulVec, pairVector, pairSign, hij.symm, hr]

@[simp]
private theorem pairCorrection_apply_zero_left (r : ℝ) {i j k l : Five}
    (hki : k ≠ i) (hkj : k ≠ j) : pairCorrection r i j k l = 0 := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hki, hkj]

@[simp]
private theorem pairCorrection_apply_zero_right (r : ℝ) {i j k l : Five}
    (hli : l ≠ i) (hlj : l ≠ j) : pairCorrection r i j k l = 0 := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hli, hlj]

private theorem factorGram_apply_comm (i j : Five) : factorGram i j = factorGram j i := by
  simp only [factorGram, Matrix.sum_apply, Matrix.vecMulVec_apply]
  congr 1
  funext k
  ring

@[simp] private theorem factorGram_10 : factorGram 1 0 = factorGram 0 1 :=
  factorGram_apply_comm 1 0

@[simp] private theorem factorGram_20 : factorGram 2 0 = factorGram 0 2 :=
  factorGram_apply_comm 2 0

@[simp] private theorem factorGram_21 : factorGram 2 1 = factorGram 1 2 :=
  factorGram_apply_comm 2 1

@[simp] private theorem factorGram_30 : factorGram 3 0 = factorGram 0 3 :=
  factorGram_apply_comm 3 0

@[simp] private theorem factorGram_31 : factorGram 3 1 = factorGram 1 3 :=
  factorGram_apply_comm 3 1

@[simp] private theorem factorGram_32 : factorGram 3 2 = factorGram 2 3 :=
  factorGram_apply_comm 3 2

@[simp] private theorem factorGram_40 : factorGram 4 0 = factorGram 0 4 :=
  factorGram_apply_comm 4 0

@[simp] private theorem factorGram_41 : factorGram 4 1 = factorGram 1 4 :=
  factorGram_apply_comm 4 1

@[simp] private theorem factorGram_42 : factorGram 4 2 = factorGram 2 4 :=
  factorGram_apply_comm 4 2

@[simp] private theorem factorGram_43 : factorGram 4 3 = factorGram 3 4 :=
  factorGram_apply_comm 4 3

private theorem certificateMatrix_offDiagonal {i j : Five} (hij : i ≠ j) :
    certificateMatrix i j = targetOffDiagonal i j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [certificateMatrix, residual, targetOffDiagonal]

private def diagonal₀ : ℝ :=
  factorGram 0 0 + 1 / 10000000 + |residual 0 1| + |residual 0 2| +
    |residual 0 3| + |residual 0 4|

private def diagonal₁ : ℝ :=
  factorGram 1 1 + 1 / 10000000 + |residual 0 1| + |residual 1 2| +
    |residual 1 3| + |residual 1 4|

private def diagonal₂ : ℝ :=
  factorGram 2 2 + 1 / 10000000 + |residual 0 2| + |residual 1 2| +
    |residual 2 3| + |residual 2 4|

private def diagonal₃ : ℝ :=
  factorGram 3 3 + 1 / 10000000 + |residual 0 3| + |residual 1 3| +
    |residual 2 3| + |residual 3 4|

private def diagonal₄ : ℝ :=
  factorGram 4 4 + 1 / 10000000 + |residual 0 4| + |residual 1 4| +
    |residual 2 4| + |residual 3 4|

private theorem certificateMatrix_diagonal₀_eq : certificateMatrix 0 0 = diagonal₀ := by
  simp [certificateMatrix, diagonal₀]

private theorem certificateMatrix_diagonal₁_eq : certificateMatrix 1 1 = diagonal₁ := by
  simp [certificateMatrix, diagonal₁]

private theorem certificateMatrix_diagonal₂_eq : certificateMatrix 2 2 = diagonal₂ := by
  simp [certificateMatrix, diagonal₂]

private theorem certificateMatrix_diagonal₃_eq : certificateMatrix 3 3 = diagonal₃ := by
  simp [certificateMatrix, diagonal₃]

private theorem certificateMatrix_diagonal₄_eq : certificateMatrix 4 4 = diagonal₄ := by
  simp [certificateMatrix, diagonal₄]

private theorem certificateMatrix_diagonal₀ :
    certificateMatrix 0 0 = 2294557211 / 3225000000 := by
  rw [certificateMatrix_diagonal₀_eq]
  simp only [diagonal₀, residual]
  rw [factorGram_eq_values]
  simp [factorGramValues, targetOffDiagonal]
  norm_num [redSeparationMultiplier, blueSeparationMultiplier]

private theorem certificateMatrix_diagonal₁ :
    certificateMatrix 1 1 = 231458397 / 700000000 := by
  rw [certificateMatrix_diagonal₁_eq]
  simp only [diagonal₁, residual]
  rw [factorGram_eq_values]
  simp [factorGramValues, targetOffDiagonal]
  norm_num [redSeparationMultiplier, blueSeparationMultiplier]

private theorem certificateMatrix_diagonal₂ :
    certificateMatrix 2 2 = 119445887 / 172000000 := by
  rw [certificateMatrix_diagonal₂_eq]
  simp only [diagonal₂, residual]
  rw [factorGram_eq_values]
  simp [factorGramValues, targetOffDiagonal]
  norm_num [redSeparationMultiplier, blueSeparationMultiplier]

private theorem certificateMatrix_diagonal₃ :
    certificateMatrix 3 3 = 87591241 / 150000000 := by
  rw [certificateMatrix_diagonal₃_eq]
  simp only [diagonal₃, residual]
  rw [factorGram_eq_values]
  simp [factorGramValues, targetOffDiagonal]
  norm_num [redSeparationMultiplier, blueSeparationMultiplier]

private theorem certificateMatrix_diagonal₄ :
    certificateMatrix 4 4 = 301942251 / 430000000 := by
  rw [certificateMatrix_diagonal₄_eq]
  simp only [diagonal₄, residual]
  rw [factorGram_eq_values]
  simp [factorGramValues, targetOffDiagonal]
  norm_num [redSeparationMultiplier, blueSeparationMultiplier]

private theorem gram_sum_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Five → E) :
    0 ≤ ∑ i, ∑ j, certificateMatrix i j * ⟪v i, v j⟫_ℝ := by
  have hmatrix := certificateMatrix_posSemidef.hadamard (Matrix.posSemidef_gram ℝ v)
  have h := hmatrix.dotProduct_mulVec_nonneg (fun _ ↦ (1 : ℝ))
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using h

private theorem certificate_gram_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) :
    0 ≤ certificateMatrix 0 0 * ‖e‖ ^ 2 + certificateMatrix 1 1 * ‖p₁‖ ^ 2 +
      certificateMatrix 2 2 * ‖p₂‖ ^ 2 + certificateMatrix 3 3 * ‖w₁‖ ^ 2 +
      certificateMatrix 4 4 * ‖w₂‖ ^ 2 +
      2 * (5 / 28) * ⟪e, p₁⟫_ℝ + 2 * (15 / 43) * ⟪e, p₂⟫_ℝ +
      2 * (5 / 28 + 4 / 15) * ⟪e, w₁⟫_ℝ + 2 * (15 / 43) * ⟪e, w₂⟫_ℝ +
      2 * redSeparationMultiplier * ⟪p₁, p₂⟫_ℝ - 2 * (5 / 28) * ⟪p₁, w₁⟫_ℝ -
      2 * (15 / 43) * ⟪p₂, w₂⟫_ℝ +
      2 * blueSeparationMultiplier * ⟪w₁, w₂⟫_ℝ := by
  let v : Five → E := ![e, p₁, p₂, w₁, w₂]
  have h := gram_sum_nonneg v
  simp [Fin.sum_univ_five, v] at h
  rw [certificateMatrix_offDiagonal (by decide : (0 : Five) ≠ 1),
    certificateMatrix_offDiagonal (by decide : (0 : Five) ≠ 2),
    certificateMatrix_offDiagonal (by decide : (0 : Five) ≠ 3),
    certificateMatrix_offDiagonal (by decide : (0 : Five) ≠ 4),
    certificateMatrix_offDiagonal (by decide : (1 : Five) ≠ 0),
    certificateMatrix_offDiagonal (by decide : (1 : Five) ≠ 2),
    certificateMatrix_offDiagonal (by decide : (1 : Five) ≠ 3),
    certificateMatrix_offDiagonal (by decide : (1 : Five) ≠ 4),
    certificateMatrix_offDiagonal (by decide : (2 : Five) ≠ 0),
    certificateMatrix_offDiagonal (by decide : (2 : Five) ≠ 1),
    certificateMatrix_offDiagonal (by decide : (2 : Five) ≠ 3),
    certificateMatrix_offDiagonal (by decide : (2 : Five) ≠ 4),
    certificateMatrix_offDiagonal (by decide : (3 : Five) ≠ 0),
    certificateMatrix_offDiagonal (by decide : (3 : Five) ≠ 1),
    certificateMatrix_offDiagonal (by decide : (3 : Five) ≠ 2),
    certificateMatrix_offDiagonal (by decide : (3 : Five) ≠ 4),
    certificateMatrix_offDiagonal (by decide : (4 : Five) ≠ 0),
    certificateMatrix_offDiagonal (by decide : (4 : Five) ≠ 1),
    certificateMatrix_offDiagonal (by decide : (4 : Five) ≠ 2),
    certificateMatrix_offDiagonal (by decide : (4 : Five) ≠ 3)] at h
  simp [targetOffDiagonal, real_inner_comm] at h
  nlinarith

private theorem weighted_norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight alpha : ℝ) (halpha : 0 < alpha) :
    weight * ‖x‖ ≤ alpha * ‖x‖ ^ 2 + weight ^ 2 / (4 * alpha) := by
  have hdiv : (4 * alpha) * (weight ^ 2 / (4 * alpha)) = weight ^ 2 := by
    field_simp [halpha.ne']
  nlinarith [sq_nonneg (2 * alpha * ‖x‖ - weight)]

private theorem radial_secant {r d l u : ℝ} (hd : 0 ≤ d) (hl : l ≤ r) (hu : r ≤ u)
    (hsum : 0 < l + u) :
    -d * r ≤ -d / (l + u) * r ^ 2 - d * l * u / (l + u) := by
  have hproduct : 0 ≤ (r - l) * (u - r) :=
    mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  have hbase : r ^ 2 + l * u ≤ (l + u) * r := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (div_nonneg hd hsum.le)
  field_simp [hsum.ne'] at hscaled ⊢
  nlinarith

private theorem norm_sub_sub_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x y : E) :
    ‖e - x - y‖ ^ 2 = ‖e‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      2 * ⟪e, x⟫_ℝ - 2 * ⟪e, y⟫_ℝ + 2 * ⟪x, y⟫_ℝ := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left]
  ring

private theorem norm_sub_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x : E) :
    ‖e - x‖ ^ 2 = ‖e‖ ^ 2 + ‖x‖ ^ 2 - 2 * ⟪e, x⟫_ℝ := by
  rw [norm_sub_sq_real]
  ring

private def firstBlueRadialPenalty (c : ℝ) : ℝ := (5 * c - 1) / 4

private def secondBlueRadialPenalty (c : ℝ) : ℝ := (5 * c + 1) / 4

private def secondRedRadialPenalty (c : ℝ) : ℝ := 2 * c - 1

private def balance₀ : ℝ :=
  certificateMatrix 0 0 + 5 / 28 + 15 / 43 + 4 / 15

private def balance₁ : ℝ :=
  certificateMatrix 1 1 + 5 / 28 + redSeparationMultiplier

private def balance₂ (c : ℝ) : ℝ :=
  certificateMatrix 2 2 + 15 / 43 + redSeparationMultiplier -
    secondRedRadialPenalty c / c

private def balance₃ (c : ℝ) : ℝ :=
  certificateMatrix 3 3 + 5 / 28 + 4 / 15 + blueSeparationMultiplier -
    firstBlueRadialPenalty c / c

private def balance₄ (c : ℝ) : ℝ :=
  certificateMatrix 4 4 + 15 / 43 + blueSeparationMultiplier -
    secondBlueRadialPenalty c / c

private theorem balance₀_nonneg : 0 ≤ balance₀ := by
  rw [balance₀, certificateMatrix_diagonal₀]
  norm_num

private theorem balance₁_nonneg : 0 ≤ balance₁ := by
  rw [balance₁, certificateMatrix_diagonal₁]
  norm_num [redSeparationMultiplier]

private theorem balance₂_nonneg : 0 ≤ balance₂ barC := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  have hc := barC_pos
  rw [balance₂, certificateMatrix_diagonal₂]
  norm_num [redSeparationMultiplier, secondRedRadialPenalty] at hlower hupper ⊢
  field_simp [hc.ne'] at ⊢
  nlinarith

private theorem balance₃_nonneg : 0 ≤ balance₃ barC := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  have hc := barC_pos
  rw [balance₃, certificateMatrix_diagonal₃]
  norm_num [blueSeparationMultiplier, firstBlueRadialPenalty] at hlower hupper ⊢
  field_simp [hc.ne'] at ⊢
  nlinarith

private theorem balance₄_nonneg : 0 ≤ balance₄ barC := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  have hc := barC_pos
  rw [balance₄, certificateMatrix_diagonal₄]
  norm_num [blueSeparationMultiplier, secondBlueRadialPenalty] at hlower hupper ⊢
  field_simp [hc.ne'] at ⊢
  nlinarith

private def certificateUpper (c : ℝ) : ℝ :=
  7 / 5 + 129 / 80 + 15 / 16 -
    (3 * c - 2) / 2 * c - (9 * c - 7) / 4 * c -
    firstBlueRadialPenalty c * (c - 1) / c -
    secondBlueRadialPenalty c * (c - 1) / c -
    secondRedRadialPenalty c * (c - 1) / c - 1 / 2 +
    balance₀ + balance₁ + balance₂ c + balance₃ c + balance₄ c -
    (redSeparationMultiplier + blueSeparationMultiplier) * c ^ 2

private theorem certificateUpper_neg : certificateUpper barC < 0 := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  have hc := barC_pos
  rw [certificateUpper, balance₀, balance₁, balance₂, balance₃, balance₄,
    certificateMatrix_diagonal₀, certificateMatrix_diagonal₁,
    certificateMatrix_diagonal₂, certificateMatrix_diagonal₃,
    certificateMatrix_diagonal₄]
  norm_num [redSeparationMultiplier, blueSeparationMultiplier, firstBlueRadialPenalty,
    secondBlueRadialPenalty, secondRedRadialPenalty] at hlower hupper ⊢
  field_simp [hc.ne'] at ⊢
  nlinarith [sq_nonneg (barC - 13866128436518096 / 10 ^ 16)]

private theorem tangentQuadratic_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖) (hblueSeparation : barC ≤ ‖w₁ - w₂‖) :
    5 / 28 * ‖e - p₁ - w₁‖ ^ 2 + 15 / 43 * ‖e - p₂ - w₂‖ ^ 2 +
        4 / 15 * ‖e - w₁‖ ^ 2 -
        firstBlueRadialPenalty barC / barC * ‖w₁‖ ^ 2 -
        secondBlueRadialPenalty barC / barC * ‖w₂‖ ^ 2 -
        secondRedRadialPenalty barC / barC * ‖p₂‖ ^ 2 ≤
      balance₀ + balance₁ + balance₂ barC + balance₃ barC + balance₄ barC -
        (redSeparationMultiplier + blueSeparationMultiplier) * barC ^ 2 := by
  have hredSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    exact (sq_le_sq₀ barC_pos.le (norm_nonneg _)).2 hredSeparation
  have hblueSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    exact (sq_le_sq₀ barC_pos.le (norm_nonneg _)).2 hblueSeparation
  rw [norm_sub_sq_real] at hredSq hblueSq
  have hredScaled := mul_le_mul_of_nonneg_left hredSq
    (show 0 ≤ redSeparationMultiplier by norm_num [redSeparationMultiplier])
  have hblueScaled := mul_le_mul_of_nonneg_left hblueSq
    (show 0 ≤ blueSeparationMultiplier by norm_num [blueSeparationMultiplier])
  have hp₁Sq : ‖p₁‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg p₁]
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg w₁]
  have hw₂Sq : ‖w₂‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg w₂]
  have hbalance₁ := mul_le_mul_of_nonneg_left hp₁Sq balance₁_nonneg
  have hbalance₂ := mul_le_mul_of_nonneg_left hp₂Sq balance₂_nonneg
  have hbalance₃ := mul_le_mul_of_nonneg_left hw₁Sq balance₃_nonneg
  have hbalance₄ := mul_le_mul_of_nonneg_left hw₂Sq balance₄_nonneg
  have hgram := certificate_gram_nonneg e p₁ p₂ w₁ w₂
  simp only [he, one_pow] at hgram
  rw [norm_sub_sub_sq e p₁ w₁, norm_sub_sub_sq e p₂ w₂,
    norm_sub_sq e w₁]
  simp only [he, one_pow]
  simp only [balance₁] at hbalance₁
  simp only [balance₂] at hbalance₂
  simp only [balance₃] at hbalance₃
  simp only [balance₄] at hbalance₄
  simp only [balance₀, balance₁, balance₂, balance₃, balance₄]
  nlinarith

/-- The exact Gram separator for the crossed root--edge term. -/
theorem rootEdge_type12_expanded_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖) (hblueSeparation : barC ≤ ‖w₁ - w₂‖) :
    ‖e - p₁ - w₁‖ + 3 / 2 * ‖e - p₂ - w₂‖ + ‖e - w₁‖ +
        (2 - 3 * barC) / 2 * ‖p₁ - p₂‖ +
        (7 - 9 * barC) / 4 * ‖w₁ - w₂‖ +
        (1 - 5 * barC) / 4 * ‖w₁‖ -
        (1 + 5 * barC) / 4 * ‖w₂‖ +
        (1 - 2 * barC) * ‖p₂‖ - 1 / 2 < 0 := by
  have hredSum : barC ≤ ‖p₁‖ + ‖p₂‖ :=
    hredSeparation.trans (norm_sub_le p₁ p₂)
  have hblueSum : barC ≤ ‖w₁‖ + ‖w₂‖ :=
    hblueSeparation.trans (norm_sub_le w₁ w₂)
  have hp₁Lower : barC - 1 ≤ ‖p₁‖ := by linarith
  have hp₂Lower : barC - 1 ≤ ‖p₂‖ := by linarith
  have hw₁Lower : barC - 1 ≤ ‖w₁‖ := by linarith
  have hw₂Lower : barC - 1 ≤ ‖w₂‖ := by linarith
  have hfirstPenalty : 0 ≤ firstBlueRadialPenalty barC := by
    simp only [firstBlueRadialPenalty]
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hsecondPenalty : 0 ≤ secondBlueRadialPenalty barC := by
    simp only [secondBlueRadialPenalty]
    nlinarith [barC_pos]
  have hredPenalty : 0 ≤ secondRedRadialPenalty barC := by
    simp only [secondRedRadialPenalty]
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hfirstRadial := radial_secant hfirstPenalty hw₁Lower hw₁ (by linarith [barC_pos])
  have hsecondRadial := radial_secant hsecondPenalty hw₂Lower hw₂
    (by linarith [barC_pos])
  have hredRadial := radial_secant hredPenalty hp₂Lower hp₂ (by linarith [barC_pos])
  simp only [sub_add_cancel, mul_one] at hfirstRadial hsecondRadial hredRadial
  have hredDistance :
      (2 - 3 * barC) / 2 * ‖p₁ - p₂‖ ≤ (2 - 3 * barC) / 2 * barC := by
    have hcoefficient : 0 ≤ (3 * barC - 2) / 2 := by
      nlinarith [one_lt_barC_and_barC_lt_two.1]
    have hscaled := mul_le_mul_of_nonneg_left hredSeparation hcoefficient
    nlinarith
  have hblueDistance :
      (7 - 9 * barC) / 4 * ‖w₁ - w₂‖ ≤ (7 - 9 * barC) / 4 * barC := by
    have hcoefficient : 0 ≤ (9 * barC - 7) / 4 := by
      nlinarith [one_lt_barC_and_barC_lt_two.1]
    have hscaled := mul_le_mul_of_nonneg_left hblueSeparation hcoefficient
    nlinarith
  have htangent₁ := weighted_norm_tangent (e - p₁ - w₁) 1 (5 / 28) (by norm_num)
  have htangent₂ := weighted_norm_tangent (e - p₂ - w₂) (3 / 2) (15 / 43)
    (by norm_num)
  have htangent₃ := weighted_norm_tangent (e - w₁) 1 (4 / 15) (by norm_num)
  norm_num at htangent₁ htangent₂ htangent₃
  have hquadratic := tangentQuadratic_le e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂
    hredSeparation hblueSeparation
  have hupper := certificateUpper_neg
  simp only [certificateUpper] at hupper
  simp only [firstBlueRadialPenalty] at hfirstRadial
  simp only [secondBlueRadialPenalty] at hsecondRadial
  simp only [secondRedRadialPenalty] at hredRadial
  simp only [firstBlueRadialPenalty, secondBlueRadialPenalty,
    secondRedRadialPenalty] at hquadratic hupper
  have hfirstRadial' :
      (1 - 5 * barC) / 4 * ‖w₁‖ ≤
        -((5 * barC - 1) / 4) / barC * ‖w₁‖ ^ 2 -
          (5 * barC - 1) / 4 * (barC - 1) / barC := by
    convert hfirstRadial using 1
    all_goals ring
  have hsecondRadial' :
      -(1 + 5 * barC) / 4 * ‖w₂‖ ≤
        -((5 * barC + 1) / 4) / barC * ‖w₂‖ ^ 2 -
          (5 * barC + 1) / 4 * (barC - 1) / barC := by
    convert hsecondRadial using 1
    all_goals ring
  have hredRadial' :
      (1 - 2 * barC) * ‖p₂‖ ≤
        -(2 * barC - 1) / barC * ‖p₂‖ ^ 2 -
          (2 * barC - 1) * (barC - 1) / barC := by
    convert hredRadial using 1
    all_goals ring
  have hpreUpper :
      ‖e - p₁ - w₁‖ + 3 / 2 * ‖e - p₂ - w₂‖ + ‖e - w₁‖ +
          (2 - 3 * barC) / 2 * ‖p₁ - p₂‖ +
          (7 - 9 * barC) / 4 * ‖w₁ - w₂‖ +
          (1 - 5 * barC) / 4 * ‖w₁‖ -
          (1 + 5 * barC) / 4 * ‖w₂‖ +
          (1 - 2 * barC) * ‖p₂‖ - 1 / 2 ≤
        5 / 28 * ‖e - p₁ - w₁‖ ^ 2 + 15 / 43 * ‖e - p₂ - w₂‖ ^ 2 +
          4 / 15 * ‖e - w₁‖ ^ 2 -
          (5 * barC - 1) / 4 / barC * ‖w₁‖ ^ 2 -
          (5 * barC + 1) / 4 / barC * ‖w₂‖ ^ 2 -
          (2 * barC - 1) / barC * ‖p₂‖ ^ 2 +
          7 / 5 + 129 / 80 + 15 / 16 +
          (2 - 3 * barC) / 2 * barC + (7 - 9 * barC) / 4 * barC -
          (5 * barC - 1) / 4 * (barC - 1) / barC -
          (5 * barC + 1) / 4 * (barC - 1) / barC -
          (2 * barC - 1) * (barC - 1) / barC - 1 / 2 := by
    ring_nf at htangent₁
    ring_nf at htangent₂
    ring_nf at htangent₃
    ring_nf at hredDistance
    ring_nf at hblueDistance
    ring_nf at hfirstRadial'
    ring_nf at hsecondRadial'
    ring_nf at hredRadial'
    ring_nf
    linarith only [htangent₁, htangent₂, htangent₃, hredDistance, hblueDistance,
      hfirstRadial', hsecondRadial', hredRadial']
  linarith only [hpreUpper, hquadratic, hupper]

/-- Matching, endpoint, and crossed root--edge slacks have a strictly negative separator. -/
theorem rootEdge_type12_separator_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖) (hblueSeparation : barC ≤ ‖w₁ - w₂‖) :
    matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
          ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖ +
        redEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
          ‖w₁‖ ‖w₂‖ ‖e - p₁ - w₁‖ +
        2 * redRootEdgeType12Slack barC ‖w₁ - w₂‖ ‖p₂‖ ‖w₁‖ ‖w₂‖
          ‖e - w₁‖ ‖e - p₂ - w₂‖ < 0 := by
  have h := rootEdge_type12_expanded_lt e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂
    hredSeparation hblueSeparation
  simp only [matchingFailureSlack, redEndpointFailureSlack,
    redRootEdgeType12Slack]
  ring_nf at h ⊢
  nlinarith

/-- A matching and its first coincident endpoint exclude the crossed red root--edge term. -/
theorem redRootEdgeType12Slack_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖) (hblueSeparation : barC ≤ ‖w₁ - w₂‖)
    (hmatching : 0 ≤ matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖)
    (hendpoint : 0 ≤ redEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖w₁‖ ‖w₂‖ ‖e - p₁ - w₁‖) :
    redRootEdgeType12Slack barC ‖w₁ - w₂‖ ‖p₂‖ ‖w₁‖ ‖w₂‖
      ‖e - w₁‖ ‖e - p₂ - w₂‖ < 0 := by
  have hseparator := rootEdge_type12_separator_lt e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂
    hredSeparation hblueSeparation
  nlinarith

/-- In an admissible configuration, the selected matching and endpoint code `0` exclude the
red crossed `(left,right)` root--edge term. -/
theorem SixPointConfiguration.redRootEdgeType12Slack_neg_of_matching_endpoint
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hendpoint : redSiblingTriangleFailure configuration (.endpoint 0)) :
    redRootEdgeType12Slack barC
      (dist (configuration .blue .left) (configuration .blue .right))
      (dist (configuration .red .root) (configuration .red .right))
      (dist (configuration .blue .root) (configuration .blue .left))
      (dist (configuration .blue .root) (configuration .blue .right))
      (dist (configuration .red .root) (configuration .blue .left))
      (dist (configuration .red .right) (configuration .blue .right)) < 0 := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hL : ‖p₁ - p₂‖ =
      dist (configuration .red .left) (configuration .red .right) := by
    rw [← dist_eq_norm, configuration.dist_redDisplacement]
  have hM : ‖w₁ - w₂‖ =
      dist (configuration .blue .left) (configuration .blue .right) := by
    rw [← dist_eq_norm, configuration.dist_bluePullback]
  have hr₂ : ‖p₂‖ = dist (configuration .red .root) (configuration .red .right) := by
    simp [p₂, SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]
  have hb₁ : ‖w₁‖ = dist (configuration .blue .root) (configuration .blue .left) := by
    simp [w₁, SixPointConfiguration.bluePullback, dist_eq_norm]
  have hb₂ : ‖w₂‖ = dist (configuration .blue .root) (configuration .blue .right) := by
    simp [w₂, SixPointConfiguration.bluePullback, dist_eq_norm]
  have hB₁₁ : ‖e - p₁ - w₁‖ =
      dist (configuration .red .left) (configuration .blue .left) := by
    exact (configuration.dist_red_blue_eq_norm .left .left).symm
  have hB₂₂ : ‖e - p₂ - w₂‖ =
      dist (configuration .red .right) (configuration .blue .right) := by
    exact (configuration.dist_red_blue_eq_norm .right .right).symm
  have hA₁ : ‖e - w₁‖ =
      dist (configuration .red .root) (configuration .blue .left) := by
    simpa [e, p₁, w₁, SixPointConfiguration.redDisplacement] using
      (configuration.dist_red_blue_eq_norm .root .left).symm
  have hredSeparation : barC ≤ ‖p₁ - p₂‖ := by
    have hsibling := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hsibling
    exact hsibling
  have hblueSeparation : barC ≤ ‖w₁ - w₂‖ := by
    have hsibling := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hsibling
    exact hsibling
  have hmatching' : 0 ≤ matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖ := by
    simp only [hL, hM, hB₁₁, hB₂₂, matchingFailureSlack]
    apply sub_nonneg.mpr
    simpa [SelectedDiagonalMatchingFails, incidenceCrossDistance, incidenceChild] using
      hmatching
  have hendpoint' : 0 ≤ redEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖w₁‖ ‖w₂‖ ‖e - p₁ - w₁‖ := by
    simp only [hL, hM, hb₁, hb₂, hB₁₁, redEndpointFailureSlack]
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, rootedTriangleTotalRadius, redSiblingBlueTriangleReach,
      canonicalTriangleRadius, incidenceFirst, incidenceSecond, incidenceChild] at hendpoint
    linarith
  have hnegative := redRootEdgeType12Slack_neg e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hredSeparation hblueSeparation
    hmatching' hendpoint'
  simpa only [hM, hr₂, hb₁, hb₂, hA₁, hB₂₂] using hnegative

end LeanPool.Besicovitch

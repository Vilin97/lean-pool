/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.MatrixCorrections
public import LeanPool.Besicovitch.SixPoint.WeightedReduction
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# Local Gram certificates for the weighted six-point score

The weighted pair score at the small rational weights `1/12` and `13/14` is a positive combination
of six norms minus two radial penalties.  Replacing each norm by a quadratic tangent, each radial
penalty by a secant on a radius box, and adding two nonnegative separation multipliers turns the
score into a quadratic form in the five configuration vectors.  A rank-three rational factor,
completed by elementary two-vector squares, dominates that form, so the score is bounded by an
explicit rational number depending only on the certificate.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

/-- Indices of the five vectors in a six-point Gram certificate. -/
abbrev Five := Fin 5

/-- Indices of the three rows in the rational Gram factor. -/
abbrev Three := Fin 3

/-- The small rational weight on the coincident-endpoint slack. -/
def gramLambda : ℝ := 1 / 12

/-- The small rational weight on the balanced root--edge slack. -/
def gramMu : ℝ := 13 / 14

theorem gramLambda_pos : 0 < gramLambda := by norm_num [gramLambda]

theorem gramMu_pos : 0 < gramMu := by norm_num [gramMu]

/-- Half the first-child radial penalty at the small rational weights. -/
def gramFirstPenalty : ℝ := weightedFirstPenalty barC gramLambda gramMu / 2

/-- Half the second-child radial penalty at the small rational weights. -/
def gramSecondPenalty : ℝ := weightedSecondPenalty barC gramLambda gramMu / 2

theorem gramFirstPenalty_pos : 0 < gramFirstPenalty := by
  norm_num [gramFirstPenalty, weightedFirstPenalty, gramLambda, gramMu, barC]

theorem gramSecondPenalty_pos : 0 < gramSecondPenalty := by
  norm_num [gramSecondPenalty, weightedSecondPenalty, gramLambda, gramMu, barC]

/-- A local certificate on one rectangle of second-child radii. -/
structure GramCertificate where
  /-- Lower bound for the second red radius. -/
  pLower : ℚ
  /-- Upper bound for the second red radius. -/
  pUpper : ℚ
  /-- Lower bound for the second blue radius. -/
  wLower : ℚ
  /-- Upper bound for the second blue radius. -/
  wUpper : ℚ
  /-- Tangent parameter for `e - p₁ - w₁`. -/
  alpha₀ : ℚ
  /-- Tangent parameter for `e - p₂ - w₂`. -/
  alpha₁ : ℚ
  /-- Tangent parameter for `e - p₁`. -/
  alpha₂ : ℚ
  /-- Tangent parameter for `e - w₁`. -/
  alpha₃ : ℚ
  /-- Tangent parameter for `e - p₁ - w₂`. -/
  alpha₄ : ℚ
  /-- Tangent parameter for `e - w₁ - p₂`. -/
  alpha₅ : ℚ
  /-- Multiplier for the red separation constraint. -/
  etaP : ℚ
  /-- Multiplier for the blue separation constraint. -/
  etaW : ℚ
  /-- The rank-three rational Gram factor. -/
  factor : Fin 3 → Fin 5 → ℚ

/-- Scale a table of integers by `10⁻⁴`. -/
def tenThousandthFactor (entries : Fin 3 → Fin 5 → ℤ) : Fin 3 → Fin 5 → ℚ :=
  fun i j ↦ entries i j / 10000

/-- One rational Gram-factor row, cast to real coordinates. -/
def factorRow (certificate : GramCertificate) (k : Three) : Five → ℝ :=
  fun i ↦ certificate.factor k i

/-- The positive semidefinite Gram matrix represented by the three factor rows. -/
def factorGram (certificate : GramCertificate) : Matrix Five Five ℝ :=
  ∑ k, Matrix.vecMulVec (factorRow certificate k) (factorRow certificate k)

/-- The negated off-diagonal coefficients of the quadratic form. -/
def targetOffDiagonal (certificate : GramCertificate) : Matrix Five Five ℝ :=
  !![0, certificate.alpha₀ + certificate.alpha₂ + certificate.alpha₄,
        certificate.alpha₁ + certificate.alpha₅,
        certificate.alpha₀ + certificate.alpha₃ + certificate.alpha₅,
        certificate.alpha₁ + certificate.alpha₄;
      certificate.alpha₀ + certificate.alpha₂ + certificate.alpha₄, 0, certificate.etaP,
        -certificate.alpha₀, -certificate.alpha₄;
      certificate.alpha₁ + certificate.alpha₅, certificate.etaP, 0,
        -certificate.alpha₅, -certificate.alpha₁;
      certificate.alpha₀ + certificate.alpha₃ + certificate.alpha₅,
        -certificate.alpha₀, -certificate.alpha₅, 0, certificate.etaW;
      certificate.alpha₁ + certificate.alpha₄, -certificate.alpha₄, -certificate.alpha₁,
        certificate.etaW, 0]

/-- The discrepancy between the target quadratic form and its rational Gram factor. -/
def residual (certificate : GramCertificate) (i j : Five) : ℝ :=
  targetOffDiagonal certificate i j - factorGram certificate i j

private def certificateMatrix (certificate : GramCertificate) : Matrix Five Five ℝ :=
  factorGram certificate +
    pairCorrection (residual certificate 0 1) 0 1 +
    pairCorrection (residual certificate 0 2) 0 2 +
    pairCorrection (residual certificate 0 3) 0 3 +
    pairCorrection (residual certificate 0 4) 0 4 +
    pairCorrection (residual certificate 1 2) 1 2 +
    pairCorrection (residual certificate 1 3) 1 3 +
    pairCorrection (residual certificate 1 4) 1 4 +
    pairCorrection (residual certificate 2 3) 2 3 +
    pairCorrection (residual certificate 2 4) 2 4 +
    pairCorrection (residual certificate 3 4) 3 4

private theorem certificateMatrix_posSemidef (certificate : GramCertificate) :
    (certificateMatrix certificate).PosSemidef := by
  have hfactor : (factorGram certificate).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact Matrix.posSemidef_vecMulVec_self_star (factorRow certificate i)
  have h := hfactor.add (pairCorrection_posSemidef (residual certificate 0 1) 0 1)
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 2) 0 2)
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 3) 0 3)
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 4) 0 4)
  have h := h.add (pairCorrection_posSemidef (residual certificate 1 2) 1 2)
  have h := h.add (pairCorrection_posSemidef (residual certificate 1 3) 1 3)
  have h := h.add (pairCorrection_posSemidef (residual certificate 1 4) 1 4)
  have h := h.add (pairCorrection_posSemidef (residual certificate 2 3) 2 3)
  have h := h.add (pairCorrection_posSemidef (residual certificate 2 4) 2 4)
  exact h.add (pairCorrection_posSemidef (residual certificate 3 4) 3 4)

private theorem factorGram_apply_comm (certificate : GramCertificate) (i j : Five) :
    factorGram certificate i j = factorGram certificate j i := by
  simp only [factorGram, Matrix.sum_apply, Matrix.vecMulVec_apply]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

@[simp] private theorem factorGram_10 (certificate : GramCertificate) :
    factorGram certificate 1 0 = factorGram certificate 0 1 :=
  factorGram_apply_comm certificate 1 0

@[simp] private theorem factorGram_20 (certificate : GramCertificate) :
    factorGram certificate 2 0 = factorGram certificate 0 2 :=
  factorGram_apply_comm certificate 2 0

@[simp] private theorem factorGram_21 (certificate : GramCertificate) :
    factorGram certificate 2 1 = factorGram certificate 1 2 :=
  factorGram_apply_comm certificate 2 1

@[simp] private theorem factorGram_30 (certificate : GramCertificate) :
    factorGram certificate 3 0 = factorGram certificate 0 3 :=
  factorGram_apply_comm certificate 3 0

@[simp] private theorem factorGram_31 (certificate : GramCertificate) :
    factorGram certificate 3 1 = factorGram certificate 1 3 :=
  factorGram_apply_comm certificate 3 1

@[simp] private theorem factorGram_32 (certificate : GramCertificate) :
    factorGram certificate 3 2 = factorGram certificate 2 3 :=
  factorGram_apply_comm certificate 3 2

@[simp] private theorem factorGram_40 (certificate : GramCertificate) :
    factorGram certificate 4 0 = factorGram certificate 0 4 :=
  factorGram_apply_comm certificate 4 0

@[simp] private theorem factorGram_41 (certificate : GramCertificate) :
    factorGram certificate 4 1 = factorGram certificate 1 4 :=
  factorGram_apply_comm certificate 4 1

@[simp] private theorem factorGram_42 (certificate : GramCertificate) :
    factorGram certificate 4 2 = factorGram certificate 2 4 :=
  factorGram_apply_comm certificate 4 2

@[simp] private theorem factorGram_43 (certificate : GramCertificate) :
    factorGram certificate 4 3 = factorGram certificate 3 4 :=
  factorGram_apply_comm certificate 4 3

private theorem certificateMatrix_offDiagonal (certificate : GramCertificate) {i j : Five}
    (hij : i ≠ j) :
    certificateMatrix certificate i j = targetOffDiagonal certificate i j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [certificateMatrix, residual, targetOffDiagonal]

/-- Diagonal entry 0 after adding the rank-one residual corrections. -/
def diagonal₀ (certificate : GramCertificate) : ℝ :=
  factorGram certificate 0 0 + |residual certificate 0 1| +
    |residual certificate 0 2| + |residual certificate 0 3| + |residual certificate 0 4|

/-- Diagonal entry 1 after adding the rank-one residual corrections. -/
def diagonal₁ (certificate : GramCertificate) : ℝ :=
  factorGram certificate 1 1 + |residual certificate 0 1| +
    |residual certificate 1 2| + |residual certificate 1 3| + |residual certificate 1 4|

/-- Diagonal entry 2 after adding the rank-one residual corrections. -/
def diagonal₂ (certificate : GramCertificate) : ℝ :=
  factorGram certificate 2 2 + |residual certificate 0 2| +
    |residual certificate 1 2| + |residual certificate 2 3| + |residual certificate 2 4|

/-- Diagonal entry 3 after adding the rank-one residual corrections. -/
def diagonal₃ (certificate : GramCertificate) : ℝ :=
  factorGram certificate 3 3 + |residual certificate 0 3| +
    |residual certificate 1 3| + |residual certificate 2 3| + |residual certificate 3 4|

/-- Diagonal entry 4 after adding the rank-one residual corrections. -/
def diagonal₄ (certificate : GramCertificate) : ℝ :=
  factorGram certificate 4 4 + |residual certificate 0 4| +
    |residual certificate 1 4| + |residual certificate 2 4| + |residual certificate 3 4|

private theorem certificateMatrix_diagonal₀ (certificate : GramCertificate) :
    certificateMatrix certificate 0 0 = diagonal₀ certificate := by
  simp [certificateMatrix, diagonal₀]

private theorem certificateMatrix_diagonal₁ (certificate : GramCertificate) :
    certificateMatrix certificate 1 1 = diagonal₁ certificate := by
  simp [certificateMatrix, diagonal₁]

private theorem certificateMatrix_diagonal₂ (certificate : GramCertificate) :
    certificateMatrix certificate 2 2 = diagonal₂ certificate := by
  simp [certificateMatrix, diagonal₂]

private theorem certificateMatrix_diagonal₃ (certificate : GramCertificate) :
    certificateMatrix certificate 3 3 = diagonal₃ certificate := by
  simp [certificateMatrix, diagonal₃]

private theorem certificateMatrix_diagonal₄ (certificate : GramCertificate) :
    certificateMatrix certificate 4 4 = diagonal₄ certificate := by
  simp [certificateMatrix, diagonal₄]

private theorem gram_sum_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : GramCertificate) (v : Five → E) :
    0 ≤ ∑ i, ∑ j, certificateMatrix certificate i j * ⟪v i, v j⟫_ℝ := by
  exact matrix_inner_sum_nonneg (certificateMatrix_posSemidef certificate) v

/-- The lower bound the separation forces on the first red radius. -/
def redFirstLower (certificate : GramCertificate) : ℝ := barC - certificate.pUpper

/-- The lower bound the separation forces on the first blue radius. -/
def blueFirstLower (certificate : GramCertificate) : ℝ := barC - certificate.wUpper

private theorem certificate_gram_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : GramCertificate) (e p₁ p₂ w₁ w₂ : E) :
    0 ≤ diagonal₀ certificate * ‖e‖ ^ 2 +
      diagonal₁ certificate * ‖p₁‖ ^ 2 +
      diagonal₂ certificate * ‖p₂‖ ^ 2 +
      diagonal₃ certificate * ‖w₁‖ ^ 2 +
      diagonal₄ certificate * ‖w₂‖ ^ 2 +
      2 * (certificate.alpha₀ + certificate.alpha₂ + certificate.alpha₄) * ⟪e, p₁⟫_ℝ +
      2 * (certificate.alpha₁ + certificate.alpha₅) * ⟪e, p₂⟫_ℝ +
      2 * (certificate.alpha₀ + certificate.alpha₃ + certificate.alpha₅) * ⟪e, w₁⟫_ℝ +
      2 * (certificate.alpha₁ + certificate.alpha₄) * ⟪e, w₂⟫_ℝ +
      2 * certificate.etaP * ⟪p₁, p₂⟫_ℝ -
      2 * certificate.alpha₀ * ⟪p₁, w₁⟫_ℝ -
      2 * certificate.alpha₄ * ⟪p₁, w₂⟫_ℝ -
      2 * certificate.alpha₅ * ⟪p₂, w₁⟫_ℝ -
      2 * certificate.alpha₁ * ⟪p₂, w₂⟫_ℝ +
      2 * certificate.etaW * ⟪w₁, w₂⟫_ℝ := by
  let v : Five → E := ![e, p₁, p₂, w₁, w₂]
  have h := gram_sum_nonneg certificate v
  simp only [Fin.sum_univ_five, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, v] at h
  rw [certificateMatrix_diagonal₀, certificateMatrix_diagonal₁,
    certificateMatrix_diagonal₂, certificateMatrix_diagonal₃,
    certificateMatrix_diagonal₄] at h
  rw [certificateMatrix_offDiagonal certificate (by decide : (0 : Five) ≠ 1),
    certificateMatrix_offDiagonal certificate (by decide : (0 : Five) ≠ 2),
    certificateMatrix_offDiagonal certificate (by decide : (0 : Five) ≠ 3),
    certificateMatrix_offDiagonal certificate (by decide : (0 : Five) ≠ 4),
    certificateMatrix_offDiagonal certificate (by decide : (1 : Five) ≠ 0),
    certificateMatrix_offDiagonal certificate (by decide : (1 : Five) ≠ 2),
    certificateMatrix_offDiagonal certificate (by decide : (1 : Five) ≠ 3),
    certificateMatrix_offDiagonal certificate (by decide : (1 : Five) ≠ 4),
    certificateMatrix_offDiagonal certificate (by decide : (2 : Five) ≠ 0),
    certificateMatrix_offDiagonal certificate (by decide : (2 : Five) ≠ 1),
    certificateMatrix_offDiagonal certificate (by decide : (2 : Five) ≠ 3),
    certificateMatrix_offDiagonal certificate (by decide : (2 : Five) ≠ 4),
    certificateMatrix_offDiagonal certificate (by decide : (3 : Five) ≠ 0),
    certificateMatrix_offDiagonal certificate (by decide : (3 : Five) ≠ 1),
    certificateMatrix_offDiagonal certificate (by decide : (3 : Five) ≠ 2),
    certificateMatrix_offDiagonal certificate (by decide : (3 : Five) ≠ 4),
    certificateMatrix_offDiagonal certificate (by decide : (4 : Five) ≠ 0),
    certificateMatrix_offDiagonal certificate (by decide : (4 : Five) ≠ 1),
    certificateMatrix_offDiagonal certificate (by decide : (4 : Five) ≠ 2),
    certificateMatrix_offDiagonal certificate (by decide : (4 : Five) ≠ 3)] at h
  simp [targetOffDiagonal, real_inner_comm] at h
  nlinarith

/-- The balance of the root vector. -/
def balance₀ (certificate : GramCertificate) : ℝ :=
  diagonal₀ certificate + certificate.alpha₀ + certificate.alpha₁ + certificate.alpha₂ +
    certificate.alpha₃ + certificate.alpha₄ + certificate.alpha₅

/-- The balance of the first red vector. -/
def balance₁ (certificate : GramCertificate) : ℝ :=
  diagonal₁ certificate + certificate.alpha₀ + certificate.alpha₂ + certificate.alpha₄ -
    gramFirstPenalty / (redFirstLower certificate + 1) + certificate.etaP

/-- The balance of the second red vector. -/
def balance₂ (certificate : GramCertificate) : ℝ :=
  diagonal₂ certificate + certificate.alpha₁ + certificate.alpha₅ -
    gramSecondPenalty / (certificate.pLower + certificate.pUpper) + certificate.etaP

/-- The balance of the first blue vector. -/
def balance₃ (certificate : GramCertificate) : ℝ :=
  diagonal₃ certificate + certificate.alpha₀ + certificate.alpha₃ + certificate.alpha₅ -
    gramFirstPenalty / (blueFirstLower certificate + 1) + certificate.etaW

/-- The balance of the second blue vector. -/
def balance₄ (certificate : GramCertificate) : ℝ :=
  diagonal₄ certificate + certificate.alpha₁ + certificate.alpha₄ -
    gramSecondPenalty / (certificate.wLower + certificate.wUpper) + certificate.etaW

/-- The radius-box maximum of the diagonal form after the Gram corrections. -/
def dualRadialBound (certificate : GramCertificate) : ℝ :=
  balance₀ certificate +
    positivePart (balance₁ certificate) -
    negativePart (balance₁ certificate) * redFirstLower certificate ^ 2 +
    positivePart (balance₂ certificate) * certificate.pUpper ^ 2 -
    negativePart (balance₂ certificate) * certificate.pLower ^ 2 +
    positivePart (balance₃ certificate) -
    negativePart (balance₃ certificate) * blueFirstLower certificate ^ 2 +
    positivePart (balance₄ certificate) * certificate.wUpper ^ 2 -
    negativePart (balance₄ certificate) * certificate.wLower ^ 2 -
    (certificate.etaP + certificate.etaW) * barC ^ 2

/-- The exact rational upper bound the certificate proves for the weighted score. -/
def GramCertificate.upperBound (certificate : GramCertificate) : ℝ :=
  -weightedConstantTerm barC gramLambda gramMu +
    (1 + gramLambda) ^ 2 / (4 * certificate.alpha₀) +
    1 / (4 * certificate.alpha₁) +
    (gramMu / 2) ^ 2 / (4 * certificate.alpha₂) +
    (gramMu / 2) ^ 2 / (4 * certificate.alpha₃) +
    (gramMu / 2) ^ 2 / (4 * certificate.alpha₄) +
    (gramMu / 2) ^ 2 / (4 * certificate.alpha₅) -
    gramFirstPenalty * redFirstLower certificate / (redFirstLower certificate + 1) -
    gramSecondPenalty * certificate.pLower * certificate.pUpper /
      (certificate.pLower + certificate.pUpper) -
    gramFirstPenalty * blueFirstLower certificate / (blueFirstLower certificate + 1) -
    gramSecondPenalty * certificate.wLower * certificate.wUpper /
      (certificate.wLower + certificate.wUpper) +
    dualRadialBound certificate

/-- The arithmetic conditions making a certificate usable. -/
def GramCertificate.Valid (certificate : GramCertificate) : Prop :=
  barC - 1 ≤ (certificate.pLower : ℝ) ∧
    (certificate.pLower : ℝ) ≤ certificate.pUpper ∧ (certificate.pUpper : ℝ) ≤ 1 ∧
    barC - 1 ≤ (certificate.wLower : ℝ) ∧
    (certificate.wLower : ℝ) ≤ certificate.wUpper ∧ (certificate.wUpper : ℝ) ≤ 1 ∧
    0 < (certificate.alpha₀ : ℝ) ∧ 0 < (certificate.alpha₁ : ℝ) ∧
    0 < (certificate.alpha₂ : ℝ) ∧ 0 < (certificate.alpha₃ : ℝ) ∧
    0 < (certificate.alpha₄ : ℝ) ∧ 0 < (certificate.alpha₅ : ℝ) ∧
    0 ≤ (certificate.etaP : ℝ) ∧ 0 ≤ (certificate.etaW : ℝ) ∧
    certificate.upperBound ≤ -(1 / 2000)

private theorem certificate_dual_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : GramCertificate) (hvalid : certificate.Valid)
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hp₁Lower : redFirstLower certificate ≤ ‖p₁‖)
    (hw₁Lower : blueFirstLower certificate ≤ ‖w₁‖)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖)
    (hpLower : (certificate.pLower : ℝ) ≤ ‖p₂‖)
    (hpUpper : ‖p₂‖ ≤ certificate.pUpper)
    (hwLower : (certificate.wLower : ℝ) ≤ ‖w₂‖)
    (hwUpper : ‖w₂‖ ≤ certificate.wUpper) :
    (certificate.alpha₀ + certificate.alpha₁ + certificate.alpha₂ + certificate.alpha₃ +
        certificate.alpha₄ + certificate.alpha₅) * ‖e‖ ^ 2 +
      (certificate.alpha₀ + certificate.alpha₂ + certificate.alpha₄ -
        gramFirstPenalty / (redFirstLower certificate + 1)) * ‖p₁‖ ^ 2 +
      (certificate.alpha₁ + certificate.alpha₅ -
        gramSecondPenalty / (certificate.pLower + certificate.pUpper)) * ‖p₂‖ ^ 2 +
      (certificate.alpha₀ + certificate.alpha₃ + certificate.alpha₅ -
        gramFirstPenalty / (blueFirstLower certificate + 1)) * ‖w₁‖ ^ 2 +
      (certificate.alpha₁ + certificate.alpha₄ -
        gramSecondPenalty / (certificate.wLower + certificate.wUpper)) * ‖w₂‖ ^ 2 -
      2 * (certificate.alpha₀ + certificate.alpha₂ + certificate.alpha₄) * ⟪e, p₁⟫_ℝ -
      2 * (certificate.alpha₁ + certificate.alpha₅) * ⟪e, p₂⟫_ℝ -
      2 * (certificate.alpha₀ + certificate.alpha₃ + certificate.alpha₅) * ⟪e, w₁⟫_ℝ -
      2 * (certificate.alpha₁ + certificate.alpha₄) * ⟪e, w₂⟫_ℝ +
      2 * certificate.alpha₀ * ⟪p₁, w₁⟫_ℝ +
      2 * certificate.alpha₄ * ⟪p₁, w₂⟫_ℝ +
      2 * certificate.alpha₅ * ⟪p₂, w₁⟫_ℝ +
      2 * certificate.alpha₁ * ⟪p₂, w₂⟫_ℝ ≤ dualRadialBound certificate := by
  obtain ⟨hpL1, hpLU, hpU1, hwL1, hwLU, hwU1, _, _, _, _, _, _, hetaP, hetaW, _⟩ := hvalid
  have hbarC := one_lt_barC_and_barC_lt_two.1
  have hredLower : (0 : ℝ) ≤ redFirstLower certificate := by
    simp only [redFirstLower]; linarith
  have hblueLower : (0 : ℝ) ≤ blueFirstLower certificate := by
    simp only [blueFirstLower]; linarith
  have hpSum : (0 : ℝ) < certificate.pLower + certificate.pUpper := by linarith
  have hwSum : (0 : ℝ) < certificate.wLower + certificate.wUpper := by linarith
  have hpsepSq := (sq_le_sq₀ (by linarith) (norm_nonneg _)).2 hpsep
  have hwsepSq := (sq_le_sq₀ (by linarith) (norm_nonneg _)).2 hwsep
  rw [norm_sub_sq_real] at hpsepSq hwsepSq
  have hb₀ := balance_mul_sq_le (a := balance₁ certificate) hredLower hp₁Lower hp₁
  have hb₁ := balance_mul_sq_le (a := balance₂ certificate) (by linarith) hpLower hpUpper
  have hb₂ := balance_mul_sq_le (a := balance₃ certificate) hblueLower hw₁Lower hw₁
  have hb₃ := balance_mul_sq_le (a := balance₄ certificate) (by linarith) hwLower hwUpper
  have hgram := certificate_gram_nonneg certificate e p₁ p₂ w₁ w₂
  simp only [dualRadialBound, balance₀, balance₁, balance₂, balance₃,
    balance₄, he, one_pow] at hgram hb₀ hb₁ hb₂ hb₃ ⊢
  have hpsepWeighted := mul_le_mul_of_nonneg_left hpsepSq hetaP
  have hwsepWeighted := mul_le_mul_of_nonneg_left hwsepSq hetaW
  linarith only [hgram, hb₀, hb₁, hb₂, hb₃, hpsepWeighted, hwsepWeighted]

/-- A valid certificate bounds the weighted pair score on its radius rectangle. -/
theorem weightedPairScore_le_of_gramCertificate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : GramCertificate) (hvalid : certificate.Valid)
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖)
    (hpLower : (certificate.pLower : ℝ) ≤ ‖p₂‖)
    (hpUpper : ‖p₂‖ ≤ certificate.pUpper)
    (hwLower : (certificate.wLower : ℝ) ≤ ‖w₂‖)
    (hwUpper : ‖w₂‖ ≤ certificate.wUpper) :
    weightedPairScore e barC gramLambda gramMu p₁ p₂ w₁ w₂ ≤ -(1 / 2000) := by
  obtain ⟨hpL1, hpLU, hpU1, hwL1, hwLU, hwU1, ha₀, ha₁, ha₂, ha₃, ha₄, ha₅,
    hetaP, hetaW, hbound⟩ := hvalid
  have hbarC := one_lt_barC_and_barC_lt_two.1
  have hpSum : (0 : ℝ) < certificate.pLower + certificate.pUpper := by linarith
  have hwSum : (0 : ℝ) < certificate.wLower + certificate.wUpper := by linarith
  -- the separation forces the first radii away from the origin
  have hp₁Lower : redFirstLower certificate ≤ ‖p₁‖ := by
    have := norm_sub_le p₁ p₂
    simp only [redFirstLower]; linarith
  have hw₁Lower : blueFirstLower certificate ≤ ‖w₁‖ := by
    have := norm_sub_le w₁ w₂
    simp only [blueFirstLower]; linarith
  have hredLower : (0 : ℝ) ≤ redFirstLower certificate := by
    simp only [redFirstLower]; linarith
  have hblueLower : (0 : ℝ) ≤ blueFirstLower certificate := by
    simp only [blueFirstLower]; linarith
  have hdual := certificate_dual_bound certificate
    ⟨hpL1, hpLU, hpU1, hwL1, hwLU, hwU1, ha₀, ha₁, ha₂, ha₃, ha₄, ha₅, hetaP, hetaW,
      hbound⟩ e p₁ p₂ w₁ w₂ he hp₁ hw₁ hp₁Lower hw₁Lower hpsep hwsep hpLower
      hpUpper hwLower hwUpper
  -- six quadratic norm tangents
  have ht₀ := weightedNorm_le_quadratic (e - p₁ - w₁) (1 + gramLambda) certificate.alpha₀ ha₀
  have ht₁ := weightedNorm_le_quadratic (e - p₂ - w₂) 1 certificate.alpha₁ ha₁
  have ht₂ := weightedNorm_le_quadratic (e - p₁) (gramMu / 2) certificate.alpha₂ ha₂
  have ht₃ := weightedNorm_le_quadratic (e - w₁) (gramMu / 2) certificate.alpha₃ ha₃
  have ht₄ := weightedNorm_le_quadratic (e - p₁ - w₂) (gramMu / 2) certificate.alpha₄ ha₄
  have ht₅ := weightedNorm_le_quadratic (e - w₁ - p₂) (gramMu / 2) certificate.alpha₅ ha₅
  rw [norm_sub_sub_sq e p₁ w₁] at ht₀
  rw [norm_sub_sub_sq e p₂ w₂] at ht₁
  rw [norm_sub_sq_real] at ht₂ ht₃
  rw [norm_sub_sub_sq e p₁ w₂] at ht₄
  rw [norm_sub_sub_sq e w₁ p₂] at ht₅
  have hcomm : ⟪w₁, p₂⟫_ℝ = ⟪p₂, w₁⟫_ℝ := real_inner_comm _ _
  -- four radial secants
  have hr₀ := radial_secant (d := gramFirstPenalty) (l := redFirstLower certificate) (u := 1)
    (r := ‖p₁‖) gramFirstPenalty_pos.le hp₁Lower hp₁ (by linarith)
  have hr₁ := radial_secant (d := gramSecondPenalty) (l := certificate.pLower)
    (u := certificate.pUpper) (r := ‖p₂‖) gramSecondPenalty_pos.le hpLower hpUpper hpSum
  have hr₂ := radial_secant (d := gramFirstPenalty) (l := blueFirstLower certificate) (u := 1)
    (r := ‖w₁‖) gramFirstPenalty_pos.le hw₁Lower hw₁ (by linarith)
  have hr₃ := radial_secant (d := gramSecondPenalty) (l := certificate.wLower)
    (u := certificate.wUpper) (r := ‖w₂‖) gramSecondPenalty_pos.le hwLower hwUpper hwSum
  simp only [he, one_pow] at ht₀ ht₁ ht₂ ht₃ ht₄ ht₅ hdual
  have hscore : weightedPairScore e barC gramLambda gramMu p₁ p₂ w₁ w₂ ≤
      certificate.upperBound := by
    have htangent := add_le_add (add_le_add (add_le_add ht₀ ht₁) (add_le_add ht₂ ht₃))
      (add_le_add ht₄ ht₅)
    have hradial := add_le_add (add_le_add hr₀ hr₁) (add_le_add hr₂ hr₃)
    rw [hcomm] at htangent
    simp only [weightedPairScore, GramCertificate.upperBound] at ⊢
    rw [show weightedFirstPenalty barC gramLambda gramMu / 2 = gramFirstPenalty from rfl,
      show weightedSecondPenalty barC gramLambda gramMu / 2 = gramSecondPenalty from rfl]
    ring_nf at htangent hradial hdual ⊢
    linarith only [htangent, hradial, hdual]
  linarith [hscore, hbound]

end LeanPool.Besicovitch

/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# The endpoint-balanced `E0/S0` lens inequality

The positive distance terms are first replaced by quadratic norm tangents.  The two second-child
radii are then divided into a small rational cover.  On every rectangle, an explicit three-square
Gram majorant, corrected by elementary two-vector squares, proves the required strict bound.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

private abbrev Five := Fin 5

private abbrev Three := Fin 3

private def comparisonChord : ℝ := 6933 / 5000

private def redFirstPenalty : ℝ := 3 * (comparisonChord - 1)

private def redSecondPenalty : ℝ := 3 * (comparisonChord + 1)

private def blueFirstPenalty : ℝ := 9 / 2 * (comparisonChord - 1)

private def blueSecondPenalty : ℝ := 9 / 2 * (comparisonChord + 1)

private structure LensCertificate where
  redLower : ℚ
  redUpper : ℚ
  blueLower : ℚ
  blueUpper : ℚ
  alpha₁₁ : ℚ
  alpha₁₂ : ℚ
  alpha₂₂ : ℚ
  redSeparation : ℚ
  blueSeparation : ℚ
  factor : Three → Five → ℚ

private def millionth (n : ℤ) : ℚ := n / 1000000

private def tenThousandthFactor (entries : Three → Five → ℤ) : Three → Five → ℚ :=
  fun i j ↦ entries i j / 10000

private def factorRow (certificate : LensCertificate) (k : Three) : Five → ℝ :=
  fun i ↦ certificate.factor k i

private def factorGram (certificate : LensCertificate) : Matrix Five Five ℝ :=
  ∑ k, Matrix.vecMulVec (factorRow certificate k) (factorRow certificate k)

private def targetOffDiagonal (certificate : LensCertificate) : Matrix Five Five ℝ :=
  !![0, certificate.alpha₁₁ + certificate.alpha₁₂, certificate.alpha₂₂,
        certificate.alpha₁₁, certificate.alpha₁₂ + certificate.alpha₂₂;
      certificate.alpha₁₁ + certificate.alpha₁₂, 0, certificate.redSeparation,
        -certificate.alpha₁₁, -certificate.alpha₁₂;
      certificate.alpha₂₂, certificate.redSeparation, 0, 0,
        -certificate.alpha₂₂;
      certificate.alpha₁₁, -certificate.alpha₁₁, 0, 0,
        certificate.blueSeparation;
      certificate.alpha₁₂ + certificate.alpha₂₂,
        -certificate.alpha₁₂, -certificate.alpha₂₂,
        certificate.blueSeparation, 0]

private def pairSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

private def pairVector (r : ℝ) (i j : Five) : Five → ℝ :=
  fun k ↦ if k = i then 1 else if k = j then pairSign r else 0

private def pairCorrection (r : ℝ) (i j : Five) : Matrix Five Five ℝ :=
  |r| • Matrix.vecMulVec (pairVector r i j) (pairVector r i j)

private def residual (certificate : LensCertificate) (i j : Five) : ℝ :=
  targetOffDiagonal certificate i j - factorGram certificate i j

private def certificateMatrix (certificate : LensCertificate) : Matrix Five Five ℝ :=
  factorGram certificate + (1 / 1000000 : ℝ) • 1 +
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

private theorem pairCorrection_posSemidef (r : ℝ) (i j : Five) :
    (pairCorrection r i j).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (pairVector r i j)).smul (abs_nonneg r)

private theorem certificateMatrix_posSemidef (certificate : LensCertificate) :
    (certificateMatrix certificate).PosSemidef := by
  have hfactor : (factorGram certificate).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact Matrix.posSemidef_vecMulVec_self_star (factorRow certificate i)
  have hepsilon : ((1 / 1000000 : ℝ) • (1 : Matrix Five Five ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by norm_num)
  have h := hfactor.add hepsilon
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 1) 0 1)
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 2) 0 2)
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 3) 0 3)
  have h := h.add (pairCorrection_posSemidef (residual certificate 0 4) 0 4)
  have h := h.add (pairCorrection_posSemidef (residual certificate 1 2) 1 2)
  have h := h.add (pairCorrection_posSemidef (residual certificate 1 3) 1 3)
  have h := h.add (pairCorrection_posSemidef (residual certificate 1 4) 1 4)
  have h := h.add (pairCorrection_posSemidef (residual certificate 2 3) 2 3)
  have h := h.add (pairCorrection_posSemidef (residual certificate 2 4) 2 4)
  exact h.add (pairCorrection_posSemidef (residual certificate 3 4) 3 4)

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
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hij.symm, abs_mul_pairSign,
    mul_comm]

@[simp]
private theorem pairCorrection_apply_left_left (r : ℝ) {i j : Five} :
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

private theorem factorGram_apply_comm (certificate : LensCertificate) (i j : Five) :
    factorGram certificate i j = factorGram certificate j i := by
  simp only [factorGram, Matrix.sum_apply, Matrix.vecMulVec_apply]
  congr 1
  funext k
  ring

@[simp] private theorem factorGram_10 (certificate : LensCertificate) :
    factorGram certificate 1 0 = factorGram certificate 0 1 :=
  factorGram_apply_comm certificate 1 0

@[simp] private theorem factorGram_20 (certificate : LensCertificate) :
    factorGram certificate 2 0 = factorGram certificate 0 2 :=
  factorGram_apply_comm certificate 2 0

@[simp] private theorem factorGram_21 (certificate : LensCertificate) :
    factorGram certificate 2 1 = factorGram certificate 1 2 :=
  factorGram_apply_comm certificate 2 1

@[simp] private theorem factorGram_30 (certificate : LensCertificate) :
    factorGram certificate 3 0 = factorGram certificate 0 3 :=
  factorGram_apply_comm certificate 3 0

@[simp] private theorem factorGram_31 (certificate : LensCertificate) :
    factorGram certificate 3 1 = factorGram certificate 1 3 :=
  factorGram_apply_comm certificate 3 1

@[simp] private theorem factorGram_32 (certificate : LensCertificate) :
    factorGram certificate 3 2 = factorGram certificate 2 3 :=
  factorGram_apply_comm certificate 3 2

@[simp] private theorem factorGram_40 (certificate : LensCertificate) :
    factorGram certificate 4 0 = factorGram certificate 0 4 :=
  factorGram_apply_comm certificate 4 0

@[simp] private theorem factorGram_41 (certificate : LensCertificate) :
    factorGram certificate 4 1 = factorGram certificate 1 4 :=
  factorGram_apply_comm certificate 4 1

@[simp] private theorem factorGram_42 (certificate : LensCertificate) :
    factorGram certificate 4 2 = factorGram certificate 2 4 :=
  factorGram_apply_comm certificate 4 2

@[simp] private theorem factorGram_43 (certificate : LensCertificate) :
    factorGram certificate 4 3 = factorGram certificate 3 4 :=
  factorGram_apply_comm certificate 4 3

private theorem certificateMatrix_offDiagonal (certificate : LensCertificate) {i j : Five}
    (hij : i ≠ j) :
    certificateMatrix certificate i j = targetOffDiagonal certificate i j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [certificateMatrix, residual, targetOffDiagonal]

private def diagonal₀ (certificate : LensCertificate) : ℝ :=
  factorGram certificate 0 0 + 1 / 1000000 + |residual certificate 0 1| +
    |residual certificate 0 2| + |residual certificate 0 3| + |residual certificate 0 4|

private def diagonal₁ (certificate : LensCertificate) : ℝ :=
  factorGram certificate 1 1 + 1 / 1000000 + |residual certificate 0 1| +
    |residual certificate 1 2| + |residual certificate 1 3| + |residual certificate 1 4|

private def diagonal₂ (certificate : LensCertificate) : ℝ :=
  factorGram certificate 2 2 + 1 / 1000000 + |residual certificate 0 2| +
    |residual certificate 1 2| + |residual certificate 2 3| + |residual certificate 2 4|

private def diagonal₃ (certificate : LensCertificate) : ℝ :=
  factorGram certificate 3 3 + 1 / 1000000 + |residual certificate 0 3| +
    |residual certificate 1 3| + |residual certificate 2 3| + |residual certificate 3 4|

private def diagonal₄ (certificate : LensCertificate) : ℝ :=
  factorGram certificate 4 4 + 1 / 1000000 + |residual certificate 0 4| +
    |residual certificate 1 4| + |residual certificate 2 4| + |residual certificate 3 4|

private theorem certificateMatrix_diagonal₀ (certificate : LensCertificate) :
    certificateMatrix certificate 0 0 = diagonal₀ certificate := by
  simp [certificateMatrix, diagonal₀]

private theorem certificateMatrix_diagonal₁ (certificate : LensCertificate) :
    certificateMatrix certificate 1 1 = diagonal₁ certificate := by
  simp [certificateMatrix, diagonal₁]

private theorem certificateMatrix_diagonal₂ (certificate : LensCertificate) :
    certificateMatrix certificate 2 2 = diagonal₂ certificate := by
  simp [certificateMatrix, diagonal₂]

private theorem certificateMatrix_diagonal₃ (certificate : LensCertificate) :
    certificateMatrix certificate 3 3 = diagonal₃ certificate := by
  simp [certificateMatrix, diagonal₃]

private theorem certificateMatrix_diagonal₄ (certificate : LensCertificate) :
    certificateMatrix certificate 4 4 = diagonal₄ certificate := by
  simp [certificateMatrix, diagonal₄]

private theorem gram_sum_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : LensCertificate) (v : Five → E) :
    0 ≤ ∑ i, ∑ j, certificateMatrix certificate i j * ⟪v i, v j⟫_ℝ := by
  have hmatrix := (certificateMatrix_posSemidef certificate).hadamard
    (Matrix.posSemidef_gram ℝ v)
  have h := hmatrix.dotProduct_mulVec_nonneg (fun _ ↦ (1 : ℝ))
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using h

private def positivePart (x : ℝ) : ℝ := max x 0

private def negativePart (x : ℝ) : ℝ := max (-x) 0

private theorem positivePart_sub_negativePart (x : ℝ) :
    positivePart x - negativePart x = x := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, hx', neg_nonneg.mpr hx']

private theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := le_max_right _ _

private theorem negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := le_max_right _ _

private def dualY (certificate : LensCertificate) : ℝ :=
  diagonal₀ certificate + certificate.alpha₁₁ + certificate.alpha₁₂ +
    certificate.alpha₂₂

private def redFirstBalance (certificate : LensCertificate) : ℝ :=
  diagonal₁ certificate + certificate.alpha₁₁ + certificate.alpha₁₂ -
    redFirstPenalty + certificate.redSeparation

private def redSecondBalance (certificate : LensCertificate) : ℝ :=
  diagonal₂ certificate + certificate.alpha₂₂ -
    redSecondPenalty / (certificate.redLower + certificate.redUpper) +
    certificate.redSeparation

private def blueFirstBalance (certificate : LensCertificate) : ℝ :=
  diagonal₃ certificate + certificate.alpha₁₁ - blueFirstPenalty +
    certificate.blueSeparation

private def blueSecondBalance (certificate : LensCertificate) : ℝ :=
  diagonal₄ certificate + certificate.alpha₁₂ + certificate.alpha₂₂ -
    blueSecondPenalty / (certificate.blueLower + certificate.blueUpper) +
    certificate.blueSeparation

private def dualRadialBound (certificate : LensCertificate) : ℝ :=
  dualY certificate + positivePart (redFirstBalance certificate) +
    positivePart (redSecondBalance certificate) * certificate.redUpper ^ 2 -
    negativePart (redSecondBalance certificate) * certificate.redLower ^ 2 +
    positivePart (blueFirstBalance certificate) +
    positivePart (blueSecondBalance certificate) * certificate.blueUpper ^ 2 -
    negativePart (blueSecondBalance certificate) * certificate.blueLower ^ 2 -
    (certificate.redSeparation + certificate.blueSeparation) * comparisonChord ^ 2

private def certificateUpperBound (certificate : LensCertificate) : ℝ :=
  -9 + 59 / 2 * comparisonChord - 85 / 2 * comparisonChord ^ 2 +
    17 ^ 2 / (4 * certificate.alpha₁₁) +
    3 ^ 2 / (4 * certificate.alpha₁₂) +
    5 ^ 2 / (4 * certificate.alpha₂₂) -
    redSecondPenalty * certificate.redLower * certificate.redUpper /
      (certificate.redLower + certificate.redUpper) -
    blueSecondPenalty * certificate.blueLower * certificate.blueUpper /
      (certificate.blueLower + certificate.blueUpper) + dualRadialBound certificate

private def LensCertificate.Valid (certificate : LensCertificate) : Prop :=
  0 < certificate.redLower ∧ certificate.redLower ≤ certificate.redUpper ∧
    certificate.redUpper ≤ 1 ∧ 0 < certificate.blueLower ∧
    certificate.blueLower ≤ certificate.blueUpper ∧ certificate.blueUpper ≤ 1 ∧
    0 < certificate.alpha₁₁ ∧ 0 < certificate.alpha₁₂ ∧
    0 < certificate.alpha₂₂ ∧ 0 ≤ certificate.redSeparation ∧
    0 ≤ certificate.blueSeparation ∧ certificateUpperBound certificate < 0

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

private theorem certificate_gram_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : LensCertificate) (e p₁ p₂ w₁ w₂ : E) :
    0 ≤ diagonal₀ certificate * ‖e‖ ^ 2 +
      diagonal₁ certificate * ‖p₁‖ ^ 2 +
      diagonal₂ certificate * ‖p₂‖ ^ 2 +
      diagonal₃ certificate * ‖w₁‖ ^ 2 +
      diagonal₄ certificate * ‖w₂‖ ^ 2 +
      2 * (certificate.alpha₁₁ + certificate.alpha₁₂) * ⟪e, p₁⟫_ℝ +
      2 * certificate.alpha₂₂ * ⟪e, p₂⟫_ℝ +
      2 * certificate.alpha₁₁ * ⟪e, w₁⟫_ℝ +
      2 * (certificate.alpha₁₂ + certificate.alpha₂₂) * ⟪e, w₂⟫_ℝ +
      2 * certificate.redSeparation * ⟪p₁, p₂⟫_ℝ -
      2 * certificate.alpha₁₁ * ⟪p₁, w₁⟫_ℝ -
      2 * certificate.alpha₁₂ * ⟪p₁, w₂⟫_ℝ -
      2 * certificate.alpha₂₂ * ⟪p₂, w₂⟫_ℝ +
      2 * certificate.blueSeparation * ⟪w₁, w₂⟫_ℝ := by
  let v : Five → E := ![e, p₁, p₂, w₁, w₂]
  have h := gram_sum_nonneg certificate v
  simp [Fin.sum_univ_five, v] at h
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

private theorem balance_mul_sq_le {a r l u : ℝ} (hl : 0 ≤ l) (hlr : l ≤ r) (hru : r ≤ u) :
    a * r ^ 2 ≤ positivePart a * u ^ 2 - negativePart a * l ^ 2 := by
  have hr := hl.trans hlr
  have hu := hr.trans hru
  have hupperSq := (sq_le_sq₀ hr hu).2 hru
  have hlowerSq := (sq_le_sq₀ hl hr).2 hlr
  have hupper := mul_le_mul_of_nonneg_left hupperSq (positivePart_nonneg a)
  have hlower := mul_le_mul_of_nonneg_left hlowerSq (negativePart_nonneg a)
  have hparts := congrArg (fun x : ℝ ↦ x * r ^ 2) (positivePart_sub_negativePart a)
  linarith only [hparts, hupper, hlower]

private theorem balance_mul_sq_le_one {a r : ℝ} (hr : 0 ≤ r) (hru : r ≤ 1) :
    a * r ^ 2 ≤ positivePart a := by
  simpa using balance_mul_sq_le (a := a) (l := 0) (u := 1) (by norm_num) hr hru

private theorem certificate_dual_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : LensCertificate) (hvalid : certificate.Valid)
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1)
    (hpsep : comparisonChord ≤ ‖p₁ - p₂‖) (hwsep : comparisonChord ≤ ‖w₁ - w₂‖)
    (hp₂Lower : certificate.redLower ≤ ‖p₂‖)
    (hp₂Upper : ‖p₂‖ ≤ certificate.redUpper)
    (hw₂Lower : certificate.blueLower ≤ ‖w₂‖)
    (hw₂Upper : ‖w₂‖ ≤ certificate.blueUpper) :
    (certificate.alpha₁₁ + certificate.alpha₁₂ + certificate.alpha₂₂) * ‖e‖ ^ 2 +
        (certificate.alpha₁₁ + certificate.alpha₁₂ - redFirstPenalty) * ‖p₁‖ ^ 2 +
        (certificate.alpha₂₂ - redSecondPenalty /
          (certificate.redLower + certificate.redUpper)) * ‖p₂‖ ^ 2 +
        (certificate.alpha₁₁ - blueFirstPenalty) * ‖w₁‖ ^ 2 +
        (certificate.alpha₁₂ + certificate.alpha₂₂ - blueSecondPenalty /
          (certificate.blueLower + certificate.blueUpper)) * ‖w₂‖ ^ 2 -
        2 * (certificate.alpha₁₁ + certificate.alpha₁₂) * ⟪e, p₁⟫_ℝ -
        2 * certificate.alpha₂₂ * ⟪e, p₂⟫_ℝ -
        2 * certificate.alpha₁₁ * ⟪e, w₁⟫_ℝ -
        2 * (certificate.alpha₁₂ + certificate.alpha₂₂) * ⟪e, w₂⟫_ℝ +
        2 * certificate.alpha₁₁ * ⟪p₁, w₁⟫_ℝ +
        2 * certificate.alpha₁₂ * ⟪p₁, w₂⟫_ℝ +
        2 * certificate.alpha₂₂ * ⟪p₂, w₂⟫_ℝ ≤ dualRadialBound certificate := by
  rcases hvalid with
    ⟨hredLower, _, _, hblueLower, _, _, _, _, _, hredSeparation, hblueSeparation, _⟩
  have hredLowerR : (0 : ℝ) < certificate.redLower := by exact_mod_cast hredLower
  have hblueLowerR : (0 : ℝ) < certificate.blueLower := by exact_mod_cast hblueLower
  have hredSeparationR : (0 : ℝ) ≤ certificate.redSeparation := by
    exact_mod_cast hredSeparation
  have hblueSeparationR : (0 : ℝ) ≤ certificate.blueSeparation := by
    exact_mod_cast hblueSeparation
  have hpsepSq := (sq_le_sq₀ (by norm_num [comparisonChord]) (norm_nonneg _)).2 hpsep
  have hwsepSq := (sq_le_sq₀ (by norm_num [comparisonChord]) (norm_nonneg _)).2 hwsep
  rw [norm_sub_sq_real] at hpsepSq hwsepSq
  have hredFirst := balance_mul_sq_le_one (a := redFirstBalance certificate)
    (norm_nonneg p₁) hp₁
  have hredSecond := balance_mul_sq_le (a := redSecondBalance certificate)
    hredLowerR.le hp₂Lower hp₂Upper
  have hblueFirst := balance_mul_sq_le_one (a := blueFirstBalance certificate)
    (norm_nonneg w₁) hw₁
  have hblueSecond := balance_mul_sq_le (a := blueSecondBalance certificate)
    hblueLowerR.le hw₂Lower hw₂Upper
  have hgram := certificate_gram_nonneg certificate e p₁ p₂ w₁ w₂
  simp only [he, one_pow, dualRadialBound, dualY, redFirstBalance, redSecondBalance,
    blueFirstBalance, blueSecondBalance] at hgram hredFirst hredSecond hblueFirst hblueSecond ⊢
  have hpsepWeighted := mul_le_mul_of_nonneg_left hpsepSq hredSeparationR
  have hwsepWeighted := mul_le_mul_of_nonneg_left hwsepSq hblueSeparationR
  linarith only [hgram, hredFirst, hredSecond, hblueFirst, hblueSecond, hpsepWeighted,
    hwsepWeighted]

private theorem certificate_analytic_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : LensCertificate) (hvalid : certificate.Valid)
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1)
    (hpsep : comparisonChord ≤ ‖p₁ - p₂‖) (hwsep : comparisonChord ≤ ‖w₁ - w₂‖)
    (hp₂Lower : certificate.redLower ≤ ‖p₂‖)
    (hp₂Upper : ‖p₂‖ ≤ certificate.redUpper)
    (hw₂Lower : certificate.blueLower ≤ ‖w₂‖)
    (hw₂Upper : ‖w₂‖ ≤ certificate.blueUpper) :
    17 * ‖e - p₁ - w₁‖ + 3 * ‖e - p₁ - w₂‖ + 5 * ‖e - p₂ - w₂‖ -
        redFirstPenalty * ‖p₁‖ - redSecondPenalty * ‖p₂‖ -
        blueFirstPenalty * ‖w₁‖ -
        blueSecondPenalty * ‖w₂‖ ≤ dualRadialBound certificate +
        17 ^ 2 / (4 * certificate.alpha₁₁) + 3 ^ 2 / (4 * certificate.alpha₁₂) +
        5 ^ 2 / (4 * certificate.alpha₂₂) -
        redSecondPenalty * certificate.redLower * certificate.redUpper /
          (certificate.redLower + certificate.redUpper) -
        blueSecondPenalty * certificate.blueLower * certificate.blueUpper /
          (certificate.blueLower + certificate.blueUpper) := by
  have hdual := certificate_dual_bound certificate hvalid e p₁ p₂ w₁ w₂ he hp₁ hw₁ hpsep
    hwsep hp₂Lower hp₂Upper hw₂Lower hw₂Upper
  rcases hvalid with
    ⟨hredLower, hredBounds, _, hblueLower, hblueBounds, _, halpha₁₁, halpha₁₂,
      halpha₂₂, _, _, _⟩
  have hredLowerR : (0 : ℝ) < certificate.redLower := by exact_mod_cast hredLower
  have hredBoundsR : (certificate.redLower : ℝ) ≤ certificate.redUpper := by
    exact_mod_cast hredBounds
  have hblueLowerR : (0 : ℝ) < certificate.blueLower := by exact_mod_cast hblueLower
  have hblueBoundsR : (certificate.blueLower : ℝ) ≤ certificate.blueUpper := by
    exact_mod_cast hblueBounds
  have halpha₁₁R : (0 : ℝ) < certificate.alpha₁₁ := by exact_mod_cast halpha₁₁
  have halpha₁₂R : (0 : ℝ) < certificate.alpha₁₂ := by exact_mod_cast halpha₁₂
  have halpha₂₂R : (0 : ℝ) < certificate.alpha₂₂ := by exact_mod_cast halpha₂₂
  have htangent₁₁ :=
    weighted_norm_tangent (e - p₁ - w₁) 17 certificate.alpha₁₁ halpha₁₁R
  have htangent₁₂ :=
    weighted_norm_tangent (e - p₁ - w₂) 3 certificate.alpha₁₂ halpha₁₂R
  have htangent₂₂ :=
    weighted_norm_tangent (e - p₂ - w₂) 5 certificate.alpha₂₂ halpha₂₂R
  rw [norm_sub_sub_sq e p₁ w₁] at htangent₁₁
  rw [norm_sub_sub_sq e p₁ w₂] at htangent₁₂
  rw [norm_sub_sub_sq e p₂ w₂] at htangent₂₂
  have hredFirst := radial_secant (d := redFirstPenalty) (l := 0) (u := 1) (r := ‖p₁‖)
    (by norm_num [redFirstPenalty, comparisonChord]) (norm_nonneg p₁) hp₁ (by norm_num)
  have hredSecond := radial_secant (d := redSecondPenalty) (l := certificate.redLower)
    (u := certificate.redUpper) (r := ‖p₂‖) (by norm_num [redSecondPenalty, comparisonChord])
    hp₂Lower hp₂Upper (by linarith)
  have hblueFirst := radial_secant (d := blueFirstPenalty) (l := 0) (u := 1) (r := ‖w₁‖)
    (by norm_num [blueFirstPenalty, comparisonChord]) (norm_nonneg w₁) hw₁ (by norm_num)
  have hblueSecond := radial_secant (d := blueSecondPenalty) (l := certificate.blueLower)
    (u := certificate.blueUpper) (r := ‖w₂‖)
    (by norm_num [blueSecondPenalty, comparisonChord]) hw₂Lower hw₂Upper (by linarith)
  simp only [he, one_pow] at htangent₁₁ htangent₁₂ htangent₂₂ hdual
  norm_num at hredFirst hblueFirst
  have htangent := add_le_add (add_le_add htangent₁₁ htangent₁₂) htangent₂₂
  have hradial := add_le_add (add_le_add hredFirst hredSecond)
    (add_le_add hblueFirst hblueSecond)
  ring_nf at htangent hradial hdual ⊢
  linarith only [htangent, hradial, hdual]

private theorem lens_bound_of_certificate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (certificate : LensCertificate) (hvalid : certificate.Valid)
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1)
    (hpsep : comparisonChord ≤ ‖p₁ - p₂‖) (hwsep : comparisonChord ≤ ‖w₁ - w₂‖)
    (hp₂Lower : certificate.redLower ≤ ‖p₂‖)
    (hp₂Upper : ‖p₂‖ ≤ certificate.redUpper)
    (hw₂Lower : certificate.blueLower ≤ ‖w₂‖)
    (hw₂Upper : ‖w₂‖ ≤ certificate.blueUpper) :
    17 * ‖e - p₁ - w₁‖ + 3 * ‖e - p₁ - w₂‖ + 5 * ‖e - p₂ - w₂‖ -
        redFirstPenalty * ‖p₁‖ - redSecondPenalty * ‖p₂‖ -
        blueFirstPenalty * ‖w₁‖ - blueSecondPenalty * ‖w₂‖ - 9 +
        59 / 2 * comparisonChord - 85 / 2 * comparisonChord ^ 2 < 0 := by
  have hanalytic :=
    certificate_analytic_bound certificate hvalid e p₁ p₂ w₁ w₂ he hp₁ hw₁ hpsep hwsep
      hp₂Lower hp₂Upper hw₂Lower hw₂Upper
  have hbound := hvalid.2.2.2.2.2.2.2.2.2.2.2
  unfold certificateUpperBound at hbound
  nlinarith

private def lensCertificates : Fin 28 → LensCertificate := ![
  { redLower := 3 / 8, redUpper := 17 / 32, blueLower := 17 / 32,
    blueUpper := 11 / 16, alpha₁₁ := millionth 2890506, alpha₁₂ := millionth 741364,
    alpha₂₂ := millionth 1740227, redSeparation := millionth 2610026,
    blueSeparation := millionth 3088621, factor := tenThousandthFactor ![
      ![1819, 5355, -14521, -6987, 8937],
      ![18915, -1699, 289, 22440, 15183],
      ![-14886, -25903, -13097, 8243, 3714]] },
  { redLower := 3 / 8, redUpper := 17 / 32, blueLower := 11 / 16,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2890526, alpha₁₂ := millionth 685572,
    alpha₂₂ := millionth 1557844, redSeparation := millionth 2674058,
    blueSeparation := millionth 2455362, factor := tenThousandthFactor ![
      ![2883, 4729, -14967, -6530, 8047],
      ![16496, -7023, -2108, 22922, 12897],
      ![-18229, -25224, -12820, 3853, 636]] },
  { redLower := 3 / 8, redUpper := 17 / 32, blueLower := 27 / 32,
    blueUpper := 1, alpha₁₁ := millionth 2888910, alpha₁₂ := millionth 636035,
    alpha₂₂ := millionth 1415361, redSeparation := millionth 2739077,
    blueSeparation := millionth 2019493, factor := tenThousandthFactor ![
      ![3562, 4247, -15198, -6410, 7294],
      ![16378, -8330, -2662, 22473, 11054],
      ![-18933, -25026, -12638, 2975, 100]] },
  { redLower := 3 / 8, redUpper := 11 / 16, blueLower := 3 / 8,
    blueUpper := 17 / 32, alpha₁₁ := millionth 2888154, alpha₁₂ := millionth 802554,
    alpha₂₂ := millionth 1845176, redSeparation := millionth 2096492,
    blueSeparation := millionth 4126527, factor := tenThousandthFactor ![
      ![1216, -5449, 12634, 7692, -10525],
      ![19867, 24129, 10515, -1989, 972],
      ![-12893, 8041, 3083, -24739, -20031]] },
  { redLower := 17 / 32, redUpper := 39 / 64, blueLower := 11 / 16,
    blueUpper := 49 / 64, alpha₁₁ := millionth 2890715, alpha₁₂ := millionth 699051,
    alpha₂₂ := millionth 1478460, redSeparation := millionth 2076689,
    blueSeparation := millionth 2589614, factor := tenThousandthFactor ![
      ![1098, 3719, -13437, -5799, 9155],
      ![12308, -11547, -3390, 23612, 13196],
      ![-21559, -23054, -9478, -224, -2100]] },
  { redLower := 17 / 32, redUpper := 39 / 64, blueLower := 49 / 64,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2890329, alpha₁₂ := millionth 672867,
    alpha₂₂ := millionth 1409783, redSeparation := millionth 2110108,
    blueSeparation := millionth 2329345, factor := tenThousandthFactor ![
      ![1575, 3405, -13606, -5619, 8740],
      ![13050, -11276, -3156, 23316, 12118],
      ![-21385, -23293, -9520, 300, -1700]] },
  { redLower := 17 / 32, redUpper := 39 / 64, blueLower := 27 / 32,
    blueUpper := 1, alpha₁₁ := millionth 2888957, alpha₁₂ := millionth 636683,
    alpha₂₂ := millionth 1320165, redSeparation := millionth 2160931,
    blueSeparation := millionth 2014317, factor := tenThousandthFactor ![
      ![2143, 3005, -13776, -5489, 8179],
      ![13591, -11381, -3093, 22909, 10785],
      ![-21416, -23384, -9506, 500, -1475]] },
  { redLower := 17 / 32, redUpper := 11 / 16, blueLower := 17 / 32,
    blueUpper := 39 / 64, alpha₁₁ := millionth 2890043, alpha₁₂ := millionth 757466,
    alpha₂₂ := millionth 1599317, redSeparation := millionth 1851458,
    blueSeparation := millionth 3329045, factor := tenThousandthFactor ![
      ![694, -4320, 12397, 6363, -10337],
      ![17975, 24958, 9362, -5826, -1583],
      ![-16468, 4911, 1029, -23640, -16474]] },
  { redLower := 17 / 32, redUpper := 11 / 16, blueLower := 39 / 64,
    blueUpper := 11 / 16, alpha₁₁ := millionth 2890674, alpha₁₂ := millionth 726523,
    alpha₂₂ := millionth 1510374, redSeparation := millionth 1880532,
    blueSeparation := millionth 2908577, factor := tenThousandthFactor ![
      ![60, 3849, -12703, -5873, 9861],
      ![426, 21194, 7118, -20718, -11445],
      ![-24677, -14283, -6029, -12086, -9238]] },
  { redLower := 39 / 64, redUpper := 11 / 16, blueLower := 11 / 16,
    blueUpper := 49 / 64, alpha₁₁ := millionth 2890627, alpha₁₂ := millionth 698596,
    alpha₂₂ := millionth 1404137, redSeparation := millionth 1790421,
    blueSeparation := millionth 2594204, factor := tenThousandthFactor ![
      ![314, 3316, -12524, -5394, 9616],
      ![7405, -15990, -4516, 23177, 12391],
      ![-23890, -19937, -7442, -4986, -4834]] },
  { redLower := 39 / 64, redUpper := 11 / 16, blueLower := 49 / 64,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2890214, alpha₁₂ := millionth 672530,
    alpha₂₂ := millionth 1341186, redSeparation := millionth 1820424,
    blueSeparation := millionth 2332636, factor := tenThousandthFactor ![
      ![804, 2976, -12686, -5183, 9205],
      ![10103, -14061, -3669, 23282, 11717],
      ![-23126, -21445, -7843, -2507, -3269]] },
  { redLower := 39 / 64, redUpper := 11 / 16, blueLower := 27 / 32,
    blueUpper := 1, alpha₁₁ := millionth 2888950, alpha₁₂ := millionth 636503,
    alpha₂₂ := millionth 1258997, redSeparation := millionth 1867383,
    blueSeparation := millionth 2015753, factor := tenThousandthFactor ![
      ![1399, 2541, -12852, -5017, 8646],
      ![11507, -13342, -3285, 22979, 10511],
      ![-22803, -22037, -7967, -1381, -2478]] },
  { redLower := 11 / 16, redUpper := 93 / 128, blueLower := 49 / 64,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2890244, alpha₁₂ := millionth 672089,
    alpha₂₂ := millionth 1298911, redSeparation := millionth 1662157,
    blueSeparation := millionth 2336817, factor := tenThousandthFactor ![
      ![380, 2799, -12132, -4941, 9461],
      ![8100, -15708, -3899, 23062, 11366],
      ![-24015, -20087, -6916, -4334, -4224]] },
  { redLower := 11 / 16, redUpper := 49 / 64, blueLower := 39 / 64,
    blueUpper := 11 / 16, alpha₁₁ := millionth 2890577, alpha₁₂ := millionth 725524,
    alpha₂₂ := millionth 1409255, redSeparation := millionth 1559772,
    blueSeparation := millionth 2920064, factor := tenThousandthFactor ![
      ![844, -3525, 11590, 5444, -10380],
      ![9191, 24556, 7344, -15494, -7519],
      ![-23152, -5999, -2749, -18438, -12584]] },
  { redLower := 11 / 16, redUpper := 49 / 64, blueLower := 11 / 16,
    blueUpper := 93 / 128, alpha₁₁ := millionth 2890648, alpha₁₂ := millionth 704649,
    alpha₂₂ := millionth 1359487, redSeparation := millionth 1579603,
    blueSeparation := millionth 2675037, factor := tenThousandthFactor ![
      ![387, -3211, 11753, 5173, -10054],
      ![830, -20393, -5591, 21290, 10961],
      ![-25084, -15057, -5424, -10740, -8021]] },
  { redLower := 11 / 16, redUpper := 49 / 64, blueLower := 93 / 128,
    blueUpper := 49 / 64, alpha₁₁ := millionth 2890553, alpha₁₂ := millionth 691258,
    alpha₂₂ := millionth 1328595, redSeparation := millionth 1593341,
    blueSeparation := millionth 2531027, factor := tenThousandthFactor ![
      ![114, -3019, 11844, 5031, -9843],
      ![4630, -18070, -4692, 22498, 11449],
      ![-24785, -17841, -6182, -7437, -6056]] },
  { redLower := 11 / 16, redUpper := 49 / 64, blueLower := 27 / 32,
    blueUpper := 1, alpha₁₁ := millionth 2888899, alpha₁₂ := millionth 635992,
    alpha₂₂ := millionth 1208968, redSeparation := millionth 1658631,
    blueSeparation := millionth 2020063, factor := tenThousandthFactor ![
      ![864, 2297, -12122, -4676, 8981],
      ![9735, -14826, -3364, 22900, 10238],
      ![-23761, -20825, -6907, -2946, -3244]] },
  { redLower := 11 / 16, redUpper := 27 / 32, blueLower := 17 / 32,
    blueUpper := 39 / 64, alpha₁₁ := millionth 2889781, alpha₁₂ := millionth 756524,
    alpha₂₂ := millionth 1455451, redSeparation := millionth 1447399,
    blueSeparation := millionth 3357122, factor := tenThousandthFactor ![
      ![1869, -4000, 10966, 5885, -10988],
      ![17273, 24865, 7546, -7627, -2669],
      ![-17617, 3258, 300, -23258, -16339]] },
  { redLower := 11 / 16, redUpper := 1, blueLower := 3 / 8,
    blueUpper := 17 / 32, alpha₁₁ := millionth 2887389, alpha₁₂ := millionth 800698,
    alpha₂₂ := millionth 1505942, redSeparation := millionth 1270742,
    blueSeparation := millionth 4192122, factor := tenThousandthFactor ![
      ![3645, -4876, 9822, 6921, -11762],
      ![19553, 24033, 6933, -4683, -868],
      ![-14413, 5782, 1441, -24635, -20156]] },
  { redLower := 93 / 128, redUpper := 49 / 64, blueLower := 49 / 64,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2890160, alpha₁₂ := millionth 671737,
    alpha₂₂ := millionth 1272329, redSeparation := millionth 1569159,
    blueSeparation := millionth 2340282, factor := tenThousandthFactor ![
      ![131, 2717, -11791, -4797, 9612],
      ![6838, -16654, -3996, 22852, 11117],
      ![-24475, -19192, -6378, -5450, -4786]] },
  { redLower := 49 / 64, redUpper := 27 / 32, blueLower := 39 / 64,
    blueUpper := 11 / 16, alpha₁₁ := millionth 2890443, alpha₁₂ := millionth 724599,
    alpha₂₂ := millionth 1349809, redSeparation := millionth 1393656,
    blueSeparation := millionth 2930837, factor := tenThousandthFactor ![
      ![1311, -3436, 10958, 5212, -10647],
      ![10634, 24698, 6771, -14535, -6807],
      ![-22672, -4560, -2144, -19265, -12958]] },
  { redLower := 49 / 64, redUpper := 27 / 32, blueLower := 11 / 16,
    blueUpper := 49 / 64, alpha₁₁ := millionth 2890494, alpha₁₂ := millionth 697000,
    alpha₂₂ := millionth 1289028, redSeparation := millionth 1418570,
    blueSeparation := millionth 2610671, factor := tenThousandthFactor ![
      ![710, -3007, 11164, 4847, -10219],
      ![-263, -20923, -5207, 20851, 10341],
      ![-25285, -14055, -4730, -11513, -8249]] },
  { redLower := 49 / 64, redUpper := 27 / 32, blueLower := 49 / 64,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2890126, alpha₁₂ := millionth 671071,
    alpha₂₂ := millionth 1234650, redSeparation := millionth 1444940,
    blueSeparation := millionth 2346630, factor := tenThousandthFactor ![
      ![204, -2634, 11319, 4600, -9812],
      ![5122, -17829, -4063, 22488, 10748],
      ![-24987, -17928, -5682, -6920, -5504]] },
  { redLower := 49 / 64, redUpper := 27 / 32, blueLower := 27 / 32,
    blueUpper := 1, alpha₁₁ := millionth 2888793, alpha₁₂ := millionth 635251,
    alpha₂₂ := millionth 1163098, redSeparation := millionth 1486455,
    blueSeparation := millionth 2026651, factor := tenThousandthFactor ![
      ![419, 2157, -11480, -4387, 9256],
      ![8138, -16031, -3368, 22732, 9966],
      ![-24483, -19686, -6066, -4318, -3874]] },
  { redLower := 27 / 32, redUpper := 1, blueLower := 17 / 32,
    blueUpper := 11 / 16, alpha₁₁ := millionth 2889918, alpha₁₂ := millionth 737429,
    alpha₂₂ := millionth 1300581, redSeparation := millionth 1182097,
    blueSeparation := millionth 3138952, factor := tenThousandthFactor ![
      ![2217, -3663, 10032, 5168, -11170],
      ![14771, 24847, 6230, -11034, -4727],
      ![-20284, -189, -778, -21717, -14710]] },
  { redLower := 27 / 32, redUpper := 1, blueLower := 11 / 16,
    blueUpper := 49 / 64, alpha₁₁ := millionth 2890275, alpha₁₂ := millionth 695389,
    alpha₂₂ := millionth 1215912, redSeparation := millionth 1215199,
    blueSeparation := millionth 2628085, factor := tenThousandthFactor ![
      ![1271, -2964, 10353, 4526, -10537],
      ![3252, 22189, 4968, -19530, -9358],
      ![-25257, -11489, -3654, -13730, -9303]] },
  { redLower := 27 / 32, redUpper := 1, blueLower := 49 / 64,
    blueUpper := 27 / 32, alpha₁₁ := millionth 2889921, alpha₁₂ := millionth 669445,
    alpha₂₂ := millionth 1166568, redSeparation := millionth 1239233,
    blueSeparation := millionth 2362262, factor := tenThousandthFactor ![
      ![760, -2574, 10504, 4258, -10134],
      ![2413, -19429, -3999, 21746, 10108],
      ![-25567, -15832, -4628, -9124, -6529]] },
  { redLower := 27 / 32, redUpper := 1, blueLower := 27 / 32,
    blueUpper := 1, alpha₁₁ := millionth 2888619, alpha₁₂ := millionth 633708,
    alpha₂₂ := millionth 1101333, redSeparation := millionth 1277300,
    blueSeparation := millionth 2039948, factor := tenThousandthFactor ![
      ![128, -2073, 10661, 4020, -9581],
      ![6137, -17374, -3275, 22407, 9598],
      ![-25233, -18195, -5107, -5978, -4590]] }
]

private structure LensBox where
  redLower : ℚ
  redUpper : ℚ
  blueLower : ℚ
  blueUpper : ℚ

private def lensBox (i : Fin 28) : LensBox :=
  match i.val with
  | 0 => ⟨3 / 8, 17 / 32, 17 / 32, 11 / 16⟩
  | 1 => ⟨3 / 8, 17 / 32, 11 / 16, 27 / 32⟩
  | 2 => ⟨3 / 8, 17 / 32, 27 / 32, 1⟩
  | 3 => ⟨3 / 8, 11 / 16, 3 / 8, 17 / 32⟩
  | 4 => ⟨17 / 32, 39 / 64, 11 / 16, 49 / 64⟩
  | 5 => ⟨17 / 32, 39 / 64, 49 / 64, 27 / 32⟩
  | 6 => ⟨17 / 32, 39 / 64, 27 / 32, 1⟩
  | 7 => ⟨17 / 32, 11 / 16, 17 / 32, 39 / 64⟩
  | 8 => ⟨17 / 32, 11 / 16, 39 / 64, 11 / 16⟩
  | 9 => ⟨39 / 64, 11 / 16, 11 / 16, 49 / 64⟩
  | 10 => ⟨39 / 64, 11 / 16, 49 / 64, 27 / 32⟩
  | 11 => ⟨39 / 64, 11 / 16, 27 / 32, 1⟩
  | 12 => ⟨11 / 16, 93 / 128, 49 / 64, 27 / 32⟩
  | 13 => ⟨11 / 16, 49 / 64, 39 / 64, 11 / 16⟩
  | 14 => ⟨11 / 16, 49 / 64, 11 / 16, 93 / 128⟩
  | 15 => ⟨11 / 16, 49 / 64, 93 / 128, 49 / 64⟩
  | 16 => ⟨11 / 16, 49 / 64, 27 / 32, 1⟩
  | 17 => ⟨11 / 16, 27 / 32, 17 / 32, 39 / 64⟩
  | 18 => ⟨11 / 16, 1, 3 / 8, 17 / 32⟩
  | 19 => ⟨93 / 128, 49 / 64, 49 / 64, 27 / 32⟩
  | 20 => ⟨49 / 64, 27 / 32, 39 / 64, 11 / 16⟩
  | 21 => ⟨49 / 64, 27 / 32, 11 / 16, 49 / 64⟩
  | 22 => ⟨49 / 64, 27 / 32, 49 / 64, 27 / 32⟩
  | 23 => ⟨49 / 64, 27 / 32, 27 / 32, 1⟩
  | 24 => ⟨27 / 32, 1, 17 / 32, 11 / 16⟩
  | 25 => ⟨27 / 32, 1, 11 / 16, 49 / 64⟩
  | 26 => ⟨27 / 32, 1, 49 / 64, 27 / 32⟩
  | 27 => ⟨27 / 32, 1, 27 / 32, 1⟩
  | _ => ⟨27 / 32, 1, 27 / 32, 1⟩

private theorem lensCertificate_box (i : Fin 28) :
    (lensCertificates i).redLower = (lensBox i).redLower ∧
      (lensCertificates i).redUpper = (lensBox i).redUpper ∧
      (lensCertificates i).blueLower = (lensBox i).blueLower ∧
      (lensCertificates i).blueUpper = (lensBox i).blueUpper := by
  fin_cases i <;>
    norm_num [lensCertificates, lensBox, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

@[simp] private theorem lensCertificate_redLower (i : Fin 28) :
    (lensCertificates i).redLower = (lensBox i).redLower := (lensCertificate_box i).1

@[simp] private theorem lensCertificate_redUpper (i : Fin 28) :
    (lensCertificates i).redUpper = (lensBox i).redUpper := (lensCertificate_box i).2.1

@[simp] private theorem lensCertificate_blueLower (i : Fin 28) :
    (lensCertificates i).blueLower = (lensBox i).blueLower := (lensCertificate_box i).2.2.1

@[simp] private theorem lensCertificate_blueUpper (i : Fin 28) :
    (lensCertificates i).blueUpper = (lensBox i).blueUpper := (lensCertificate_box i).2.2.2

private theorem lensCertificates_valid_0 (j : Fin 28) (hj : j = 0) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_1 (j : Fin 28) (hj : j = 1) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_2 (j : Fin 28) (hj : j = 2) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_3 (j : Fin 28) (hj : j = 3) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_4 (j : Fin 28) (hj : j = 4) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_5 (j : Fin 28) (hj : j = 5) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_6 (j : Fin 28) (hj : j = 6) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_7 (j : Fin 28) (hj : j = 7) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_8 (j : Fin 28) (hj : j = 8) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_9 (j : Fin 28) (hj : j = 9) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_10 (j : Fin 28) (hj : j = 10) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_11 (j : Fin 28) (hj : j = 11) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_12 (j : Fin 28) (hj : j = 12) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_13 (j : Fin 28) (hj : j = 13) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_14 (j : Fin 28) (hj : j = 14) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_15 (j : Fin 28) (hj : j = 15) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_16 (j : Fin 28) (hj : j = 16) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_17 (j : Fin 28) (hj : j = 17) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_18 (j : Fin 28) (hj : j = 18) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_19 (j : Fin 28) (hj : j = 19) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_20 (j : Fin 28) (hj : j = 20) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_21 (j : Fin 28) (hj : j = 21) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_22 (j : Fin 28) (hj : j = 22) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_23 (j : Fin 28) (hj : j = 23) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_24 (j : Fin 28) (hj : j = 24) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_25 (j : Fin 28) (hj : j = 25) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_26 (j : Fin 28) (hj : j = 26) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid_27 (j : Fin 28) (hj : j = 27) : (lensCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [lensCertificates, LensCertificate.Valid, certificateUpperBound, dualRadialBound,
      dualY, redFirstBalance, redSecondBalance, blueFirstBalance, blueSecondBalance, diagonal₀,
      diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow, Matrix.vecMulVec,
      residual, targetOffDiagonal, positivePart, negativePart, millionth, tenThousandthFactor,
      comparisonChord, redFirstPenalty, redSecondPenalty, blueFirstPenalty, blueSecondPenalty,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

private theorem lensCertificates_valid (i : Fin 28) : (lensCertificates i).Valid := by
  fin_cases i
  · exact lensCertificates_valid_0 _ rfl
  · exact lensCertificates_valid_1 _ rfl
  · exact lensCertificates_valid_2 _ rfl
  · exact lensCertificates_valid_3 _ rfl
  · exact lensCertificates_valid_4 _ rfl
  · exact lensCertificates_valid_5 _ rfl
  · exact lensCertificates_valid_6 _ rfl
  · exact lensCertificates_valid_7 _ rfl
  · exact lensCertificates_valid_8 _ rfl
  · exact lensCertificates_valid_9 _ rfl
  · exact lensCertificates_valid_10 _ rfl
  · exact lensCertificates_valid_11 _ rfl
  · exact lensCertificates_valid_12 _ rfl
  · exact lensCertificates_valid_13 _ rfl
  · exact lensCertificates_valid_14 _ rfl
  · exact lensCertificates_valid_15 _ rfl
  · exact lensCertificates_valid_16 _ rfl
  · exact lensCertificates_valid_17 _ rfl
  · exact lensCertificates_valid_18 _ rfl
  · exact lensCertificates_valid_19 _ rfl
  · exact lensCertificates_valid_20 _ rfl
  · exact lensCertificates_valid_21 _ rfl
  · exact lensCertificates_valid_22 _ rfl
  · exact lensCertificates_valid_23 _ rfl
  · exact lensCertificates_valid_24 _ rfl
  · exact lensCertificates_valid_25 _ rfl
  · exact lensCertificates_valid_26 _ rfl
  · exact lensCertificates_valid_27 _ rfl

private theorem exists_certificate_first_red_band (r b : ℝ)
    (hrl : 3 / 8 ≤ r) (hru : r ≤ 17 / 32) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨3, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 11 / 16
  · refine ⟨0, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 27 / 32
  · refine ⟨1, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨2, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_certificate_second_red_band (r b : ℝ)
    (hrl : 17 / 32 ≤ r) (hru : r ≤ 39 / 64) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨3, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 39 / 64
  · refine ⟨7, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 11 / 16
  · refine ⟨8, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₃ : b ≤ 49 / 64
  · refine ⟨4, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₄ : b ≤ 27 / 32
  · refine ⟨5, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨6, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_certificate_third_red_band (r b : ℝ)
    (hrl : 39 / 64 ≤ r) (hru : r ≤ 11 / 16) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨3, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 39 / 64
  · refine ⟨7, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 11 / 16
  · refine ⟨8, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₃ : b ≤ 49 / 64
  · refine ⟨9, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₄ : b ≤ 27 / 32
  · refine ⟨10, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨11, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_certificate_fourth_red_band (r b : ℝ)
    (hrl : 11 / 16 ≤ r) (hru : r ≤ 93 / 128) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨18, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 39 / 64
  · refine ⟨17, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 11 / 16
  · refine ⟨13, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₃ : b ≤ 93 / 128
  · refine ⟨14, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₄ : b ≤ 49 / 64
  · refine ⟨15, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₅ : b ≤ 27 / 32
  · refine ⟨12, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨16, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_certificate_fifth_red_band (r b : ℝ)
    (hrl : 93 / 128 ≤ r) (hru : r ≤ 49 / 64) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨18, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 39 / 64
  · refine ⟨17, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 11 / 16
  · refine ⟨13, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₃ : b ≤ 93 / 128
  · refine ⟨14, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₄ : b ≤ 49 / 64
  · refine ⟨15, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₅ : b ≤ 27 / 32
  · refine ⟨19, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨16, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_certificate_sixth_red_band (r b : ℝ)
    (hrl : 49 / 64 ≤ r) (hru : r ≤ 27 / 32) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨18, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 39 / 64
  · refine ⟨17, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 11 / 16
  · refine ⟨20, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₃ : b ≤ 49 / 64
  · refine ⟨21, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₄ : b ≤ 27 / 32
  · refine ⟨22, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨23, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_certificate_seventh_red_band (r b : ℝ)
    (hrl : 27 / 32 ≤ r) (hru : r ≤ 1) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hb₀ : b ≤ 17 / 32
  · refine ⟨18, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₁ : b ≤ 11 / 16
  · refine ⟨24, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₂ : b ≤ 49 / 64
  · refine ⟨25, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  by_cases hb₃ : b ≤ 27 / 32
  · refine ⟨26, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith
  · refine ⟨27, ?_, ?_, ?_, ?_⟩ <;> norm_num [lensBox, Fin.coe_ofNat_eq_mod] <;> linarith

private theorem exists_lens_certificate (r b : ℝ)
    (hrl : 3 / 8 ≤ r) (hru : r ≤ 1) (hbl : 3 / 8 ≤ b) (hbu : b ≤ 1) :
    ∃ i, (lensCertificates i).redLower ≤ r ∧ r ≤ (lensCertificates i).redUpper ∧
      (lensCertificates i).blueLower ≤ b ∧ b ≤ (lensCertificates i).blueUpper := by
  by_cases hr₀ : r ≤ 17 / 32
  · exact exists_certificate_first_red_band r b hrl hr₀ hbl hbu
  by_cases hr₁ : r ≤ 39 / 64
  · exact exists_certificate_second_red_band r b (by linarith) hr₁ hbl hbu
  by_cases hr₂ : r ≤ 11 / 16
  · exact exists_certificate_third_red_band r b (by linarith) hr₂ hbl hbu
  by_cases hr₃ : r ≤ 93 / 128
  · exact exists_certificate_fourth_red_band r b (by linarith) hr₃ hbl hbu
  by_cases hr₄ : r ≤ 49 / 64
  · exact exists_certificate_fifth_red_band r b (by linarith) hr₄ hbl hbu
  by_cases hr₅ : r ≤ 27 / 32
  · exact exists_certificate_sixth_red_band r b (by linarith) hr₅ hbl hbu
  · exact exists_certificate_seventh_red_band r b (by linarith) hru hbl hbu

private theorem comparisonChord_lt_barC : comparisonChord < barC := by
  have hc := barC_mem_isolation_box.1
  norm_num [comparisonChord] at hc ⊢
  linarith

private theorem second_norm_lower {E : Type*} [SeminormedAddCommGroup E] (p₁ p₂ : E)
    (hp₁ : ‖p₁‖ ≤ 1) (hsep : comparisonChord ≤ ‖p₁ - p₂‖) :
    3 / 8 ≤ ‖p₂‖ := by
  have htriangle := norm_sub_le p₁ p₂
  norm_num [comparisonChord] at hsep ⊢
  linarith

private theorem rational_chord_bound_implies_endpoint {E : Type*}
    [SeminormedAddCommGroup E] (e p₁ p₂ w₁ w₂ : E)
    (hbound :
      17 * ‖e - p₁ - w₁‖ + 3 * ‖e - p₁ - w₂‖ + 5 * ‖e - p₂ - w₂‖ -
          redFirstPenalty * ‖p₁‖ - redSecondPenalty * ‖p₂‖ -
          blueFirstPenalty * ‖w₁‖ - blueSecondPenalty * ‖w₂‖ - 9 +
          59 / 2 * comparisonChord - 85 / 2 * comparisonChord ^ 2 < 0) :
    17 * ‖e - p₁ - w₁‖ + 3 * ‖e - p₁ - w₂‖ + 5 * ‖e - p₂ - w₂‖ -
        3 * (barC - 1) * ‖p₁‖ - 3 * (barC + 1) * ‖p₂‖ -
        9 / 2 * (barC - 1) * ‖w₁‖ - 9 / 2 * (barC + 1) * ‖w₂‖ - 9 +
        59 / 2 * barC - 85 / 2 * barC ^ 2 < 0 := by
  have hc := comparisonChord_lt_barC
  have hslope : 0 ≤
      3 * ‖p₁‖ + 3 * ‖p₂‖ + 9 / 2 * ‖w₁‖ + 9 / 2 * ‖w₂‖ := by positivity
  have hpenalty := mul_nonneg (sub_nonneg.mpr hc.le) hslope
  have hfactor : 0 < 85 / 2 * (barC + comparisonChord) - 59 / 2 := by
    norm_num [comparisonChord] at hc ⊢
    linarith
  have hconstant := mul_pos (sub_pos.mpr hc) hfactor
  unfold redFirstPenalty redSecondPenalty blueFirstPenalty blueSecondPenalty at hbound
  nlinarith

private theorem endpoint_balanced_lens_vector_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    17 * ‖e - p₁ - w₁‖ + 3 * ‖e - p₁ - w₂‖ + 5 * ‖e - p₂ - w₂‖ -
        3 * (barC - 1) * ‖p₁‖ - 3 * (barC + 1) * ‖p₂‖ -
        9 / 2 * (barC - 1) * ‖w₁‖ - 9 / 2 * (barC + 1) * ‖w₂‖ - 9 +
        59 / 2 * barC - 85 / 2 * barC ^ 2 < 0 := by
  have hpsep' := comparisonChord_lt_barC.le.trans hpsep
  have hwsep' := comparisonChord_lt_barC.le.trans hwsep
  have hp₂Lower := second_norm_lower p₁ p₂ hp₁ hpsep'
  have hw₂Lower := second_norm_lower w₁ w₂ hw₁ hwsep'
  rcases exists_lens_certificate ‖p₂‖ ‖w₂‖ hp₂Lower hp₂ hw₂Lower hw₂ with
    ⟨i, hpLower, hpUpper, hwLower, hwUpper⟩
  apply rational_chord_bound_implies_endpoint e p₁ p₂ w₁ w₂
  exact lens_bound_of_certificate (lensCertificates i) (lensCertificates_valid i)
    e p₁ p₂ w₁ w₂ he hp₁ hw₁ hpsep' hwsep' hpLower hpUpper hwLower hwUpper

/-- The endpoint-balanced `E0/S0` lens separator is negative for every admissible
six-point configuration. -/
theorem endpointBalancedE0S0LensBound_of_admissible
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    EndpointBalancedE0S0LensBound configuration := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hpsep : barC ≤ ‖p₁ - p₂‖ := by
    have hred := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hred
    exact hred
  have hwsep : barC ≤ ‖w₁ - w₂‖ := by
    have hblue := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hblue
    exact hblue
  have hcertificate := endpoint_balanced_lens_vector_bound e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hpsep hwsep
  simp only [EndpointBalancedE0S0LensBound, diagonalMatchingReducedSlack,
    redEndpointReducedSlack, blueBalancedReducedSlack, balancedIncidencePenalty,
    incidenceCrossDistance_eq_norm, incidenceChildRadius_red_eq_norm,
    incidenceChildRadius_blue_eq_norm]
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild]
  dsimp only [e, p₁, p₂, w₁, w₂] at hcertificate
  nlinarith

end LeanPool.Besicovitch

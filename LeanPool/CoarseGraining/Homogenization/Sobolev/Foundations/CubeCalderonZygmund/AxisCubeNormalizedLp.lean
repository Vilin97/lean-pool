/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.IntegralLpSeminorm
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingCubeGeometry

/-! # Axis Cube Normalized Lp -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# Normalized finite-`p` norms on axis cubes

This module records the `ENNReal` bridge from a normalized axis-cube
`eLpNorm` to its powered local integral.  The local comparison argument uses
the raw set integral after this bridge; no real-valued `toReal` conversion is
needed here.
-/

private theorem finiteLpExponent_exponent_ne_zero (p : FiniteLpExponent) :
    p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem finiteLpExponent_exponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (finiteLpExponent_exponent_ne_zero p) p.lt_top.ne

/-- The `p`th power of a finite `eLpNorm` is its defining norm-power
lintegral. -/
theorem axisCube_integralLpSeminorm_rpow_exponent_eq_lintegral_enorm
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) (L : ℝ) (p : FiniteLpExponent) (F : Vec d → E) :
    (Gagliardo.integralLpSeminorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
      ∫⁻ x, ‖F x‖ₑ ^ p.exponent.toReal ∂axisCubeNormalizedMeasure z L := by
  simp only [Gagliardo.integralLpSeminorm,
    if_neg (finiteLpExponent_exponent_ne_zero p), if_neg p.lt_top.ne,
    eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 :=
    finiteLpExponent_exponent_toReal_pos p |>.ne'
  rw [one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]

/-- The norm-power integrand has the source-facing `ofReal` spelling. -/
theorem axisCube_lintegral_enorm_rpow_eq_lintegral_ofReal_norm_rpow
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) (L : ℝ) (p : FiniteLpExponent) (F : Vec d → E) :
    (∫⁻ x, ‖F x‖ₑ ^ p.exponent.toReal ∂axisCubeNormalizedMeasure z L) =
      ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal)
        ∂axisCubeNormalizedMeasure z L := by
  apply lintegral_congr
  intro x
  calc
    ‖F x‖ₑ ^ p.exponent.toReal = (ENNReal.ofReal ‖F x‖) ^ p.exponent.toReal := by
      rw [ofReal_norm]
    _ = ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal) :=
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (F x)) ENNReal.toReal_nonneg

/-- The normalized local norm-power integral is exactly the normalized raw
volume integral over a positive axis cube. -/
theorem axisCube_lintegral_ofReal_norm_rpow_eq_normalized_setLIntegral
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent) (F : Vec d → E) :
    (∫⁻ x, ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal)
      ∂axisCubeNormalizedMeasure z L) =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in axisCube z L, ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal)
          ∂volume := by
  rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict z L hL,
    lintegral_smul_measure]
  rfl

/-- The powered normalized finite-`p` norm is the normalized raw local
norm-power integral. -/
theorem axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_setLIntegral
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent) (F : Vec d → E) :
    (Gagliardo.integralLpSeminorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in axisCube z L, ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal)
          ∂volume := by
  rw [axisCube_integralLpSeminorm_rpow_exponent_eq_lintegral_enorm,
    axisCube_lintegral_enorm_rpow_eq_lintegral_ofReal_norm_rpow,
    axisCube_lintegral_ofReal_norm_rpow_eq_normalized_setLIntegral z hL]

/-- `MemLp` supplies the finiteness required when the powered norm is used in
an `ENNReal` inequality. -/
theorem axisCube_eLpNorm_rpow_exponent_lt_top
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) (L : ℝ) (p : FiniteLpExponent) (F : Vec d → E)
    (hF : MemLp F p.exponent (axisCubeNormalizedMeasure z L)) :
    (eLpNorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal < ∞ :=
  ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hF.eLpNorm_lt_top.ne

/-- The open axis cube has the expected closed sup-ball realization. -/
theorem axisCube_ae_eq_closedBall_axisCubeCenter {d : ℕ} [NeZero d]
    (z : Vec d) {L : ℝ} (hL : 0 < L) :
    axisCube z L =ᵐ[volume] Metric.closedBall (axisCubeCenter z L) (L / 2) := by
  have hcorner : stoppingAxisCubeCorner (axisCubeCenter z L) 1 (L / 2) = z := by
    ext i
    simp only [stoppingAxisCubeCorner, axisCubeCenter]
    ring
  have hside : stoppingAxisCubeSide 1 (L / 2) = L := by
    simp only [stoppingAxisCubeSide]
    ring
  have hball :
      axisCube (stoppingAxisCubeCorner (axisCubeCenter z L) 1 (L / 2))
          (stoppingAxisCubeSide 1 (L / 2)) =ᵐ[volume]
        Metric.closedBall (axisCubeCenter z L) (1 * (L / 2)) :=
    axisCube_stoppingAxisCubeCorner_ae_eq_closedBall (d := d)
      (axisCubeCenter z L) (S := 1) (r := L / 2) (by norm_num) (by linarith)
  rw [hcorner, hside] at hball
  simpa only [one_mul] using hball

/-- A raw local lintegral is invariant under replacing an axis cube by an
a.e.-equal set, in particular by its closed sup-ball realization. -/
theorem axisCube_setLIntegral_eq_of_ae_eq
    {d : ℕ} (z : Vec d) (L : ℝ) (B : Set (Vec d))
    (hB : axisCube z L =ᵐ[volume] B) (f : Vec d → ℝ≥0∞) :
    (∫⁻ x in axisCube z L, f x ∂volume) = ∫⁻ x in B, f x ∂volume := by
  rw [Measure.restrict_congr_set hB]

/-- The powered norm bridge written over the closed sup-ball associated to a
positive axis cube. -/
theorem axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_closedBallLIntegral
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent) (F : Vec d → E) :
    (Gagliardo.integralLpSeminorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in Metric.closedBall (axisCubeCenter z L) (L / 2),
          ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal) ∂volume := by
  rw [axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_setLIntegral z hL]
  congr 1
  exact axisCube_setLIntegral_eq_of_ae_eq z L _
    (axisCube_ae_eq_closedBall_axisCubeCenter z hL) _

/-- The squared normalized `L²` norm is the normalized raw squared-energy
integral on a positive axis cube. -/
theorem axisCube_integralLpSeminorm_two_sq_eq_normalized_setLIntegral
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (F : Vec d → E) :
    (Gagliardo.integralLpSeminorm F 2 (axisCubeNormalizedMeasure z L)) ^ (2 : ℝ) =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in axisCube z L, ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume := by
  simpa only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat, Real.rpow_two] using
    (axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_setLIntegral z hL
      FiniteLpExponent.two F)

/-- The squared normalized `L²` norm has the same closed-ball integral form. -/
theorem axisCube_integralLpSeminorm_two_sq_eq_normalized_closedBallLIntegral
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (F : Vec d → E) :
    (Gagliardo.integralLpSeminorm F 2 (axisCubeNormalizedMeasure z L)) ^ (2 : ℝ) =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in Metric.closedBall (axisCubeCenter z L) (L / 2),
          ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume := by
  simpa only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat, Real.rpow_two] using
    (axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_closedBallLIntegral z hL
      FiniteLpExponent.two F)

/-- The integral identity expressed using Mathlib’s norm for a measurable function. -/
theorem axisCube_eLpNorm_rpow_exponent_eq_lintegral_enorm
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) (L : ℝ) (p : FiniteLpExponent) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (axisCubeNormalizedMeasure z L)) :
    (eLpNorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
      ∫⁻ x, ‖F x‖ₑ ^ p.exponent.toReal ∂axisCubeNormalizedMeasure z L := by
  rw [← Gagliardo.integralLpSeminorm_eq_eLpNorm F p.exponent _ hF]
  exact axisCube_integralLpSeminorm_rpow_exponent_eq_lintegral_enorm z L p F

/-- The integral identity expressed using Mathlib’s norm for a measurable function. -/
theorem axisCube_eLpNorm_rpow_exponent_eq_normalized_setLIntegral
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (axisCubeNormalizedMeasure z L)) :
    (eLpNorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in axisCube z L, ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal)
          ∂volume := by
  rw [← Gagliardo.integralLpSeminorm_eq_eLpNorm F p.exponent _ hF]
  exact axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_setLIntegral z hL p F

/-- The integral identity expressed using Mathlib’s norm for a measurable function. -/
theorem axisCube_eLpNorm_rpow_exponent_eq_normalized_closedBallLIntegral
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (axisCubeNormalizedMeasure z L)) :
    (eLpNorm F p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in Metric.closedBall (axisCubeCenter z L) (L / 2),
          ENNReal.ofReal (‖F x‖ ^ p.exponent.toReal) ∂volume := by
  rw [← Gagliardo.integralLpSeminorm_eq_eLpNorm F p.exponent _ hF]
  exact axisCube_integralLpSeminorm_rpow_exponent_eq_normalized_closedBallLIntegral z hL p F

/-- The integral identity expressed using Mathlib’s norm for a measurable function. -/
theorem axisCube_eLpNorm_two_sq_eq_normalized_setLIntegral
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (axisCubeNormalizedMeasure z L)) :
    (eLpNorm F 2 (axisCubeNormalizedMeasure z L)) ^ (2 : ℝ) =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in axisCube z L, ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume := by
  rw [← Gagliardo.integralLpSeminorm_eq_eLpNorm F 2 _ hF]
  exact axisCube_integralLpSeminorm_two_sq_eq_normalized_setLIntegral z hL F

/-- The integral identity expressed using Mathlib’s norm for a measurable function. -/
theorem axisCube_eLpNorm_two_sq_eq_normalized_closedBallLIntegral
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (axisCubeNormalizedMeasure z L)) :
    (eLpNorm F 2 (axisCubeNormalizedMeasure z L)) ^ (2 : ℝ) =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∫⁻ x in Metric.closedBall (axisCubeCenter z L) (L / 2),
          ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume := by
  rw [← Gagliardo.integralLpSeminorm_eq_eLpNorm F 2 _ hF]
  exact axisCube_integralLpSeminorm_two_sq_eq_normalized_closedBallLIntegral z hL F

end CubeCalderonZygmund

end

end Homogenization

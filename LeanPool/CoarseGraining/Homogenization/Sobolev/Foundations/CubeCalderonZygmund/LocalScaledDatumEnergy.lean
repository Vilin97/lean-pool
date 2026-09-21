/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalComparisonBridges

/-! # Local Scaled Datum Energy -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# Normalized energy bookkeeping for the scaled comparison datum

The local harmonic-replacement construction controls its zero-trace correction
in the raw Hilbert `L²` realization.  This file transports that estimate to the
normalized measure of the same axis cube.  Both sides acquire exactly the same
normalizing factor, so the datum is naturally the scaled field
`sigma0⁻¹ • hilbertifyVecField H`; in particular no volume or dimension factor
is introduced.
-/

private theorem axisCube_normalization_factor_ne_zero
    {d : ℕ} (L : ℝ) (hL : 0 < L) :
    ENNReal.ofReal ((L ^ d)⁻¹) ≠ 0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hL _)))

/-- The raw restricted Hilbert `L²` norm of an `H¹` gradient is exactly its
Hilbert-valued `eLpNorm`. -/
theorem eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2
    {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    eLpNorm (hilbertifyVecField u.grad) 2 (volume.restrict U) =
      ENNReal.ofReal ‖u.gradToHilbertVectorL2‖ := by
  let hu : MemHilbertVectorL2 U (hilbertifyVecField u.grad) :=
    memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2
  calc
    eLpNorm (hilbertifyVecField u.grad) 2 (volume.restrict U) =
        ‖hu.toLp (hilbertifyVecField u.grad)‖ₑ := (Lp.enorm_toLp hu).symm
    _ = ENNReal.ofReal ‖hu.toLp (hilbertifyVecField u.grad)‖ :=
      (ofReal_norm _).symm
    _ = ENNReal.ofReal ‖u.gradToHilbertVectorL2‖ := by
      rfl

/-- The raw restricted Hilbert `L²` norm of a plain vector datum is exactly
the `eLpNorm` of its Hilbert realization. -/
theorem eLpNorm_hilbertifyVecField_two_eq_ofReal_norm_toHilbertVectorL2
    {d : ℕ} {U : Set (Vec d)} {H : Vec d → Vec d}
    (hH : MemVectorL2 U H) :
    eLpNorm (hilbertifyVecField H) 2 (volume.restrict U) =
      ENNReal.ofReal ‖toHilbertVectorL2OfVecField hH‖ := by
  let hHH : MemHilbertVectorL2 U (hilbertifyVecField H) :=
    memHilbertVectorL2_hilbertifyVecField hH
  calc
    eLpNorm (hilbertifyVecField H) 2 (volume.restrict U) =
        ‖hHH.toLp (hilbertifyVecField H)‖ₑ := (Lp.enorm_toLp hHH).symm
    _ = ENNReal.ofReal ‖hHH.toLp (hilbertifyVecField H)‖ :=
      (ofReal_norm _).symm
    _ = ENNReal.ofReal ‖toHilbertVectorL2OfVecField hH‖ := by
      rfl

/-- On a positive axis cube, the local harmonic-replacement energy estimate
becomes the exact normalized `L²` estimate for the datum scaled by
`sigma0⁻¹`.  The normalizing volume factor is common to both sides and hence
cancels without a dimension loss. -/
theorem axisCubeNormalized_eLpNorm_harmonicCorrection_le_scaledDatum
    {d : ℕ} (z : Vec d) {L sigma0 : ℝ} (hL : 0 < L) (hsigma0 : 0 < sigma0)
    (w : H1Function (axisCube z L)) {H : Vec d → Vec d}
    (hH : MemVectorL2 (axisCube z L) H)
    (henergy : ‖w.gradToHilbertVectorL2‖ ≤
      sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hH‖) :
    eLpNorm (hilbertifyVecField w.grad) 2 (axisCubeNormalizedMeasure z L) ≤
      eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
        (axisCubeNormalizedMeasure z L) := by
  let U : Set (Vec d) := axisCube z L
  let c : ℝ≥0∞ := ENNReal.ofReal ((L ^ d)⁻¹)
  have hc : c ≠ 0 := by
    simpa only [c] using axisCube_normalization_factor_ne_zero (d := d) L hL
  have hraw :
      eLpNorm (hilbertifyVecField w.grad) 2 (volume.restrict U) ≤
        eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2 (volume.restrict U) := by
    rw [MeasureTheory.eLpNorm_const_smul,
      eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2,
      eLpNorm_hilbertifyVecField_two_eq_ofReal_norm_toHilbertVectorL2 hH]
    rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hsigma0.le)]
    exact ENNReal.ofReal_le_ofReal henergy
  change eLpNorm (hilbertifyVecField w.grad) 2 (axisCubeNormalizedMeasure z L) ≤
    eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2 (axisCubeNormalizedMeasure z L)
  rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict z L hL]
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero hc,
    MeasureTheory.eLpNorm_smul_measure_of_ne_zero hc]
  exact mul_le_mul_right hraw _

/-- A Hilbert-vector `L²` field on an axis cube is also `L²` for its
normalized measure.  This is only a finite rescaling of the restricted volume
measure. -/
theorem memHilbertVectorL2_axisCubeNormalizedMeasure
    {d : ℕ} (z : Vec d) {L : ℝ} (hL : 0 < L)
    {F : Vec d → HilbertVec d}
    (hF : MemHilbertVectorL2 (axisCube z L) F) :
    MemLp F 2 (axisCubeNormalizedMeasure z L) := by
  rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict z L hL]
  exact hF.smul_measure ENNReal.ofReal_ne_top

/-- Minkowski's inequality in the normalized measure of a cube, with local
`L²` witnesses supplying the measurability required by the real-variable
argument. -/
theorem axisCubeNormalized_eLpNorm_two_sub_le
    {d : ℕ} (z : Vec d) {L : ℝ} (hL : 0 < L)
    {F G : Vec d → HilbertVec d}
    (hF : MemHilbertVectorL2 (axisCube z L) F)
    (hG : MemHilbertVectorL2 (axisCube z L) G) :
    eLpNorm (F - G) 2 (axisCubeNormalizedMeasure z L) ≤
      eLpNorm F 2 (axisCubeNormalizedMeasure z L) +
        eLpNorm G 2 (axisCubeNormalizedMeasure z L) := by
  exact eLpNorm_sub_le
    (memHilbertVectorL2_axisCubeNormalizedMeasure z hL hF).aestronglyMeasurable
    (memHilbertVectorL2_axisCubeNormalizedMeasure z hL hG).aestronglyMeasurable
    (by norm_num)

end CubeCalderonZygmund

end

end Homogenization

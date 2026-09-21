/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.OverlapCubeVectorNormalized

/-!
# Finite-`p` overlap Poincaré assembly at one depth

This module assembles the normalized vector overlap-cube Poincaré estimate
over one retained depth.  All constants are chosen before the cube, depth,
and vector field.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem finiteLpExponent_ne_zero (q : FiniteLpExponent) : q.exponent ≠ 0 :=
  (zero_lt_one.trans q.one_lt).ne'

private theorem eLpNorm_rpow_eq_lintegral_enorm {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (q : FiniteLpExponent) (μ : Measure α) (f : α → E) :
    (eLpNorm f q.exponent μ) ^ q.exponent.toReal =
      ∫⁻ x, ‖f x‖ₑ ^ q.exponent.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (finiteLpExponent_ne_zero q) q.lt_top.ne,
    ← ENNReal.rpow_mul]
  have hq : q.exponent.toReal ≠ 0 :=
    ENNReal.toReal_pos (finiteLpExponent_ne_zero q) q.lt_top.ne |>.ne'
  rw [one_div, inv_mul_cancel₀ hq, ENNReal.rpow_one]

private theorem aemeasurable_jacobian_enorm_rpow_parent {d : ℕ}
    {Q : TriadicCube d} (q : FiniteLpExponent) (V : CubeVectorW1pFunction Q q) :
    AEMeasurable (fun x => ‖HilbertMat.ofMat (V.jacobian x)‖ₑ ^ q.exponent.toReal)
      (volume.restrict (cubeSet Q)) := by
  have hjacobian : AEMeasurable (fun x => HilbertMat.ofMat (V.jacobian x))
      (volume.restrict (cubeSet Q)) := by
    have hnorm := V.jacobianHilbertMemLp.aemeasurable
    have hcoeff : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))
    simpa [normalizedCubeMeasure, cubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := volume.restrict (cubeSet Q))
        (f := fun x => HilbertMat.ofMat (V.jacobian x)) hcoeff).1 hnorm
  exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hjacobian.enorm

private theorem aemeasurable_jacobian_enorm_rpow_overlap {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} (q : FiniteLpExponent)
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j) (V : CubeVectorW1pFunction Q q) :
    AEMeasurable (fun x => ‖HilbertMat.ofMat (V.jacobian x)‖ₑ ^ q.exponent.toReal)
      (volume.restrict (ScalarOverlap.cubeSet S)) := by
  have hsub : ScalarOverlap.cubeSet S ⊆ cubeSet Q :=
    ScalarOverlap.cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  have hparent := aemeasurable_jacobian_enorm_rpow_parent q V
  have hrestricted := hparent.restrict (s := ScalarOverlap.cubeSet S)
  rw [Measure.restrict_restrict_of_subset hsub] at hrestricted
  exact hrestricted

/-- One-depth powered overlap Poincaré assembly for an arbitrary cube-vector
finite-`W¹ᵖ` field. -/
theorem exists_cubeEuclideanPositiveBesovOverlapDepthENorm_rpow_le
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (Q : TriadicCube d) (j : ℕ) (V : CubeVectorW1pFunction Q q),
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q q V.toField j) ^
            q.exponent.toReal ≤
          C * (ENNReal.ofReal (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^
              q.exponent.toReal *
            (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
              q.exponent (normalizedCubeMeasure Q)) ^ q.exponent.toReal := by
  obtain ⟨C, hC_top, hC⟩ :=
    exists_overlapCubeVector_normalized_poincare_constant (d := d) q
  refine ⟨C ^ q.exponent.toReal * (3 ^ d : ℝ≥0∞),
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC_top)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), ?_⟩
  intro Q j V
  let D : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let ℓ : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let g : Vec d → ℝ≥0∞ := fun x =>
    ‖HilbertMat.ofMat (V.jacobian x)‖ₑ ^ q.exponent.toReal
  have hlocal : ∀ S ∈ D,
      (eLpNorm (fun x => HilbertVec.ofVec
        (V.toField x - ScalarOverlap.cubeAverageVec S V.toField))
        q.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ q.exponent.toReal ≤
        (C ^ q.exponent.toReal *
          (ENNReal.ofReal (overlapCubeScaleFactor S)) ^ q.exponent.toReal) *
        ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S := by
    intro S hS
    have hpow := ENNReal.rpow_le_rpow (hC Q j S (by simpa [D] using hS) V)
      (show 0 ≤ q.exponent.toReal from ENNReal.toReal_nonneg)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
      ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
      eLpNorm_rpow_eq_lintegral_enorm, eLpNorm_rpow_eq_lintegral_enorm] at hpow
    calc
      (eLpNorm (fun x => HilbertVec.ofVec
          (V.toField x - ScalarOverlap.cubeAverageVec S V.toField))
          q.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ q.exponent.toReal =
          ∫⁻ x, ‖HilbertVec.ofVec
            (V.toField x - ScalarOverlap.cubeAverageVec S V.toField)‖ₑ ^
              q.exponent.toReal ∂ScalarOverlap.normalizedCubeMeasure S :=
            eLpNorm_rpow_eq_lintegral_enorm q _ _
      _ ≤ C ^ q.exponent.toReal *
          (ENNReal.ofReal (overlapCubeScaleFactor S)) ^ q.exponent.toReal *
          ∫⁻ x, ‖HilbertMat.ofMat (V.jacobian x)‖ₑ ^ q.exponent.toReal ∂
            ScalarOverlap.normalizedCubeMeasure S := hpow
      _ = _ := by rfl
  have hscale : ∀ S ∈ D,
      overlapCubeScaleFactor S = ℓ := by
    intro S hS
    simpa [D, ℓ] using
      overlapCubeScaleFactor_eq_cubeScaleFactor_div_pow_of_mem_overlapCentersAtDepth
        (Q := Q) (j := j) hS
  have hassembly :
      ((D.card : ℝ≥0∞)⁻¹) *
        D.sum (fun S => ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S) ≤
      (3 ^ d : ℝ≥0∞) * ∫⁻ x, g x ∂normalizedCubeMeasure Q := by
    simpa [D, g] using!
      overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le Q j
        (aemeasurable_jacobian_enorm_rpow_parent q V)
        (fun S hS => aemeasurable_jacobian_enorm_rpow_overlap q hS V)
  rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
  calc
    ((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
        (eLpNorm (fun x => HilbertVec.ofVec
          (V.toField x - ScalarOverlap.cubeAverageVec S.1 V.toField))
          q.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ q.exponent.toReal) ≤
        ((D.card : ℝ≥0∞)⁻¹) * D.sum (fun S =>
          (C ^ q.exponent.toReal * (ENNReal.ofReal ℓ) ^ q.exponent.toReal) *
            ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S) := by
          apply mul_le_mul_right
          calc
            D.attach.sum (fun S =>
                (eLpNorm (fun x => HilbertVec.ofVec
                  (V.toField x - ScalarOverlap.cubeAverageVec S.1 V.toField))
                  q.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
                  q.exponent.toReal) ≤
                D.attach.sum (fun S =>
                  (C ^ q.exponent.toReal * (ENNReal.ofReal ℓ) ^ q.exponent.toReal) *
                    ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S.1) := by
                  exact Finset.sum_le_sum fun S hS => by
                    rw [← hscale S.1 S.2]
                    exact hlocal S.1 S.2
            _ = D.sum (fun S =>
                (C ^ q.exponent.toReal * (ENNReal.ofReal ℓ) ^ q.exponent.toReal) *
                  ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S) := by
                  simpa using (Finset.sum_attach D (fun S =>
                    (C ^ q.exponent.toReal * (ENNReal.ofReal ℓ) ^ q.exponent.toReal) *
                      ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S))
    _ = (C ^ q.exponent.toReal * (ENNReal.ofReal ℓ) ^ q.exponent.toReal) *
        (((D.card : ℝ≥0∞)⁻¹) *
          D.sum (fun S => ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S)) := by
          rw [← Finset.mul_sum]
          ac_rfl
    _ ≤ (C ^ q.exponent.toReal * (ENNReal.ofReal ℓ) ^ q.exponent.toReal) *
        ((3 ^ d : ℝ≥0∞) * ∫⁻ x, g x ∂normalizedCubeMeasure Q) := by
          exact mul_le_mul_right hassembly _
    _ = (C ^ q.exponent.toReal * (3 ^ d : ℝ≥0∞)) *
        (ENNReal.ofReal ℓ) ^ q.exponent.toReal *
        (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
          q.exponent (normalizedCubeMeasure Q)) ^ q.exponent.toReal := by
          rw [eLpNorm_rpow_eq_lintegral_enorm]
          ring
    _ = _ := by rfl

end

end Homogenization

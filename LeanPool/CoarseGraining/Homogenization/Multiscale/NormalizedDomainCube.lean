/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedMeasurableDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms

/-!
# Triadic cubes as bounded measurable domains

This module packages the operational half-open carrier of a triadic cube as a
`BoundedMeasurableDomain`.  The source-facing open cube remains only
almost-everywhere equal to this carrier; no equality of the two sets is used or
claimed here.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The half-open carrier of a triadic cube, packaged with its geometric
regularity and positive volume. -/
noncomputable def cubeBoundedMeasurableDomain {d : ℕ} (Q : TriadicCube d) :
    BoundedMeasurableDomain d where
  carrier := cubeSet Q
  measurableSet := measurableSet_cubeSet Q
  isBoundedDomain := by
    refine ⟨‖cubeCenter Q‖ + cubeRadius Q + 1, ?_, ?_⟩
    · have hnonneg : 0 ≤ ‖cubeCenter Q‖ + cubeRadius Q :=
        add_nonneg (norm_nonneg _) (cubeRadius_nonneg Q)
      linarith
    · intro x hx i
      have hxball : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
        cubeSet_subset_closedBall Q hx
      have hdist : ‖x - cubeCenter Q‖ ≤ cubeRadius Q := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
      have hxnorm : ‖x‖ ≤ ‖cubeCenter Q‖ + cubeRadius Q + 1 := by
        calc
          ‖x‖ = ‖(x - cubeCenter Q) + cubeCenter Q‖ := by
            congr 1
            abel
          _ ≤ ‖x - cubeCenter Q‖ + ‖cubeCenter Q‖ := norm_add_le _ _
          _ ≤ cubeRadius Q + ‖cubeCenter Q‖ := add_le_add hdist le_rfl
          _ = ‖cubeCenter Q‖ + cubeRadius Q := by ring
          _ ≤ ‖cubeCenter Q‖ + cubeRadius Q + 1 := by linarith
      exact (by
        simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hxnorm)
  volume_pos := by
    rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq]
    exact ENNReal.ofReal_pos.mpr (cubeVolume_pos Q)

@[simp] theorem coe_cubeBoundedMeasurableDomain {d : ℕ} (Q : TriadicCube d) :
    (cubeBoundedMeasurableDomain Q : Set (Vec d)) = cubeSet Q :=
  rfl

/-- Restricting volume to the safe cube domain is exactly the existing cube
measure. -/
@[simp] theorem cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure
    {d : ℕ} (Q : TriadicCube d) :
    (cubeBoundedMeasurableDomain Q).restrictedVolume = cubeMeasure Q :=
  rfl

/-- The safe-domain normalization agrees exactly with the established normalized
cube measure. -/
theorem cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) :
    (cubeBoundedMeasurableDomain Q).normalizedVolume = normalizedCubeMeasure Q := by
  change (MeasureTheory.volume (cubeSet Q))⁻¹ • MeasureTheory.volume.restrict (cubeSet Q) =
    ENNReal.ofReal ((cubeVolume Q)⁻¹) • MeasureTheory.volume.restrict (cubeSet Q)
  rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq,
    ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]

/-- The operational half-open cube and the source-facing open cube induce the
same restricted volume measure. -/
theorem cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet
    {d : ℕ} (Q : TriadicCube d) :
    (cubeBoundedMeasurableDomain Q).restrictedVolume =
      MeasureTheory.volume.restrict (openCubeSet Q) := by
  change MeasureTheory.volume.restrict (cubeSet Q) =
    MeasureTheory.volume.restrict (openCubeSet Q)
  exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q

/-- Almost-everywhere statements for the safe cube domain can equivalently be
read over the source-facing open cube. -/
theorem ae_cubeBoundedMeasurableDomain_restrictedVolume_iff_openCubeSet
    {d : ℕ} (Q : TriadicCube d) {p : Vec d → Prop} :
    (∀ᵐ x ∂(cubeBoundedMeasurableDomain Q).restrictedVolume, p x) ↔
      ∀ᵐ x ∂MeasureTheory.volume.restrict (openCubeSet Q), p x := by
  rw [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]

/-- The proof-carrying safe-domain average is the existing cube average. -/
theorem cubeBoundedMeasurableDomain_average_eq_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f (cubeBoundedMeasurableDomain Q).restrictedVolume) :
    (cubeBoundedMeasurableDomain Q).average f hf = cubeAverage Q f := by
  change ∫ x, f x ∂(cubeBoundedMeasurableDomain Q).normalizedVolume = cubeAverage Q f
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    ← cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The safe-domain average has the source-facing open-cube formula.  This is
an a.e. bridge, rather than an assertion that the two cube carriers coincide. -/
theorem cubeBoundedMeasurableDomain_average_eq_openCubeSet_average {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f (cubeBoundedMeasurableDomain Q).restrictedVolume) :
    (cubeBoundedMeasurableDomain Q).average f hf =
      (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume := by
  rw [BoundedMeasurableDomain.average_eq_volume_toReal_inv_mul_setIntegral]
  change (MeasureTheory.volume (cubeSet Q)).toReal⁻¹ *
      ∫ x in cubeSet Q, f x ∂MeasureTheory.volume =
    (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
      ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume
  rw [volume_openCubeSet_eq_volume_cubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

end

end Homogenization

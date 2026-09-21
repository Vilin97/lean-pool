/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Localization
import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Descendants
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimate
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalizedEnergyProfile
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.Descendants

/-! # Gradient -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Descendant summation for the small-cube Caccioppoli route

The LaTeX proof estimates the cutoff pairing on small cubes and then sums over
those cubes.  This file isolates the measure-theoretic bookkeeping: a
cube-average over `Q` is the descendants-average of the cube-averages over the
depth-`j` descendants, hence its absolute value is controlled by the
descendants-average of the local absolute values.
-/

/-- Descendant-local gradient `circ` bound with the parent canonical
coefficient.

This is the scale-cancellation step in the small-cube proof: the negative
scale weight of the descendant cancels the `3^{r j}` growth in the localized
ellipticity bound. -/
theorem cubeBesovCircPartialNorm_component_le_parent_canonicalGradientAcirc_of_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (r : ℝ)
    (hr : 0 < r) {g : Vec d → Vec d} {energy : Vec d → ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight r 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm R r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))) *
        Real.sqrt (cubeAverage R energy) := by
  have henergy_nonneg_R : ∀ x ∈ cubeSet R, 0 ≤ energy x := by
    intro x hx
    exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
  have henergy_int_R :
      MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume :=
    henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hgrad_R : CubeAverageGradientEnergyControl R a g energy :=
    hgrad.restrict_to_descendant hR
  have hsum_R :
      Summable (fun n : ℕ =>
        geometricWeight r 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a r hr.le hR hsum
  have hpartial :
      cubeBesovNegativeVectorPartialSeminorm R r N g ≤
        (geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq R r (.finite 1) a) (-1 / 2 : ℝ) *
          Real.sqrt (cubeAverage R energy) :=
    coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
      R a r hr g energy N henergy_nonneg_R henergy_int_R hgrad_R hsum_R
  have hlambda :
      Real.rpow (lambdaSq R r (.finite 1) a) (-1 / 2 : ℝ) ≤
        Real.rpow (3 : ℝ) (r * (j : ℝ)) *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ) :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a r hr.le hR hsum
  have hdisc_nonneg : 0 ≤ (geometricDiscount r 1)⁻¹ := by
    exact inv_nonneg.mpr (geometricDiscount_pos (by simpa using hr)).le
  have hscale_R_nonneg : 0 ≤ cubeBesovScaleWeight (-r) R :=
    cubeBesovScaleWeight_nonneg (-r) R
  have hsqrt_nonneg : 0 ≤ Real.sqrt (cubeAverage R energy) := Real.sqrt_nonneg _
  have hscale_cancel :
      cubeBesovScaleWeight (-r) R * Real.rpow (3 : ℝ) (r * (j : ℝ)) =
        cubeBesovScaleWeight (-r) Q := by
    exact cubeBesovScaleWeight_neg_mul_rpow_eq_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) r hR
  calc
    cubeBesovCircPartialNorm R r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i)
        ≤ cubeBesovScaleWeight (-r) R *
            cubeBesovNegativeVectorPartialSeminorm R r N g := by
          exact
            cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
              R r g i N
    _ ≤ cubeBesovScaleWeight (-r) R *
          (((geometricDiscount r 1)⁻¹ *
            Real.rpow (lambdaSq R r (.finite 1) a) (-1 / 2 : ℝ)) *
            Real.sqrt (cubeAverage R energy)) := by
          exact mul_le_mul_of_nonneg_left hpartial hscale_R_nonneg
    _ ≤ cubeBesovScaleWeight (-r) R *
          (((geometricDiscount r 1)⁻¹ *
            (Real.rpow (3 : ℝ) (r * (j : ℝ)) *
              Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))) *
            Real.sqrt (cubeAverage R energy)) := by
          refine mul_le_mul_of_nonneg_left ?_ hscale_R_nonneg
          refine mul_le_mul_of_nonneg_right ?_ hsqrt_nonneg
          exact mul_le_mul_of_nonneg_left hlambda hdisc_nonneg
    _ =
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))) *
        Real.sqrt (cubeAverage R energy) := by
          rw [← hscale_cancel]
          ring

/-- Descendant-local gradient `circ` bound with the local canonical
coefficient.

This is the small-cube version of the gradient-control line in the LaTeX
proof: before localization to the parent cube, each descendant keeps its own
`A^\circ_r(R)` factor. -/
theorem cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (r : ℝ)
    (hr : 0 < r) {g : Vec d → Vec d} {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight r 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))) *
        Real.sqrt (cubeAverage Q energy) := by
  have hpartial :
      cubeBesovNegativeVectorPartialSeminorm Q r N g ≤
        (geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy) :=
    coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
      Q a r hr g energy N henergy_nonneg henergy_int hgrad hsum
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-r) Q :=
    cubeBesovScaleWeight_nonneg (-r) Q
  calc
    cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i)
        ≤ cubeBesovScaleWeight (-r) Q *
            cubeBesovNegativeVectorPartialSeminorm Q r N g := by
          exact
            cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
              Q r g i N
    _ ≤ cubeBesovScaleWeight (-r) Q *
          (((geometricDiscount r 1)⁻¹ *
            Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ)) *
            Real.sqrt (cubeAverage Q energy)) := by
          exact mul_le_mul_of_nonneg_left hpartial hscale_nonneg
    _ =
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))) *
        Real.sqrt (cubeAverage Q energy) := by
          ring

/-- A local canonical gradient `A^\circ_r(R)` on a depth-`j` descendant is
bounded by the parent canonical factor after the usual descendant scale
cancellation. -/
theorem local_canonicalGradientAcirc_core_le_parent_of_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (r : ℝ)
    (hr : 0 < r)
    (hR : R ∈ descendantsAtDepth Q j)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight r 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    cubeBesovScaleWeight (-r) R *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq R r (.finite 1) a) (-1 / 2 : ℝ)) ≤
      cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ)) := by
  have hlambda :
      Real.rpow (lambdaSq R r (.finite 1) a) (-1 / 2 : ℝ) ≤
        Real.rpow (3 : ℝ) (r * (j : ℝ)) *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ) :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a r hr.le hR hsum
  have hdisc_nonneg : 0 ≤ (geometricDiscount r 1)⁻¹ := by
    exact inv_nonneg.mpr (geometricDiscount_pos (by simpa using hr)).le
  have hscale_R_nonneg : 0 ≤ cubeBesovScaleWeight (-r) R :=
    cubeBesovScaleWeight_nonneg (-r) R
  have hscale_cancel :
      cubeBesovScaleWeight (-r) R * Real.rpow (3 : ℝ) (r * (j : ℝ)) =
        cubeBesovScaleWeight (-r) Q := by
    exact cubeBesovScaleWeight_neg_mul_rpow_eq_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) r hR
  calc
    cubeBesovScaleWeight (-r) R *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq R r (.finite 1) a) (-1 / 2 : ℝ))
        ≤
      cubeBesovScaleWeight (-r) R *
        ((geometricDiscount r 1)⁻¹ *
          (Real.rpow (3 : ℝ) (r * (j : ℝ)) *
            Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlambda hdisc_nonneg) hscale_R_nonneg
    _ =
      cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ)) := by
          rw [← hscale_cancel]
          ring

end

end Homogenization

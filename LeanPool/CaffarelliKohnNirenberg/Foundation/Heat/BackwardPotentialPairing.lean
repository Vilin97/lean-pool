/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotential

/-!
# Backward Potential Pairing

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private theorem integral_kernel_pairing
    {K : ParabolicPoint → ParabolicPoint → ℝ}
    {f ζ : ParabolicPoint → ℝ}
    (hF : Integrable
      (fun q : ParabolicPoint × ParabolicPoint =>
        K q.1 q.2 * ζ q.1 * f q.2)
      ((volume : Measure ParabolicPoint).prod volume))
    :
    ∫ v, f v * (∫ z, K z v * ζ z) =
      ∫ z, (∫ v, K z v * f v) * ζ z := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  let F : ParabolicPoint × ParabolicPoint → ℝ := fun q =>
    K q.1 q.2 * ζ q.1 * f q.2
  have hleft :
      ∫ v, ∫ z, F (z, v) = ∫ z, ∫ v, F (z, v) := by
    calc
      ∫ v, ∫ z, F (z, v) =
          ∫ q : ParabolicPoint × ParabolicPoint, F q.swap ∂
            ((volume : Measure ParabolicPoint).prod volume) := by
        simpa only [Prod.swap_prod_mk] using
          (integral_prod (μ := (volume : Measure ParabolicPoint))
            (ν := (volume : Measure ParabolicPoint))
            (fun q : ParabolicPoint × ParabolicPoint => F q.swap) hF.swap).symm
      _ = ∫ q : ParabolicPoint × ParabolicPoint, F q ∂
          ((volume : Measure ParabolicPoint).prod volume) := integral_prod_swap F
      _ = ∫ z, ∫ v, F (z, v) := integral_prod
        (μ := (volume : Measure ParabolicPoint))
        (ν := (volume : Measure ParabolicPoint)) F hF
  calc
    ∫ v, f v * (∫ z, K z v * ζ z) = ∫ v, ∫ z, F (z, v) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      unfold F
      ring
    _ = ∫ z, ∫ v, F (z, v) := hleft
    _ = ∫ z, (∫ v, K z v * f v) * ζ z := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with v
      unfold F
      ring

theorem backwardHeatPotential_pairing
    {f ζ : ParabolicPoint → ℝ}
    (hF : Integrable
      (fun q : ParabolicPoint × ParabolicPoint =>
        backwardHeatKernel q.1 q.2 * ζ q.1 * f q.2)
      ((volume : Measure ParabolicPoint).prod volume)) :
    ∫ v, f v * backwardHeatPotential ζ v =
      ∫ z, (∫ v, backwardHeatKernel z v * f v) * ζ z := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  unfold backwardHeatPotential
  exact integral_kernel_pairing hF

theorem backwardHeatPotential_spatial_pairing
    {i : Fin 3} {f ζ : ParabolicPoint → ℝ}
    (hF : Integrable
      (fun q : ParabolicPoint × ParabolicPoint =>
        backwardHeatSpatialKernel i q.1 q.2 * ζ q.1 * f q.2)
      ((volume : Measure ParabolicPoint).prod volume)) :
    ∫ v, f v * backwardHeatPotentialSpatial i ζ v =
      -∫ z, (∫ v, backwardHeatSpatialKernel i z v * f v) * ζ z := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  calc
    ∫ v, f v * backwardHeatPotentialSpatial i ζ v =
        ∫ v, -(f v * (∫ z, backwardHeatSpatialKernel i z v * ζ z)) := by
      unfold backwardHeatPotentialSpatial
      apply integral_congr_ae
      filter_upwards [] with v
      ring
    _ = -∫ v, f v * (∫ z, backwardHeatSpatialKernel i z v * ζ z) :=
      integral_neg _
    _ = -∫ z, (∫ v, backwardHeatSpatialKernel i z v * f v) * ζ z := by
      rw [integral_kernel_pairing hF]


end CKN.Foundation.Heat

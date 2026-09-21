/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Multiscale.Projection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Projection Convergence -/

namespace Homogenization

open scoped Topology

noncomputable def descendantContaining {d : ℕ} (Q : TriadicCube d) (x : Vec d) (n : ℕ)
    (hx : x ∈ cubeSet Q) : TriadicCube d :=
  Classical.choose (existsUnique_descendantAtDepth_mem_cubeSet (Q := Q) (x := x) n hx)

theorem descendantContaining_mem_descendantsAtDepth {d : ℕ} (Q : TriadicCube d) (x : Vec d)
    (n : ℕ) (hx : x ∈ cubeSet Q) :
    descendantContaining Q x n hx ∈ descendantsAtDepth Q n :=
  (Classical.choose_spec (existsUnique_descendantAtDepth_mem_cubeSet (Q := Q) (x := x) n hx)).1.1

theorem mem_cubeSet_descendantContaining {d : ℕ} (Q : TriadicCube d) (x : Vec d)
    (n : ℕ) (hx : x ∈ cubeSet Q) :
    x ∈ cubeSet (descendantContaining Q x n hx) :=
  (Classical.choose_spec (existsUnique_descendantAtDepth_mem_cubeSet (Q := Q) (x := x) n hx)).1.2

theorem cubeScaleFactor_descendantContaining {d : ℕ} (Q : TriadicCube d) (x : Vec d)
    (n : ℕ) (hx : x ∈ cubeSet Q) :
    cubeScaleFactor (descendantContaining Q x n hx) = cubeScaleFactor Q / (3 : ℝ) ^ n := by
  have hmem := descendantContaining_mem_descendantsAtDepth Q x n hx
  rw [cubeScaleFactor, scale_eq_sub_of_mem_descendantsAtDepth hmem, zpow_sub₀]
  · simp [cubeScaleFactor, div_eq_mul_inv]
  · norm_num

theorem cubeRadius_descendantContaining {d : ℕ} (Q : TriadicCube d) (x : Vec d)
    (n : ℕ) (hx : x ∈ cubeSet Q) :
    cubeRadius (descendantContaining Q x n hx) =
      ((1 / 2 : ℝ) * cubeScaleFactor Q) * ((1 / 3 : ℝ) ^ n) := by
  calc
    cubeRadius (descendantContaining Q x n hx)
        = (1 / 2 : ℝ) * (cubeScaleFactor Q / (3 : ℝ) ^ n) := by
            rw [cubeRadius, cubeScaleFactor_descendantContaining]
    _ = ((1 / 2 : ℝ) * cubeScaleFactor Q) / (3 : ℝ) ^ n := by ring
    _ = ((1 / 2 : ℝ) * cubeScaleFactor Q) * ((1 / 3 : ℝ) ^ n) := by
          simp [div_eq_mul_inv]

theorem ae_tendsto_cubeProjection_of_integrableOn {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (cubeSet Q)),
      Filter.Tendsto (fun n => cubeProjection Q n f x) Filter.atTop (𝓝 (f x)) := by
  let fQ : Vec d → ℝ := Set.indicator (cubeSet Q) f
  have hfQ : MeasureTheory.Integrable fQ MeasureTheory.volume := by
    rw [MeasureTheory.integrable_indicator_iff (measurableSet_cubeSet Q)]
    exact hf
  have hldt :=
    IsUnifLocDoublingMeasure.ae_tendsto_average
      (μ := MeasureTheory.volume) (f := fQ) (K := (1 : ℝ)) hfQ.locallyIntegrable
  refine (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
  filter_upwards [hldt] with x hx hxQ
  let R : ℕ → TriadicCube d := fun n => descendantContaining Q x n hxQ
  have hpow :
      Filter.Tendsto (fun n : ℕ => ((1 / 3 : ℝ) ^ n)) Filter.atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hrad0 :
      Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ) * cubeScaleFactor Q) * ((1 / 3 : ℝ) ^ n))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hpow.const_mul (((1 / 2 : ℝ) * cubeScaleFactor Q))
  have hrad_pos :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((1 / 2 : ℝ) * cubeScaleFactor Q) * ((1 / 3 : ℝ) ^ n) ∈ Set.Ioi (0 : ℝ) := by
    exact Filter.Eventually.of_forall fun n => by
      show 0 < ((1 / 2 : ℝ) * cubeScaleFactor Q) * ((1 / 3 : ℝ) ^ n)
      have hcube : 0 < cubeScaleFactor Q := by
        simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
      exact mul_pos (mul_pos (by norm_num) hcube) (pow_pos (by norm_num) _)
  have hrad :
      Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ) * cubeScaleFactor Q) * ((1 / 3 : ℝ) ^ n))
        Filter.atTop (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hrad0 hrad_pos
  have hδ :
      Filter.Tendsto (fun n : ℕ => cubeRadius (R n)) Filter.atTop (𝓝[>] (0 : ℝ)) := by
    convert hrad using 1
    funext n
    exact cubeRadius_descendantContaining Q x n hxQ
  have hxmem :
      ∀ᶠ n : ℕ in Filter.atTop, x ∈ Metric.closedBall (cubeCenter (R n)) (cubeRadius (R n)) := by
    exact Filter.Eventually.of_forall fun n =>
      cubeSet_subset_closedBall (R n) (mem_cubeSet_descendantContaining Q x n hxQ)
  have hconv :
      Filter.Tendsto
        (fun n => ⨍ y in Metric.closedBall (cubeCenter (R n)) (cubeRadius (R n)),
          fQ y ∂MeasureTheory.volume)
        Filter.atTop (𝓝 (fQ x)) :=
    hx (fun n => cubeCenter (R n)) (fun n => cubeRadius (R n)) hδ <| by
      simpa using hxmem
  have hproj :
      Filter.Tendsto (fun n => cubeProjection Q n f x) Filter.atTop (𝓝 (fQ x)) := by
    have hproj_eq :
        (fun n => cubeProjection Q n f x) =
          (fun n => ⨍ y in Metric.closedBall (cubeCenter (R n)) (cubeRadius (R n)),
            fQ y ∂MeasureTheory.volume) := by
      funext n
      have hRmem : R n ∈ descendantsAtDepth Q n :=
        descendantContaining_mem_descendantsAtDepth Q x n hxQ
      have hxR : x ∈ cubeSet (R n) :=
        mem_cubeSet_descendantContaining Q x n hxQ
      calc
        cubeProjection Q n f x = cubeAverage (R n) f := by
          exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hRmem hxR
        _ = ⨍ y in cubeSet (R n), f y ∂MeasureTheory.volume := by
          exact cubeAverage_eq_setAverage_cubeSet (R n) f
        _ = ⨍ y in cubeSet (R n), fQ y ∂MeasureTheory.volume := by
          symm
          apply MeasureTheory.setAverage_congr_fun (hs := measurableSet_cubeSet (R n))
          exact Filter.Eventually.of_forall fun y hy => by
            simp [fQ, Set.indicator_of_mem,
              cubeSet_subset_of_mem_descendantsAtDepth hRmem hy]
        _ = ⨍ y in Metric.closedBall (cubeCenter (R n)) (cubeRadius (R n)),
              fQ y ∂MeasureTheory.volume := by
          exact MeasureTheory.setAverage_congr (cubeSet_ae_eq_closedBall (R n))
    simpa [hproj_eq] using hconv
  simpa [fQ, Set.indicator_of_mem hxQ] using hproj

end Homogenization

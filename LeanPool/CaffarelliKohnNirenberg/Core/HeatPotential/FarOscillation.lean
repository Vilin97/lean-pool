/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.FarShell

/-!
# Far Oscillation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric
open Filter


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem heatPotential_far_shell_two_step_oscillation
    {K : ParabolicPoint → ℝ} {z p p' v : ParabolicPoint} {r A B : ℝ}
    (hp : p ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspace :
      |K (p.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p.2 - v.2)| ≤ A * vec3EuclideanNorm (p.1 - p'.1))
    (htime :
      |K (p'.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p'.2 - v.2)| ≤ B * |p.2 - p'.2|) :
    |K (p.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p'.2 - v.2)| ≤
      2 * r * (A + 2 * r * B) := by
  have hdist : parabolicDist p p' ≤ 2 * r := by
    rw [← dist_eq_parabolicDist]
    calc
      dist p p' ≤ dist p z + dist z p' := dist_triangle _ _ _
      _ ≤ r + r := add_le_add (by simpa [dist_comm] using hp)
        (by rw [dist_comm]; simpa using hp')
      _ = 2 * r := by ring
  have hspace_dist : vec3EuclideanNorm (p.1 - p'.1) ≤ 2 * r := by
    have hcomponent : vec3EuclideanNorm (p.1 - p'.1) ≤ parabolicDist p p' := by
      exact le_max_left _ _
    exact hcomponent.trans hdist
  have htime_dist : Real.sqrt |p.2 - p'.2| ≤ 2 * r := by
    have hcomponent : Real.sqrt |p.2 - p'.2| ≤ parabolicDist p p' := by
      exact le_max_right _ _
    exact hcomponent.trans hdist
  have habs_time : |p.2 - p'.2| ≤ (2 * r) ^ 2 := by
    have hsquare : (Real.sqrt |p.2 - p'.2|) ^ 2 = |p.2 - p'.2| :=
      Real.sq_sqrt (abs_nonneg _)
    have hsqrt_nonneg : 0 ≤ Real.sqrt |p.2 - p'.2| := Real.sqrt_nonneg _
    nlinarith only [hsquare, hsqrt_nonneg, htime_dist]
  calc
    |K (p.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p'.2 - v.2)| ≤
        |K (p.1 - v.1, p.2 - v.2) -
          K (p'.1 - v.1, p.2 - v.2)| +
        |K (p'.1 - v.1, p.2 - v.2) -
          K (p'.1 - v.1, p'.2 - v.2)| := by
      simpa only [sub_eq_add_neg, add_sub_assoc] using
        abs_sub_le _ _ _
    _ ≤ A * vec3EuclideanNorm (p.1 - p'.1) + B * |p.2 - p'.2| :=
      add_le_add hspace htime
    _ ≤ A * (2 * r) + B * (2 * r) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hspace_dist hA)
        (mul_le_mul_of_nonneg_left habs_time hB)
    _ = 2 * r * (A + 2 * r * B) := by ring

theorem heatPotential_far_shell_kernel_difference_abs_le_of_positive
    {z p p' v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialKernel p v - heatPotentialKernel p' v| ≤
      2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5)) := by
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) + 4) * r
  have hR : 0 < R := by positivity
  have hA : 0 ≤ 900000 / R ^ 4 := by positivity
  have hB : 0 ≤ 10000000 / R ^ 5 := by positivity
  have hspace :
      |heatPotentialKernel p v - heatPotentialKernel (p'.1, p.2) v| ≤
        (900000 / R ^ 4) * vec3EuclideanNorm (p.1 - p'.1) := by
    simpa [R] using heatPotential_far_shell_spatial_kernel_difference_abs_le
      hr hp hp' hv
  have hp'd := hp'
  rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp'd
  have hspace' : vec3EuclideanNorm (p'.1 - z.1) ≤ r :=
    (le_max_left _ _).trans hp'd
  have htime :
      |heatPotentialKernel (p'.1, p.2) v - heatPotentialKernel p' v| ≤
      (10000000 / R ^ 5) * |p.2 - p'.2| := by
    by_cases horder : p.2 ≤ p'.2
    · by_cases htp : 0 ≤ p.2 - v.2
      · apply heatPotential_time_kernel_difference_abs_le (p := (p'.1, p.2))
          (p' := p') (v := v) hR horder htp
        intro s hs
        have hsball := parabolic_ball_time_segment_mem hr.le hp hp' hspace' hs
        rcases heatPotential_far_shell_kernel_separation hr hsball hv with
          hzero | hsep
        · have hsnonneg : 0 ≤ s - v.2 := by linarith only [htp, hs.1]
          have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
          have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
          simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
        · exact hsep
      · have hpv : p.2 ≤ v.2 := by linarith only [lt_of_not_ge htp]
        by_cases htp' : 0 ≤ p'.2 - v.2
        · have htime' : v.2 ≤ p'.2 := by linarith only [htp']
          have hrev := heatPotential_time_kernel_difference_abs_le
            (p := (p'.1, v.2)) (p' := p') (v := v) hR
            (by simpa using htime') (by simp)
            (by
              intro s hs
              have hs' : s ∈ Set.Icc v.2 p'.2 := by simpa using hs
              have hsball := parabolic_ball_time_segment_mem hr.le hp hp' hspace'
                ⟨le_trans hpv hs'.1, hs'.2⟩
              rcases heatPotential_far_shell_kernel_separation hr hsball hv with
                hzero | hsep
              · have hsnonneg : 0 ≤ s - v.2 := by linarith only [hs'.1]
                have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
                have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
                simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
              · exact hsep)
          have hzero : heatPotentialKernel (p'.1, p.2) v =
              heatPotentialKernel (p'.1, v.2) v := by
            change heatKernelPlus (p'.1 - v.1, p.2 - v.2) =
              heatKernelPlus (p'.1 - v.1, v.2 - v.2)
            rw [heatKernelPlus_eq_zero_of_nonpos (sub_nonpos.mpr hpv)]
            rw [show v.2 - v.2 = 0 by ring,
              heatKernelPlus_eq_zero_of_nonpos (le_rfl)]
          rw [hzero]
          have hrev' : |heatPotentialKernel (p'.1, v.2) v -
              heatPotentialKernel p' v| ≤
              (10000000 / R ^ 5) * |v.2 - p'.2| := by
            simpa [abs_sub_comm] using hrev
          have hle : |v.2 - p'.2| ≤ |p.2 - p'.2| := by
            rw [abs_of_nonpos (sub_nonpos.mpr htime'),
              abs_of_nonpos (sub_nonpos.mpr (by linarith only [hpv, htime']))]
            linarith only [hpv]
          calc
            |heatPotentialKernel (p'.1, v.2) v - heatPotentialKernel p' v| ≤
                (10000000 / R ^ 5) * |v.2 - p'.2| := hrev'
            _ ≤ (10000000 / R ^ 5) * |p.2 - p'.2| := by
              gcongr
        · have hp'v : p'.2 ≤ v.2 := by linarith only [lt_of_not_ge htp']
          simp [heatPotentialKernel, pointSub,
            heatKernelPlus_eq_zero_of_nonpos (sub_nonpos.mpr hpv),
            heatKernelPlus_eq_zero_of_nonpos (sub_nonpos.mpr hp'v)]
          positivity
    · have horder' : p'.2 ≤ p.2 := le_of_not_ge horder
      by_cases htp' : 0 ≤ p'.2 - v.2
      · have hrev := heatPotential_time_kernel_difference_abs_le (p := p')
          (p' := (p'.1, p.2)) (v := v) hR horder' htp'
          (by
            intro s hs
            have hsball := parabolic_ball_time_segment_mem hr.le hp' hp hspace' hs
            rcases heatPotential_far_shell_kernel_separation hr hsball hv with
              hzero | hsep
            · have hsnonneg : 0 ≤ s - v.2 := by linarith only [htp', hs.1]
              have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
              have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
              simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
            · exact hsep)
        have hrev' :
            |heatPotentialKernel (p'.1, p.2) v -
                heatPotentialKernel (p'.1, p'.2) v| ≤
              (10000000 / R ^ 5) * |p.2 - p'.2| := by
          calc
            |heatPotentialKernel (p'.1, p.2) v -
                heatPotentialKernel (p'.1, p'.2) v| =
                |heatPotentialKernel (p'.1, p'.2) v -
                  heatPotentialKernel (p'.1, p.2) v| :=
              abs_sub_comm _ _
            _ ≤ (10000000 / R ^ 5) * |p'.2 - p.2| := by
              simpa only [Prod.fst, Prod.snd, Prod.eta] using hrev
            _ = (10000000 / R ^ 5) * |p.2 - p'.2| := by
              rw [abs_sub_comm]
        rw [← Prod.eta p']
        exact hrev'
      · have hp'v : p'.2 ≤ v.2 := by linarith only [lt_of_not_ge htp']
        by_cases htp : 0 ≤ p.2 - v.2
        · have htime' : v.2 ≤ p.2 := by linarith only [htp]
          have hrev := heatPotential_time_kernel_difference_abs_le
            (p := (p'.1, v.2)) (p' := (p'.1, p.2)) (v := v) hR
            (by simpa using htime') (by simp)
            (by
              intro s hs
              have hs' : s ∈ Set.Icc v.2 p.2 := by simpa using hs
              have hsball := parabolic_ball_time_segment_mem hr.le hp' hp hspace'
                ⟨le_trans hp'v hs'.1, hs'.2⟩
              rcases heatPotential_far_shell_kernel_separation hr hsball hv with
                hzero | hsep
              · have hsnonneg : 0 ≤ s - v.2 := by linarith only [hs'.1]
                have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
                have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
                simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
              · exact hsep)
          have hzero : heatPotentialKernel p' v =
              heatPotentialKernel (p'.1, v.2) v := by
            change heatKernelPlus (p'.1 - v.1, p'.2 - v.2) =
              heatKernelPlus (p'.1 - v.1, v.2 - v.2)
            rw [heatKernelPlus_eq_zero_of_nonpos (sub_nonpos.mpr hp'v)]
            rw [show v.2 - v.2 = 0 by ring,
              heatKernelPlus_eq_zero_of_nonpos (le_rfl)]
          rw [hzero]
          have hle : |p'.2 - v.2| ≤ |p.2 - p'.2| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hp'v),
              abs_of_nonneg (sub_nonneg.mpr (by linarith only [horder', htime']))]
            linarith only [htime']
          have hrev' :
              |heatPotentialKernel (p'.1, p.2) v -
                heatPotentialKernel (p'.1, v.2) v| ≤
              (10000000 / R ^ 5) * |p.2 - v.2| := by
            calc
              |heatPotentialKernel (p'.1, p.2) v -
                  heatPotentialKernel (p'.1, v.2) v| =
                  |heatPotentialKernel (p'.1, v.2) v -
                    heatPotentialKernel (p'.1, p.2) v| := abs_sub_comm _ _
              _ ≤ (10000000 / R ^ 5) * |v.2 - p.2| := by
                simpa only [Prod.fst, Prod.snd, Prod.eta] using hrev
              _ = (10000000 / R ^ 5) * |p.2 - v.2| := by
                rw [abs_sub_comm]
          calc
            |heatPotentialKernel (p'.1, p.2) v - heatPotentialKernel (p'.1, v.2) v| ≤
                (10000000 / R ^ 5) * |p.2 - v.2| := hrev'
            _ ≤ (10000000 / R ^ 5) * |p.2 - p'.2| := by
              gcongr
        · have hpv : p.2 ≤ v.2 := by linarith only [lt_of_not_ge htp]
          simp [heatPotentialKernel, pointSub,
            heatKernelPlus_eq_zero_of_nonpos (sub_nonpos.mpr hp'v),
            heatKernelPlus_eq_zero_of_nonpos (sub_nonpos.mpr hpv)]
          positivity
  simpa [R, heatPotentialKernel, pointSub] using
    heatPotential_far_shell_two_step_oscillation
    hp hp' hA hB hspace htime

theorem heatPotential_far_shell_spatial_kernel_spatial_difference_abs_le_of_positive
    {i : Fin 3} {z p p' v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialSpatialKernel i p v - heatPotentialSpatialKernel i p' v| ≤
      2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6)) := by
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) + 4) * r
  have hR : 0 < R := by positivity
  have hA : 0 ≤ 60000000 / R ^ 5 := by positivity
  have hB : 0 ≤ 30000000000 / R ^ 6 := by positivity
  have hspace :
      |heatPotentialSpatialKernel i p v - heatPotentialSpatialKernel i (p'.1, p.2) v| ≤
        (60000000 / R ^ 5) * vec3EuclideanNorm (p.1 - p'.1) := by
    simpa [R] using heatPotential_far_shell_spatial_kernel_spatial_difference_abs_le
      hr hp hp' hv
  have hp'd := hp'
  rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp'd
  have hspace' : vec3EuclideanNorm (p'.1 - z.1) ≤ r :=
    (le_max_left _ _).trans hp'd
  have htime :
      |heatPotentialSpatialKernel i (p'.1, p.2) v - heatPotentialSpatialKernel i p' v| ≤
      (30000000000 / R ^ 6) * |p.2 - p'.2| := by
    by_cases horder : p.2 ≤ p'.2
    · by_cases htp : 0 ≤ p.2 - v.2
      · apply heatPotential_spatial_time_kernel_difference_abs_le (i := i) (p := (p'.1, p.2))
          (p' := p') (v := v) hR horder htp
        intro s hs
        have hsball := parabolic_ball_time_segment_mem hr.le hp hp' hspace' hs
        rcases heatPotential_far_shell_kernel_separation hr hsball hv with
          hzero | hsep
        · have hsnonneg : 0 ≤ s - v.2 := by linarith only [htp, hs.1]
          have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
          have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
          simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
        · exact hsep
      · have hpv : p.2 ≤ v.2 := by linarith only [lt_of_not_ge htp]
        by_cases htp' : 0 ≤ p'.2 - v.2
        · have htime' : v.2 ≤ p'.2 := by linarith only [htp']
          have hrev := heatPotential_spatial_time_kernel_difference_abs_le
            (i := i) (p := (p'.1, v.2)) (p' := p') (v := v) hR
            (by simpa using htime') (by simp)
            (by
              intro s hs
              have hs' : s ∈ Set.Icc v.2 p'.2 := by simpa using hs
              have hsball := parabolic_ball_time_segment_mem hr.le hp hp' hspace'
                ⟨le_trans hpv hs'.1, hs'.2⟩
              rcases heatPotential_far_shell_kernel_separation hr hsball hv with
                hzero | hsep
              · have hsnonneg : 0 ≤ s - v.2 := by linarith only [hs'.1]
                have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
                have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
                simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
              · exact hsep)
          have hzero : heatPotentialSpatialKernel i (p'.1, p.2) v =
              heatPotentialSpatialKernel i (p'.1, v.2) v := by
            have hnot : ¬ v.2 < p.2 := by linarith only [hpv]
            simp [heatPotentialSpatialKernel, heatKernelSpaceDerivative, hnot]
          rw [hzero]
          have hrev' : |heatPotentialSpatialKernel i (p'.1, v.2) v -
              heatPotentialSpatialKernel i p' v| ≤
              (30000000000 / R ^ 6) * |v.2 - p'.2| := by
            simpa [abs_sub_comm] using hrev
          have hle : |v.2 - p'.2| ≤ |p.2 - p'.2| := by
            rw [abs_of_nonpos (sub_nonpos.mpr htime'),
              abs_of_nonpos (sub_nonpos.mpr (by linarith only [hpv, htime']))]
            linarith only [hpv]
          calc
            |heatPotentialSpatialKernel i (p'.1, v.2) v - heatPotentialSpatialKernel i p' v| ≤
                (30000000000 / R ^ 6) * |v.2 - p'.2| := hrev'
            _ ≤ (30000000000 / R ^ 6) * |p.2 - p'.2| := by
              gcongr
        · have hp'v : p'.2 ≤ v.2 := by linarith only [lt_of_not_ge htp']
          have hnotp : ¬ v.2 < p.2 := by linarith only [hpv]
          have hnotp' : ¬ v.2 < p'.2 := by linarith only [hp'v]
          simp [heatPotentialSpatialKernel, heatKernelSpaceDerivative, hnotp, hnotp']
          positivity
    · have horder' : p'.2 ≤ p.2 := le_of_not_ge horder
      by_cases htp' : 0 ≤ p'.2 - v.2
      · have hrev := heatPotential_spatial_time_kernel_difference_abs_le (i := i) (p := p')
          (p' := (p'.1, p.2)) (v := v) hR horder' htp'
          (by
            intro s hs
            have hsball := parabolic_ball_time_segment_mem hr.le hp' hp hspace' hs
            rcases heatPotential_far_shell_kernel_separation hr hsball hv with
              hzero | hsep
            · have hsnonneg : 0 ≤ s - v.2 := by linarith only [htp', hs.1]
              have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
              have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
              simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
            · exact hsep)
        have hrev' :
            |heatPotentialSpatialKernel i (p'.1, p.2) v -
                heatPotentialSpatialKernel i (p'.1, p'.2) v| ≤
              (30000000000 / R ^ 6) * |p.2 - p'.2| := by
          calc
            |heatPotentialSpatialKernel i (p'.1, p.2) v -
                heatPotentialSpatialKernel i (p'.1, p'.2) v| =
                |heatPotentialSpatialKernel i (p'.1, p'.2) v -
                  heatPotentialSpatialKernel i (p'.1, p.2) v| :=
              abs_sub_comm _ _
            _ ≤ (30000000000 / R ^ 6) * |p'.2 - p.2| := by
              simpa only [Prod.fst, Prod.snd, Prod.eta] using hrev
            _ = (30000000000 / R ^ 6) * |p.2 - p'.2| := by
              rw [abs_sub_comm]
        rw [← Prod.eta p']
        exact hrev'
      · have hp'v : p'.2 ≤ v.2 := by linarith only [lt_of_not_ge htp']
        by_cases htp : 0 ≤ p.2 - v.2
        · have htime' : v.2 ≤ p.2 := by linarith only [htp]
          have hrev := heatPotential_spatial_time_kernel_difference_abs_le
            (i := i) (p := (p'.1, v.2)) (p' := (p'.1, p.2)) (v := v) hR
            (by simpa using htime') (by simp)
            (by
              intro s hs
              have hs' : s ∈ Set.Icc v.2 p.2 := by simpa using hs
              have hsball := parabolic_ball_time_segment_mem hr.le hp' hp hspace'
                ⟨le_trans hp'v hs'.1, hs'.2⟩
              rcases heatPotential_far_shell_kernel_separation hr hsball hv with
                hzero | hsep
              · have hsnonneg : 0 ≤ s - v.2 := by linarith only [hs'.1]
                have hs0 : s - v.2 = 0 := le_antisymm hzero hsnonneg
                have hstrong := heatPotential_far_shell_rho_separation hr hsball hv
                simpa [R, rhoTwo, parabolicRho₂, hs0] using hstrong
              · exact hsep)
          have hzero : heatPotentialSpatialKernel i p' v =
              heatPotentialSpatialKernel i (p'.1, v.2) v := by
            have hnot : ¬ v.2 < p'.2 := by linarith only [hp'v]
            simp [heatPotentialSpatialKernel, heatKernelSpaceDerivative, hnot]
          rw [hzero]
          have hle : |p'.2 - v.2| ≤ |p.2 - p'.2| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hp'v),
              abs_of_nonneg (sub_nonneg.mpr (by linarith only [horder', htime']))]
            linarith only [htime']
          have hrev' :
              |heatPotentialSpatialKernel i (p'.1, p.2) v -
                heatPotentialSpatialKernel i (p'.1, v.2) v| ≤
              (30000000000 / R ^ 6) * |p.2 - v.2| := by
            calc
              |heatPotentialSpatialKernel i (p'.1, p.2) v -
                  heatPotentialSpatialKernel i (p'.1, v.2) v| =
                  |heatPotentialSpatialKernel i (p'.1, v.2) v -
                    heatPotentialSpatialKernel i (p'.1, p.2) v| := abs_sub_comm _ _
              _ ≤ (30000000000 / R ^ 6) * |v.2 - p.2| := by
                simpa only [Prod.fst, Prod.snd, Prod.eta] using hrev
              _ = (30000000000 / R ^ 6) * |p.2 - v.2| := by
                rw [abs_sub_comm]
          calc
            |heatPotentialSpatialKernel i (p'.1, p.2) v - heatPotentialSpatialKernel i (p'.1, v.2) v| ≤
                (30000000000 / R ^ 6) * |p.2 - v.2| := hrev'
            _ ≤ (30000000000 / R ^ 6) * |p.2 - p'.2| := by
              gcongr
        · have hpv : p.2 ≤ v.2 := by linarith only [lt_of_not_ge htp]
          have hnotp' : ¬ v.2 < p'.2 := by linarith only [hp'v]
          have hnotp : ¬ v.2 < p.2 := by linarith only [hpv]
          simp [heatPotentialSpatialKernel, heatKernelSpaceDerivative, hnotp', hnotp]
          positivity
  simpa [R, heatPotentialSpatialKernel, heatKernelSpaceDerivative, pointSub] using
    heatPotential_far_shell_two_step_oscillation
      (K := fun q : ParabolicPoint => heatKernelSpaceDerivative q.1 q.2 i)
    hp hp' hA hB hspace htime

theorem heatPotential_far_shell_integral_oscillation_bound
    {F : ParabolicPoint → ℝ} {z p p' : ParabolicPoint} {r : ℝ}
    {j : ℕ} {C : ℝ} {M : ℝ≥0∞} (hr : 0 < r)
    (hF : AEMeasurable F volume)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hfinite : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |F v|) < ∞)
    (hMtop : M ≠ ∞)
    (hM : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |F v|) ≤ M)
    (hpoint : ∀ v ∈ heatPotentialFarShellSet z r j,
      |heatPotentialKernel p v - heatPotentialKernel p' v| ≤ C)
    (hC : 0 ≤ C) :
    |(∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel p v * F v) -
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel p' v * F v| ≤ C * M.toReal := by
  let S : Set ParabolicPoint := heatPotentialFarShellSet z r j
  have hS : MeasurableSet S := measurableSet_heatPotentialFarShellSet z r j
  have hsource := integrableOn_abs_of_lintegral_lt_top hF hfinite
  have hK : ∀ q : ParabolicPoint,
      AEMeasurable (fun v : ParabolicPoint => heatPotentialKernel q v) volume := by
    intro q
    exact (measurable_heatPotentialKernel_translate q).aemeasurable
  let C₀ : ℝ := 1000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hKp : ∀ v ∈ S, |heatPotentialKernel p v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_kernel_abs_le hr hp hv
  have hKp' : ∀ v ∈ S, |heatPotentialKernel p' v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_kernel_abs_le hr hp' hv
  have hwi := integrableOn_mul_of_abs_integrable_of_bound hS hF (hK p)
    hfinite hC₀ hKp
  have hwi' := integrableOn_mul_of_abs_integrable_of_bound hS hF (hK p')
    hfinite hC₀ hKp'
  have hmajor : IntegrableOn (fun v => C * |F v|) S volume :=
    hsource.const_mul C
  have hsingle := heatPotential_single_kernel_shell_bound hC hS hwi hwi'
    hmajor hpoint
  have hsource' := real_integral_abs_le_of_lintegral_le hF hfinite hMtop hM
  exact hsingle.trans (mul_le_mul_of_nonneg_left hsource' hC)

theorem heatPotential_far_shell_spatial_integral_oscillation_bound
    {i : Fin 3} {G : ParabolicPoint → ℝ} {z p p' : ParabolicPoint} {r : ℝ}
    {j : ℕ} {C : ℝ} {M : ℝ≥0∞} (hr : 0 < r)
    (hG : AEMeasurable G volume)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hfinite : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |G v|) < ∞)
    (hMtop : M ≠ ∞)
    (hM : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |G v|) ≤ M)
    (hpoint : ∀ v ∈ heatPotentialFarShellSet z r j,
      |heatPotentialSpatialKernel i p v - heatPotentialSpatialKernel i p' v| ≤ C)
    (hC : 0 ≤ C) :
    |(∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i p v * G v) -
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i p' v * G v| ≤ C * M.toReal := by
  let S : Set ParabolicPoint := heatPotentialFarShellSet z r j
  have hS : MeasurableSet S := measurableSet_heatPotentialFarShellSet z r j
  have hsource := integrableOn_abs_of_lintegral_lt_top hG hfinite
  have hK : ∀ q : ParabolicPoint,
      AEMeasurable (fun v : ParabolicPoint => heatPotentialSpatialKernel i q v) volume := by
    intro q
    exact (measurable_heatPotentialSpatialKernel_translate i q).aemeasurable
  let C₀ : ℝ := 300000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hKp : ∀ v ∈ S, |heatPotentialSpatialKernel i p v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_spatial_kernel_abs_le hr hp hv
  have hKp' : ∀ v ∈ S, |heatPotentialSpatialKernel i p' v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_spatial_kernel_abs_le hr hp' hv
  have hwi := integrableOn_mul_of_abs_integrable_of_bound hS hG (hK p)
    hfinite hC₀ hKp
  have hwi' := integrableOn_mul_of_abs_integrable_of_bound hS hG (hK p')
    hfinite hC₀ hKp'
  have hmajor : IntegrableOn (fun v => C * |G v|) S volume :=
    hsource.const_mul C
  have hsingle := heatPotential_single_kernel_shell_bound hC hS hwi hwi'
    hmajor hpoint
  have hsource' := real_integral_abs_le_of_lintegral_le hG hfinite hMtop hM
  exact hsingle.trans (mul_le_mul_of_nonneg_left hsource' hC)
theorem heatPotential_far_shell_integral_oscillation_bound_of_morrey
    {F : ParabolicPoint → ℝ} {z p p' : ParabolicPoint} {r P θ : ℝ}
    {j : ℕ} (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hF : AEMeasurable F volume) (hN : morreyNorm P θ F < ∞)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    |(∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel p v * F v) -
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel p' v * F v| ≤
      (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
        ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ F).toReal := by
  let M : ℝ≥0∞ :=
    (ENNReal.ofReal
      (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
        (5 * (1 - 1 / θ)) *
      (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
      morreyNorm P θ F
  have hMtop : M ≠ ∞ := by
    dsimp [M]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · have hθ : 1 ≤ θ := hP.trans hPθ
          have hθinv : 1 / θ ≤ (1 : ℝ) := by
            simpa using one_div_le_one_div_of_le zero_lt_one hθ
          positivity
        · exact ENNReal.ofReal_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · apply sub_nonneg.mpr
          simpa using one_div_le_one_div_of_le zero_lt_one hP
        · exact Integration.volume_parabolicCylinder_lt_top.ne
    · exact hN.ne
  have hM := heatPotential_far_shell_source_l1_bound
    (z := z) hr hP hPθ hF j
  have hfinite : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |F v|) < ∞ := by
    exact hM.trans_lt (lt_top_iff_ne_top.mpr hMtop)
  have hC : 0 ≤ 2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
      2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5)) := by positivity
  have hpoint : ∀ v ∈ heatPotentialFarShellSet z r j,
      |heatPotentialKernel p v - heatPotentialKernel p' v| ≤
        2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
          2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5)) := by
    intro v hv
    exact heatPotential_far_shell_kernel_difference_abs_le_of_positive
      hr hp hp' hv
  have hbound := heatPotential_far_shell_integral_oscillation_bound
    (z := z) (p := p) (p' := p') (r := r) (j := j) hr hF hp hp'
    hfinite hMtop hM hpoint hC
  simpa [M] using hbound

theorem heatPotential_far_shell_spatial_integral_oscillation_bound_of_morrey
    {i : Fin 3} {G : ParabolicPoint → ℝ} {z p p' : ParabolicPoint} {r P θ : ℝ}
    {j : ℕ} (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hG : AEMeasurable G volume) (hN : morreyNorm P θ G < ∞)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    |(∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i p v * G v) -
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i p' v * G v| ≤
      (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ G).toReal := by
  let M : ℝ≥0∞ :=
    (ENNReal.ofReal
      (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
        (5 * (1 - 1 / θ)) *
      (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
      morreyNorm P θ G
  have hMtop : M ≠ ∞ := by
    dsimp [M]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · have hθ : 1 ≤ θ := hP.trans hPθ
          have hθinv : 1 / θ ≤ (1 : ℝ) := by
            simpa using one_div_le_one_div_of_le zero_lt_one hθ
          positivity
        · exact ENNReal.ofReal_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · apply sub_nonneg.mpr
          simpa using one_div_le_one_div_of_le zero_lt_one hP
        · exact Integration.volume_parabolicCylinder_lt_top.ne
    · exact hN.ne
  have hM := heatPotential_far_shell_source_l1_bound
    (z := z) hr hP hPθ hG j
  have hfinite : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |G v|) < ∞ := by
    exact hM.trans_lt (lt_top_iff_ne_top.mpr hMtop)
  have hC : 0 ≤ 2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
      2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6)) := by positivity
  have hpoint : ∀ v ∈ heatPotentialFarShellSet z r j,
      |heatPotentialSpatialKernel i p v - heatPotentialSpatialKernel i p' v| ≤
        2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
          2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6)) := by
    intro v hv
    exact heatPotential_far_shell_spatial_kernel_spatial_difference_abs_le_of_positive
      hr hp hp' hv
  have hbound := heatPotential_far_shell_spatial_integral_oscillation_bound
    (z := z) (p := p) (p' := p') (r := r) (j := j) hr hG hp hp'
    hfinite hMtop hM hpoint hC
  simpa [M] using hbound

theorem heatPotential_integral_near_far_split
    {f : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hcover : (Set.univ : Set ParabolicPoint) = heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j)
    (hdST : ∀ j : ℕ, Disjoint (heatPotentialNearSet z r)
      (heatPotentialFarShellSet z r j))
    (hdT : Pairwise (Function.onFun Disjoint (heatPotentialFarShellSet z r)))
    (hInt : IntegrableOn f (heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j) volume) :
    ∫ v, f v = (∫ v in heatPotentialNearSet z r, f v) +
      ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j, f v := by
  have huniv : (∫ v, f v) = ∫ v in (Set.univ : Set ParabolicPoint), f v := by
    rw [Measure.restrict_univ]
  rw [huniv, hcover]
  have hT : ∀ j : ℕ, MeasurableSet (heatPotentialFarShellSet z r j) :=
    fun j => measurableSet_heatPotentialFarShellSet z r j
  have hU : MeasurableSet (⋃ j : ℕ, heatPotentialFarShellSet z r j) :=
    MeasurableSet.iUnion hT
  have hIntS : IntegrableOn f (heatPotentialNearSet z r) volume :=
    hInt.mono_set (subset_union_left)
  have hIntU : IntegrableOn f (⋃ j : ℕ, heatPotentialFarShellSet z r j) volume :=
    hInt.mono_set (subset_union_right)
  have hsplit : volume.restrict (heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j) = volume.restrict (heatPotentialNearSet z r) +
      volume.restrict (⋃ j : ℕ, heatPotentialFarShellSet z r j) :=
    Measure.restrict_union (disjoint_iUnion_right.mpr hdST) hU
  calc
    ∫ v in heatPotentialNearSet z r ∪ ⋃ j : ℕ, heatPotentialFarShellSet z r j, f v =
        ∫ v, f v ∂(volume.restrict (heatPotentialNearSet z r ∪
          ⋃ j : ℕ, heatPotentialFarShellSet z r j)) := rfl
    _ = ∫ v, f v ∂(volume.restrict (heatPotentialNearSet z r) +
        volume.restrict (⋃ j : ℕ, heatPotentialFarShellSet z r j)) := by
      rw [hsplit]
    _ = (∫ v in heatPotentialNearSet z r, f v) +
        ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j, f v :=
      MeasureTheory.integral_add_measure hIntS hIntU
    _ = (∫ v in heatPotentialNearSet z r, f v) +
        ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j, f v :=
      congrArg (fun x : ℝ => (∫ v in heatPotentialNearSet z r, f v) + x)
        (MeasureTheory.integral_iUnion hT hdT hIntU)

end CKN.Core.HeatPotential

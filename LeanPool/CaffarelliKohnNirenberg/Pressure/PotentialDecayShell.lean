/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayUnitBall

/-!
# The radial weight `‖x‖ ^ (-3/2)` on balls

The linear-growth hypothesis of the Liouville step needs the exact scaling of
the integral of `‖x‖ ^ (-3/2)` over a ball of radius `ρ` in three dimensions:
it grows like `ρ ^ (3/2)`, so its `2/3` power grows linearly in `ρ`.  The crude
bound by the supremum of the weight times the volume of the ball would only give
`ρ ^ 3`, which is too weak.  The scaling identity below replaces the dyadic shell
sum by a single change of variables.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private lemma measurable_ofReal_inv_norm_rpow :
    Measurable (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ))) := by
  fun_prop

private lemma finrank_vec3 : Module.finrank ℝ Vec3 = 3 := by
  change Module.finrank ℝ (Fin 3 → ℝ) = 3
  rw [Module.finrank_fin_fun]

private lemma smul_mem_ball_iff {ρ : ℝ} (hρ : 0 < ρ) (z : Vec3) :
    ρ • z ∈ Metric.ball (0 : Vec3) ρ ↔ z ∈ Metric.ball (0 : Vec3) 1 := by
  rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  constructor
  · intro h
    nlinarith only [h, hρ, norm_nonneg z]
  · intro h
    nlinarith only [h, hρ, norm_nonneg z]

/-- Scaling identity for the radial weight `‖x‖ ^ (-3/2)` on balls of the
ambient three-dimensional space. -/
theorem lintegral_ball_inv_norm_rpow_eq {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x in Metric.ball (0 : Vec3) ρ, ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) =
      ENNReal.ofReal (ρ ^ (3 / 2 : ℝ)) *
        ∫⁻ x in Metric.ball (0 : Vec3) 1,
          ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) := by
  have hFmeas : Measurable ((Metric.ball (0 : Vec3) ρ).indicator
      (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)))) :=
    measurable_ofReal_inv_norm_rpow.indicator measurableSet_ball
  have hGmeas : Measurable ((Metric.ball (0 : Vec3) 1).indicator
      (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)))) :=
    measurable_ofReal_inv_norm_rpow.indicator measurableSet_ball
  have hkey : ∀ z : Vec3,
      (Metric.ball (0 : Vec3) ρ).indicator
        (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ))) (ρ • z) =
      ENNReal.ofReal (ρ ^ (-(3 / 2) : ℝ)) *
        (Metric.ball (0 : Vec3) 1).indicator
          (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ))) z := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : Vec3) 1
    · have hmem : ρ • z ∈ Metric.ball (0 : Vec3) ρ :=
        (smul_mem_ball_iff hρ z).2 hz
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hz]
      have hnorm : ‖ρ • z‖ = ρ * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      rw [hnorm, Real.mul_rpow hρ.le (norm_nonneg z),
        ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
    · have hmem : ρ • z ∉ Metric.ball (0 : Vec3) ρ := fun h =>
        hz ((smul_mem_ball_iff hρ z).1 h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hz, mul_zero]
  have hmap := Measure.map_addHaar_smul (volume : Measure Vec3) hρ.ne'
  rw [finrank_vec3] at hmap
  have h1 : ∫⁻ x, (Metric.ball (0 : Vec3) ρ).indicator
        (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ))) x
        ∂(Measure.map (fun x : Vec3 => ρ • x) volume) =
      ∫⁻ z : Vec3, (Metric.ball (0 : Vec3) ρ).indicator
        (fun x : Vec3 => ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ))) (ρ • z) :=
    lintegral_map hFmeas (measurable_const_smul ρ)
  rw [hmap, lintegral_smul_measure, lintegral_congr hkey,
    lintegral_const_mul _ hGmeas] at h1
  rw [lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball] at h1
  have habs : |((ρ : ℝ) ^ (3 : ℕ))⁻¹| = ((ρ : ℝ) ^ (3 : ℕ))⁻¹ :=
    abs_of_nonneg (by positivity)
  rw [habs] at h1
  have hscale := congrArg
    (fun t : ℝ≥0∞ => ENNReal.ofReal ((ρ : ℝ) ^ (3 : ℕ)) * t) h1
  simp only [smul_eq_mul] at hscale
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (by positivity : ((ρ : ℝ) ^ (3 : ℕ)) ≠ 0),
    ENNReal.ofReal_one, one_mul] at hscale
  rw [hscale]
  congr 2
  rw [← Real.rpow_natCast ρ 3, ← Real.rpow_add hρ]
  norm_num

/-- The universal constant in the ball estimate for the radial weight: the
integral of `‖x‖ ^ (-3/2)` over the unit ball of three-dimensional space. -/
def invNormBallConstant : ℝ :=
  (∫⁻ x in Metric.ball (0 : Vec3) 1,
    ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ))).toReal

theorem invNormBallConstant_nonneg : 0 ≤ invNormBallConstant :=
  ENNReal.toReal_nonneg

/-- The scale-invariant ball estimate: the integral of the radial weight
`‖x‖ ^ (-3/2)` over the ball of radius `ρ` is `invNormBallConstant * ρ ^ (3/2)`. -/
theorem lintegral_ball_inv_norm_rpow_eq_const {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x in Metric.ball (0 : Vec3) ρ, ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) =
      ENNReal.ofReal (invNormBallConstant * ρ ^ (3 / 2 : ℝ)) := by
  rw [lintegral_ball_inv_norm_rpow_eq hρ, invNormBallConstant,
    ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
    ENNReal.ofReal_toReal lintegral_ball_one_inv_norm_rpow_lt_top.ne]
  ring

end CKN

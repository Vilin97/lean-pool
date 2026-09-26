/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville

/-!
# Potential Decay Unit Ball

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN

/-! Integrability of the inverse-power weight `‖x‖^{-3/2}` on three-dimensional
space, in the local and unit-ball forms used to dominate the singular pressure
kernel `P` of the Caffarelli–Kohn–Nirenberg paper. -/

/-- The inverse power `‖x‖^{-3/2}` is locally integrable on three-dimensional space. -/
theorem locallyIntegrable_inv_norm_rpow_three_halves :
    LocallyIntegrable (fun x : Vec3 => ‖x‖ ^ (-(3 / 2) : ℝ)) volume := by
  refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ) (C := 1)
    (α := (3 / 2 : ℝ)) ?_ ?_ ?_ ?_
  · change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ)
    rw [Module.finrank_fin_fun]
    norm_num
  · change (3 / 2 : ℝ) < (Module.finrank ℝ (Fin 3 → ℝ) : ℝ)
    rw [Module.finrank_fin_fun]
    norm_num
  · filter_upwards with x
    have hx : 0 ≤ ‖x‖ ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (norm_nonneg x) _
    rw [Real.norm_eq_abs, abs_of_nonneg hx, one_mul]
  · exact (show Measurable (fun x : Vec3 => ‖x‖ ^ (-(3 / 2) : ℝ)) by fun_prop).aestronglyMeasurable

/-- Its integral over the unit ball is finite. -/
theorem lintegral_ball_one_inv_norm_rpow_lt_top :
    ∫⁻ x in Metric.ball (0 : Vec3) 1,
        ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) < ⊤ := by
  have hInt : IntegrableOn (fun x : Vec3 => ‖x‖ ^ (-(3 / 2) : ℝ))
      (Metric.closedBall (0 : Vec3) 1) volume :=
    locallyIntegrable_inv_norm_rpow_three_halves.integrableOn_isCompact
      (isCompact_closedBall (0 : Vec3) 1)
  have hIntBall : IntegrableOn (fun x : Vec3 => ‖x‖ ^ (-(3 / 2) : ℝ))
      (Metric.ball (0 : Vec3) 1) volume :=
    hInt.mono_set Metric.ball_subset_closedBall
  have hcongr : ∫⁻ x in Metric.ball (0 : Vec3) 1,
        ‖(fun x : Vec3 => ‖x‖ ^ (-(3 / 2) : ℝ)) x‖ₑ
      = ∫⁻ x in Metric.ball (0 : Vec3) 1,
          ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_ball
    intro x _
    exact Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg x) _)
  rw [← hcongr]
  exact hIntBall.hasFiniteIntegral

end CKN

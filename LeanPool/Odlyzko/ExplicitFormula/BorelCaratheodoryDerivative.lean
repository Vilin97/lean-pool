/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.Liouville

/-!
# Borel Caratheodory Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace NumberField.Odlyzko

theorem norm_deriv_le_of_re_le_on_ball
    {F : ℂ → ℂ} {R r A : ℝ}
    (hR : 0 < R) (_hr : 0 ≤ r) (hrR : r < R) (hA : 0 < A)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    (hFre : ∀ z ∈ Metric.ball 0 R, (F z).re ≤ A)
    (hF0 : F 0 = 0)
    {w : ℂ} (hw : w ∈ Metric.closedBall 0 r) :
    ‖deriv F w‖ ≤ 4 * A * (R + r) / (R - r) ^ 2 := by
  let d := (R - r) / 2
  let q := (R + r) / 2
  have hd : 0 < d := by grind
  have hqR : q < R := by grind
  have hwNorm : ‖w‖ ≤ r := by simp_all
  have hsphere :
      ∀ z ∈ Metric.sphere w d,
        ‖F z‖ ≤ 2 * A * (R + r) / (R - r) := by
    intro z hz
    have hzw : ‖z - w‖ = d := by simp_all
    have hzNorm : ‖z‖ ≤ q := by
      calc
        ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          simpa [add_comm] using norm_le_norm_add_norm_sub' z w
        _ ≤ r + d := add_le_add hwNorm hzw.le
        _ = q := by grind
    have hzball : z ∈ Metric.ball 0 R := by
      simpa [Metric.mem_ball, dist_zero_right] using hzNorm.trans_lt hqR
    have hborel :=
      Complex.borelCaratheodory_zero hA hF
        (fun x hx ↦ hFre x hx) hR hzball hF0
    calc
      ‖F z‖ ≤ 2 * A * ‖z‖ / (R - ‖z‖) := hborel
      _ ≤ 2 * A * q / (R - q) := by
        have hzR : ‖z‖ < R := hzNorm.trans_lt hqR
        have hmono : ‖z‖ / (R - ‖z‖) ≤ q / (R - q) := by
          rw [div_le_div_iff₀ (sub_pos.mpr hzR) (sub_pos.mpr hqR)]
          nlinarith
        calc
          2 * A * ‖z‖ / (R - ‖z‖) =
              (2 * A) * (‖z‖ / (R - ‖z‖)) := by ring
          _ ≤ (2 * A) * (q / (R - q)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
          _ = 2 * A * q / (R - q) := by ring
      _ = 2 * A * (R + r) / (R - r) := by grind
  have hclosed :
      Metric.closedBall w d ⊆ Metric.ball 0 R := by
    intro z hz
    have hzw : ‖z - w‖ ≤ d := by
      simpa [Metric.mem_closedBall, dist_eq] using hz
    have hzNorm : ‖z‖ ≤ q := by
      calc
        ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          simpa [add_comm] using norm_le_norm_add_norm_sub' z w
        _ ≤ r + d := add_le_add hwNorm hzw
        _ = q := by grind
    simpa [Metric.mem_ball, dist_zero_right] using hzNorm.trans_lt hqR
  have hcauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (c := w) (R := d) (C := 2 * A * (R + r) / (R - r))
      hd (by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball w hd.ne']
        exact hF.mono hclosed) hsphere
  calc
    ‖deriv F w‖ ≤ (2 * A * (R + r) / (R - r)) / d := hcauchy
    _ = 4 * A * (R + r) / (R - r) ^ 2 := by grind

end NumberField.Odlyzko

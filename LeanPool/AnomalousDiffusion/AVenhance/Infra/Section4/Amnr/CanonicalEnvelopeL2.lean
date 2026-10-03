/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CanonicalJetSamples

/-! The finite canonical jet envelope preserves L2 control. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Normalizing an actual measurable scalar jet cancels its positive weight. -/
theorem amnr_normalized_abs_L2_le {μ : Measure AmnrSpace} {f : AmnrSpace → ℝ}
    (hf : AEStronglyMeasurable f μ) {W G : ℝ} (hW : 0 < W)
    (hbound : eLpNorm f 2 μ ≤ ENNReal.ofReal (G * W)) :
    eLpNorm (fun z => |f z| / W) 2 μ ≤ ENNReal.ofReal G := by
  have he : (fun z => |f z| / W) = W⁻¹ • (fun z => ‖f z‖) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  rw [he, eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.mpr hW.le),
    eLpNorm_norm f hf]
  refine (mul_le_mul_right hbound _).trans_eq ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hW.le)]
  congr 1
  field_simp

end AVenhance.Infra.Section4

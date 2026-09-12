/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.VolterraFixedPoint

/-! The actual pressure-projected quadratic source passes to uniform Sobolev path limits. -/

@[expose] public section


noncomputable section

namespace EulerQuadraticSourceLimit

open Set EulerQuadraticSource EulerVolterraConvolution
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The literal quadratic source evaluated along an actual continuous state path. -/
def sourcePath {T : ℝ} (C : Coefficients (Icc (0 : ℝ) T) X Y) (u : C(Icc (0 : ℝ) T, X)) :
    C(Icc (0 : ℝ) T,Y) := pathNonlinearity T C.apply C.continuous u

/-- The actual nonlinear source map obeys the proved ball Lipschitz bound in uniform path norm. -/
theorem sourcePath_sub_bound {T : ℝ} (C : Coefficients (Icc (0 : ℝ) T) X Y)
    (R : ℝ) (hR : 0 ≤ R) (u v : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖sourcePath C u-sourcePath C v‖ ≤ C.ballLipschitz R*‖u-v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (C.ballLipschitz_nonneg R hR) (norm_nonneg (u-v)))).mpr
  intro t
  have h := C.apply_sub_bound R hR t (u t) (v t)
    ((u.norm_coe_le_norm t).trans hu) ((v.norm_coe_le_norm t).trans hv)
  exact h.trans (mul_le_mul_of_nonneg_left ((u-v).norm_coe_le_norm t) (C.ballLipschitz_nonneg R hR))

/-- Uniform convergence of actual bounded state paths gives uniform convergence of the literal
quadratic source paths. -/
theorem sourcePath_tendsto {T : ℝ} (C : Coefficients (Icc (0 : ℝ) T) X Y)
    (R : ℝ) (hR : 0 ≤ R) (u : ℕ → C(Icc (0 : ℝ) T, X)) (v : C(Icc (0 : ℝ) T, X))
    (hu : ∀ n, ‖u n‖ ≤ R) (hv : ‖v‖ ≤ R) (h : Filter.Tendsto u Filter.atTop (𝓝 v)) :
    Filter.Tendsto (fun n => sourcePath C (u n)) Filter.atTop (𝓝 (sourcePath C v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => sourcePath_sub_bound C R hR (u n) v (hu n)
      hv)
  simpa only [mul_zero] using h.const_mul (C.ballLipschitz R)

end EulerQuadraticSourceLimit

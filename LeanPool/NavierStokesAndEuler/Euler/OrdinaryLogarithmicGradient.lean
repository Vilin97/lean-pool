/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceLogarithmic
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryVorticityCoordinates

@[expose] public section

/-!
The whole-space logarithmic gradient estimate.  Every input norm belongs
to the given smooth L² field, and the vorticity is its literal curl.
The proof uses the constructed Gaussian kernel and its true heat equation.
-/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set Finset
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerVectorCalculus EulerMeanCutoffCurl EulerMeanClassical EulerWholeSpaceGaussian
open scoped ContDiff ENNReal RealInnerProductSpace Topology

def logarithmicGradientConstant : ℝ := 36*splitCost

theorem logarithmicGradientConstant_pos : 0 < logarithmicGradientConstant :=
  mul_pos (by norm_num) splitCost_pos

theorem logarithmicGradientConstant_nonneg : 0 ≤ logarithmicGradientConstant :=
  logarithmicGradientConstant_pos.le

/-- A genuine whole-space BKM logarithmic estimate from the actual
velocity, its actual H³ tensors, and its actual vorticity. -/
theorem logarithmic_gradient_bound (A : SmoothL2Field Space)
    (hdiv : ∀ y, divergence A.field y = 0) (W : ℝ)
    (hW : ∀ y, ‖vectorCurl A.field y‖ ≤ W) (x : Space) :
    ‖fderiv ℝ A.field x‖ ≤ logarithmicGradientConstant*
      (1+‖A.toLp‖+W*Real.log (Real.exp 1+tensorNorm 3 A)) := by
  have hW0 : 0 ≤ W := (norm_nonneg (vectorCurl A.field 0)).trans (hW 0)
  have hH0 := tensorNorm_nonneg 3 A
  have harg : 1 ≤ Real.exp 1+tensorNorm 3 A :=
    (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans (le_add_of_nonneg_right hH0)
  have hlog : 0 ≤ Real.log (Real.exp 1+tensorNorm 3 A) := Real.log_nonneg harg
  let K : ℝ := 4*splitCost*(1+‖A.toLp‖+W*Real.log (Real.exp 1+tensorNorm 3 A))
  have hK : 0 ≤ K := by dsimp [K]; positivity [splitCost_nonneg]
  have hcomponent (i : Fin 3) (y : Space) :
      ‖(componentField (vorticityField A) i).field y‖ ≤ W := by
    rw [componentField_apply]
    exact (PiLp.norm_apply_le ((vorticityField A).field y) i).trans
      (by simpa only [vorticityField_apply] using hW y)
  have hjet : ‖A.jetLp 3‖ ≤ tensorNorm 3 A :=
    single_le_sum (fun _ _ => norm_nonneg _) (by decide : 3 ∈ range (3+1))
  have hentries (i j : Fin 3) : ‖(fderiv ℝ A.field x (axis i)) j‖ ≤ K := by
    have h := elliptic_derivative_logarithmic (componentField A j)
      (componentField (vorticityField A) (j+1)) (componentField (vorticityField A) (j+2))
      (j+2) (j+1) i (componentField_laplacian A hdiv j) W
      (hcomponent (j+1)) (hcomponent (j+2)) (tensorNorm 3 A)
      ((componentField_jetLp_norm A j 3).trans hjet) x
    rw [componentField_partial] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) splitCost_nonneg)
    linarith [componentField_toLp_norm A j]
  have h := operator_norm_le_of_entries (fderiv ℝ A.field x) K hK hentries
  exact h.trans_eq (by unfold logarithmicGradientConstant; dsimp [K]; ring)

/-- This form discharges the entire logarithmic-estimate hypothesis of
the ordinary Euler continuation theorem. -/
theorem logarithmic_gradient_bound_solenoidal (A : SmoothL2Field Space) (W : ℝ)
    (hA : A.toLp ∈ solenoidalSpace) (hW : ∀ y, ‖vectorCurl A.field y‖ ≤ W) (x : Space) :
    ‖fderiv ℝ A.field x‖ ≤ logarithmicGradientConstant*
      (1+‖A.toLp‖+W*Real.log (Real.exp 1+tensorNorm 3 A)) :=
  logarithmic_gradient_bound A
    (solenoidal_representative_divergence A.toLp hA A.field A.smooth A.toLp_ae) W hW x

end EulerOrdinarySobolev

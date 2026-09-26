/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.ParameterSymmetry
public import LeanPool.CarlsonFunctions.Carlson.R.EulerTransform

/-! # Two-variable R-inversion on the full slit domain -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

private theorem regCarlsonRSlit_pair_inversion_of_right (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonRSlit t (pair u v) (pair x y) =
      x ^ (t + v) * y ^ (t + u) *
        regCarlsonRSlit (-u - v - t) (pair v u) (pair x y) := by
  have hz : pair x y ∈ carlsonRVariableDomain := by
    intro i; fin_cases i <;> assumption
  have hx₀ := ne_zero_of_re_pos hx
  have hy₀ := ne_zero_of_re_pos hy
  have hxi : 0 < (x⁻¹).re := carlsonRVariableDomain_inv hz 0
  have hyi : 0 < (y⁻¹).re := carlsonRVariableDomain_inv hz 1
  have hi : (fun i => (pair x y i)⁻¹) = pair x⁻¹ y⁻¹ := by
    ext i; fin_cases i <;> rfl
  have h := regCarlsonRSlit_euler t (pair u v) (carlsonRVariableDomain_subset_slitDomain hz)
  simp only [sum_pair, Fin.prod_univ_two, pair_zero, pair_one, hi,
    show -(u + v) - t = -u - v - t by ring] at h
  rw [h, regCarlsonRSlit_normalize_first _ _ hxi hyi,
    ← regCarlsonRSlit_pair_swap (-u - v - t) v u
      (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy),
    regCarlsonRSlit_normalize_first _ _ hy hx, inv_div_inv]
  have hc : x ^ (-u) * y ^ (-v) * (x⁻¹) ^ (-u - v - t) =
      x ^ (t + v) * y ^ (t + u) * y ^ (-u - v - t) := by
    simp only [cpow_def_of_ne_zero hx₀, cpow_def_of_ne_zero hy₀,
      cpow_def_of_ne_zero (inv_ne_zero hx₀),
      log_inv x (slitPlane_arg_ne_pi (carlsonRightHalfPlane_subset_slitPlane hx)), ← exp_add]
    congr 1
    ring
  linear_combination hc * regCarlsonRSlit (-u - v - t) (pair u v) (pair 1 (x / y))

/-- Two-variable R-inversion with separate principal powers, valid on the full slit domain. -/
theorem regCarlsonRSlit_pair_inversion (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    regCarlsonRSlit t (pair u v) (pair x y) =
      x ^ (t + v) * y ^ (t + u) *
        regCarlsonRSlit (-u - v - t) (pair v u) (pair x y) := by
  have hright : AnalyticOnNhd ℂ (fun z : Fin 2 → ℂ =>
      z 0 ^ (t + v) * z 1 ^ (t + u) * regCarlsonRSlit (-u - v - t) (pair v u) z)
      carlsonRSlitDomain := by
    intro z hz
    have hcoord (i : Fin 2) : AnalyticAt ℂ (fun w : Fin 2 → ℂ => w i) z :=
      (analyticAt_pi_iff.mp analyticAt_id) i
    exact (((hcoord 0).cpow analyticAt_const (hz 0)).mul
      ((hcoord 1).cpow analyticAt_const (hz 1))).mul
        (analyticOnNhd_regCarlsonRSlit (-u - v - t) (pair v u) z hz)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonRSlit t (pair u v)) hright ?_ hz
  intro z hz
  have heq : pair (z 0) (z 1) = z := by ext i; fin_cases i <;> rfl
  simpa only [heq] using regCarlsonRSlit_pair_inversion_of_right t u v (hz 0) (hz 1)

end DirichletTransform.TwoVariable

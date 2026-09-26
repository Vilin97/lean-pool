/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Basic
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv
public import LeanPool.CarlsonFunctions.Carlson.L.Properties
public import LeanPool.CarlsonFunctions.Carlson.L.SlitRelations
public import LeanPool.CarlsonFunctions.Dirichlet.Average.NewtonTaylor
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Bridge

/-!
# Two-variable L-functions and elementary logarithmic values

The two-variable interface parallels `TwoVariable.R`. The exceptional elementary
case `L_{-1}(1,1;x,y)` is Carlson (1987), (8.8). Its undivided identity includes
coincident nodes; the diagonal value is supplied separately.
-/

open Complex ProbabilityTheory
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The two-variable native regularized L-integral. -/
abbrev regLIntegral (t b₀ b₁ x y : ℂ) : ℂ :=
  regCarlsonLIntegral t (pair b₀ b₁) (pair x y)

/-- The two-variable native normalized L-integral. -/
abbrev lIntegral (t b₀ b₁ x y : ℂ) : ℂ :=
  carlsonLIntegral t (pair b₀ b₁) (pair x y)

/-- The two-variable entire regularized L-continuation. -/
abbrev regLContinued (t b₀ b₁ x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) : ℂ :=
  regCarlsonLContinued t (pair x y) hz (pair b₀ b₁)

/-- Symmetry exchanges the two parameters together with their nodes. -/
theorem regLIntegral_swap (t b₀ b₁ x y : ℂ) :
    regLIntegral t b₀ b₁ x y = regLIntegral t b₁ b₀ y x := by
  have h := regCarlsonLIntegral_perm t (pair b₀ b₁) (pair x y) swap
  simpa only [pair_comp_swap] using h.symm

private theorem regAverage_one_one (z : Fin 2 → ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage (pair 1 1) z f = carlsonUnweightedAverage z f := by
  have heq : pair (1 : ℂ) 1 = fun _ => ((1 : ℝ) : ℂ) := by
    ext i; fin_cases i <;> rfl
  rw [heq, regCarlsonDirichletAverage_ofReal one_mem_mvRealBetaDomain]
  simp [carlsonUnweightedAverage]

/-- The fundamental theorem for the uniform two-node Dirichlet average. -/
theorem sub_mul_regAverage_deriv {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f carlsonRightHalfPlane) (x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    (x - y) * regCarlsonDirichletAverage (pair 1 1) (pair x y) (deriv f) = f x - f y := by
  have h := carlsonDividedDifference_sub
    convex_carlsonRightHalfPlane hf (Fin.elim0 : Fin 0 → ℂ)
    (by rintro _ ⟨i, _⟩; exact Fin.elim0 i) (hz 0) (hz 1)
  have hp : Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → ℂ) x) y = pair x y := by
    ext i; fin_cases i <;> rfl
  simp only [carlsonDividedDifference_zero] at h
  change f x - f y = (x - y) *
    carlsonDividedDifference 1 f (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → ℂ) x) y) at h
  have hd : carlsonDividedDifference 1 f (pair x y) =
      regCarlsonDirichletAverage (pair 1 1) (pair x y) (deriv f) := by
    rw [regAverage_one_one]
    simp [carlsonDividedDifference, iteratedDeriv_succ]
  rw [hp, hd] at h
  exact h.symm

private theorem one_one_mem_mvBetaConvergent : pair (1 : ℂ) 1 ∈ mvBetaConvergent := by
  intro i; fin_cases i <;> norm_num [pair]

/-- Equation (8.8), without division by the node difference. -/
theorem sub_mul_regLContinued_neg_one_one_one (x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    (x - y) * regLContinued (-1) 1 1 x y hz = (log x ^ 2 - log y ^ 2) / 2 := by
  let f : ℂ → ℂ := fun w => log w ^ 2 / 2
  have hf : AnalyticOnNhd ℂ f carlsonRightHalfPlane := by
    intro w hw
    exact ((analyticAt_clog (carlsonRightHalfPlane_subset_slitPlane hw)).pow 2).div_const
  have hd (w : ℂ) (hw : w ∈ slitPlane) : deriv f w = carlsonLKernel (-1) w := by
    have h := ((Complex.hasDerivAt_log hw).pow 2).div_const 2
    calc
      deriv f w = (2 : ℂ) * log w ^ (2 - 1) * w⁻¹ / 2 := h.deriv
      _ = _ := by simp only [carlsonLKernel, cpow_neg_one]; ring
  have heq : regCarlsonDirichletAverage (pair 1 1) (pair x y) (deriv f) =
      regLContinued (-1) 1 1 x y hz := by
    rw [regLContinued, regCarlsonLContinued_eq_integral _ hz one_one_mem_mvBetaConvergent]
    exact regDirichletIntegral_congr _ (fun u hu => hd _ (carlsonAffineForm_mem_slitPlane hz hu))
  have h := sub_mul_regAverage_deriv hf x y hz
  rw [heq] at h
  dsimp only [f] at h
  linear_combination h

/-- The elementary divided-logarithm formula of Carlson (1987), (8.8). -/
theorem regLContinued_neg_one_one_one (x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) (hxy : x ≠ y) :
    regLContinued (-1) 1 1 x y hz = (log x ^ 2 - log y ^ 2) / (2 * (x - y)) := by
  apply (eq_div_iff (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hxy))).mpr
  linear_combination 2 * sub_mul_regLContinued_neg_one_one_one x y hz

/-- The diagonal value completes the exceptional elementary formula. -/
theorem regLContinued_neg_one_one_one_diag (x : ℂ)
    (hz : pair x x ∈ carlsonRVariableDomain) :
    regLContinued (-1) 1 1 x x hz = x⁻¹ * log x := by
  have heq : pair x x = fun _ => x := by ext i; fin_cases i <;> rfl
  have h := regCarlsonLContinued_const (-1) x (hz 0) (pair 1 1)
  norm_num [sum_pair, cpow_neg_one] at h
  simpa only [← heq] using h

/-- The uniform two-node reduction underlying (8.5), stated without division.
At `t = -1` it reduces to the logarithmic R-identity, so the separate formula
`regLContinued_neg_one_one_one` is needed to evaluate L there. -/
theorem sub_mul_regLContinued_one_one (t x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    (x - y) * ((t + 1) * regLContinued t 1 1 x y hz +
      regCarlsonRContinued t (pair x y) hz (pair 1 1)) =
        x ^ (t + 1) * log x - y ^ (t + 1) * log y := by
  have h := sub_mul_regAverage_deriv
    ((analyticOnNhd_carlsonLKernel (t + 1)).mono carlsonRightHalfPlane_subset_slitPlane) x y hz
  rw [regCarlsonDirichletAverage_deriv_LKernel (t + 1) one_one_mem_mvBetaConvergent hz] at h
  rw [show t + 1 - 1 = t by ring] at h
  simpa only [regLContinued,
    regCarlsonLContinued_eq_integral _ hz one_one_mem_mvBetaConvergent,
    regCarlsonRContinued_eq_integral _ hz one_one_mem_mvBetaConvergent, carlsonLKernel] using h

/-- Carlson (1987), (3.9), in a division-free regularized form. The identity is
valid at coincident nodes and at every complex Dirichlet parameter. -/
theorem regCarlsonLSlit_pair_contiguous (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    u * (y - x) * regCarlsonLSlit t (pair (u + 1) v) (pair x y) =
      y * regCarlsonLSlit t (pair u v) (pair x y) -
        regCarlsonLSlit (t + 1) (pair u v) (pair x y) := by
  have h₀ := regCarlsonLSlit_eq_sum_addDirichletUnit t (pair u v) hz
  have h₁ := regCarlsonLSlit_add_one_eq_sum_mul_addDirichletUnit t (pair u v) hz
  have hu : addDirichletUnit (pair u v) 0 = pair (u + 1) v := by
    ext i
    fin_cases i <;> simp [addDirichletUnit, pair]
  simp only [Fin.sum_univ_two, pair_zero, pair_one, hu] at h₀ h₁
  linear_combination h₁ - y * h₀

end DirichletTransform.TwoVariable
end

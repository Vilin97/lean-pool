/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Continuation
public import LeanPool.CarlsonFunctions.Carlson.R.EulerTransform

/-!
# Associated relations and Euler transformation for Carlson's L-function

Carlson (1987), (3.1), (3.2), (3.4), and (2.6), in regularized form.
All Dirichlet parameters and exponents are arbitrary complex numbers. In
particular, the inhomogeneous lowering relation requires no division by a
parameter or exponent. The proofs differentiate the corresponding R-identities.
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Equation (3.1), after Gamma regularization. -/
theorem regCarlsonLContinued_eq_sum_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLContinued t z hz b =
      ∑ i, b i * regCarlsonLContinued t z hz (addDirichletUnit b i) := by
  have h := hasDerivAt_regCarlsonRContinued_L t b hz
  have heq : (fun s => regCarlsonRContinued s z hz b) =
      (fun s => ∑ i, b i * regCarlsonRContinued s z hz (addDirichletUnit b i)) :=
    funext fun s => regCarlsonRContinued_eq_sum_addDirichletUnit s b hz
  rw [heq] at h
  exact h.unique (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_regCarlsonRContinued_L t (addDirichletUnit b i) hz).const_mul (b i))

/-- Equation (3.2), after Gamma regularization. -/
theorem regCarlsonLContinued_add_one_eq_sum_mul_addDirichletUnit
    (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLContinued (t + 1) z hz b =
      ∑ i, b i * z i * regCarlsonLContinued t z hz (addDirichletUnit b i) := by
  have h := (hasDerivAt_regCarlsonRContinued_L (t + 1) b hz).comp t
    ((hasDerivAt_id t).add_const 1)
  simp only [mul_one, Function.comp_def, id_eq] at h
  have heq : (fun s => regCarlsonRContinued (s + 1) z hz b) =
      (fun s => ∑ i, b i * z i * regCarlsonRContinued s z hz (addDirichletUnit b i)) :=
    funext fun s => regCarlsonRContinued_add_one_eq_sum_mul_addDirichletUnit s b hz
  rw [heq] at h
  exact h.unique (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_regCarlsonRContinued_L t (addDirichletUnit b i) hz).const_mul (b i * z i))

/-- Equation (3.4), with parameters raised instead of lowered. The two R-terms
are essential: L is not homogeneous in the exponent-dependent coefficients. -/
theorem regCarlsonLContinued_eq_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    regCarlsonLContinued t z hz b =
      ((∑ j, b j) + t) * regCarlsonLContinued t z hz (addDirichletUnit b i) -
        t * z i * regCarlsonLContinued (t - 1) z hz (addDirichletUnit b i) +
        regCarlsonRContinued t z hz (addDirichletUnit b i) -
        z i * regCarlsonRContinued (t - 1) z hz (addDirichletUnit b i) := by
  have h := hasDerivAt_regCarlsonRContinued_L t b hz
  have heq : (fun s => regCarlsonRContinued s z hz b) =
      (fun s => ((∑ j, b j) + s) * regCarlsonRContinued s z hz (addDirichletUnit b i) -
        s * z i * regCarlsonRContinued (s - 1) z hz (addDirichletUnit b i)) :=
    funext fun s => regCarlsonRContinued_eq_addDirichletUnit s b hz i
  rw [heq] at h
  have h₀ := hasDerivAt_regCarlsonRContinued_L t (addDirichletUnit b i) hz
  have h₁ := (hasDerivAt_regCarlsonRContinued_L (t - 1) (addDirichletUnit b i) hz).comp t
    ((hasDerivAt_id t).sub_const 1)
  have H := h.unique ((((hasDerivAt_id t).const_add (∑ j, b j)).mul h₀).sub
    (((hasDerivAt_id t).mul_const (z i)).mul h₁))
  simp only [id_eq] at H
  convert H using 1
  ring

/-- Equation (2.6): the Euler transformation for L has a minus sign from the
reflected exponent. It holds for all complex Dirichlet parameters after regularization. -/
theorem regCarlsonLContinued_euler (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLContinued t z hz b =
      -(∏ i, z i ^ (-b i)) * regCarlsonLContinued (-(∑ i, b i) - t)
        (fun i => (z i)⁻¹) (carlsonRVariableDomain_inv hz) b := by
  have h := hasDerivAt_regCarlsonRContinued_L t b hz
  have heq : (fun s => regCarlsonRContinued s z hz b) =
      (fun s => (∏ i, z i ^ (-b i)) * regCarlsonRContinued (-(∑ i, b i) - s)
        (fun i => (z i)⁻¹) (carlsonRVariableDomain_inv hz) b) :=
    funext fun s => regCarlsonRContinued_euler s b hz
  rw [heq] at h
  have hd := ((hasDerivAt_regCarlsonRContinued_L (-(∑ i, b i) - t) b
    (carlsonRVariableDomain_inv hz)).comp t
      ((hasDerivAt_id t).const_sub (-(∑ i, b i)))).const_mul (∏ i, z i ^ (-b i))
  convert h.unique hd using 1
  ring

end DirichletTransform
end

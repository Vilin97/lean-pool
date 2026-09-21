/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Continuation
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.TaylorContinuation

/-!
# R-polynomial expansions of Carlson's L-function

The scalar Taylor coefficients give an absolutely convergent expansion for all
complex Dirichlet parameters, not just the native convergence region. At `t = 0`
the coefficients are explicit, giving the logarithmic series of Carlson (1987),
(5.8), in powers of `z - 1` rather than `1 - z`.

The derivative-coefficient formulation is nonsingular at integral exponents.
Explicit Pochhammer/digamma evaluations at general exponents, (5.3)–(5.7),
are not yet supplied by this module.
-/

open Complex Set
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Scalar Taylor coefficients about one of the power-logarithm kernel. -/
def carlsonLCoeff (n : ℕ) (t : ℂ) : ℂ :=
  iteratedDeriv n (carlsonLKernel t) 1 / n.factorial

/-- The constant coefficient vanishes for every exponent. -/
@[simp] theorem carlsonLCoeff_zero (t : ℂ) : carlsonLCoeff 0 t = 0 := by
  simp [carlsonLCoeff, carlsonLKernel]

/-- The first coefficient is one, independently of the exponent. -/
@[simp] theorem carlsonLCoeff_one (t : ℂ) : carlsonLCoeff 1 t = 1 := by
  simp [carlsonLCoeff, iteratedDeriv_succ,
    (hasDerivAt_carlsonLKernel t one_mem_slitPlane).deriv, carlsonLKernel]

/-- The unit disk about one avoids the principal logarithm's branch cut. -/
theorem ball_one_subset_slitPlane : Metric.ball (1 : ℂ) 1 ⊆ slitPlane := by
  intro w hw
  apply carlsonRightHalfPlane_subset_slitPlane
  have hnorm : ‖w - 1‖ < 1 := by simpa [dist_eq] using hw
  have hre := Complex.abs_re_le_norm (w - 1)
  have hlow := neg_le_abs (w - 1).re
  change 0 < w.re
  simp only [sub_re, one_re] at hre hlow
  linarith

/-- The continued L-function has the R-polynomial Taylor representation on
the full unit polydisk, even at exceptional total parameters. -/
theorem hasSum_regCarlsonLContinued (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (hz1 : ‖fun i => z i - 1‖ < 1) :
    HasSum (fun n => carlsonLCoeff n t * regCarlsonR n (fun i => z i - 1) b)
      (regCarlsonLContinued t z hz b) :=
  (isRegCarlsonLContinuation_continued t hz).hasSum_taylor
    ((analyticOnNhd_carlsonLKernel t).mono ball_one_subset_slitPlane) hz1 b

/-- Absolute convergence of the continued L-expansion. -/
theorem summable_norm_regCarlsonLContinued_series (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz1 : ‖fun i => z i - 1‖ < 1) :
    Summable (fun n => ‖carlsonLCoeff n t * regCarlsonR n (fun i => z i - 1) b‖) :=
  summable_norm_regCarlsonTaylorSeries
    ((analyticOnNhd_carlsonLKernel t).mono ball_one_subset_slitPlane) hz1 b

/-- At exponent zero the Taylor coefficients are those of `log (1 + x)`. -/
theorem carlsonLCoeff_exponent_zero (n : ℕ) :
    carlsonLCoeff n 0 = -(-1 : ℂ) ^ n / n := by
  have hk : carlsonLKernel 0 = log := by funext w; simp [carlsonLKernel]
  rw [carlsonLCoeff, hk]
  cases n with
  | zero => simp
  | succ n =>
    simp [iteratedDeriv_succ_log one_mem_slitPlane, Nat.factorial_succ, pow_succ]
    field_simp [show n.factorial ≠ 0 by positivity]

/-- Equation (5.8), with the sign absorbed into the coefficients of `z - 1`.
The `n = 0` term is zero by totalized division. -/
theorem hasSum_regCarlsonLContinued_zero (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (hz1 : ‖fun i => z i - 1‖ < 1) :
    HasSum (fun n => (-(-1 : ℂ) ^ n / n) * regCarlsonR n (fun i => z i - 1) b)
      (regCarlsonLContinued 0 z hz b) := by
  simpa only [carlsonLCoeff_exponent_zero] using hasSum_regCarlsonLContinued 0 b hz hz1

end DirichletTransform
end

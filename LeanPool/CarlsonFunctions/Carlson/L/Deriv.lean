/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Basic
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Node derivatives and the Euler–Poisson system for L

The native L-integral satisfies Carlson (1987), (2.7) and (3.5). Node
analyticity and the Euler–Poisson system are instances of the general Dirichlet
average theorems, not independent integration-by-parts proofs.
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The power-logarithm kernel is holomorphic on the principal slit plane. -/
theorem analyticOnNhd_carlsonLKernel (t : ℂ) :
    AnalyticOnNhd ℂ (carlsonLKernel t) slitPlane := by
  intro w hw
  have hp : AnalyticAt ℂ (fun v : ℂ => v ^ t) w := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem hw] with v hv
    exact differentiableAt_id.cpow_const hv
  exact hp.mul (analyticAt_clog hw)

/-- Differentiating the kernel lowers the exponent and adds a power kernel. -/
theorem hasDerivAt_carlsonLKernel (t : ℂ) {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt (carlsonLKernel t)
      (t * carlsonLKernel (t - 1) w + w ^ (t - 1)) w := by
  have h := (Complex.hasStrictDerivAt_cpow_const hw (c := t)).hasDerivAt.mul
    (Complex.hasDerivAt_log hw)
  have hp : w ^ t * w⁻¹ = w ^ (t - 1) := by
    rw [cpow_sub _ _ (slitPlane_ne_zero hw), cpow_one, div_eq_mul_inv]
  apply h.congr_deriv
  change t * w ^ (t - 1) * log w + w ^ t * w⁻¹ =
    t * (w ^ (t - 1) * log w) + w ^ (t - 1)
  rw [hp]
  ring

/-- The log-power integrand is continuous on the compact simplex. -/
theorem continuousOn_carlsonLKernel_affine (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    ContinuousOn (fun u => carlsonLKernel t (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
  (analyticOnNhd_carlsonLKernel t).continuousOn.comp
    (continuous_carlsonAffineForm z).continuousOn
    (fun _ hu => carlsonAffineForm_mem_slitPlane hz hu)

/-- On the native convergence region, L is holomorphic jointly in all nodes. -/
theorem analyticOnNhd_regCarlsonLIntegral_nodes (t : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (regCarlsonLIntegral t b) carlsonRVariableDomain := by
  have h := analyticOnNhd_regCarlsonDirichletAverage_nodes
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane) hb
  exact h.mono (fun _ hz => Set.range_subset_iff.mpr hz)

/-- Equation (2.7): the complete Euler–Poisson system, including equal indices. -/
theorem carlsonEulerPoissonOperator_regCarlsonLIntegral (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (regCarlsonLIntegral t b) = 0 :=
  carlsonEulerPoissonOperator_regCarlsonDirichletAverage
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane)
    hb (Set.range_subset_iff.mpr hz) i j

/-- Averaging the derivative of the kernel gives the inhomogeneous lowering formula. -/
theorem regCarlsonDirichletAverage_deriv_LKernel (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonDirichletAverage b z (deriv (carlsonLKernel t)) =
      t * regCarlsonLIntegral (t - 1) b z + regCarlsonRIntegral (t - 1) b z := by
  have hp : ContinuousOn (fun u => carlsonAffineForm z u ^ (t - 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu => carlsonAffineForm_mem_slitPlane hz hu)
  change regDirichletIntegral b _ = _
  rw [regDirichletIntegral_congr b (g := fun u =>
    t * carlsonLKernel (t - 1) (carlsonAffineForm z u) + carlsonAffineForm z u ^ (t - 1))
      (fun u hu => (hasDerivAt_carlsonLKernel t (carlsonAffineForm_mem_slitPlane hz hu)).deriv)]
  have hl : ContinuousOn (fun u => t * carlsonLKernel (t - 1) (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    continuousOn_const.mul (continuousOn_carlsonLKernel_affine (t - 1) hz)
  rw [regDirichletIntegral_add b hl hp hb, regDirichletIntegral_smul]
  rfl

/-- Equation (3.5), in regularized form. -/
theorem carlsonPartialDeriv_regCarlsonLIntegral (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    carlsonPartialDeriv i (regCarlsonLIntegral t b) z =
      b i * (t * regCarlsonLIntegral (t - 1) (addDirichletUnit b i) z +
        regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z) := by
  change carlsonPartialDeriv i (fun z => regCarlsonDirichletAverage b z (carlsonLKernel t)) z = _
  rw [carlsonPartialDeriv_regCarlsonDirichletAverage_of_analyticOnNhd
      isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
      ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane)
      hb (Set.range_subset_iff.mpr hz),
    regCarlsonDirichletAverage_deriv_LKernel t (addDirichletUnit_mem_mvBetaConvergent hb i) hz]

end DirichletTransform
end

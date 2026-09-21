/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Exponent

/-!
# Carlson's L-function: native integrals

The kernel is `w ^ t * log w`, with the principal complex logarithm. These
native integrals are distinguished from their analytic continuations in `b`.

## References

* B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM J. Math. Anal. 18 (1987),
  550–565, equations (1.2), (1.3), (2.2), and (2.4).
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The power-logarithm kernel whose Dirichlet average is Carlson's `L_t`. -/
def carlsonLKernel (t w : ℂ) : ℂ := w ^ t * log w

/-- The native regularized `L_t / Γ(∑ i, b i)` integral. -/
def regCarlsonLIntegral (t : ℂ) (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z (carlsonLKernel t)

/-- Carlson's native normalized L-integral. -/
def carlsonLIntegral (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonLIntegral t b z

/-- Equation (1.2): differentiating the native R-integral inserts the logarithm. -/
theorem hasDerivAt_regCarlsonRIntegral_L (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s => regCarlsonRIntegral s b z) (regCarlsonLIntegral t b z) t :=
  hasDerivAt_regCarlsonRIntegral_exponent t hb hz

theorem hasDerivAt_carlsonRIntegral_L (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s => carlsonRIntegral s b z) (carlsonLIntegral t b z) t :=
  (hasDerivAt_regCarlsonRIntegral_L t hb hz).const_mul _

/-- The native L-integral is entire in its exponent on the convergence region. -/
theorem analyticOnNhd_regCarlsonLIntegral_exponent {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun t => regCarlsonLIntegral t b z) Set.univ := by
  have heq : (fun t => regCarlsonLIntegral t b z) =
      deriv (fun t => regCarlsonRIntegral t b z) :=
    funext fun t => (hasDerivAt_regCarlsonRIntegral_L t hb hz).deriv.symm
  rw [heq]
  exact (analyticOnNhd_regCarlsonRIntegral_exponent hb hz).deriv

/-- Equation (2.2), for the native regularized integral. -/
theorem regCarlsonLIntegral_perm (t : ℂ) (b z : ι → ℂ) (σ : Equiv.Perm ι) :
    regCarlsonLIntegral t (b ∘ σ) (z ∘ σ) = regCarlsonLIntegral t b z :=
  regCarlsonDirichletAverage_perm b z (carlsonLKernel t) σ

end DirichletTransform
end

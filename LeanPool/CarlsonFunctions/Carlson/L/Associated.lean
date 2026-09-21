/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Relations
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv
public import LeanPool.CarlsonFunctions.Dirichlet.Average.ContinuedRelations

/-!
# Further associated and differential identities for L

The three-node relation (3.3) and backward-shift relation (3.7) of Carlson
(1987) hold for the entire regularized continuation. The translation and Euler
differential identities (2.9) and (2.8) are stated for native integrals.
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The derivative kernel has an entire continuation expressed through L and R. -/
theorem isRegCarlsonContinuation_deriv_LKernel (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    IsRegCarlsonContinuation (deriv (carlsonLKernel t)) z
      (fun b => t * regCarlsonLContinued (t - 1) z hz b + regCarlsonRContinued (t - 1) z hz b) := by
  refine ⟨(analyticOnNhd_const.mul (analyticOnNhd_regCarlsonLContinued (t - 1) hz)).add
    (analyticOnNhd_regCarlsonRContinued (t - 1) hz), ?_⟩
  intro b hb
  dsimp only
  rw [regCarlsonLContinued_eq_integral _ hz hb, regCarlsonRContinued_eq_integral _ hz hb]
  exact (regCarlsonDirichletAverage_deriv_LKernel t hb hz).symm

/-- Equation (3.3), including coincident nodes and indices. -/
theorem regCarlsonLContinued_three_node (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i j k : ι) :
    (z i - z j) * regCarlsonLContinued t z hz (b - Pi.single k 1) +
      (z j - z k) * regCarlsonLContinued t z hz (b - Pi.single i 1) +
      (z k - z i) * regCarlsonLContinued t z hz (b - Pi.single j 1) = 0 :=
  (isRegCarlsonLContinuation_continued t hz).three_node convex_carlsonRightHalfPlane
    ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane)
    (Set.range_subset_iff.mpr hz) isOpen_carlsonRightHalfPlane b i j k

/-- Equation (3.7), in pole-free regularized form. -/
theorem regCarlsonLContinued_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    (z i - z j) * (t * regCarlsonLContinued (t - 1) z hz b +
      regCarlsonRContinued (t - 1) z hz b) =
        regCarlsonLContinued t z hz (b - Pi.single j 1) -
          regCarlsonLContinued t z hz (b - Pi.single i 1) :=
  (isRegCarlsonLContinuation_continued t hz).tangent_sub convex_carlsonRightHalfPlane
    ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane)
    (Set.range_subset_iff.mpr hz) (isRegCarlsonContinuation_deriv_LKernel t hz) b i j

/-- The first associated relation on the native convergence region. -/
theorem regCarlsonLIntegral_eq_sum_addDirichletUnit (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLIntegral t b z =
      ∑ i, b i * regCarlsonLIntegral t (addDirichletUnit b i) z := by
  simpa only [regCarlsonLContinued_eq_integral _ hz hb,
    regCarlsonLContinued_eq_integral _ hz (addDirichletUnit_mem_mvBetaConvergent hb _)] using
    regCarlsonLContinued_eq_sum_addDirichletUnit t b hz

/-- The exponent-raising relation on the native convergence region. -/
theorem regCarlsonLIntegral_add_one_eq_sum_mul_addDirichletUnit (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLIntegral (t + 1) b z =
      ∑ i, b i * z i * regCarlsonLIntegral t (addDirichletUnit b i) z := by
  simpa only [regCarlsonLContinued_eq_integral _ hz hb,
    regCarlsonLContinued_eq_integral _ hz (addDirichletUnit_mem_mvBetaConvergent hb _)] using
    regCarlsonLContinued_add_one_eq_sum_mul_addDirichletUnit t b hz

/-- Equation (2.9): the differential-difference identity for translations. -/
theorem sum_carlsonPartialDeriv_regCarlsonLIntegral (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    ∑ i, carlsonPartialDeriv i (regCarlsonLIntegral t b) z =
      t * regCarlsonLIntegral (t - 1) b z + regCarlsonRIntegral (t - 1) b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonLIntegral t hb hz]
  rw [regCarlsonLIntegral_eq_sum_addDirichletUnit (t - 1) hb hz,
    regCarlsonRIntegral_eq_sum_update_add_one (t - 1) hb hz,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [addDirichletUnit]
  ring

/-- Equation (2.8): Euler's identity has the inhomogeneous term R. -/
theorem sum_mul_carlsonPartialDeriv_regCarlsonLIntegral (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    ∑ i, z i * carlsonPartialDeriv i (regCarlsonLIntegral t b) z =
      t * regCarlsonLIntegral t b z + regCarlsonRIntegral t b z := by
  have hL := regCarlsonLIntegral_add_one_eq_sum_mul_addDirichletUnit (t - 1) hb hz
  have hR := regCarlsonRIntegral_add_one_eq_sum_mul_update (t - 1) hb hz
  simp only [sub_add_cancel] at hL hR
  simp_rw [carlsonPartialDeriv_regCarlsonLIntegral t hb hz]
  rw [hL, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [addDirichletUnit]
  ring

end DirichletTransform
end

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Continuation
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Associated

/-!
# Carlson's R-function: analyticity and differentiation

This file proves the pointwise kernel identities, differentiation under the Dirichlet
integral, and joint analyticity in the nodes for Carlson's Theorem 5.9-2 on the native
parameter convergence region and right-half-plane node domain.
-/

open Complex ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- For a fixed simplex point, Carlson's power kernel is analytic in all variables throughout
the right-half-plane domain. This is the pointwise input to the analyticity in Theorem 5.9-2. -/
theorem analyticOnNhd_cpow_carlsonAffineForm (t : ℂ) (u : ι → ℝ)
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ ↦ carlsonAffineForm z u ^ t)
      carlsonRVariableDomain := by
  intro z hz
  have haffine : AnalyticAt ℂ (carlsonAffineForm · u) z := by
    unfold carlsonAffineForm
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul
      ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt z)
  have hpow : AnalyticAt ℂ (fun w : ℂ ↦ w ^ t) (carlsonAffineForm z u) := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem
      (carlsonAffineForm_mem_slitPlane hz hu)] with w hw
    exact (differentiableAt_id.cpow_const hw)
  exact hpow.comp_of_eq haffine rfl

open scoped Classical in
/-- The coordinate derivative of Carlson's power kernel.  This is the pointwise form of
Relation 5.9-6, equation (9). -/
theorem hasDerivAt_cpow_carlsonAffineForm_update (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) (i : ι) :
    HasDerivAt (fun w ↦ carlsonAffineForm (Function.update z i w) u ^ t)
      ((u i : ℂ) * (t * carlsonAffineForm z u ^ (t - 1))) (z i) := by
  exact HasDerivAt.comp_carlsonAffineForm_update i
    (Complex.hasStrictDerivAt_cpow_const
      (carlsonAffineForm_mem_slitPlane hz hu)).hasDerivAt

omit [Fintype ι] in
open scoped Classical in
/-- A sufficiently small closed ball around one coordinate of a point in the Carlson
right-half-plane domain remains in that domain after updating that coordinate. -/
theorem update_mem_carlsonRVariableDomain_of_mem_closedBall
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι)
    {w : ℂ} (hw : w ∈ Metric.closedBall (z i) ((z i).re / 2)) :
    Function.update z i w ∈ carlsonRVariableDomain := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [Function.update_self]
    have hd : ‖w - z i‖ ≤ (z i).re / 2 := by
      simpa [dist_eq] using Metric.mem_closedBall.mp hw
    have hre : |w.re - (z i).re| ≤ ‖w - z i‖ := by
      simpa using Complex.abs_re_le_norm (w - z i)
    have hzi : 0 < (z i).re := hz i
    dsimp only [carlsonRightHalfPlane, Set.mem_ofPred_eq]
    have hlower : (z i).re / 2 ≤ w.re := by
      nlinarith [neg_le_abs (w.re - (z i).re)]
    exact lt_of_lt_of_le (half_pos hzi) hlower
  · rw [Function.update_of_ne hji]
    exact hz j

open scoped Classical in
/-- Carlson's first differentiation formula, Relation 5.9-6, equation (9), for the native
regularized `R` integral. -/
theorem hasDerivAt_regCarlsonRIntegral_update
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    HasDerivAt (fun w ↦ regCarlsonRIntegral t b (Function.update z i w))
      (t * b i * regCarlsonRIntegral (t - 1)
        (addDirichletUnit b i) z) (z i) := by
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w ^ t) carlsonRightHalfPlane := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem
      (carlsonRightHalfPlane_subset_slitPlane hw)] with v hv
    exact differentiableAt_id.cpow_const hv
  have hderiv := hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane hf hb
    (Set.range_subset_iff.mpr hz) i
  have hkernel : regDirichletIntegral b
      (fun u => (u i : ℂ) * deriv (fun w : ℂ => w ^ t) (carlsonAffineForm z u)) =
      regDirichletIntegral b
        (fun u => (u i : ℂ) * (t * carlsonAffineForm z u ^ (t - 1))) := by
    apply regDirichletIntegral_congr
    intro u hu
    dsimp only
    rw [(Complex.hasStrictDerivAt_cpow_const
      (carlsonAffineForm_mem_slitPlane hz hu)).hasDerivAt.deriv]
  rw [hkernel] at hderiv
  rw [show t * b i * regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z =
      regDirichletIntegral b (fun u ↦
        (u i : ℂ) * (t * carlsonAffineForm z u ^ (t - 1))) by
    rw [mul_assoc, regCarlsonRIntegral, regCarlsonDirichletAverage]
    rw [mul_regDirichletIntegral_addDirichletUnit hb]
    rw [← regDirichletIntegral_smul b
      (f := fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ (t - 1)) t]
    congr 1
    funext u
    ring]
  simpa [regCarlsonRIntegral] using hderiv

/-- Coordinate form of Carlson's first differentiation formula, Relation 5.9-6, equation (9). -/
theorem carlsonPartialDeriv_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    carlsonPartialDeriv i (regCarlsonRIntegral t b) z =
      t * b i * regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv]
  exact (hasDerivAt_regCarlsonRIntegral_update t hb hz i).deriv

/-- Carlson's joint analyticity assertion in Theorem 5.9-2, restricted to the nodes, for the
native regularized integral on the right-half-plane variable domain.

The coordinate differentiation theorem above supplies the derivatives. The
analytic-under-the-integral argument is stated jointly because this is the form needed for
the identity principle and for the differential equations. -/
theorem analyticOnNhd_regCarlsonRIntegral (t : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (regCarlsonRIntegral t b) carlsonRVariableDomain := by
  unfold regCarlsonRIntegral
  rw [show carlsonRVariableDomain (ι := ι) =
      {z : ι → ℂ | Set.range z ⊆ carlsonRightHalfPlane} by
    ext z
    simp only [carlsonRVariableDomain, Set.mem_ofPred_eq, Set.range_subset_iff]]
  apply analyticOnNhd_regCarlsonDirichletAverage_nodes
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane (f := fun w => w ^ t) _ hb
  intro w hw
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem
    (carlsonRightHalfPlane_subset_slitPlane hw)] with v hv
  exact differentiableAt_id.cpow_const hv

/-- The native unregularized R-integral is jointly analytic on the same variable domain. -/
theorem analyticOnNhd_carlsonRIntegral (t : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (carlsonRIntegral t b) carlsonRVariableDomain := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_regCarlsonRIntegral t hb z hz)

open scoped Classical in
/-- Euler's differential identity for the pointwise power kernel, corresponding to
the second equation of Theorem 5.9-2. -/
theorem sum_mul_deriv_cpow_carlsonAffineForm (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ∑ i, z i * deriv (fun w ↦ carlsonAffineForm (Function.update z i w) u ^ t) (z i) =
      t * carlsonAffineForm z u ^ t := by
  simp_rw [(hasDerivAt_cpow_carlsonAffineForm_update t hz hu _).deriv]
  have hne : carlsonAffineForm z u ≠ 0 :=
    slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu)
  rw [show ∑ i, z i * ((u i : ℂ) *
      (t * carlsonAffineForm z u ^ (t - 1))) =
      (∑ i, (u i : ℂ) * z i) *
        (t * carlsonAffineForm z u ^ (t - 1)) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [show ∑ i, (u i : ℂ) * z i = carlsonAffineForm z u by rfl]
  calc
    carlsonAffineForm z u * (t * carlsonAffineForm z u ^ (t - 1)) =
        t * (carlsonAffineForm z u ^ (t - 1) * carlsonAffineForm z u) := by ring
    _ = t * carlsonAffineForm z u ^ ((t - 1) + 1) := by
      rw [cpow_add _ _ hne, cpow_one]
    _ = t * carlsonAffineForm z u ^ t := by ring_nf

/- The two differential identities of Theorem 5.9-2 are derived in `Carlson.R.Relations`. -/

end DirichletTransform
end CarlsonR

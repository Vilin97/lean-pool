/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic
public import LeanPool.CarlsonFunctions.Dirichlet.Average.IntegralDomain
public import LeanPool.CarlsonFunctions.Dirichlet.Average.CauchyContinuation

/-!
# Native-integral agreement on the slit plane

Carlson's slit continuation agrees with its principal-power simplex integral
whenever the entire node convex hull avoids the branch cut, not only when all
nodes lie in the right half-plane. This identifies `regCarlsonRSlit` with the
domain-aware continuation of the power kernel and connects it to the continued
circle-Cauchy representation.

Nodewise membership in the slit plane alone is not enough for native integral
agreement: the convex hull may meet the cut. The general simply connected
continuation theorem for arbitrary scalar kernels is still separate work.
-/

open Complex ProbabilityTheory Set Metric
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The slit R-function satisfies the general-average characterization, with
native agreement wherever the full node convex hull lies in the slit plane. -/
theorem isJointRegCarlsonContinuationOn_regCarlsonRSlit (t : ℂ) :
    IsJointRegCarlsonContinuationOn slitPlane (fun w => w ^ t)
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonRSlit t p.1 p.2) := by
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ => w ^ t) slitPlane :=
    (show DifferentiableOn ℂ (fun w : ℂ => w ^ t) slitPlane from
      fun w hw => (differentiableAt_id.cpow_const hw).differentiableWithinAt).analyticOnNhd
        isOpen_slitPlane
  apply isJointRegCarlsonContinuationOn_of_convex_seed isOpen_slitPlane
    starConvex_one_slitPlane isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (show (1 : ℂ) ∈ carlsonRightHalfPlane by simp [carlsonRightHalfPlane])
    carlsonRightHalfPlane_subset_slitPlane hpow
  · intro p hp
    exact analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_fst analyticAt_snd
      (fun i => hp ⟨i, rfl⟩)
  · intro z hz b hb
    exact regCarlsonRSlit_eq_integral t hb (fun i => hz ⟨i, rfl⟩)

/-- The entire-parameter R-continuation is characterized by its native integral
on every convex-hull-admissible slit tuple. -/
theorem isRegCarlsonRContinuation_regCarlsonRSlit_of_convexHull (t : ℂ)
    {z : ι → ℂ} (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    IsRegCarlsonRContinuation t z (fun b => regCarlsonRSlit t b z) :=
  (isJointRegCarlsonContinuationOn_regCarlsonRSlit t).isRegCarlsonContinuation hz

/-- Principal-branch native agreement on the full admissible convex-hull domain. -/
theorem regCarlsonRSlit_eq_integral_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    regCarlsonRSlit t b z = regCarlsonRIntegral t b z :=
  (isRegCarlsonRContinuation_regCarlsonRSlit_of_convexHull t hz).eq_integral hb

/-- The same native agreement with the ordinary normalization. -/
theorem carlsonRSlit_eq_integral_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    carlsonRSlit t b z = carlsonRIntegral t b z := by
  rw [carlsonRSlit, carlsonRIntegral, regCarlsonRSlit_eq_integral_of_convexHull t hb hz]

/-- The circle form of the generalized Cauchy representation for `R_t`, at all
complex parameters. This is the power-kernel specialization of 6.3-4, not the
different beta-resolvent ellipse formula 6.8-7. -/
theorem regCarlsonRSlit_eq_circleIntegral (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hD : closedBall c R ⊆ slitPlane) (hz : Set.range z ⊆ ball c R) :
    regCarlsonRSlit t b z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∮ s in C(c, R), continuedRegCarlsonResolvent 0 b z s * s ^ t := by
  have hh : convexHull ℝ (Set.range z) ⊆ slitPlane :=
    (convexHull_min hz (convex_ball c R)).trans (ball_subset_closedBall.trans hD)
  have hp : DifferentiableOn ℂ (fun w : ℂ => w ^ t) slitPlane :=
    fun w hw => (differentiableAt_id.cpow_const hw).differentiableWithinAt
  have h := (isRegCarlsonRContinuation_regCarlsonRSlit_of_convexHull t hh).eq_circleIntegral
    (n := 0) (f := fun w : ℂ => w ^ t) hR (hp.diffContOnCl_ball hD) hz b
  simpa only [Nat.factorial_zero, Nat.cast_one, one_mul] using h

end DirichletTransform
end

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.SlitContinuation
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv
public import LeanPool.CarlsonFunctions.Carlson.R.SlitIntegral

/-!
# Native power-logarithm averages on the slit plane

The slit L-function is the domain-aware continuation of `w ^ t * log w`.
Native-integral agreement and the exponent-derivative relation now hold whenever
the entire node convex hull lies in the slit plane. Merely asking that each node
avoid the cut would be insufficient. All statements allow empty index types.
-/

open Complex ProbabilityTheory Set
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The slit L-function is the domain-aware continuation of the power-logarithm kernel. -/
theorem isJointRegCarlsonContinuationOn_regCarlsonLSlit (t : ℂ) :
    IsJointRegCarlsonContinuationOn slitPlane (carlsonLKernel t)
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonLSlit t p.1 p.2) := by
  apply isJointRegCarlsonContinuationOn_of_convex_seed isOpen_slitPlane
    starConvex_one_slitPlane isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (show (1 : ℂ) ∈ carlsonRightHalfPlane by simp [carlsonRightHalfPlane])
    carlsonRightHalfPlane_subset_slitPlane (analyticOnNhd_carlsonLKernel t)
  · intro p hp
    exact analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_fst analyticAt_snd
      (fun i => hp ⟨i, rfl⟩)
  · intro z hz b hb
    exact regCarlsonLSlit_eq_integral t (fun i => hz ⟨i, rfl⟩) hb

/-- Entire-parameter characterization at every native-admissible slit tuple. -/
theorem isRegCarlsonContinuation_regCarlsonLSlit_of_convexHull (t : ℂ)
    {z : ι → ℂ} (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    IsRegCarlsonContinuation (carlsonLKernel t) z (fun b => regCarlsonLSlit t b z) :=
  (isJointRegCarlsonContinuationOn_regCarlsonLSlit t).isRegCarlsonContinuation hz

/-- Native L-integral agreement wherever the whole node convex hull avoids the cut. -/
theorem regCarlsonLSlit_eq_integral_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    regCarlsonLSlit t b z = regCarlsonLIntegral t b z :=
  (isRegCarlsonContinuation_regCarlsonLSlit_of_convexHull t hz).eq_native hb

/-- Native agreement with the ordinary L-normalization. -/
theorem carlsonLSlit_eq_integral_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    carlsonLSlit t b z = carlsonLIntegral t b z := by
  rw [carlsonLSlit, carlsonLIntegral, regCarlsonLSlit_eq_integral_of_convexHull t hb hz]

/-- Differentiating the native R-integral inserts the logarithm on the full
convex-hull-admissible node domain, with no right-half-plane restriction. -/
theorem hasDerivAt_regCarlsonRIntegral_L_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    HasDerivAt (fun s => regCarlsonRIntegral s b z) (regCarlsonLIntegral t b z) t := by
  have heq : (fun s => regCarlsonRIntegral s b z) = (fun s => regCarlsonRSlit s b z) :=
    funext fun s => (regCarlsonRSlit_eq_integral_of_convexHull s hb hz).symm
  rw [heq, ← regCarlsonLSlit_eq_integral_of_convexHull t hb hz]
  exact hasDerivAt_regCarlsonRSlit_L t b
    (fun i => hz (subset_convexHull ℝ (Set.range z) ⟨i, rfl⟩))

end DirichletTransform
end

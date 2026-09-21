/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.ResolventContinuation
public import LeanPool.CarlsonFunctions.Dirichlet.Average.HolomorphicDomain
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.ContourIntegral

/-!
# Continued Cauchy representations of Dirichlet averages

The circle version of Carlson (1969), §5, Theorem 3, for every derivative order
and all complex Dirichlet parameters. This extends the native-parameter circle
formula in `Dirichlet.Average.Cauchy`. The continued contour expression is
jointly holomorphic in parameters and interior nodes, even when the boundary
function is only continuous. For a function holomorphic in the disk it is the
unique regularized continuation of the corresponding derivative average.

General Jordan contours and their contour-adapted resolvent branches remain
necessary for Carlson's Theorems 5 and 8 on nonconvex simply connected domains.
The multiply connected and Riemann-surface extensions are left open.
-/

open Complex MeasureTheory ProbabilityTheory Set Metric
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A circle surrounding all nodes avoids all their simplex affine combinations. -/
theorem mem_carlsonResolventDomain_of_mem_sphere
    {c s : ℂ} {R : ℝ} {z : ι → ℂ}
    (hz : Set.range z ⊆ ball c R) (hs : s ∈ sphere c R) :
    (s, z) ∈ carlsonResolventDomain := by
  apply mem_carlsonResolventDomain_of_not_mem_convexHull
  intro h
  have hl := mem_ball.mp (convexHull_min hz (convex_ball c R) h)
  have he := mem_sphere.mp hs
  linarith

/-- The continued circle-Cauchy expression for the average of the `n`th derivative. -/
def continuedRegCarlsonCauchyRepresentation
    (n : ℕ) (b z : ι → ℂ) (c : ℂ) (R : ℝ) (f : ℂ → ℂ) : ℂ :=
  (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∮ s in C(c, R), continuedRegCarlsonResolvent n b z s * f s

/-- The continued contour expression is jointly holomorphic in all complex
Dirichlet parameters and interior nodes. Boundary continuity of `f` suffices. -/
theorem analyticOnNhd_continuedRegCarlsonCauchyRepresentation (n : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere c R)) :
    AnalyticOnNhd ℂ
      (fun p : (ι → ℂ) × (ι → ℂ) =>
        continuedRegCarlsonCauchyRepresentation n p.1 p.2 c R f)
      {p | Set.range p.2 ⊆ ball c R} := by
  let W : Set (((ι → ℂ) × (ι → ℂ)) × ℂ) :=
    {p | (p.2, p.1.2) ∈ carlsonResolventDomain}
  have hH : AnalyticOnNhd ℂ
      (fun p : ((ι → ℂ) × (ι → ℂ)) × ℂ =>
        continuedRegCarlsonResolvent n p.1.1 p.1.2 p.2) W := by
    intro p hp
    exact (analyticOnNhd_continuedRegCarlsonResolvent n
      (p.1.1, p.2, p.1.2) ⟨mem_univ _, hp⟩).comp_of_eq
      ((analyticAt_fst.comp_of_eq analyticAt_fst rfl).prod
        (analyticAt_snd.prod (analyticAt_snd.comp_of_eq analyticAt_fst rfl))) rfl
  have hU : IsOpen {p : (ι → ℂ) × (ι → ℂ) | Set.range p.2 ⊆ ball c R} := by
    simp only [Set.range_subset_iff, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_ball.preimage
      ((continuous_apply i).comp continuous_snd)
  exact analyticOnNhd_const.mul (analyticOnNhd_circleIntegral_kernel_mulCarlson hU hH hR hf
    (fun _ hp _ hs => mem_carlsonResolventDomain_of_mem_sphere hp hs))

/-- The circle expression recovers the native average on its convergence region. -/
theorem continuedRegCarlsonCauchyRepresentation_eq_native (n : ℕ)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hz : Set.range z ⊆ ball c R) :
    continuedRegCarlsonCauchyRepresentation n b z c R f =
      regCarlsonDirichletAverage b z (iteratedDeriv n f) := by
  rw [regCarlsonDirichletAverage_iteratedDeriv_eq_circleIntegral n hb z hR hf hz]
  unfold continuedRegCarlsonCauchyRepresentation
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro s hs
  dsimp only
  rw [continuedRegCarlsonResolvent_eq_native n hb
    (mem_carlsonResolventDomain_of_mem_sphere hz hs)]

/-- Carlson's circle-Cauchy expression is an entire regularized continuation,
for every derivative order; no boundary derivatives are required. -/
theorem isRegCarlsonContinuation_continuedRegCarlsonCauchyRepresentation (n : ℕ)
    {z : ι → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hz : Set.range z ⊆ ball c R) :
    IsRegCarlsonContinuation (iteratedDeriv n f) z
      (fun b => continuedRegCarlsonCauchyRepresentation n b z c R f) := by
  refine ⟨?_, fun b hb => continuedRegCarlsonCauchyRepresentation_eq_native n hb hR hf hz⟩
  intro b _
  exact (analyticOnNhd_continuedRegCarlsonCauchyRepresentation n hR.le
    (hf.continuousOn_ball.mono sphere_subset_closedBall) (b, z) hz).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl

/-- The circle construction supplies a domain-aware joint continuation on its
interior disk, ready for comparison and gluing with other local constructions. -/
theorem isJointRegCarlsonContinuationOn_circle (n : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) :
    IsJointRegCarlsonContinuationOn (ball c R) (iteratedDeriv n f)
      (fun p : (ι → ℂ) × (ι → ℂ) =>
        continuedRegCarlsonCauchyRepresentation n p.1 p.2 c R f) := by
  refine ⟨analyticOnNhd_continuedRegCarlsonCauchyRepresentation n hR.le
    (hf.continuousOn_ball.mono sphere_subset_closedBall), ?_⟩
  intro z hz b hb
  exact continuedRegCarlsonCauchyRepresentation_eq_native n hb hR hf
    ((subset_convexHull ℝ (Set.range z)).trans hz)

/-- Any established entire continuation has the circle-Cauchy representation
at every complex Dirichlet parameter, including poles of the unregularized average. -/
theorem IsRegCarlsonContinuation.eq_circleIntegral {n : ℕ}
    {f : ℂ → ℂ} {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation (iteratedDeriv n f) z G)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hz : Set.range z ⊆ ball c R) (b : ι → ℂ) :
    G b = (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∮ s in C(c, R), continuedRegCarlsonResolvent n b z s * f s :=
  congrFun (hG.eq
    (isRegCarlsonContinuation_continuedRegCarlsonCauchyRepresentation n hR hf hz)) b

/-- Independence of the enclosing circle for all complex parameters. Both
circles must bound disks on which the same scalar function is holomorphic. -/
theorem continuedRegCarlsonCauchyRepresentation_eq_of_disks (n : ℕ)
    {f : ℂ → ℂ} {z : ι → ℂ} {c d : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S)
    (hfR : DiffContOnCl ℂ f (ball c R)) (hfS : DiffContOnCl ℂ f (ball d S))
    (hzR : Set.range z ⊆ ball c R) (hzS : Set.range z ⊆ ball d S) (b : ι → ℂ) :
    continuedRegCarlsonCauchyRepresentation n b z c R f =
      continuedRegCarlsonCauchyRepresentation n b z d S f :=
  congrFun ((isRegCarlsonContinuation_continuedRegCarlsonCauchyRepresentation n hR hfR hzR).eq
    (isRegCarlsonContinuation_continuedRegCarlsonCauchyRepresentation n hS hfS hzS)) b

end DirichletTransform
end

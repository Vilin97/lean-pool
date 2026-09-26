/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Cauchy
public import LeanPool.CarlsonFunctions.Dirichlet.Average.JointContinuation

/-!
# Entire-parameter continuation of the Cauchy resolvent

This is the convex-hull-complement part of Carlson (1969), §5, Lemma 1. The
regularized integer resolvent is jointly holomorphic in the Dirichlet parameters,
the nodes, and the exterior evaluation point. All complex Dirichlet parameters
are allowed, without Gamma-pole exclusions. The proof uses the parametric
simplex integration-by-parts construction rather than a logarithmic branch.

This is not yet the contour-adapted branch on a nonconvex Jordan domain in
Carlson's Theorems 4–5. That construction and the simply connected extension of
Theorem 8 remain further work. Extensions to multiply connected domains and to
Riemann surfaces are deliberately left open.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Evaluation points which avoid every affine combination of the nodes on the
real simplex. This form of the domain makes its openness follow from compactness. -/
def carlsonResolventDomain : Set (ℂ × (ι → ℂ)) :=
  {p | ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
    p.1 - carlsonAffineForm p.2 u ≠ 0}

/-- The resolvent domain is open jointly in its evaluation point and nodes. -/
theorem isOpen_carlsonResolventDomain : IsOpen (carlsonResolventDomain (ι := ι)) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  apply (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).eventually_forall_of_forall_eventually
  intro u hu
  have hc : Continuous (fun q : (ℂ × (ι → ℂ)) × (ι → ℝ) =>
      q.1.1 - carlsonAffineForm q.1.2 q.2) := by
    unfold carlsonAffineForm
    fun_prop
  exact (isOpen_ne_fun hc continuous_const).eventually_mem (hp u hu)

/-- In particular, every point outside the convex hull is in the resolvent domain. -/
theorem mem_carlsonResolventDomain_of_not_mem_convexHull
    {s : ℂ} {z : ι → ℂ} (hs : s ∉ convexHull ℝ (Set.range z)) :
    (s, z) ∈ carlsonResolventDomain :=
  fun _ hu => sub_carlsonAffineForm_ne_zero hs hu

/-- Separate the evaluation coordinate from the node coordinates. -/
def resolventCoordinates (q : Option ι → ℂ) : ℂ × (ι → ℂ) :=
  (q none, fun i => q (some i))

/-- Coordinate form of the joint entire-parameter resolvent construction. -/
theorem exists_joint_regCarlsonResolvent (n : ℕ) :
    ∃ H : ((ι → ℂ) × (Option ι → ℂ)) → ℂ,
      AnalyticOnNhd ℂ H (univ ×ˢ (resolventCoordinates ⁻¹' carlsonResolventDomain)) ∧
      ∀ q, resolventCoordinates q ∈ carlsonResolventDomain →
        Set.EqOn (fun b => H (b, q))
          (fun b => regCarlsonResolvent n b (fun i => q (some i)) (q none))
          mvBetaConvergent := by
  let A := fun p : (Option ι → ℂ) × (ι → ℂ) =>
    p.1 none - ∑ i, p.1 (some i) * p.2 i
  have hA : AnalyticOnNhd ℂ A univ := by
    intro p _
    apply AnalyticAt.sub
    · exact ((ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq
        analyticAt_fst rfl
    · apply Finset.analyticAt_fun_sum
      intro i _
      exact (((ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt
        p.1).comp_of_eq
        analyticAt_fst rfl).mul
        (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2).comp_of_eq
          analyticAt_snd rfl)
  have hU : IsOpen (resolventCoordinates ⁻¹' carlsonResolventDomain (ι := ι)) :=
    isOpen_carlsonResolventDomain.preimage (by unfold resolventCoordinates; fun_prop)
  have hW : IsOpen {p | A p ≠ 0} :=
    isOpen_ne_fun (continuousOn_univ.mp hA.continuousOn) continuous_const
  obtain ⟨H, hH, hHeq⟩ := exists_entire_joint_regDirichletContinuation_kernel hU hW
    (H := fun p => A p ^ (-(n + 1 : ℤ)))
    (fun p hp => (hA p (mem_univ _)).zpow hp)
    (fun q hq u hu => by
      change q none - ∑ i, q (some i) * (u i : ℂ) ≠ 0
      simpa only [carlsonAffineForm, resolventCoordinates, mul_comm] using hq u hu)
  refine ⟨H, hH, ?_⟩
  simpa only [regCarlsonResolvent, regCarlsonDirichletAverage, carlsonAffineForm,
    A, Set.mem_preimage, mul_comm] using hHeq

/-- The entire-parameter regularized integer resolvent. Values outside
`carlsonResolventDomain` are unspecified; theorems only use it on that domain. -/
def continuedRegCarlsonResolvent (n : ℕ) (b z : ι → ℂ) (s : ℂ) : ℂ :=
  (exists_joint_regCarlsonResolvent (ι := ι) n).choose (b, fun i => i.elim s z)

/-- Joint analyticity in all parameters, evaluation point, and nodes. -/
theorem analyticOnNhd_continuedRegCarlsonResolvent (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : (ι → ℂ) × (ℂ × (ι → ℂ)) =>
        continuedRegCarlsonResolvent n p.1 p.2.2 p.2.1)
      (univ ×ˢ carlsonResolventDomain) := by
  intro p hp
  have he : AnalyticAt ℂ (fun q : (ι → ℂ) × (ℂ × (ι → ℂ)) =>
      (q.1, fun i : Option ι => i.elim q.2.1 q.2.2)) p := by
    apply analyticAt_fst.prod
    apply analyticAt_pi_iff.mpr
    intro i
    cases i with
    | none => exact analyticAt_fst.comp_of_eq analyticAt_snd rfl
    | some i =>
      exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2.2).comp_of_eq
        (analyticAt_snd.comp_of_eq analyticAt_snd rfl) rfl
  exact ((exists_joint_regCarlsonResolvent (ι := ι) n).choose_spec.1
    (p.1, fun i => i.elim p.2.1 p.2.2) ⟨mem_univ _, hp.2⟩).comp_of_eq he rfl

/-- The continued kernel agrees with the native resolvent on the convergence region. -/
theorem continuedRegCarlsonResolvent_eq_native (n : ℕ) {b z : ι → ℂ} {s : ℂ}
    (hb : b ∈ mvBetaConvergent) (hs : (s, z) ∈ carlsonResolventDomain) :
    continuedRegCarlsonResolvent n b z s = regCarlsonResolvent n b z s :=
  (exists_joint_regCarlsonResolvent (ι := ι) n).choose_spec.2 (fun i => i.elim s z) hs hb

/-- At a fixed exterior point the resolvent is the unique entire continuation of
the corresponding native Carlson average. -/
theorem isRegCarlsonContinuation_continuedRegCarlsonResolvent (n : ℕ)
    {z : ι → ℂ} {s : ℂ} (hs : (s, z) ∈ carlsonResolventDomain) :
    IsRegCarlsonContinuation (fun w => (s - w) ^ (-(n + 1 : ℤ))) z
      (fun b => continuedRegCarlsonResolvent n b z s) := by
  refine ⟨?_, fun b hb => continuedRegCarlsonResolvent_eq_native n hb hs⟩
  intro b _
  exact (analyticOnNhd_continuedRegCarlsonResolvent n (b, s, z) ⟨mem_univ _, hs⟩).comp_of_eq
    (analyticAt_id.prod analyticAt_const) rfl

end DirichletTransform
end

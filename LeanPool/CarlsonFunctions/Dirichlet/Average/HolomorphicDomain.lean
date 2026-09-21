/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.JointContinuation

/-!
# Dirichlet continuation on holomorphy domains

The domain-aware continuation predicate makes sense even on a nonconvex domain:
native integral agreement is required only when the node convex hull is inside
the domain. Values of the scalar function outside its domain are not used to
characterize the continuation there.

We prove uniqueness on connected open domains and gluing along increasing open
connected domains. Together these isolate the gluing step of the proposed
simply connected planar version of Carlson (1969), Theorem 8. Existence of the
local contour constructions on nonconvex Jordan domains, and existence of an
appropriate Jordan-domain exhaustion, are still required. The theorems here do
not assume or assert those missing existence results.

Extensions to multiply connected domains (where branches can acquire poles on
collision diagonals) and to Riemann surfaces are left open.
-/

open Complex ProbabilityTheory Set Filter Metric
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A joint continuation on a possibly nonconvex holomorphy domain. Native
agreement is required only for node tuples whose entire convex hull is in `D`. -/
def IsJointRegCarlsonContinuationOn (D : Set ℂ) (f : ℂ → ℂ)
    (G : ((ι → ℂ) × (ι → ℂ)) → ℂ) : Prop :=
  AnalyticOnNhd ℂ G {p | Set.range p.2 ⊆ D} ∧
    ∀ z, convexHull ℝ (Set.range z) ⊆ D →
      Set.EqOn (fun b => G (b, z))
        (fun b => regCarlsonDirichletAverage b z f) mvBetaConvergent

omit [Fintype ι] in
/-- A finite tuple of points in an open scalar domain varies in an open set. -/
theorem isOpen_carlsonNodeDomain [Finite ι] {D : Set ℂ} (hD : IsOpen D) :
    IsOpen {z : ι → ℂ | Set.range z ⊆ D} := by
  classical
  let _ := Fintype.ofFinite ι
  simp only [Set.range_subset_iff, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => hD.preimage (continuous_apply i)

/-- Native-compatible node tuples recover the previous fixed-node predicate. -/
theorem IsJointRegCarlsonContinuationOn.isRegCarlsonContinuation
    {D : Set ℂ} {f : ℂ → ℂ} {G : ((ι → ℂ) × (ι → ℂ)) → ℂ}
    (hG : IsJointRegCarlsonContinuationOn D f G) {z : ι → ℂ}
    (hz : convexHull ℝ (Set.range z) ⊆ D) :
    IsRegCarlsonContinuation f z (fun b => G (b, z)) := by
  refine ⟨?_, hG.2 z hz⟩
  intro b _
  exact (hG.1 (b, z) ((subset_convexHull ℝ (Set.range z)).trans hz)).comp_of_eq
    (analyticAt_id.prod analyticAt_const) rfl

/-- Restricting the scalar domain preserves a joint continuation. -/
theorem IsJointRegCarlsonContinuationOn.mono
    {D V : Set ℂ} {f : ℂ → ℂ} {G : ((ι → ℂ) × (ι → ℂ)) → ℂ}
    (hG : IsJointRegCarlsonContinuationOn D f G) (hVD : V ⊆ D) :
    IsJointRegCarlsonContinuationOn V f G :=
  ⟨hG.1.mono (fun _ hp => hp.trans hVD), fun z hz => hG.2 z (hz.trans hVD)⟩

/-- Changing the scalar function outside its holomorphy domain does not change
the continuation predicate. In particular, a total Lean function does not impose
spurious native-integral conditions outside `D`. -/
theorem IsJointRegCarlsonContinuationOn.congr_fun
    {D : Set ℂ} {f g : ℂ → ℂ} {G : ((ι → ℂ) × (ι → ℂ)) → ℂ}
    (hG : IsJointRegCarlsonContinuationOn D f G) (hfg : Set.EqOn f g D) :
    IsJointRegCarlsonContinuationOn D g G := by
  refine ⟨hG.1, ?_⟩
  intro z hz b hb
  apply (hG.2 z hz hb).trans
  apply regDirichletIntegral_congr
  intro u hu
  exact hfg (hz (carlsonAffineForm_mem_convexHull z hu))

/-- Uniqueness on a connected open scalar domain. Agreement is first obtained
on a full neighborhood of a diagonal tuple, not just on the diagonal itself. -/
theorem IsJointRegCarlsonContinuationOn.eqOn
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    {f : ℂ → ℂ} {G H : ((ι → ℂ) × (ι → ℂ)) → ℂ}
    (hG : IsJointRegCarlsonContinuationOn D f G)
    (hH : IsJointRegCarlsonContinuationOn D f H) :
    Set.EqOn G H {p | Set.range p.2 ⊆ D} := by
  obtain ⟨c, hc⟩ := hDc.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hDo c hc
  have hconn : IsPreconnected {z : ι → ℂ | Set.range z ⊆ D} := by
    convert isPreconnected_univ_pi (fun _ : ι => hDc.isPreconnected) using 1
    ext z
    simp [Set.range_subset_iff]
  intro p hp
  have hGa : AnalyticOnNhd ℂ (fun z => G (p.1, z)) {z | Set.range z ⊆ D} :=
    fun z hz => (hG.1 (p.1, z) hz).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hHa : AnalyticOnNhd ℂ (fun z => H (p.1, z)) {z | Set.range z ⊆ D} :=
    fun z hz => (hH.1 (p.1, z) hz).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  apply hGa.eqOn_of_preconnected_of_eventuallyEq hHa hconn
    (z₀ := fun _ => c) (by simpa [Set.range_subset_iff] using fun _ : ι => hc) ?_ hp
  have hnear : (fun _ : ι => c) ∈ {z : ι → ℂ | Set.range z ⊆ ball c r} := by
    simpa [Set.range_subset_iff] using fun _ : ι => (mem_ball_self hr : c ∈ ball c r)
  filter_upwards [(isOpen_carlsonNodeDomain isOpen_ball).eventually_mem hnear] with z hz
  have hzD : convexHull ℝ (Set.range z) ⊆ D :=
    (convexHull_min hz (convex_ball c r)).trans hball
  exact congrFun ((hG.isRegCarlsonContinuation hzD).eq
    (hH.isRegCarlsonContinuation hzD)) p.1

/-- The established convex-domain theorem supplies the domain-aware predicate. -/
theorem exists_isJointRegCarlsonContinuationOn_of_convex
    {D : Set ℂ} (hDo : IsOpen D) (hDc : Convex ℝ D)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ, IsJointRegCarlsonContinuationOn D f G := by
  obtain ⟨G, hG, hGeq⟩ := exists_joint_isRegCarlsonContinuation hDo hDc hf (ι := ι)
  exact ⟨G, hG, fun z hz => (hGeq z ((subset_convexHull ℝ (Set.range z)).trans hz)).2⟩

open scoped Classical in
/-- Local joint continuations on increasing connected open scalar domains glue
to a joint continuation on their union. Compactness handles both the node set
and, for native agreement, its entire convex hull. No nonempty-index assumption
is needed. This theorem does not construct the local continuations or the cover. -/
theorem exists_isJointRegCarlsonContinuationOn_iUnion
    (U : ℕ → Set ℂ) (hUo : ∀ n, IsOpen (U n))
    (hUc : ∀ n, IsConnected (U n)) (hUm : Monotone U)
    {f : ℂ → ℂ}
    (hF : ∀ n, ∃ F : ((ι → ℂ) × (ι → ℂ)) → ℂ,
      IsJointRegCarlsonContinuationOn (U n) f F) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ,
      IsJointRegCarlsonContinuationOn (⋃ n, U n) f G := by
  choose F hF using hF
  have hcompat (n m : ℕ) (p : (ι → ℂ) × (ι → ℂ))
      (hn : Set.range p.2 ⊆ U n) (hm : Set.range p.2 ⊆ U m) : F n p = F m p := by
    rcases le_total n m with hnm | hmn
    · exact (hF n).eqOn (hUo n) (hUc n) ((hF m).mono (hUm hnm)) hn
    · exact ((hF m).eqOn (hUo m) (hUc m) ((hF n).mono (hUm hmn)) hm).symm
  let G := fun p : (ι → ℂ) × (ι → ℂ) =>
    if h : ∃ n, Set.range p.2 ⊆ U n then F h.choose p else 0
  have heq (n : ℕ) (p : (ι → ℂ) × (ι → ℂ))
      (hp : Set.range p.2 ⊆ U n) : G p = F n p := by
    have h : ∃ m, Set.range p.2 ⊆ U m := ⟨n, hp⟩
    dsimp only [G]
    rw [dite_eq_left h]
    exact hcompat h.choose n p h.choose_spec hp
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    obtain ⟨n, hn⟩ := (Set.finite_range p.2).isCompact.elim_directed_cover
      U hUo hp hUm.directed_le
    apply ((hF n).1 p hn).congr
    have ho : IsOpen {q : (ι → ℂ) × (ι → ℂ) | Set.range q.2 ⊆ U n} :=
      (isOpen_carlsonNodeDomain (hUo n)).preimage continuous_snd
    filter_upwards [ho.eventually_mem hn] with q hq
    exact (heq n q hq).symm
  · intro z hz b hb
    obtain ⟨n, hn⟩ := ((Set.finite_range z).isCompact_convexHull ℝ).elim_directed_cover
      U hUo hz hUm.directed_le
    dsimp only
    rw [heq n (b, z) ((subset_convexHull ℝ (Set.range z)).trans hn)]
    exact (hF n).2 z hn hb

end DirichletTransform
end

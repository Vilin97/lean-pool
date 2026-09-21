/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.HolomorphicDomain

/-!
# The native node domain of a holomorphic Dirichlet average

For any open scalar domain `D`, not necessarily convex, the node tuples whose
convex hull lies in `D` form an open set. The regularized average continues
jointly to all Dirichlet parameters on this node set. If `D` is star-convex,
this node set is star-convex too, giving a useful uniqueness domain.

This does not extend the average to tuples whose convex hull leaves `D`.
That is the additional content of Carlson (1969), Theorem 8, on simply
connected domains; its general existence assertion remains open here.
-/

open Complex ProbabilityTheory Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The node tuples on which the scalar domain contains the whole simplex image. -/
def carlsonIntegralNodeDomain (D : Set ℂ) : Set (ι → ℂ) :=
  {z | convexHull ℝ (Set.range z) ⊆ D}

/-- Convex-hull containment can be tested on the simplex coordinates. -/
theorem mem_carlsonIntegralNodeDomain_iff {D : Set ℂ} {z : ι → ℂ} :
    z ∈ carlsonIntegralNodeDomain D ↔
      ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, carlsonAffineForm z u ∈ D := by
  constructor
  · exact fun hz u hu => hz (carlsonAffineForm_mem_convexHull z hu)
  · intro hz x hx
    obtain ⟨u, rfl⟩ := (mem_convexHull_range_iff_carlsonAffineForm z x).mp hx
    exact hz u.coordinates u.coordinates_mem

omit [Fintype ι] in
/-- Each individual node lies in the scalar domain whenever the whole hull does. -/
theorem range_subset_of_mem_carlsonIntegralNodeDomain {D : Set ℂ} {z : ι → ℂ}
    (hz : z ∈ carlsonIntegralNodeDomain D) : Set.range z ⊆ D :=
  (subset_convexHull ℝ (Set.range z)).trans hz

/-- Compactness of the simplex gives openness without requiring convexity of `D`. -/
theorem isOpen_carlsonIntegralNodeDomain {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (carlsonIntegralNodeDomain (ι := ι) D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hc : Continuous (fun p : (ι → ℂ) × (ι → ℝ) => carlsonAffineForm p.1 p.2) := by
    unfold carlsonAffineForm
    fun_prop
  have h := (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).eventually_forall_of_forall_eventually
    (x₀ := z) (P := fun w u => carlsonAffineForm w u ∈ D)
    (fun u hu => (hD.preimage hc).eventually_mem
      (mem_carlsonIntegralNodeDomain_iff.mp hz u hu))
  exact h.mono fun _ hw => mem_carlsonIntegralNodeDomain_iff.mpr hw

/-- Constant node tuples belong whenever their common value belongs. -/
theorem const_mem_carlsonIntegralNodeDomain {D : Set ℂ} {c : ℂ} (hc : c ∈ D) :
    (fun _ : ι => c) ∈ carlsonIntegralNodeDomain D := by
  apply mem_carlsonIntegralNodeDomain_iff.mpr
  intro u hu
  simpa only [carlsonAffineForm_const hu] using hc

/-- Star-convexity passes from the scalar domain to the admissible node tuples. -/
theorem starConvex_carlsonIntegralNodeDomain {D : Set ℂ} {c : ℂ}
    (hD : StarConvex ℝ c D) :
    StarConvex ℝ (fun _ : ι => c) (carlsonIntegralNodeDomain D) := by
  intro z hz a b ha hb hab
  apply mem_carlsonIntegralNodeDomain_iff.mpr
  intro u hu
  have heq : carlsonAffineForm (a • (fun _ : ι => c) + b • z) u =
      a • c + b • carlsonAffineForm z u := by
    rw [← carlsonAffineFormCLM_apply, map_add,
      LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower,
      carlsonAffineFormCLM_apply, carlsonAffineFormCLM_apply,
      carlsonAffineForm_const hu]
  rw [heq]
  exact hD (mem_carlsonIntegralNodeDomain_iff.mp hz u hu) ha hb hab

/-- The admissible node domain is connected for a nonempty star-convex scalar domain. -/
theorem isConnected_carlsonIntegralNodeDomain {D : Set ℂ} {c : ℂ}
    (hD : StarConvex ℝ c D) (hc : c ∈ D) :
    IsConnected (carlsonIntegralNodeDomain (ι := ι) D) :=
  ((starConvex_carlsonIntegralNodeDomain hD).isPathConnected
    (const_mem_carlsonIntegralNodeDomain hc)).isConnected

/-- Joint entire-parameter continuation over the native node domain of any open
holomorphy domain. Convexity of that scalar domain is not required. -/
theorem exists_joint_isRegCarlsonContinuation_on_integralDomain
    {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ,
      AnalyticOnNhd ℂ G (univ ×ˢ carlsonIntegralNodeDomain D) ∧
      ∀ z ∈ carlsonIntegralNodeDomain D,
        IsRegCarlsonContinuation f z (fun b => G (b, z)) := by
  let A := fun p : (ι → ℂ) × (ι → ℂ) => ∑ i, p.1 i * p.2 i
  have hA : AnalyticOnNhd ℂ A univ := by
    intro p _
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq
      analyticAt_fst rfl).mul
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2).comp_of_eq
        analyticAt_snd rfl)
  have hW : IsOpen (A ⁻¹' D) := hDo.preimage (continuousOn_univ.mp hA.continuousOn)
  have hH : AnalyticOnNhd ℂ (fun p => f (A p)) (A ⁻¹' D) :=
    fun p hp => (hf (A p) hp).comp_of_eq (hA p (mem_univ _)) rfl
  obtain ⟨G, hG, hGeq⟩ := exists_entire_joint_regDirichletContinuation_kernel
    (isOpen_carlsonIntegralNodeDomain hDo) hW hH (fun z hz u hu => by
      simpa only [A, Set.mem_preimage, carlsonAffineForm, mul_comm] using
        mem_carlsonIntegralNodeDomain_iff.mp hz u hu)
  refine ⟨G, hG, fun z hz => ⟨?_, ?_⟩⟩
  · intro b _
    exact (hG (b, z) ⟨mem_univ _, hz⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  · simpa only [regCarlsonDirichletAverage, carlsonAffineForm, A, mul_comm] using hGeq z hz

/-- Recognize native agreement throughout a star-convex scalar domain from
agreement on a convex open seed containing its star center. Joint holomorphy
on the full product domain is a hypothesis, not an existence conclusion. -/
theorem isJointRegCarlsonContinuationOn_of_convex_seed
    {D V : Set ℂ} {c : ℂ} (hDo : IsOpen D) (hDc : StarConvex ℝ c D)
    (hVo : IsOpen V) (hVc : Convex ℝ V) (hc : c ∈ V) (hVD : V ⊆ D)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D)
    {F : ((ι → ℂ) × (ι → ℂ)) → ℂ}
    (hF : AnalyticOnNhd ℂ F {p | Set.range p.2 ⊆ D})
    (hseed : ∀ z, Set.range z ⊆ V → ∀ b ∈ mvBetaConvergent,
      F (b, z) = regCarlsonDirichletAverage b z f) :
    IsJointRegCarlsonContinuationOn D f F := by
  obtain ⟨G, hG, hGeq⟩ := exists_joint_isRegCarlsonContinuation_on_integralDomain hDo hf (ι := ι)
  refine ⟨hF, ?_⟩
  intro z hz b hb
  have hFa : AnalyticOnNhd ℂ (fun w => F (b, w)) (carlsonIntegralNodeDomain D) :=
    fun w hw => (hF (b, w) (range_subset_of_mem_carlsonIntegralNodeDomain hw)).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hGa : AnalyticOnNhd ℂ (fun w => G (b, w)) (carlsonIntegralNodeDomain D) :=
    fun w hw => (hG (b, w) ⟨mem_univ _, hw⟩).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (isConnected_carlsonIntegralNodeDomain hDc (hVD hc)).isPreconnected
    (const_mem_carlsonIntegralNodeDomain (ι := ι) (hVD hc)) ?_
  · exact (hEq hz).trans ((hGeq z hz).eq_native hb)
  · have hnear : (fun _ : ι => c) ∈ {w : ι → ℂ | Set.range w ⊆ V} := by
      simpa [Set.range_subset_iff] using fun _ : ι => hc
    filter_upwards [(isOpen_carlsonNodeDomain hVo).eventually_mem hnear] with w hw
    have hwD : w ∈ carlsonIntegralNodeDomain D := (convexHull_min hw hVc).trans hVD
    exact (hseed w hw b hb).trans ((hGeq w hwD).eq_native hb).symm

end DirichletTransform
end

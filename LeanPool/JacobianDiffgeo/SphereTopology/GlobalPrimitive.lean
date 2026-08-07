/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path
import LeanPool.JacobianDiffgeo.Forms
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Convex.PathConnected

/-!
# The genus-0 engine: simply connected ⇒ every `Form1` has a global primitive (CC-sphere-topology)

Unit: sphere-topology (`docs/design/sphere-topology.md` §3). Forster 10.5: on a simply connected
compact surface, every holomorphic 1-form is exact (indeed zero, since a global primitive is a
holomorphic function on a compact connected surface, hence constant). The "engine" atom
(`contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id`) is shared, in spirit, with the
monodromy unit's discrete-continuation route (see module docstring of `docs/design/
sphere-topology.md` §3.1 for the reuse note) — monodromy is free to reuse it verbatim or
re-derive it.

Main declarations:
* `RS.SphereTopology.contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` — a primitive of
  `η` along the identity map is a genuine holomorphic global primitive with `mdifferential = η`.
* `RS.SphereTopology.exists_isPrimitiveAlongMap_id` — construction of the global primitive on a
  simply connected `X`, via `pathIntegral` from a fixed base point.
* `RS.SphereTopology.form1_eq_zero_of_simplyConnectedSpace`, the `Subsingleton (Form1 X)`
  instance, and the headline `RS.SphereTopology.genus_eq_zero_of_simplyConnectedSpace`.
-/

open scoped ContDiff Manifold
open Set Filter Topology IsManifold RS Metric
open scoped Convex

noncomputable section

namespace RS.SphereTopology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The "monodromy engine" atom: a primitive of `η` along the identity map is a genuine
holomorphic global primitive, and it IS `η`'s antiderivative in Forms' sense. -/
theorem contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id
    {η : RS.Form1 X} {F : X → ℂ}
    (hF : RS.IsPrimitiveAlongMap (id : X → X) η F Set.univ) :
    ∃ hF' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F, RS.mdifferential F hF' = η := by
  -- The re-charted local data at each point `x`, in the preferred chart.
  have hkey : ∀ x : X, ∃ g' : ℂ → ℂ,
      (∀ᶠ z in 𝓝 (chartAt ℂ x x), HasDerivAt g' (RS.coeffIn (chartAt ℂ x) η z) z) ∧
        F ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)] g' := by
    intro x
    obtain ⟨g', hg', hFeq⟩ := hF.rechart (Set.mem_univ x) continuousWithinAt_id
      (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
    refine ⟨g', hg', ?_⟩
    rw [nhdsWithin_univ] at hFeq
    have hcont : ContinuousAt (chartAt ℂ x).symm (chartAt ℂ x x) :=
      (chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x)
    have hval : (chartAt ℂ x).symm (chartAt ℂ x x) = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have htendsto : Tendsto (chartAt ℂ x).symm (𝓝 (chartAt ℂ x x)) (𝓝 x) := by
      have h := hcont.tendsto
      rwa [hval] at h
    have hev := htendsto.eventually hFeq
    filter_upwards [hev, (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz hzt
    simp only [id_eq] at hz
    change F ((chartAt ℂ x).symm z) = g' z
    rw [hz.2, (chartAt ℂ x).right_inv hzt]
  -- Step 1–2 of the design: `F` composed with the chart inverse is analytic (via the local
  -- primitive `g'`'s analyticity, transported through the eventual equality).
  have hana : ∀ x : X, AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
    intro x
    obtain ⟨g', hg', hFeq⟩ := hkey x
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg'
    have hg'diffOn : DifferentiableOn ℂ g' (Metric.ball (chartAt ℂ x x) ε) :=
      fun z hz => (hball z hz).differentiableAt.differentiableWithinAt
    have hg'an : AnalyticOnNhd ℂ g' (Metric.ball (chartAt ℂ x x) ε) :=
      hg'diffOn.analyticOnNhd Metric.isOpen_ball
    exact (hg'an _ (Metric.mem_ball_self hε)).congr hFeq.symm
  -- Step 3: holomorphy.
  -- named rather than inlined into the anonymous constructor: inline, the proof reaches the
  -- goal as a delayed-assignment metavariable that `rw` cannot match against
  have hFcm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F :=
    fun x => contMDiffAt_iff_analyticAt_comp_chartAt.mpr (hana x)
  refine ⟨hFcm, ?_⟩
  -- Step 4–5: coefficient matching, then `Form1.ext_coeffAt`.
  refine RS.Form1.ext_coeffAt fun x => ?_
  obtain ⟨g', hg', hFeq⟩ := hkey x
  rw [RS.coeffAt_mdifferential F hFcm x, hFeq.deriv_eq, hg'.self_of_nhds.deriv]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Construction of the global primitive on a simply connected `X`, via `pathIntegral` from a
fixed base point (well-defined by `pathIntegral_eq_of_simplyConnected`). -/
theorem exists_isPrimitiveAlongMap_id [SimplyConnectedSpace X] (x₀ : X) (η : RS.Form1 X) :
    ∃ F : X → ℂ, RS.IsPrimitiveAlongMap (id : X → X) η F Set.univ ∧ F x₀ = 0 := by
  set F : X → ℂ := fun x => RS.pathIntegral (PathConnectedSpace.somePath x₀ x) η with hF_def
  -- Path-independence (simple connectivity) transported through concatenation.
  have hstep : ∀ {p q : X} (γ : Path p q), F q = F p + RS.pathIntegral γ η := by
    intro p q γ
    change RS.pathIntegral (PathConnectedSpace.somePath x₀ q) η
        = RS.pathIntegral (PathConnectedSpace.somePath x₀ p) η + RS.pathIntegral γ η
    rw [← RS.pathIntegral_trans]
    exact RS.pathIntegral_eq_of_simplyConnected _ _ η
  have hF0 : F x₀ = 0 := by
    change RS.pathIntegral (PathConnectedSpace.somePath x₀ x₀) η = 0
    rw [RS.pathIntegral_eq_of_simplyConnected (PathConnectedSpace.somePath x₀ x₀)
      (Path.refl x₀) η]
    exact RS.pathIntegral_refl x₀ η
  refine ⟨F, fun a _ => ?_, hF0⟩
  simp only [id_eq]
  set e := chartAt ℂ a with he_def
  obtain ⟨r, hr, hballsub⟩ := Metric.isOpen_iff.mp e.open_target (e a) (mem_chart_target ℂ a)
  set c := e a with hc_def
  obtain ⟨g, hgc, hg⟩ :=
    RS.exists_hasDerivAt_ball (η.analyticOnNhd_coeffIn (chart_mem_maximalAtlas a))
      hballsub (mem_ball_self hr) (w := F a)
  refine ⟨e, chart_mem_maximalAtlas a, mem_chart_source ℂ a, g, ?_, ?_⟩
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz using hg z hz
  · rw [nhdsWithin_univ]
    have hUopen : IsOpen (e.source ∩ e ⁻¹' (ball c r)) := e.isOpen_inter_preimage isOpen_ball
    have haU : a ∈ e.source ∩ e ⁻¹' (ball c r) := ⟨mem_chart_source ℂ a, mem_ball_self hr⟩
    filter_upwards [hUopen.mem_nhds haU] with b hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨hb1, ?_⟩
    -- The chart-local straight segment from `x₀`'s neighbour `a` to `b`, transported through
    -- `e.symm`; the whole path stays in the single chart-ball `(e, ball c r)`.
    set segCplx : Path c (e b) := Path.segment c (e b) with hsegCplx_def
    have hrange : Set.range segCplx = [c -[ℝ] (e b)] := Path.range_segment c (e b)
    have hsegSub : ([c -[ℝ] (e b)] : Set ℂ) ⊆ ball c r :=
      (convex_ball c r).segment_subset (mem_ball_self hr) hb2
    have hextend_mem : ∀ u : ℝ, segCplx.extend u ∈ ball c r := by
      intro u
      apply hsegSub
      rw [← hrange]
      exact ⟨Set.projIcc 0 1 zero_le_one u, rfl⟩
    have hcontOn : ContinuousOn e.symm (Set.range segCplx) := by
      rw [hrange]
      exact e.continuousOn_symm.mono (hsegSub.trans hballsub)
    set δ0 : Path (e.symm c) (e.symm (e b)) := segCplx.map' hcontOn with hδ0_def
    have hextd : ∀ u : ℝ, δ0.extend u = e.symm (segCplx.extend u) := fun u => rfl
    have heq2 : ∀ u : ℝ, e (δ0.extend u) = segCplx.extend u := by
      intro u
      rw [hextd u, e.right_inv (hballsub (hextend_mem u))]
    have hmaps : ∀ u ∈ (Set.univ : Set ℝ),
        δ0.extend u ∈ e.source ∧ e (δ0.extend u) ∈ ball c r := by
      intro u _
      refine ⟨?_, ?_⟩
      · rw [hextd u]; exact e.map_target (hballsub (hextend_mem u))
      · rw [heq2 u]; exact hextend_mem u
    have hprim0 : RS.IsPrimitiveAlong δ0 η (fun u => g (e (δ0.extend u))) :=
      RS.isPrimitiveAlongMap_of_ball (chart_mem_maximalAtlas a) hg hmaps
    have hpi0 : RS.pathIntegral δ0 η = g (e b) - F a := by
      rw [hprim0.pathIntegral_eq]
      show g (e (δ0.extend 1)) - g (e (δ0.extend 0)) = g (e b) - F a
      rw [heq2 1, heq2 0, segCplx.extend_one, segCplx.extend_zero, hgc]
    set δ : Path a b :=
      δ0.cast (e.left_inv (mem_chart_source ℂ a)).symm (e.left_inv hb1).symm with hδ_def
    have hpi : RS.pathIntegral δ η = g (e b) - F a := by
      rw [hδ_def, RS.pathIntegral_cast]
      exact hpi0
    change F b = g (e b)
    rw [hstep δ, hpi]
    ring

omit [T2Space X] in
/-- **Forster 10.5.** On a simply connected compact surface every holomorphic 1-form vanishes. -/
theorem form1_eq_zero_of_simplyConnectedSpace [SimplyConnectedSpace X] (η : RS.Form1 X) :
    η = 0 := by
  obtain ⟨F, hFprim, -⟩ := exists_isPrimitiveAlongMap_id (Classical.arbitrary X) η
  obtain ⟨hF', hFη⟩ := contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id hFprim
  obtain ⟨v, hv⟩ := (hF'.mdifferentiable (by simp)).exists_eq_const_of_compactSpace
  subst hv
  rw [← hFη]
  have hcm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : X => v) := contMDiff_const
  have hval : RS.mdifferential (Function.const X v) hF' = RS.mdifferential (fun _ : X => v) hcm :=
    rfl
  rw [hval, RS.mdifferential_const]

instance [SimplyConnectedSpace X] : Subsingleton (RS.Form1 X) :=
  ⟨fun η η' => by
    rw [form1_eq_zero_of_simplyConnectedSpace η, form1_eq_zero_of_simplyConnectedSpace η']⟩

/-- The step-2 headline. -/
theorem genus_eq_zero_of_simplyConnectedSpace [SimplyConnectedSpace X] : genus X = 0 :=
  genus_eq_zero_iff_subsingleton.mpr inferInstance

end RS.SphereTopology

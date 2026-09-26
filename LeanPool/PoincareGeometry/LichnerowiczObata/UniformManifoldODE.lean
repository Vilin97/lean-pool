/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.UniformChartODE
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Uniform local manifold ODE intervals

The chart-lifting calculation follows Mathlib's
`exists_isMIntegralCurveAt_of_contMDiffAt`, by Winston Yin, at Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Here the chart-domain control and
time interval hold uniformly for nearby initial points.
-/

@[expose] public noncomputable section
open Function Manifold Set
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
/-- A jointly continuous manifold flow, with C1 integral curves, on a common
interval for all initial points in a neighborhood. -/
theorem exists_uniform_manifold_flow_contMDiff {v : Π x : M, TangentSpace I x} {x : M}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)) x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∃ α : M × ℝ → M, ContinuousOn α (V ×ˢ Metric.ball 0 δ) ∧
        ∀ y ∈ V, α (y, 0) = y ∧
          IsMIntegralCurveOn (fun t => α (y, t)) v (Metric.ball 0 δ) ∧
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t => α (y, t)) (Metric.ball 0 δ) := by
  let φ := extChartAt I x
  let w : E → E := fun z => tangentCoordChange I (φ.symm z) x (φ.symm z) (v (φ.symm z))
  rw [contMDiffAt_iff] at hv
  have hw : ContDiffAt ℝ 1 w (φ x) := by
    exact (hv.2.contDiffAt (by simp [I.range_eq_univ])).snd
  have htarget : φ.target ∈ 𝓝 (φ x) :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds (φ.map_source (mem_extChartAt_source x))
  obtain ⟨U, hU, hwc⟩ := contDiffAt_zero.mp (hw.of_le (by norm_num : (0 : ℕ∞ω) ≤ 1))
  obtain ⟨W, hW, δ, hδ, α, hαc, hsol⟩ := exists_uniform_chart_flow hw (Filter.inter_mem htarget hU)
  let V := φ.source ∩ φ ⁻¹' W
  have hV : V ∈ 𝓝 x :=
    Filter.inter_mem ((isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x))
      ((continuousAt_extChartAt (I := I) x) hW)
  refine ⟨V, hV, δ, hδ, fun z => φ.symm (α (φ z.1, z.2)), ?_, ?_⟩
  · have hcoord : ContinuousOn (fun z : M × ℝ => (φ z.1, z.2)) (V ×ˢ Metric.ball 0 δ) :=
      ((continuousOn_extChartAt (I := I) x).comp continuous_fst.continuousOn
        (fun z hz => hz.1.1)).prodMk continuous_snd.continuousOn
    have hα' := hαc.comp hcoord (fun z hz => ⟨hz.1.2, hz.2⟩)
    exact (contMDiffOn_extChartAt_symm (I := I) (n := 1) x).continuousOn.comp hα'
      (fun z hz => ((hsol (φ z.1) hz.1.2).2 z.2 hz.2).1.1)
  intro y hy
  let f : ℝ → E := fun t => α (φ y, t)
  obtain ⟨hf0, hf⟩ := hsol (φ y) hy.2
  change φ.symm (f 0) = y ∧ IsMIntegralCurveOn (φ.symm ∘ f) v (Metric.ball 0 δ) ∧
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (φ.symm ∘ f) (Metric.ball 0 δ)
  refine ⟨?_, ?_, ?_⟩
  · simp only [f, hf0, φ.left_inv hy.1]
  · intro t ht
    let z : M := φ.symm (f t)
    have h : HasDerivAt f (tangentCoordChange I z x z (v z)) t := (hf t ht).2
    have hf3' : f t ∈ φ.target := (hf t ht).1.1
    have hft1 : z ∈ φ.source := φ.map_target hf3'
    have hft2 := mem_extChartAt_source (I := I) z
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivWithinAt ((extChartAt I z ∘ φ.symm) ∘ f) (v z) univ t
    apply HasDerivAt.hasDerivWithinAt
    let vz : E := v z
    change HasDerivAt ((extChartAt I z ∘ φ.symm) ∘ f) vz t
    rw [← tangentCoordChange_self (I := I) (x := z) (z := z) (v := vz) hft2,
      ← tangentCoordChange_comp (x := x) (v := vz) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ (by simp [I.range_eq_univ])
    rw [← φ.right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · have hfc : ContinuousOn f (Metric.ball 0 δ) :=
      fun t ht => ((hf t ht).2.continuousAt).continuousWithinAt
    have hdc : ContinuousOn (deriv f) (Metric.ball 0 δ) := by
      apply (hwc.comp hfc (fun t ht => (hf t ht).1.2)).congr
      intro t ht
      exact (hf t ht).2.deriv
    have hfd : ContDiffOn ℝ 1 f (Metric.ball 0 δ) := by
      rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
        contDiffOn_succ_iff_deriv_of_isOpen Metric.isOpen_ball]
      exact ⟨fun t ht => (hf t ht).2.differentiableAt.differentiableWithinAt,
        by simp, contDiffOn_zero.mpr hdc⟩
    exact (contMDiffOn_extChartAt_symm x).comp hfd.contMDiffOn
      (fun t ht => (hf t ht).1.1)

/-- The individual C1 curves supplied by the jointly continuous local flow. -/
theorem exists_uniform_manifold_ode_contMDiff {v : Π x : M, TangentSpace I x} {x : M}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)) x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ V, ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Metric.ball 0 δ) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Metric.ball 0 δ) := by
  obtain ⟨V, hV, δ, hδ, α, hc, hα⟩ := exists_uniform_manifold_flow_contMDiff hv
  exact ⟨V, hV, δ, hδ, fun y hy => ⟨fun t => α (y, t), hα y hy⟩⟩

/-- The existence-only interface for the local C1 curves. -/
theorem exists_uniform_manifold_ode {v : Π x : M, TangentSpace I x} {x : M}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)) x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ V, ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Metric.ball 0 δ) := by
  obtain ⟨V, hV, δ, hδ, hsol⟩ := exists_uniform_manifold_ode_contMDiff hv
  exact ⟨V, hV, δ, hδ, fun y hy => (hsol y hy).imp (fun _ h => ⟨h.1, h.2.1⟩)⟩

/-- Any local integral curve of a C1 field is C1, by comparison with the
regular local solution. -/
theorem contMDiffAt_integralCurve [T2Space M]
    {v : Π x : M, TangentSpace I x} {γ : ℝ → M} {t : ℝ}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)) (γ t))
    (hγ : IsMIntegralCurveAt γ v t) : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t := by
  obtain ⟨V, hV, δ, hδ, hsol⟩ := exists_uniform_manifold_ode_contMDiff hv
  obtain ⟨α, hα0, hα, hαc⟩ := hsol (γ t) (mem_of_mem_nhds hV)
  have hαat := hαc.contMDiffAt (Metric.ball_mem_nhds (0 : ℝ) hδ)
  have hβc : ContMDiffAt 𝓘(ℝ, ℝ) I 1 (α ∘ (fun s : ℝ => s - t)) t := by
    have hsub : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => s - t) t :=
      ((contDiff_id.sub contDiff_const).contDiffAt).contMDiffAt
    exact hαat.comp_of_eq hsub (sub_self t)
  have hβ : IsMIntegralCurveAt (α ∘ (fun s : ℝ => s - t)) v t := by
    have h := (isMIntegralCurveAt_comp_sub (dt := t)).mpr
      (hα.isMIntegralCurveAt (Metric.ball_mem_nhds (0 : ℝ) hδ))
    simpa only [zero_add] using h
  have he := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hv hγ hβ
    (by simp only [Function.comp_apply, sub_self, hα0])
  exact he.contMDiffAt_iff.mpr hβc

/-- Compactness turns local uniform intervals into one interval valid for
every initial point of the manifold. -/
theorem exists_uniform_compact_manifold_ode [CompactSpace M]
    {v : Π x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : M, ∃ γ : ℝ → M,
      γ 0 = y ∧ IsMIntegralCurveOn γ v (Metric.ball 0 δ) := by
  classical
  choose V hV δ hδ hsol using fun x => exists_uniform_manifold_ode (hv x)
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have hmin : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε ≤ δ x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨ε, hε, he⟩ := ih
      refine ⟨min ε (δ x), lt_min hε (hδ x), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (he y hy)
  obtain ⟨ε, hε, he⟩ := hmin
  refine ⟨ε, hε, ?_⟩
  intro y
  have hy : y ∈ ⋃ x ∈ s, V x := by rw [hs]; trivial
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp hy
  obtain ⟨γ, hγ0, hγ⟩ := hsol x y hyx
  exact ⟨γ, hγ0, hγ.mono (Metric.ball_subset_ball (he x hxs))⟩

/-- Every C1 vector field on a compact boundaryless Hausdorff manifold is
complete. The uniform time bound is proved above, not an extra hypothesis. -/
theorem exists_global_integralCurve_compact [CompactSpace M] [T2Space M]
    {v : Π x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨δ, hδ, hsol⟩ := exists_uniform_compact_manifold_ode hv
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hδ _ x
  intro y
  obtain ⟨γ, hγ0, hγ⟩ := hsol y
  refine ⟨γ, hγ0, ?_⟩
  simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hγ

end LichnerowiczObata

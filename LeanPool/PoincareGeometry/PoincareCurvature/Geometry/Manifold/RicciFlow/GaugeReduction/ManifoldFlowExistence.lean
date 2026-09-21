/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Manifold integral-curve existence scaffolding toward the compact-manifold
gauge-flow construction (roadmap point 4, Item 2).

This module assembles the mathlib integral-curve API into the exact shapes the
gauge-flow construction consumes:

* `exists_local_integralCurve_Ioo` — per-point local existence of an integral
  curve on an open interval `Ioo (-ε) ε`, in the precise shape the globalization
  lemma wants;
* `exists_perpoint_integralCurve_time` — the per-point existence time on a
  compact boundaryless manifold (each point gets its own `εₓ`);
* `exists_global_integralCurve_of_uniform` — globalization: a *uniform* existence
  time immediately yields a global integral curve through every point.

The remaining gap to a *uniform* existence time (a single `ε` for all start
points) is the manifold "flow box" — continuous dependence of integral curves on
the initial point. Mathlib v4.29.1 provides this only at the Banach-space level
(`PicardLindelof`), not lifted to the manifold `IsMIntegralCurveOn` API; supplying
that neighborhood-uniform local existence lemma is the precise next increment.
-/
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Manifold Flow Existence -/

open scoped Manifold Topology
open Set Filter

namespace PoincareCurvature.ManifoldFlow
/-- **Per-point local integral curve in `Ioo` shape.** For a `C¹` vector field `v`
on a boundaryless complete manifold, every point `x₀` admits some `ε > 0` and an
integral curve through `x₀` (at time `0`) on `Ioo (-ε) ε`. This is the exact shape
the globalization lemma `exists_isMIntegralCurve_of_isMIntegralCurveOn` consumes. -/
theorem exists_local_integralCurve_Ioo {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x₀ : M) :
    ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  obtain ⟨γ, hγ0, hγat⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) (x₀ := x₀) hv.contMDiffAt
  obtain ⟨ε, hε, hon⟩ := (isMIntegralCurveAt_iff').mp hγat
  refine ⟨ε, hε, γ, hγ0, ?_⟩
  rw [show Set.Ioo (-ε) ε = Metric.ball (0 : ℝ) ε by rw [Real.ball_eq_Ioo]; simp]
  exact hon

/-- **Per-point existence time on a compact boundaryless manifold.** Each point of
a compact boundaryless manifold admits an integral curve through it on its *own*
interval `Ioo (-εₓ) εₓ`. This is the strongest statement mathlib's local-existence
API supports directly; promoting it to a *uniform* `ε` requires the manifold flow
box (see the module docstring). -/
theorem exists_perpoint_integralCurve_time {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ∀ x : M, ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) :=
  fun x => exists_local_integralCurve_Ioo hv x

/-- **Globalization.** A *uniform* existence time (a single `ε > 0` working for
every start point) immediately yields a global integral curve through every point,
by mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`. This isolates the
remaining obligation: prove the uniform-time hypothesis. -/
theorem exists_global_integralCurve_of_uniform {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (ε : ℝ) (hε : 0 < ε)
    (huniform : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε))
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
  exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε huniform x

/-- **Manifold flow box: neighborhood-uniform local existence.** For a `C¹` vector
field `v` on a boundaryless complete manifold, around every point `x₀` there is a
neighborhood `U` and a single `ε > 0` such that *every* start point `y ∈ U` admits
an integral curve through `y` on the common interval `Ioo (-ε) ε`.

This generalizes mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt` (a single
curve at one point) to all nearby start points sharing one time interval, by
lifting the continuous-flow Picard–Lindelöf theorem through a chart and using a
tube-lemma argument to keep the nearby curves inside the chart target. It is the
piece mathlib lacks (continuous dependence of integral curves on the initial point,
lifted to the manifold `IsMIntegralCurveOn` API). -/
theorem exists_nhds_uniform_integralCurve {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x₀ : M) :
    ∃ U ∈ nhds x₀, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  letI : ContinuousSMul ℝ E := IsBoundedSMul.continuousSMul
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hc : extChartAt I x₀ x₀ ∈ interior (extChartAt I x₀).target := (I.isInteriorPoint_iff).mp hx
  have hvx := (hv x₀)
  rw [contMDiffAt_iff] at hvx
  obtain ⟨_, hvx⟩ := hvx
  have hF := hvx.contDiffAt (range_mem_nhds_isInteriorPoint hx) |>.snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hflow, hcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hgc : ContinuousOn (fun t => α (extChartAt I x₀ x₀, t)) (Icc (0 - ε) (0 + ε)) :=
    hcont.comp (by fun_prop) (fun t ht => ⟨Metric.mem_closedBall_self hr.le, ht⟩)
  have hg0 : ContinuousAt (fun t => α (extChartAt I x₀ x₀, t)) 0 :=
    hgc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hαc0 : α (extChartAt I x₀ x₀, (0 : ℝ)) ∈ interior (extChartAt I x₀).target := by
    have h0 := (hflow (extChartAt I x₀ x₀) (Metric.mem_closedBall_self hr.le)).1
    simp only at h0
    rw [show α (extChartAt I x₀ x₀, (0 : ℝ)) = extChartAt I x₀ x₀ from h0]
    exact hc
  have g0W : (fun t => α (extChartAt I x₀ x₀, t)) ⁻¹' (interior (extChartAt I x₀).target) ∈ 𝓝 (0 : ℝ) :=
    hg0.preimage_mem_nhds (isOpen_interior.mem_nhds hαc0)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp g0W
  set ε₁ := min δ ε / 2 with hε₁def
  have hminpos : 0 < min δ ε := lt_min hδ hε
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; linarith
  have hε₁ltδ : ε₁ < δ := by
    rw [hε₁def]; have := min_le_left δ ε; linarith
  have hε₁ltε : ε₁ < ε := by
    rw [hε₁def]; have := min_le_right δ ε; linarith
  have htube : ∀ᶠ x in 𝓝 (extChartAt I x₀ x₀),
      ∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target := by
    apply IsCompact.eventually_forall_of_forall_eventually isCompact_Icc
    intro t htK
    have htIoo : t ∈ Ioo (0 - ε) (0 + ε) :=
      ⟨by have := htK.1; linarith, by have := htK.2; linarith⟩
    have hSnhds : (Metric.ball (extChartAt I x₀ x₀) (↑r) ×ˢ Ioo (0 - ε) (0 + ε))
        ∈ 𝓝 (extChartAt I x₀ x₀, t) :=
      (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨Metric.mem_ball_self hr, htIoo⟩
    have hcontAt : ContinuousAt α (extChartAt I x₀ x₀, t) :=
      hcont.continuousAt (mem_of_superset hSnhds
        (Set.prod_mono Metric.ball_subset_closedBall Ioo_subset_Icc_self))
    have hαW : α (extChartAt I x₀ x₀, t) ∈ interior (extChartAt I x₀).target := by
      apply hsub
      rw [Real.ball_eq_Ioo]
      exact ⟨by have := htK.1; linarith, by have := htK.2; linarith⟩
    exact hcontAt.preimage_mem_nhds (isOpen_interior.mem_nhds hαW)
  have hUmem : (extChartAt I x₀) ⁻¹'
      {x | (∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target) ∧
        x ∈ Metric.ball (extChartAt I x₀ x₀) (↑r)} ∈ 𝓝 x₀ :=
    (continuousAt_extChartAt x₀).preimage_mem_nhds
      (htube.and (Metric.ball_mem_nhds _ hr))
  refine ⟨(extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹'
      {x | (∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target) ∧
        x ∈ Metric.ball (extChartAt I x₀ x₀) (↑r)},
    Filter.inter_mem (extChartAt_source_mem_nhds x₀) hUmem, ε₁, hε₁pos, ?_⟩
  intro y hy
  set x := extChartAt I x₀ y with hxdef
  have hxball : x ∈ Metric.closedBall (extChartAt I x₀ x₀) (↑r) :=
    Metric.ball_subset_closedBall hy.2.2
  have hball2 : ∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target := hy.2.1
  set g : ℝ → E := fun s => α (x, s) with hgdef
  refine ⟨(extChartAt I x₀).symm ∘ g, ?_, ?_⟩
  · have h0 := (hflow x hxball).1
    simp only at h0
    show (extChartAt I x₀).symm (g 0) = y
    rw [hgdef]
    beta_reduce
    rw [show α (x, (0 : ℝ)) = x from h0, hxdef,
      PartialEquiv.left_inv _ hy.1]
  · intro t ht
    let xₜ : M := (extChartAt I x₀).symm (g t)
    have htIcc : t ∈ Icc (0 - ε) (0 + ε) :=
      ⟨by have := ht.1; linarith, by have := ht.2; linarith⟩
    have h : HasDerivAt g (x := t) <|
        fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
          (range I) (extChartAt I xₜ xₜ) (v xₜ) :=
      ((hflow x hxball).2 t htIcc).hasDerivAt (Icc_mem_nhds (by have := ht.1; linarith)
        (by have := ht.2; linarith))
    rw [← tangentCoordChange_def] at h
    have hf3 : g t ∈ interior (extChartAt I x₀).target :=
      hball2 t (Ioo_subset_Icc_self ht)
    have hf3' := mem_of_mem_of_subset hf3 interior_subset
    have hft1 := mem_preimage.mp <|
      mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
    have hft2 := mem_extChartAt_source (I := I) xₜ
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ g) (v xₜ) univ t
    apply HasDerivAt.hasDerivWithinAt
    let vz : E := v xₜ
    change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ g) vz t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := vz) hft2,
      ← tangentCoordChange_comp (x := x₀) (v := vz) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, hf3⟩
    rw [← (extChartAt I x₀).right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- **Neighbourhood-uniform *jointly continuous* local flow box.** Strengthening of
`exists_nhds_uniform_integralCurve` that additionally exposes the local flow map `Ψ : M → ℝ → M`
(the chart-conjugated Picard flow) together with its *joint* `(y, t)`-continuity on
`U ×ˢ Ioo (-ε) ε`.  For a `C¹` vector field `v` on a boundaryless complete manifold, every point
`x₀` has a neighbourhood `U` and time radius `ε > 0` such that each `y ∈ U` flows along an integral
curve `Ψ y` anchored at `y` (`Ψ y 0 = y`), and the total flow map `(y, t) ↦ Ψ y t` is continuous
on `U ×ˢ Ioo (-ε) ε`.  The joint continuity is inherited from the model Picard flow `α`'s
`ContinuousOn` through the chart `extChartAt I x₀` and its continuous inverse — the datum the
manifold gauge-flow orbit-confinement control (`exists_Ioo_forall_mem_of_continuousAt_source`)
consumes but that `exists_nhds_uniform_integralCurve` discards. -/
theorem exists_nhds_uniform_localFlow_continuousOn {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x₀ : M) :
    ∃ U ∈ nhds x₀, ∃ ε > 0, ∃ Ψ : M → ℝ → M,
      (∀ y ∈ U, Ψ y 0 = y ∧ IsMIntegralCurveOn (Ψ y) v (Set.Ioo (-ε) ε)) ∧
      ContinuousOn (fun p : M × ℝ => Ψ p.1 p.2) (U ×ˢ Set.Ioo (-ε) ε) := by
  letI : ContinuousSMul ℝ E := IsBoundedSMul.continuousSMul
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hc : extChartAt I x₀ x₀ ∈ interior (extChartAt I x₀).target := (I.isInteriorPoint_iff).mp hx
  have hvx := (hv x₀)
  rw [contMDiffAt_iff] at hvx
  obtain ⟨_, hvx⟩ := hvx
  have hF := hvx.contDiffAt (range_mem_nhds_isInteriorPoint hx) |>.snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hflow, hcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hgc : ContinuousOn (fun t => α (extChartAt I x₀ x₀, t)) (Icc (0 - ε) (0 + ε)) :=
    hcont.comp (by fun_prop) (fun t ht => ⟨Metric.mem_closedBall_self hr.le, ht⟩)
  have hg0 : ContinuousAt (fun t => α (extChartAt I x₀ x₀, t)) 0 :=
    hgc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hαc0 : α (extChartAt I x₀ x₀, (0 : ℝ)) ∈ interior (extChartAt I x₀).target := by
    have h0 := (hflow (extChartAt I x₀ x₀) (Metric.mem_closedBall_self hr.le)).1
    simp only at h0
    rw [show α (extChartAt I x₀ x₀, (0 : ℝ)) = extChartAt I x₀ x₀ from h0]
    exact hc
  have g0W : (fun t => α (extChartAt I x₀ x₀, t)) ⁻¹' (interior (extChartAt I x₀).target) ∈ 𝓝 (0 : ℝ) :=
    hg0.preimage_mem_nhds (isOpen_interior.mem_nhds hαc0)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp g0W
  set ε₁ := min δ ε / 2 with hε₁def
  have hminpos : 0 < min δ ε := lt_min hδ hε
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; linarith
  have hε₁ltδ : ε₁ < δ := by
    rw [hε₁def]; have := min_le_left δ ε; linarith
  have hε₁ltε : ε₁ < ε := by
    rw [hε₁def]; have := min_le_right δ ε; linarith
  have htube : ∀ᶠ x in 𝓝 (extChartAt I x₀ x₀),
      ∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target := by
    apply IsCompact.eventually_forall_of_forall_eventually isCompact_Icc
    intro t htK
    have htIoo : t ∈ Ioo (0 - ε) (0 + ε) :=
      ⟨by have := htK.1; linarith, by have := htK.2; linarith⟩
    have hSnhds : (Metric.ball (extChartAt I x₀ x₀) (↑r) ×ˢ Ioo (0 - ε) (0 + ε))
        ∈ 𝓝 (extChartAt I x₀ x₀, t) :=
      (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨Metric.mem_ball_self hr, htIoo⟩
    have hcontAt : ContinuousAt α (extChartAt I x₀ x₀, t) :=
      hcont.continuousAt (mem_of_superset hSnhds
        (Set.prod_mono Metric.ball_subset_closedBall Ioo_subset_Icc_self))
    have hαW : α (extChartAt I x₀ x₀, t) ∈ interior (extChartAt I x₀).target := by
      apply hsub
      rw [Real.ball_eq_Ioo]
      exact ⟨by have := htK.1; linarith, by have := htK.2; linarith⟩
    exact hcontAt.preimage_mem_nhds (isOpen_interior.mem_nhds hαW)
  have hUmem : (extChartAt I x₀) ⁻¹'
      {x | (∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target) ∧
        x ∈ Metric.ball (extChartAt I x₀ x₀) (↑r)} ∈ 𝓝 x₀ :=
    (continuousAt_extChartAt x₀).preimage_mem_nhds
      (htube.and (Metric.ball_mem_nhds _ hr))
  set U := (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹'
      {x | (∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target) ∧
        x ∈ Metric.ball (extChartAt I x₀ x₀) (↑r)} with hUdef
  refine ⟨U, Filter.inter_mem (extChartAt_source_mem_nhds x₀) hUmem, ε₁, hε₁pos,
    fun y t => (extChartAt I x₀).symm (α (extChartAt I x₀ y, t)), ?_, ?_⟩
  · -- integral-curve clause
    intro y hy
    rw [hUdef] at hy
    set x := extChartAt I x₀ y with hxdef
    have hxball : x ∈ Metric.closedBall (extChartAt I x₀ x₀) (↑r) :=
      Metric.ball_subset_closedBall hy.2.2
    have hball2 : ∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target := hy.2.1
    set g : ℝ → E := fun s => α (x, s) with hgdef
    refine ⟨?_, ?_⟩
    · show (extChartAt I x₀).symm (g 0) = y
      have h0 := (hflow x hxball).1
      simp only at h0
      rw [hgdef]
      beta_reduce
      rw [show α (x, (0 : ℝ)) = x from h0, hxdef,
        PartialEquiv.left_inv _ hy.1]
    · show IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ g) v (Set.Ioo (-ε₁) ε₁)
      intro t ht
      let xₜ : M := (extChartAt I x₀).symm (g t)
      have htIcc : t ∈ Icc (0 - ε) (0 + ε) :=
        ⟨by have := ht.1; linarith, by have := ht.2; linarith⟩
      have h : HasDerivAt g (x := t) <|
          fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
            (range I) (extChartAt I xₜ xₜ) (v xₜ) :=
        ((hflow x hxball).2 t htIcc).hasDerivAt (Icc_mem_nhds (by have := ht.1; linarith)
          (by have := ht.2; linarith))
      rw [← tangentCoordChange_def] at h
      have hf3 : g t ∈ interior (extChartAt I x₀).target :=
        hball2 t (Ioo_subset_Icc_self ht)
      have hf3' := mem_of_mem_of_subset hf3 interior_subset
      have hft1 := mem_preimage.mp <|
        mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
      have hft2 := mem_extChartAt_source (I := I) xₜ
      apply HasMFDerivAt.hasMFDerivWithinAt
      refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
        HasDerivWithinAt.hasFDerivWithinAt ?_⟩
      simp only [mfld_simps, hasDerivWithinAt_univ]
      change HasDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ g) (v xₜ) univ t
      apply HasDerivAt.hasDerivWithinAt
      let vz : E := v xₜ
      change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ g) vz t
      rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := vz) hft2,
        ← tangentCoordChange_comp (x := x₀) (v := vz) ⟨⟨hft2, hft1⟩, hft2⟩]
      apply HasFDerivAt.comp_hasDerivAt _ _ h
      apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
        mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
          subset_trans interior_subset (extChartAt_target_subset_range ..),
          isOpen_interior, hf3⟩
      rw [← (extChartAt I x₀).right_inv hf3']
      exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · -- joint continuity clause
    show ContinuousOn
      (fun p : M × ℝ => (extChartAt I x₀).symm (α (extChartAt I x₀ p.1, p.2)))
      (U ×ˢ Set.Ioo (-ε₁) ε₁)
    have hprod : ContinuousOn (fun p : M × ℝ => (extChartAt I x₀ p.1, p.2))
        (U ×ˢ Set.Ioo (-ε₁) ε₁) := by
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      refine (continuousOn_extChartAt x₀).comp continuousOn_fst ?_
      intro p hp
      rw [hUdef] at hp
      exact hp.1.1
    have halpha : ContinuousOn (fun p : M × ℝ => α (extChartAt I x₀ p.1, p.2))
        (U ×ˢ Set.Ioo (-ε₁) ε₁) := by
      refine hcont.comp hprod ?_
      intro p hp
      rw [hUdef] at hp
      exact ⟨Metric.ball_subset_closedBall hp.1.2.2,
        by have := hp.2.1; linarith, by have := hp.2.2; linarith⟩
    refine (continuousOn_extChartAt_symm x₀).comp halpha ?_
    intro p hp
    rw [hUdef] at hp
    exact mem_of_mem_of_subset (hp.1.2.1 p.2 (Ioo_subset_Icc_self hp.2)) interior_subset

/-- **Joint continuity at the anchor of an autonomous manifold flow — from the jointly-continuous
local flow box and integral-curve uniqueness.** For a `C¹` vector field `v` on a boundaryless
complete manifold, any flow map `Φ : ℝ → M → M` that is *anchored* (`Φ 0 y = y` for `y` near `x₀`)
and whose orbits `τ ↦ Φ τ y` solve the field ODE on a *uniform* window `Ioo (-ε₀) ε₀` (for `y` near
`x₀`) is jointly `(t, y)`-continuous at the anchor point `(0, x₀)`.  The chosen orbit is pinned to the
jointly-continuous local flow `Ψ` of `exists_nhds_uniform_localFlow_continuousOn` by uniqueness of
integral curves (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`), transferring `Ψ`'s
continuity across the coordinate swap `(t, y) ↦ (y, t)`.  This is the `ContinuousAt Φ (t₀, x)` datum
the orbit-confinement control `exists_Ioo_forall_mem_of_continuousAt_source` consumes on the
raw-manifold side of the step-(v) gauge-flow slice regularity. -/
theorem continuousAt_zero_prod_flow_of_isMIntegralCurveOn {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {Φ : ℝ → M → M} {x₀ : M} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hanchor : ∀ᶠ y in 𝓝 x₀, Φ 0 y = y)
    (horbit : ∀ᶠ y in 𝓝 x₀, IsMIntegralCurveOn (fun τ => Φ τ y) v (Set.Ioo (-ε₀) ε₀)) :
    ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x₀) := by
  obtain ⟨U₁, hU₁, ε₁, hε₁, Ψ, hΨ, hΨcont⟩ := exists_nhds_uniform_localFlow_continuousOn hv x₀
  set ε₂ := min ε₀ ε₁ with hε₂def
  have hε₂pos : 0 < ε₂ := lt_min hε₀ hε₁
  have hsub₀ : Set.Ioo (-ε₂) ε₂ ⊆ Set.Ioo (-ε₀) ε₀ :=
    Set.Ioo_subset_Ioo (by have := min_le_left ε₀ ε₁; linarith) (min_le_left ε₀ ε₁)
  have hsub₁ : Set.Ioo (-ε₂) ε₂ ⊆ Set.Ioo (-ε₁) ε₁ :=
    Set.Ioo_subset_Ioo (by have := min_le_right ε₀ ε₁; linarith) (min_le_right ε₀ ε₁)
  set W : Set M := U₁ ∩ {y | Φ 0 y = y} ∩
      {y | IsMIntegralCurveOn (fun τ => Φ τ y) v (Set.Ioo (-ε₀) ε₀)} with hWdef
  have hWnhds : W ∈ 𝓝 x₀ :=
    Filter.inter_mem (Filter.inter_mem hU₁ hanchor) horbit
  have hagree : ∀ y ∈ W, ∀ τ ∈ Set.Ioo (-ε₂) ε₂, Φ τ y = Ψ y τ := by
    intro y hyW τ hτ
    rw [hWdef] at hyW
    obtain ⟨hΨ0, hΨorbit⟩ := hΨ y hyW.1.1
    have heq : Set.EqOn (fun τ => Φ τ y) (Ψ y) (Set.Ioo (-ε₂) ε₂) := by
      refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (a := -ε₂) (b := ε₂) (t₀ := 0) ⟨by linarith, by linarith⟩ hv
        (hyW.2.mono hsub₀) (hΨorbit.mono hsub₁) ?_
      show Φ 0 y = Ψ y 0
      rw [hyW.1.2, hΨ0]
    exact heq hτ
  have hΨcontAt : ContinuousAt (fun p : M × ℝ => Ψ p.1 p.2) (x₀, 0) :=
    hΨcont.continuousAt (prod_mem_nhds hU₁ (Ioo_mem_nhds (by linarith) hε₁))
  have hswapcont : ContinuousAt (fun z : ℝ × M => ((z.2, z.1) : M × ℝ)) (0, x₀) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  have hcompAt := hΨcontAt.comp_of_eq hswapcont rfl
  refine hcompAt.congr ?_
  have htime : Set.Ioo (-ε₂) ε₂ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε₂pos
  filter_upwards [prod_mem_nhds htime hWnhds] with z hz
  exact (hagree z.2 hz.2 z.1 hz.1).symm

/-- **Uniform existence time from the flow box and compactness.** On a compact
manifold, the neighborhood-uniform flow box yields a single `ε > 0` working for
*every* start point, by extracting a finite subcover and taking the minimum
lifespan. -/
theorem exists_uniform_time_of_nhds_uniform {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [CompactSpace M]
    {v : (x : M) → TangentSpace I x}
    (hbox : ∀ x₀ : M, ∃ U ∈ nhds x₀, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧
      IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε)) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  choose U hUmem ε hεpos hprop using hbox
  have hopen : ∀ x : M, ∃ t, t ⊆ U x ∧ IsOpen t ∧ x ∈ t := fun x => mem_nhds_iff.mp (hUmem x)
  choose V hVsub hVopen hVmem using hopen
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVopen
    (fun x _ => mem_iUnion.mpr ⟨x, hVmem x⟩)
  rcases t.eq_empty_or_nonempty with hte | htne
  · subst hte
    refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x ∈ (∅ : Set M) := by
      have h := ht (mem_univ x); simp at h
    exact absurd hx (notMem_empty x)
  · refine ⟨t.inf' htne ε, ?_, fun x => ?_⟩
    · exact (Finset.lt_inf'_iff htne).mpr (fun i _ => hεpos i)
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (mem_univ x))
      obtain ⟨γ, hγ0, hγon⟩ := hprop i x (hVsub i hxi)
      refine ⟨γ, hγ0, hγon.mono ?_⟩
      have hle : t.inf' htne ε ≤ ε i := Finset.inf'_le ε hi
      exact Ioo_subset_Ioo (by linarith) hle

/-- **Uniform existence time on a compact boundaryless manifold.** For a `C¹` vector
field `v` on a compact boundaryless complete manifold, there is a single `ε > 0`
such that every point admits an integral curve through it on `Ioo (-ε) ε`. Combines
the flow box with the compactness reduction. -/
theorem exists_uniform_integralCurve_time {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) :=
  exists_uniform_time_of_nhds_uniform (fun x₀ => exists_nhds_uniform_integralCurve hv x₀)

/-- **Global integral curves on a compact boundaryless manifold.** For a `C¹` vector
field on a compact boundaryless complete manifold, every point lies on a *global*
integral curve. This is the assembled flow-existence result the gauge-flow
construction needs: flow box ⇒ uniform time ⇒ globalization. -/
theorem exists_global_integralCurve_compact {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, huniform⟩ := exists_uniform_integralCurve_time hv
  exact exists_global_integralCurve_of_uniform hv ε hε huniform x

/-! ### Time-dependent integral curves via autonomization

A *time-dependent* field `X : ℝ → (x : M) → TangentSpace I x` is integrated by
autonomizing: on the product manifold `ℝ × M`, the *autonomous* field
`(s, x) ↦ (1, X s x)` has integral curves whose first coordinate tracks the time
parameter, so projecting to `M` yields a time-dependent integral curve. The product
tangent space splits definitionally,
`TangentSpace (𝓘(ℝ,ℝ).prod I) (s, x) = ℝ × TangentSpace I x`, so the two fiber
components are handled independently. -/

/-- **Autonomization projection.** An integral curve `Γ` of the autonomous field
`(1, X · ·)` on `ℝ × M` whose first coordinate is the identity (`(Γ t).1 = t`)
projects, via the second coordinate, to a *time-dependent* integral curve of `X` on
`M`: `∂ₜ (Γ ·).2 = X t (Γ t).2`. -/
theorem isTimeDependentIntegralCurve_of_autonomous {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ}
    (hfst : ∀ t ∈ s, (Γ t).1 = t)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => (Γ τ).2) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Γ t).2))) := by
  letI : ContinuousSMul ℝ ℝ := ContinuousMul.to_continuousSMul
  intro t ht
  have hsnd : HasMFDerivAt ((𝓘(ℝ, ℝ)).prod I) I Prod.snd (Γ t)
      (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ t).1) (TangentSpace I (Γ t).2)) :=
    hasMFDerivAt_snd (Γ t)
  have hcomp := hsnd.comp_hasMFDerivWithinAt t (hΓ t ht)
  have hfun : (Prod.snd ∘ Γ) = (fun τ => (Γ τ).2) := rfl
  rw [hfun] at hcomp
  have hclm : (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ t).1)
        (TangentSpace I (Γ t).2)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))
      = (1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Γ t).2)) := by
    ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, hfst t ht]
    change (1 : ℝ) • X t (Γ t).2 = _
    exact one_smul _ _
  exact hclm ▸ hcomp

/-- **The time component tracks the parameter.** An integral curve `Γ` of the
autonomous field `(1, X · ·)` on `ℝ × M` over a preconnected open set `s ∋ 0`, with
`(Γ 0).1 = 0`, has `(Γ t).1 = t` throughout `s` — because its first coordinate has
constant derivative `1`. -/
theorem autonomous_fst_eq_id {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ}
    (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hconn : IsPreconnected s)
    (hΓ0 : (Γ 0).1 = 0)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, (Γ t).1 = t := by
  letI : ContinuousSMul ℝ ℝ := ContinuousMul.to_continuousSMul
  set φ : ℝ → ℝ := fun τ => (Γ τ).1 with hφ
  have hd : ∀ τ ∈ s, HasDerivWithinAt φ 1 s τ := by
    intro τ hτ
    have hcomp :=
      ((hasMFDerivAt_fst (Γ τ)).hasMFDerivWithinAt (s := univ)).comp τ (hΓ τ hτ)
        (by rw [preimage_univ]; exact subset_univ s)
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hcomp
    let D : ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ τ).1)
        (TangentSpace I (Γ τ).2)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (((1 : ℝ), X (Γ τ).1 (Γ τ).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ τ)))
    have hcomp' : HasFDerivWithinAt (Prod.fst ∘ Γ) D s τ := hcomp
    have hdw := hcomp'.hasDerivWithinAt
    have hfun : (Prod.fst ∘ Γ) = φ := rfl
    rw [hfun] at hdw
    refine hdw.congr_deriv ?_
    show ((ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ τ).1) (TangentSpace I (Γ τ).2)).comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((1 : ℝ), X (Γ τ).1 (Γ τ).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ τ))))
        (1 : ℝ) = (1 : ℝ)
    change (1 : ℝ) * 1 = 1
    exact mul_one _
  have hderiv : ∀ τ ∈ s, deriv φ τ = 1 := fun τ hτ =>
    ((hd τ hτ).hasDerivAt (hs.mem_nhds hτ)).deriv
  have hdiff : DifferentiableOn ℝ φ s := fun τ hτ => (hd τ hτ).differentiableWithinAt
  have hg : ∀ τ ∈ s, deriv (fun y : ℝ => y) τ = 1 := fun τ _ => by simp
  have heq : EqOn φ (fun y : ℝ => y) s := by
    refine hs.eqOn_of_deriv_eq hconn hdiff differentiable_id.differentiableOn ?_ h0 ?_
    · intro τ hτ
      rw [hderiv τ hτ, hg τ hτ]
    · exact hΓ0
  intro t ht
  simpa [hφ] using heq ht

/-- **The time component tracks the parameter, anchored at an arbitrary start time.**
Generalises `autonomous_fst_eq_id` (anchor `t₀ = 0`): an integral curve `Γ` of the
autonomous field `(1, X · ·)` on a preconnected open set `s ∋ 0`, with
`(Γ 0).1 = t₀`, has `(Γ t).1 = t₀ + t` throughout `s` — the first coordinate has
constant derivative `1`, so it is the affine map `t ↦ t₀ + t`. This lets an
autonomous curve *anchored at time `t₀`* (not `0`) be recognised, after the time
shift `σ ↦ σ - t₀`, as a genuine time-dependent integral curve. -/
theorem autonomous_fst_eq_add {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ} {t₀ : ℝ}
    (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hconn : IsPreconnected s)
    (hΓ0 : (Γ 0).1 = t₀)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, (Γ t).1 = t₀ + t := by
  letI : ContinuousSMul ℝ ℝ := ContinuousMul.to_continuousSMul
  set φ : ℝ → ℝ := fun τ => (Γ τ).1 with hφ
  have hd : ∀ τ ∈ s, HasDerivWithinAt φ 1 s τ := by
    intro τ hτ
    have hcomp :=
      ((hasMFDerivAt_fst (Γ τ)).hasMFDerivWithinAt (s := univ)).comp τ (hΓ τ hτ)
        (by rw [preimage_univ]; exact subset_univ s)
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hcomp
    let D : ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ τ).1)
        (TangentSpace I (Γ τ).2)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (((1 : ℝ), X (Γ τ).1 (Γ τ).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ τ)))
    have hcomp' : HasFDerivWithinAt (Prod.fst ∘ Γ) D s τ := hcomp
    have hdw := hcomp'.hasDerivWithinAt
    have hfun : (Prod.fst ∘ Γ) = φ := rfl
    rw [hfun] at hdw
    refine hdw.congr_deriv ?_
    show ((ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ τ).1) (TangentSpace I (Γ τ).2)).comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((1 : ℝ), X (Γ τ).1 (Γ τ).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ τ))))
        (1 : ℝ) = (1 : ℝ)
    change (1 : ℝ) * 1 = 1
    exact mul_one _
  have hderiv : ∀ τ ∈ s, deriv φ τ = 1 := fun τ hτ =>
    ((hd τ hτ).hasDerivAt (hs.mem_nhds hτ)).deriv
  have hdiff : DifferentiableOn ℝ φ s := fun τ hτ => (hd τ hτ).differentiableWithinAt
  have hg : ∀ τ ∈ s, deriv (fun y : ℝ => t₀ + y) τ = 1 := fun τ _ =>
    ((hasDerivAt_id τ).const_add t₀).deriv
  have heq : EqOn φ (fun y : ℝ => t₀ + y) s := by
    refine hs.eqOn_of_deriv_eq hconn hdiff (by fun_prop) ?_ h0 ?_
    · intro τ hτ
      rw [hderiv τ hτ, hg τ hτ]
    · show φ 0 = t₀ + 0
      rw [add_zero]; exact hΓ0
  intro t ht
  simpa [hφ] using heq ht

/-- **Time-dependent integral curve from an autonomous one** (combined form): if
`Γ` is an autonomous integral curve of `(1, X)` on a preconnected open `s ∋ 0` with
`(Γ 0).1 = 0`, then `(Γ ·).2` is a time-dependent integral curve of `X` on `s`. -/
theorem isTimeDependentIntegralCurve_of_autonomous_of_fst {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ}
    (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hconn : IsPreconnected s)
    (hΓ0 : (Γ 0).1 = 0)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => (Γ τ).2) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Γ t).2))) :=
  isTimeDependentIntegralCurve_of_autonomous (autonomous_fst_eq_id hs h0 hconn hΓ0 hΓ) hΓ

/-! ### Time-dependent integral-curve existence and uniqueness

Assembling the flow box on `ℝ × M` with the autonomization bridge gives existence
and uniqueness of time-dependent integral curves on a (boundaryless, T2) manifold.
Existence uses the *non-compact* flow box per start point (since `ℝ × M` is never
compact); uniqueness uses mathlib's autonomous uniqueness on the product. -/

/-- **Per-point time-dependent local existence.** For a jointly-`C¹` time-dependent
field `X` on a boundaryless complete manifold, every start point `x` (at time `0`)
admits a time-dependent integral curve of `X` on some `Ioo (-ε) ε`. -/
theorem exists_timeDependent_integralCurve {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (x : M) :
    ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  obtain ⟨U, hU, ε, hε, hcurve⟩ := exists_nhds_uniform_integralCurve (I := (𝓘(ℝ, ℝ)).prod I) hX (0, x)
  have hmem : ((0 : ℝ), x) ∈ U := mem_of_mem_nhds hU
  obtain ⟨Γ, hΓ0, hΓint⟩ := hcurve ((0 : ℝ), x) hmem
  refine ⟨ε, hε, fun τ => (Γ τ).2, ?_, ?_⟩
  · show (Γ 0).2 = x
    rw [hΓ0]
  · have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
    have hΓ0fst : (Γ 0).1 = 0 := by rw [hΓ0]
    refine isTimeDependentIntegralCurve_of_autonomous_of_fst
      isOpen_Ioo h0 isPreconnected_Ioo hΓ0fst ?_
    intro t ht
    exact hΓint t ht

/-- The continuous-linear-map identity underlying the lift of an `M`-curve to the
product manifold: `(id, (1).smulRight v) = (1).smulRight (1, v)`. -/
private theorem timeDependent_lift_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (v : E') :
    (ContinuousLinearMap.id ℝ ℝ).prod ((1 : ℝ →L[ℝ] ℝ).smulRight v)
      = (1 : ℝ →L[ℝ] ℝ).smulRight ((1, v) : ℝ × E') := by
  apply ContinuousLinearMap.ext
  intro r
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply]

/-- **Reverse autonomization lift.** A time-dependent integral curve `γ` of `X` on
`M` lifts to an autonomous integral curve `τ ↦ (τ, γ τ)` of `(1, X)` on `ℝ × M`. -/
theorem autonomousLift_hasMFDerivWithinAt {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ} {t : ℝ} (ht : t ∈ s)
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) :
    HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) (fun τ => (τ, γ τ)) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), X t (γ t)) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (t, γ t))) := by
  have hid : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (id : ℝ → ℝ) s t
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) := hasMFDerivWithinAt_id s t
  have h := hid.prodMk hγ
  refine h.congr_mfderiv ?_
  refine ContinuousLinearMap.ext fun r => ?_
  refine Prod.ext ?_ rfl
  let r' : ℝ := r
  change r' = r' * 1
  exact (mul_one _).symm


/-- **Joint continuity at the anchor of a *time-dependent* manifold flow — via autonomisation and the
jointly-continuous flow box.** For a jointly-`C¹` time-dependent field `X` on a boundaryless complete
`T2` manifold, any flow map `Φ : ℝ → M → M` that is anchored (`Φ 0 y = y` for `y` near `x₀`) and whose
orbits `τ ↦ Φ τ y` solve the time-dependent ODE on a *uniform* window `Ioo (-ε₀) ε₀` (for `y` near
`x₀`) is jointly `(t, y)`-continuous at the anchor `(0, x₀)`.  The lifted orbit `τ ↦ (τ, Φ τ y)` is a
genuine integral curve of the autonomous field `(1, X · ·)` on `ℝ × M` (`autonomousLift_hasMFDerivWithinAt`),
so it is pinned by uniqueness (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`) to the
jointly-continuous local flow `Ψ` of `exists_nhds_uniform_localFlow_continuousOn` at the lifted anchor
`(0, y)`, whence `Φ τ y = (Ψ (0, y) τ).2` inherits `Ψ`'s continuity.  This is the `ContinuousAt Φ (0, x)`
datum the raw-manifold orbit-confinement control `exists_Ioo_forall_mem_of_continuousAt_source` consumes
for the compact time-dependent gauge flow of Item 2. -/
theorem continuousAt_zero_prod_timeDependent_flow_of_hasMFDerivWithinAt {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {Φ : ℝ → M → M} {x₀ : M} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hanchor : ∀ᶠ y in 𝓝 x₀, Φ 0 y = y)
    (horbit : ∀ᶠ y in 𝓝 x₀, ∀ τ ∈ Set.Ioo (-ε₀) ε₀,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ => Φ σ y) (Set.Ioo (-ε₀) ε₀) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) :
    ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x₀) := by
  obtain ⟨Ũ, hŨ, ε₁, hε₁, Ψ, hΨ, hΨcont⟩ :=
    exists_nhds_uniform_localFlow_continuousOn (I := (𝓘(ℝ, ℝ)).prod I) hX (0, x₀)
  set ε₂ := min ε₀ ε₁ with hε₂def
  have hε₂pos : 0 < ε₂ := lt_min hε₀ hε₁
  have hsub₀ : Set.Ioo (-ε₂) ε₂ ⊆ Set.Ioo (-ε₀) ε₀ :=
    Set.Ioo_subset_Ioo (by have := min_le_left ε₀ ε₁; linarith) (min_le_left ε₀ ε₁)
  have hsub₁ : Set.Ioo (-ε₂) ε₂ ⊆ Set.Ioo (-ε₁) ε₁ :=
    Set.Ioo_subset_Ioo (by have := min_le_right ε₀ ε₁; linarith) (min_le_right ε₀ ε₁)
  have h0mem : (fun y : M => ((0 : ℝ), y)) ⁻¹' Ũ ∈ 𝓝 x₀ :=
    ((continuous_const.prodMk continuous_id).continuousAt).preimage_mem_nhds hŨ
  set W : Set M := ((fun y : M => ((0 : ℝ), y)) ⁻¹' Ũ) ∩ {y | Φ 0 y = y} ∩
      {y | ∀ τ ∈ Set.Ioo (-ε₀) ε₀,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ => Φ σ y) (Set.Ioo (-ε₀) ε₀) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))} with hWdef
  have hWnhds : W ∈ 𝓝 x₀ :=
    Filter.inter_mem (Filter.inter_mem h0mem hanchor) horbit
  have hagree : ∀ y ∈ W, ∀ τ ∈ Set.Ioo (-ε₂) ε₂, Φ τ y = (Ψ (0, y) τ).2 := by
    intro y hyW τ hτ
    rw [hWdef] at hyW
    obtain ⟨hΨ0, hΨorbit⟩ := hΨ (0, y) hyW.1.1
    have hΓint : IsMIntegralCurveOn (fun σ => ((σ, Φ σ y) : ℝ × M))
        (fun q : ℝ × M => ((1 : ℝ), X q.1 q.2)) (Set.Ioo (-ε₀) ε₀) :=
      fun t ht => autonomousLift_hasMFDerivWithinAt ht (hyW.2 t ht)
    have heq : Set.EqOn (fun σ => ((σ, Φ σ y) : ℝ × M)) (Ψ (0, y)) (Set.Ioo (-ε₂) ε₂) := by
      refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (a := -ε₂) (b := ε₂) (t₀ := 0) ⟨by linarith, by linarith⟩ hX
        (hΓint.mono hsub₀) (hΨorbit.mono hsub₁) ?_
      show ((0, Φ 0 y) : ℝ × M) = Ψ (0, y) 0
      rw [hyW.1.2, hΨ0]
    have hh : ((τ, Φ τ y) : ℝ × M) = Ψ (0, y) τ := heq hτ
    exact congrArg Prod.snd hh
  have hΨcontAt : ContinuousAt (fun P : (ℝ × M) × ℝ => Ψ P.1 P.2) ((0, x₀), 0) :=
    hΨcont.continuousAt (prod_mem_nhds hŨ (Ioo_mem_nhds (by linarith) hε₁))
  have hembed : ContinuousAt (fun z : ℝ × M => ((((0 : ℝ), z.2), z.1) : (ℝ × M) × ℝ)) (0, x₀) :=
    ((continuous_const.prodMk continuous_snd).prodMk continuous_fst).continuousAt
  have hcomp := hΨcontAt.comp_of_eq hembed rfl
  refine (hcomp.snd).congr ?_
  have htime : Set.Ioo (-ε₂) ε₂ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε₂pos
  filter_upwards [prod_mem_nhds htime hWnhds] with z hz
  exact (hagree z.2 hz.2 z.1 hz.1).symm

/-- **Uniqueness of time-dependent integral curves.** Two time-dependent integral
curves of a jointly-`C¹` field `X` on a boundaryless T2 manifold that agree at
`t = 0` agree throughout `Ioo a b` (with `0 ∈ Ioo a b`). Proved by lifting to
autonomous curves on `ℝ × M` and applying mathlib's autonomous uniqueness. -/
theorem timeDependent_integralCurve_unique {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {γ γ' : ℝ → M} {a b : ℝ} (hab : (0 : ℝ) ∈ Set.Ioo a b)
    (hγ : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hγ' : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ' (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ' t))))
    (h0 : γ 0 = γ' 0) :
    Set.EqOn γ γ' (Set.Ioo a b) := by
  set w : (x : ℝ × M) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) x :=
    fun p => ((1 : ℝ), X p.1 p.2) with hw
  set Γ : ℝ → ℝ × M := fun t => (t, γ t) with hΓdef
  set Γ' : ℝ → ℝ × M := fun t => (t, γ' t) with hΓ'def
  have hΓint : IsMIntegralCurveOn Γ w (Set.Ioo a b) := by
    intro t ht
    exact autonomousLift_hasMFDerivWithinAt ht (hγ t ht)
  have hΓ'int : IsMIntegralCurveOn Γ' w (Set.Ioo a b) := by
    intro t ht
    exact autonomousLift_hasMFDerivWithinAt ht (hγ' t ht)
  have hv : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun x => (⟨x, w x⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) := hX
  have hstart : Γ 0 = Γ' 0 := by simp [hΓdef, hΓ'def, h0]
  have heq : Set.EqOn Γ Γ' (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hab hv hΓint hΓ'int hstart
  intro t ht
  have h2 : (Γ t).2 = (Γ' t).2 := by rw [heq ht]
  simpa [hΓdef, hΓ'def] using h2

/-! ### Flow group law and mutual inverse

For an *autonomous* `C¹` field on a boundaryless T2 manifold, the flow `Φ` (with
`Φ 0 x = x` and each `τ ↦ Φ τ x` an integral curve) satisfies the group law
`Φ (s+t) = Φ s ∘ Φ t`, hence `Φ t` and `Φ (-t)` are mutual inverses. These follow
from integral-curve *uniqueness* alone — no smooth dependence on the initial
condition is needed — and supply the mutual-inverse data that
`SmoothSelfDiffeomorph3Family.ofInverse` consumes. -/

/-- **Flow group law.** For an autonomous `C¹` field, the flow satisfies
`Φ (s + t) x = Φ s (Φ t x)`, by uniqueness of the integral curve through `Φ t x`. -/
theorem flow_group_law {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Φ t x) v)
    (s t : ℝ) (x : M) :
    Φ (s + t) x = Φ s (Φ t x) := by
  have hγ1 : IsMIntegralCurve (fun τ => Φ (τ + t) x) v := by
    simpa [Function.comp_def] using (hcurve x).comp_add t
  have hγ2 : IsMIntegralCurve (fun τ => Φ τ (Φ t x)) v := hcurve (Φ t x)
  have heq : (fun τ => Φ (τ + t) x) = (fun τ => Φ τ (Φ t x)) :=
    isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
      (fun τ => BoundarylessManifold.isInteriorPoint) hv hγ1 hγ2
      (by simp [hanchor])
  exact congrFun heq s

/-- The flow's left/right inverses from the group law (pure algebra). -/
theorem flow_leftInverse {M : Type*} {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : M), Φ (s + t) x = Φ s (Φ t x)) (t : ℝ) :
    Function.LeftInverse (Φ (-t)) (Φ t) :=
  fun x => by rw [← hgroup (-t) t x, neg_add_cancel, hanchor]

theorem flow_rightInverse {M : Type*} {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : M), Φ (s + t) x = Φ s (Φ t x)) (t : ℝ) :
    Function.RightInverse (Φ (-t)) (Φ t) :=
  fun x => by rw [← hgroup t (-t) x, add_neg_cancel, hanchor]

/-- **The complete mutual-inverse package** for `SmoothSelfDiffeomorph3Family.ofInverse`:
from the flow's defining properties, both `Φ t` and `Φ (-t)` are mutual inverses for
every `t`. Derived from integral-curve uniqueness; no smooth dependence needed. -/
theorem flow_inverse_package {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Φ t x) v) :
    (∀ t, Function.LeftInverse (Φ (-t)) (Φ t)) ∧ (∀ t, Function.RightInverse (Φ (-t)) (Φ t)) := by
  have hgroup : ∀ (s t : ℝ) (x : M), Φ (s + t) x = Φ s (Φ t x) :=
    fun s t x => flow_group_law hv hanchor hcurve s t x
  exact ⟨fun t => flow_leftInverse hanchor hgroup t,
         fun t => flow_rightInverse hanchor hgroup t⟩

/-! ### Uniform time-dependent local flow on a compact manifold

The DeTurck gauge field is *time-dependent*. Integrating it uniformly over all
start points requires autonomizing to the product `ℝ × M`, which is *never*
compact, so `exists_uniform_integralCurve_time` (whole space compact) does not
apply. What *is* compact is the **initial-time slice** `{0} × M`; a uniform lifespan
over that slice suffices, because every start point `x` enters the autonomization
as `(0, x)`. This subsection supplies the compact-*slice* uniform-time reduction and
assembles the compact-manifold time-dependent local flow existence the gauge-flow
construction consumes. -/

/-- **Uniform existence time over a compact subset from the flow box.** The
neighborhood-uniform flow box yields, over any *compact subset* `S` of a (possibly
noncompact) manifold, a single `ε > 0` working for every start point in `S`, by
extracting a finite subcover of `S` and taking the minimum lifespan. This is the
compact-*slice* refinement of `exists_uniform_time_of_nhds_uniform` (which needs the
whole space compact); applied to the compact initial-time slice `{0} × M` of the
noncompact autonomization space `ℝ × M`, it integrates a *time-dependent* field with
a single uniform lifespan. -/
theorem exists_uniform_time_of_nhds_uniform_on_compact {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {v : (x : M) → TangentSpace I x}
    (hbox : ∀ x₀ : M, ∃ U ∈ nhds x₀, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧
      IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε))
    {S : Set M} (hS : IsCompact S) :
    ∃ ε > 0, ∀ x ∈ S, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  choose U hUmem ε hεpos hprop using hbox
  have hopen : ∀ x : M, ∃ t, t ⊆ U x ∧ IsOpen t ∧ x ∈ t := fun x => mem_nhds_iff.mp (hUmem x)
  choose V hVsub hVopen hVmem using hopen
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover V hVopen
    (fun x _ => mem_iUnion.mpr ⟨x, hVmem x⟩)
  rcases t.eq_empty_or_nonempty with hte | htne
  · subst hte
    refine ⟨1, one_pos, fun x hx => ?_⟩
    have h := ht hx; simp at h
  · refine ⟨t.inf' htne ε, (Finset.lt_inf'_iff htne).mpr (fun i _ => hεpos i), fun x hx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    obtain ⟨γ, hγ0, hγon⟩ := hprop i x (hVsub i hxi)
    refine ⟨γ, hγ0, hγon.mono ?_⟩
    have hle : t.inf' htne ε ≤ ε i := Finset.inf'_le ε hi
    exact Ioo_subset_Ioo (by linarith) hle

/-- **Uniform time-dependent local flow existence on a compact manifold.** For a
jointly-`C¹` time-dependent field `X` on a compact boundaryless complete manifold,
there is a *single* `ε > 0` such that every start point `x` (at time `0`) admits a
time-dependent integral curve of `X` on the common interval `Ioo (-ε) ε`. Because the
DeTurck gauge field is time-dependent, this — not the autonomous
`exists_uniform_integralCurve_time` — is the existence core the gauge flow consumes.
Proved by autonomizing to the noncompact `ℝ × M` and taking the uniform lifespan over
the *compact initial-time slice* `{0} × M` via
`exists_uniform_time_of_nhds_uniform_on_compact`, then projecting through
`isTimeDependentIntegralCurve_of_autonomous_of_fst`. -/
theorem exists_uniform_timeDependent_integralCurve_time {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  have hScompact : IsCompact (({(0 : ℝ)} ×ˢ (Set.univ : Set M)) : Set (ℝ × M)) :=
    isCompact_singleton.prod isCompact_univ
  obtain ⟨ε, hε, huniform⟩ := exists_uniform_time_of_nhds_uniform_on_compact
    (fun p => exists_nhds_uniform_integralCurve (I := (𝓘(ℝ, ℝ)).prod I) hX p) hScompact
  refine ⟨ε, hε, fun x => ?_⟩
  obtain ⟨Γ, hΓ0, hΓon⟩ := huniform (0, x) (by simp)
  refine ⟨fun τ => (Γ τ).2, by simp [hΓ0], ?_⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hΓ0fst : (Γ 0).1 = 0 := by rw [hΓ0]
  exact isTimeDependentIntegralCurve_of_autonomous_of_fst
    isOpen_Ioo h0 isPreconnected_Ioo hΓ0fst (fun t ht => hΓon t ht)

/-- **Bundled uniform time-dependent flow on a compact manifold.** Packages
`exists_uniform_timeDependent_integralCurve_time` into a flow map `Φ : ℝ → M → M`
with `Φ 0 = id` such that, for every `x`, the orbit `τ ↦ Φ τ x` is a time-dependent
integral curve of `X` on the common interval `Ioo (-ε) ε`. This is the anchored
integral-curve family the compact-manifold gauge-flow construction is built on. -/
theorem exists_timeDependent_flow_compact {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))) := by
  obtain ⟨ε, hε, huniform⟩ := exists_uniform_timeDependent_integralCurve_time hX
  choose γ hγ0 hγon using huniform
  exact ⟨ε, hε, fun t x => γ x t, hγ0, fun x t ht => hγon x t ht⟩

/-- **Compact time-dependent gauge flow with joint continuity at the anchor.** Strengthening of
`exists_timeDependent_flow_compact`: on a compact boundaryless `T2` manifold, the uniform-lifespan
time-dependent flow `Φ` of a jointly-`C¹` field `X` additionally has, at *every* base point `x`, a
jointly `(t, y)`-continuous total flow map at the anchor `(0, x)`
(`continuousAt_zero_prod_timeDependent_flow_of_hasMFDerivWithinAt`, the anchor/orbit hypotheses being
the flow's own `∀ x` clauses).  This is precisely the `ContinuousAt Φ (0, x)` datum
`ManifoldFlow.exists_Ioo_forall_mem_of_continuousAt_source` consumes to confine each orbit to a chart
patch over a short window (`hγ_src`), the raw-manifold input of the GAP-1 step-(v) slice-`C³`
capstone. -/
theorem exists_timeDependent_flow_compact_continuousAt {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ x, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) := by
  obtain ⟨ε, hε, Φ, hanchor, horbit⟩ := exists_timeDependent_flow_compact hX
  refine ⟨ε, hε, Φ, hanchor, horbit, fun x => ?_⟩
  exact continuousAt_zero_prod_timeDependent_flow_of_hasMFDerivWithinAt hX hε
    (Filter.Eventually.of_forall hanchor) (Filter.Eventually.of_forall horbit)

/-- **Uniqueness of time-dependent integral curves anchored at any interior time.**
For a jointly-`C¹` time-dependent field `X` on a boundaryless T2 manifold, two
time-dependent integral curves on `Ioo a b` that agree at a *single interior time*
`t₀ ∈ Ioo a b` agree on all of `Ioo a b`. Generalises
`timeDependent_integralCurve_unique` (anchor `t₀ = 0`) by anchoring at an arbitrary
interior time; proved by lifting to autonomous curves on `ℝ × M` and applying
mathlib's autonomous uniqueness at `t₀`. Anchoring at an arbitrary time is what
yields injectivity of each time-`t` flow map. -/
theorem timeDependent_integralCurve_eqOn_of_eq {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {γ γ' : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hγ' : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ' (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ' t))))
    (h0 : γ t₀ = γ' t₀) :
    Set.EqOn γ γ' (Set.Ioo a b) := by
  set w : (x : ℝ × M) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) x :=
    fun p => ((1 : ℝ), X p.1 p.2) with hw
  set Γ : ℝ → ℝ × M := fun t => (t, γ t) with hΓdef
  set Γ' : ℝ → ℝ × M := fun t => (t, γ' t) with hΓ'def
  have hΓint : IsMIntegralCurveOn Γ w (Set.Ioo a b) := fun t ht =>
    autonomousLift_hasMFDerivWithinAt ht (hγ t ht)
  have hΓ'int : IsMIntegralCurveOn Γ' w (Set.Ioo a b) := fun t ht =>
    autonomousLift_hasMFDerivWithinAt ht (hγ' t ht)
  have hstart : Γ t₀ = Γ' t₀ := by simp [hΓdef, hΓ'def, h0]
  have heq : Set.EqOn Γ Γ' (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hX hΓint hΓ'int hstart
  intro t ht
  have h2 : (Γ t).2 = (Γ' t).2 := by rw [heq ht]
  simpa [hΓdef, hΓ'def] using h2

/-- **Injectivity of each time-`t` flow map.** For a jointly-`C¹` time-dependent
field `X` on a compact boundaryless T2 manifold, if a flow `Φ` is anchored
(`Φ 0 = id`) with every orbit `τ ↦ Φ τ x` a time-dependent integral curve of `X` on
`Ioo (-ε) ε`, then for each `t ∈ Ioo (-ε) ε` the time-`t` map `x ↦ Φ t x` is
injective: two orbits agreeing at time `t` agree everywhere on `Ioo (-ε) ε`, in
particular at time `0`, where the anchor reads off the two start points. This is the
diffeomorphism-onto-image (injectivity) half the compact-manifold gauge flow of
Item 2 consumes. -/
theorem timeDependent_flow_injective {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε : ℝ} (hε : 0 < ε) {Φ : ℝ → M → M} (hanchor : ∀ x, Φ 0 x = x)
    (hflow : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    Function.Injective (Φ t) := by
  intro x y hxy
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have heq : Set.EqOn (fun τ => Φ τ x) (fun τ => Φ τ y) (Set.Ioo (-ε) ε) :=
    timeDependent_integralCurve_eqOn_of_eq hX ht (hflow x) (hflow y) hxy
  have h0 := heq h0mem
  simpa [hanchor] using h0

/-- **Bundled injective time-dependent flow on a compact manifold.** Combines
`exists_timeDependent_flow_compact` with `timeDependent_flow_injective`: for a
jointly-`C¹` time-dependent field `X` on a compact boundaryless T2 manifold there is a
uniform `ε > 0` and an anchored flow `Φ` (`Φ 0 = id`) whose orbits `τ ↦ Φ τ x` solve
the field's ODE on `Ioo (-ε) ε` and whose every time-`t` slice `x ↦ Φ t x` is
injective. This is the compact-manifold time-dependent local flow with injective
time-slices — the existence-plus-injectivity (diffeomorphism-onto-image) datum the
compact-manifold gauge flow of Item 2 consumes for its forward family `F`. -/
theorem exists_timeDependent_flow_compact_injective {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, Function.Injective (Φ t)) := by
  obtain ⟨ε, hε, Φ, hanchor, hflow⟩ := exists_timeDependent_flow_compact hX
  exact ⟨ε, hε, Φ, hanchor, hflow,
    fun t ht => timeDependent_flow_injective hX hε hanchor hflow ht⟩

/-- **Uniqueness (canonicity) of the anchored time-dependent flow.** For a jointly-`C¹`
time-dependent field `X` on a boundaryless T2 manifold, any two flows `Φ`, `Φ'` that are
anchored (`Φ 0 = Φ' 0 = id`) with orbits solving the field's ODE on `Ioo (-ε) ε` agree
on `Ioo (-ε) ε`: for every `x` the two orbits agree at `0`, hence everywhere by
`timeDependent_integralCurve_eqOn_of_eq`. Together with existence and injectivity this
makes the compact-manifold local flow a *canonically determined* family of injections. -/
theorem timeDependent_flow_unique {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε : ℝ} (hε : 0 < ε) {Φ Φ' : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x) (hanchor' : ∀ x, Φ' 0 x = x)
    (hflow : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ' τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x))))
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) (x : M) :
    Φ t x = Φ' t x := by
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have h0 : (fun τ => Φ τ x) 0 = (fun τ => Φ' τ x) 0 := by simp [hanchor, hanchor']
  have heq : Set.EqOn (fun τ => Φ τ x) (fun τ => Φ' τ x) (Set.Ioo (-ε) ε) :=
    timeDependent_integralCurve_eqOn_of_eq hX h0mem (hflow x) (hflow' x) h0
  exact heq ht

/-! ### Backward reachability and bijectivity of the compact-manifold flow

The forward flow `Φ` has injective time-slices (`timeDependent_flow_injective`), but
surjectivity of `x ↦ Φ t x` on a compact manifold is *not* automatic from injectivity
and continuity (invariance of domain would be needed); it requires a genuine backward
flow — an integral curve of `X` run from time `t` *back* to time `0`. Such curves need
the time-dependent existence *anchored at an arbitrary time* `t₀`, which the uniform
lifespan over the compact **time-slab** `Icc (-r) r ×ˢ univ` supplies (a single `δ`
covering every start time in `[-r, r]`). Reconciling that slab lifespan with the forward
lifespan closes surjectivity, hence bijectivity, of every time-slice — the
diffeomorphism-onto-image datum (its `G t` inverse half) Item 2's gauge flow consumes. -/

/-- **Uniform time-dependent integral-curve existence anchored at any time in a slab.**
For a jointly-`C¹` time-dependent field `X` on a compact boundaryless complete manifold
and any `r > 0`, there is a single `δ > 0` such that *every* start time `t₀ ∈ [-r, r]`
and *every* point `y` admit a time-dependent integral curve `γ` of `X` on the common
window `Ioo (t₀ - δ) (t₀ + δ)` with `γ t₀ = y`. Proved by taking the uniform lifespan of
the autonomization `(1, X)` over the compact time-slab `Icc (-r) r ×ˢ univ ⊆ ℝ × M`
(via `exists_uniform_time_of_nhds_uniform_on_compact`) and time-shifting the autonomous
curve anchored at `(t₀, y)` by `σ ↦ σ - t₀` (its first coordinate then tracks the
parameter by `autonomous_fst_eq_add`, so it descends to a time-dependent curve). This is
the anchored-anywhere existence the backward flow — and hence surjectivity — consumes. -/
theorem exists_uniform_timeDependent_integralCurve_anchored {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ t₀ ∈ Set.Icc (-r) r, ∀ y : M, ∃ γ : ℝ → M, γ t₀ = y ∧
      ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ
        (Set.Ioo (t₀ - δ) (t₀ + δ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  have hScompact : IsCompact ((Set.Icc (-r) r ×ˢ (Set.univ : Set M)) : Set (ℝ × M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨δ, hδ, huniform⟩ := exists_uniform_time_of_nhds_uniform_on_compact
    (fun p => exists_nhds_uniform_integralCurve (I := (𝓘(ℝ, ℝ)).prod I) hX p) hScompact
  refine ⟨δ, hδ, fun t₀ ht₀ y => ?_⟩
  obtain ⟨Γ, hΓ0, hΓon⟩ := huniform (t₀, y) ⟨ht₀, Set.mem_univ _⟩
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hΓ0fst : (Γ 0).1 = t₀ := by rw [hΓ0]
  -- the first coordinate of Γ is the affine map `ρ ↦ t₀ + ρ`
  have hfst_orig : ∀ ρ ∈ Set.Ioo (-δ) δ, (Γ ρ).1 = t₀ + ρ :=
    autonomous_fst_eq_add isOpen_Ioo h0mem isPreconnected_Ioo hΓ0fst (fun ρ hρ => hΓon ρ hρ)
  -- the shifted curve is an autonomous integral curve on `Ioo (t₀-δ) (t₀+δ)`
  have hΓs_curve : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) (fun σ => Γ (σ - t₀))
        (Set.Ioo (t₀ - δ) (t₀ + δ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (((1 : ℝ), X (Γ (t - t₀)).1 (Γ (t - t₀)).2) :
            TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ (t - t₀)))) := by
    have h := hΓon.comp_add (-t₀)
    have he1 : (Γ ∘ (· + (-t₀))) = (fun σ => Γ (σ - t₀)) := by
      funext σ; simp only [Function.comp_apply, sub_eq_add_neg]
    have he2 : {σ : ℝ | σ + (-t₀) ∈ Set.Ioo (-δ) δ} = Set.Ioo (t₀ - δ) (t₀ + δ) := by
      ext σ; simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [he1, he2] at h
    exact fun t ht => h t ht
  -- the shifted first coordinate tracks the parameter
  have hfst : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), (Γ (t - t₀)).1 = t := by
    intro t ht
    rcases ht with ⟨h1, h2⟩
    have hρ : t - t₀ ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    rw [hfst_orig (t - t₀) hρ]; ring
  refine ⟨fun σ => (Γ (σ - t₀)).2, ?_, ?_⟩
  · show (Γ (t₀ - t₀)).2 = y
    rw [sub_self, hΓ0]
  · exact isTimeDependentIntegralCurve_of_autonomous (Γ := fun σ => Γ (σ - t₀)) hfst hΓs_curve

/-- **Surjectivity of every time-slice of the compact-manifold flow.** For a jointly-`C¹`
time-dependent field `X` on a compact boundaryless T2 manifold, given the forward flow `Φ`
(anchored, orbits solving the ODE on `Ioo (-ε₁) ε₁`) and the slab-uniform anchored
existence (lifespan `δ` over `Icc (-ε₁) ε₁`), every time-`t` slice `x ↦ Φ t x` with
`|t| < min ε₁ δ` is surjective: run the backward integral curve from `(t, y)` to time `0`,
landing at `x`; then `Φ · x` and that backward curve are two time-dependent integral curves
agreeing at time `0`, so by uniqueness they agree at `t`, giving `Φ t x = y`. This is the
surjectivity (`G t`-inverse) half of the diffeomorphism-onto-image that injectivity
(`timeDependent_flow_injective`) alone does not supply on a compact manifold. -/
theorem timeDependent_flow_surjective {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε₁ δ : ℝ} (hε₁ : 0 < ε₁) (hδ : 0 < δ) {Φ : ℝ → M → M} (hanchor : ∀ x, Φ 0 x = x)
    (hflow : ∀ x, ∀ t ∈ Set.Ioo (-ε₁) ε₁, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
      (Set.Ioo (-ε₁) ε₁) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hanch : ∀ t₀ ∈ Set.Icc (-ε₁) ε₁, ∀ y : M, ∃ γ : ℝ → M, γ t₀ = y ∧
      ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ
        (Set.Ioo (t₀ - δ) (t₀ + δ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    {t : ℝ} (ht : t ∈ Set.Ioo (-min ε₁ δ) (min ε₁ δ)) :
    Function.Surjective (Φ t) := by
  have hεleδ : min ε₁ δ ≤ δ := min_le_right _ _
  have hεle₁ : min ε₁ δ ≤ ε₁ := min_le_left _ _
  rcases ht with ⟨htl, htr⟩
  intro y
  have htIcc : t ∈ Set.Icc (-ε₁) ε₁ := ⟨by linarith, by linarith⟩
  obtain ⟨γ, hγt, hγcurve⟩ := hanch t htIcc y
  refine ⟨γ 0, ?_⟩
  set a := max (-min ε₁ δ) (t - δ) with ha_def
  set b := min (min ε₁ δ) (t + δ) with hb_def
  have ha0 : a < 0 := by rw [ha_def]; exact max_lt (by linarith) (by linarith)
  have hb0 : 0 < b := by rw [hb_def]; exact lt_min (by linarith) (by linarith)
  have hta : a < t := by rw [ha_def]; exact max_lt (by linarith) (by linarith)
  have htb : t < b := by rw [hb_def]; exact lt_min (by linarith) (by linarith)
  have h0mem : (0 : ℝ) ∈ Set.Ioo a b := ⟨ha0, hb0⟩
  have htmem : t ∈ Set.Ioo a b := ⟨hta, htb⟩
  have hsub_ε : Set.Ioo a b ⊆ Set.Ioo (-ε₁) ε₁ := by
    apply Set.Ioo_subset_Ioo
    · rw [ha_def]; exact le_max_of_le_left (by linarith)
    · rw [hb_def]; exact le_trans (min_le_left _ _) (by linarith)
  have hsub_tδ : Set.Ioo a b ⊆ Set.Ioo (t - δ) (t + δ) := by
    apply Set.Ioo_subset_Ioo
    · rw [ha_def]; exact le_max_right _ _
    · rw [hb_def]; exact min_le_right _ _
  have hΦcurve : ∀ σ ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ (γ 0))
      (Set.Ioo a b) σ ((1 : ℝ →L[ℝ] ℝ).smulRight (X σ (Φ σ (γ 0)))) :=
    fun σ hσ => (hflow (γ 0) σ (hsub_ε hσ)).mono hsub_ε
  have hγcurve' : ∀ σ ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ
      (Set.Ioo a b) σ ((1 : ℝ →L[ℝ] ℝ).smulRight (X σ (γ σ))) :=
    fun σ hσ => (hγcurve σ (hsub_tδ hσ)).mono hsub_tδ
  have hagree0 : (fun τ => Φ τ (γ 0)) 0 = γ 0 := hanchor (γ 0)
  have heqon : Set.EqOn (fun τ => Φ τ (γ 0)) γ (Set.Ioo a b) :=
    timeDependent_integralCurve_eqOn_of_eq hX h0mem hΦcurve hγcurve' hagree0
  have hfin := heqon htmem
  rw [hγt] at hfin
  exact hfin

/-- **The compact-manifold time-dependent local flow is a family of bijections.** For a
jointly-`C¹` time-dependent field `X` on a compact boundaryless T2 manifold there is a
uniform `ε > 0` and an anchored flow `Φ` (`Φ 0 = id`) whose orbits `τ ↦ Φ τ x` solve the
field's ODE on `Ioo (-ε) ε` and whose *every* time-`t` slice `x ↦ Φ t x` is **bijective**.
Bundles `exists_timeDependent_flow_compact` (existence + ODE), `timeDependent_flow_injective`
(injectivity) and `timeDependent_flow_surjective` (surjectivity via backward reachability):
the forward lifespan `ε₁` and the slab lifespan `δ` (`exists_uniform_timeDependent_integralCurve_anchored`)
are reconciled by `ε := min ε₁ δ`. With `timeDependent_flow_unique` (canonicity) this is the
canonically-determined family of **bijections** whose per-time inverse `G t := (Φ t).invFun`
is exactly the `G`-datum `GaugeFlowAssembly.gaugeFlow_of_inverse_flow` consumes. -/
theorem exists_timeDependent_flow_compact_bijective {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, Function.Bijective (Φ t)) := by
  obtain ⟨ε₁, hε₁, Φ, hanchor, hflow⟩ := exists_timeDependent_flow_compact hX
  obtain ⟨δ, hδ, hanch⟩ := exists_uniform_timeDependent_integralCurve_anchored hX hε₁
  refine ⟨min ε₁ δ, lt_min hε₁ hδ, Φ, hanchor, ?_, ?_⟩
  · intro x t ht
    have hsub : Set.Ioo (-min ε₁ δ) (min ε₁ δ) ⊆ Set.Ioo (-ε₁) ε₁ :=
      Set.Ioo_subset_Ioo (by simp [min_le_left]) (min_le_left _ _)
    exact (hflow x t (hsub ht)).mono hsub
  · intro t ht
    have hsub : Set.Ioo (-min ε₁ δ) (min ε₁ δ) ⊆ Set.Ioo (-ε₁) ε₁ :=
      Set.Ioo_subset_Ioo (by simp [min_le_left]) (min_le_left _ _)
    have hε : (0 : ℝ) < min ε₁ δ := lt_min hε₁ hδ
    have hflow' : ∀ x, ∀ s ∈ Set.Ioo (-min ε₁ δ) (min ε₁ δ),
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x) (Set.Ioo (-min ε₁ δ) (min ε₁ δ)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ s x))) :=
      fun x s hs => (hflow x s (hsub hs)).mono hsub
    refine ⟨timeDependent_flow_injective hX hε hanchor hflow' ht,
      timeDependent_flow_surjective hX hε₁ hδ hanchor hflow hanch ht⟩

/-- **Concrete mutually-inverse time-slice maps for the compact-manifold flow.** On a
compact boundaryless (nonempty) T2 manifold, the forward flow `Φ` and the explicit
inverse family `G t := Function.invFun (Φ t)` are mutually inverse on every window time,
with both anchored at the identity: `G t` is a genuine two-sided inverse of the bijection
`Φ t` (`Function.leftInverse_invFun` / `rightInverse_invFun` on the bijectivity of every
slice). This is the concrete `F := Φ`, `G` mutually-inverse time-slice datum
`GaugeFlowAssembly.gaugeFlow_of_inverse_flow` consumes (on the window; the sole remaining
analytic obligation being the spatial `C³` regularity of `F t`/`G t`). -/
theorem exists_timeDependent_flow_compact_inverse {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ G : ℝ → M → M, (∀ x, Φ 0 x = x) ∧ (∀ x, G 0 x = x) ∧
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) := by
  obtain ⟨ε, hε, Φ, hanchor, hflow, hbij⟩ := exists_timeDependent_flow_compact_bijective hX
  refine ⟨ε, hε, Φ, fun t => Function.invFun (Φ t), hanchor, ?_, hflow, ?_, ?_⟩
  · intro x
    show Function.invFun (Φ 0) x = x
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
    have h := Function.leftInverse_invFun (hbij 0 h0mem).injective x
    rwa [hanchor x] at h
  · intro t ht; exact Function.leftInverse_invFun (hbij t ht).injective
  · intro t ht; exact Function.rightInverse_invFun (hbij t ht).surjective

/-- **Space-time tangent jet from a jointly-smooth time-dependent vector field.**  The
autonomisation field `(1, X)` on `ℝ × M` — the `hX` datum every compact time-dependent flow
existence lemma above consumes, phrased as a `C^n` section of the *product* tangent bundle
`TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)` — is `C^n` as soon as the underlying vector field `X`
is `C^n` jointly in `(t, x)` as a section of the plain tangent bundle `TangentBundle I M`.

This converts the exotic product-tangent-bundle smoothness obligation `hX` into the natural
smoothness `ContMDiff ((𝓘(ℝ, ℝ)).prod I) I.tangent n (fun p ↦ ⟨p.2, X p.1 p.2⟩)` of the field
itself — exactly the shape a joint space-time regularity result for the (real) Ricci–DeTurck gauge
field produces, and the current bottleneck of the compact-manifold gauge-flow lift.  The proof pairs
the constant `∂_t` section on `ℝ` (the unit vector field pulled back along `Prod.fst`) with the `X`
section via `ContMDiff.prodMk`, then transports through the smooth inverse of Mathlib's canonical
tangent-bundle-of-a-product equivalence `equivTangentBundleProd`. -/
theorem contMDiff_spaceTimeField_of_contMDiff_tangentSection {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : WithTop ℕ∞}
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I.tangent n
      (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) n
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) := by
  have hconst : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent n
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : ℝ => (1 : ℝ))).mpr contDiff_const
  have h1 : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ)).tangent n
      (fun p : ℝ × M => (⟨p.1, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    hconst.comp contMDiff_fst
  have hpair := h1.prodMk hX
  exact (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I) (M' := M) (n := n)).comp hpair

/-- **Joint space-time continuity of an *abstract* time-dependent flow, derived from its ODE alone.**
Any time-dependent flow `Φ` on a compact boundaryless T2 manifold that is anchored at `0`
(`Φ 0 x = x`) and solves the flow ODE of a jointly-`C¹` field `X` on `Set.Ioo (-ε) ε` is jointly
continuous in space-time at each anchor point `(0, x)` — even though **no** continuity of `Φ` is
assumed as a hypothesis.  The point is that the canonical continuous flow
`exists_timeDependent_flow_compact_continuousAt` produces a flow `Φ'` with the *same* anchor and ODE,
and by the manifold flow uniqueness `timeDependent_flow_unique` the two agree on the intersection of
their windows — an open space-time neighbourhood `Set.Ioo (-m) m ×ˢ Set.univ` of `(0, x)` — so `Φ`
inherits `Φ'`'s `ContinuousAt` at `(0, x)` via `ContinuousAt.congr`.

This is exactly the `hcontA` hypothesis of `contMDiffOn_flowSlice_perPatch_of_flow`, so it lets the
compact gauge-flow slice-`C³` route consume an abstract flow — e.g. the `hslicesC3`-supplied flow of
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`, for which only the anchor and ODE are
available and no joint continuity is given. -/
theorem continuousAt_timeDependent_flow_of_anchor_ode {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε : ℝ} (hε : 0 < ε) {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hflow : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (x : M) :
    ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x) := by
  obtain ⟨ε', hε', Φ', hanchor', hflow', hcont'⟩ :=
    exists_timeDependent_flow_compact_continuousAt hX
  have hmpos : (0 : ℝ) < min ε ε' := lt_min hε hε'
  have hmono : Set.Ioo (-min ε ε') (min ε ε') ⊆ Set.Ioo (-ε) ε :=
    Set.Ioo_subset_Ioo (neg_le_neg (min_le_left ε ε')) (min_le_left ε ε')
  have hmono' : Set.Ioo (-min ε ε') (min ε ε') ⊆ Set.Ioo (-ε') ε' :=
    Set.Ioo_subset_Ioo (neg_le_neg (min_le_right ε ε')) (min_le_right ε ε')
  have hflowm : ∀ y, ∀ t ∈ Set.Ioo (-min ε ε') (min ε ε'),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ y) (Set.Ioo (-min ε ε') (min ε ε')) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t y))) :=
    fun y t ht => (hflow y t (hmono ht)).mono hmono
  have hflow'm : ∀ y, ∀ t ∈ Set.Ioo (-min ε ε') (min ε ε'),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ' τ y) (Set.Ioo (-min ε ε') (min ε ε')) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t y))) :=
    fun y t ht => (hflow' y t (hmono' ht)).mono hmono'
  have hnhds : Set.Ioo (-min ε ε') (min ε ε') ×ˢ (Set.univ : Set M) ∈ nhds ((0 : ℝ), x) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨neg_lt_zero.mpr hmpos, hmpos⟩, Set.mem_univ _⟩
  have hEq : (fun z : ℝ × M => Φ' z.1 z.2) =ᶠ[nhds ((0 : ℝ), x)] (fun z => Φ z.1 z.2) := by
    filter_upwards [hnhds] with z hz
    show Φ' z.1 z.2 = Φ z.1 z.2
    exact (timeDependent_flow_unique hX hmpos hanchor hanchor' hflowm hflow'm hz.1 z.2).symm
  exact (hcont' x).congr hEq

end PoincareCurvature.ManifoldFlow

/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ModelManifoldGaugeFlow
import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.TimeDependentGram

/-!
# Item 2 (GAP 1) capstone — compact-manifold `C³` gauge flow from time-dependent raising data

This module composes the two halves of Item 2's compact-manifold gauge-flow existence:

* the **globally-defined metric-raised gauge field** and its per-patch joint `(t, x)`-smoothness,
  packaged coordinate-free in `PoincareCurvature/Analysis/TimeDependentGram.lean`
  (`exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection`), and
* the **compact-manifold flow-by-time-dependent-vector-field** with `C³` regularity, built in
  `AnalyticPDE/ModelManifoldGaugeFlow.lean`
  (`exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact`).

The final composition instantiates the *abstract vector-bundle* raised-field lemma at the tangent
bundle `V := TangentSpace I`.  This crosses a genuine Mathlib instance-resolution wall: synthesising
`FiberBundle`/`VectorBundle ℝ E (TangentSpace I)` in the heavy compact-manifold instance context runs a
non-terminating `whnf` (a transported-instance diamond between the canonical tangent-bundle fibre
structure and the `NormedAddCommGroup`-derived one).  The wall is defeated here by:

1. pinning **every** bundle instance of the abstract lemma positionally via `@`, bridging each with a
   tactic-mode `by exact` (which unifies the two defeq-but-not-syntactic instance paths where a bare
   term-level `:=` reports a spurious type mismatch), and
2. supplying the flow's vector field `X` as the **same** `@`-pinned `raisedGaugeField` expression, so the
   raw-manifold flow goal and the abstract lemma's conclusion are *syntactically identical* on the
   section; the only residual defeq is the definitional `I.tangent = I.prod 𝓘(ℝ, E)`, discharged
   cheaply rather than through the diamond.

The result `exists_gaugeFlow_Ioo_of_timeDependent_raisingData` is the general-`M` flow capstone of Item 2
GAP 1: on a compact boundaryless manifold, the metric-raised time-dependent gauge field flows to a
`C³`-in-space diffeomorphism family on an open time interval around `0`, with no restricting instance.
-/

open Set Filter Topology Bundle
open scoped Topology NNReal Manifold ContDiff
open PoincareCurvature.ParametrizedInner

namespace PoincareCurvature.ParametrizedInner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- **Item 2 (GAP 1) capstone: compact-manifold `C³` gauge flow from time-dependent raising data.**
Let `M` be a compact boundaryless `C^∞` manifold modelled on `E`, `g : ℝ → ContMDiffRiemannianMetric`
a time-dependent smooth Riemannian metric on the tangent bundle, and `om : ℝ → Ω¹` a time-dependent
one-form, with joint `(t, x)`-smoothness of the metric inner product (`hg`) and of the one-form
(`hom`).  Then the metric-raised gauge field `raisedGaugeField (g t) (om t) bas`, read as a
time-dependent tangent vector field, flows: there is a family `Φ : ℝ → M → M` and an open interval
`Ioo c d ∋ 0` on which `Φ` is anchored at the identity at time `0` and each time-`t` map is
`C³`.  This is the general (non-model, non-Levi-Civita-background) compact-manifold gauge-flow
existence targeted by Item 2 GAP 1. -/
theorem exists_gaugeFlow_Ioo_of_timeDependent_raisingData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    (g : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (om : ℝ → ∀ y : M, TangentSpace I y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hg : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)))
    (hom : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ (TangentSpace I y →L[ℝ] ℝ)) p.2 (om p.1 p.2))) :
    ∃ (Φ : ℝ → M → M) (c d : ℝ), (∀ x, Φ 0 x = x) ∧ (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) := by
  refine RicciFlow.AnalyticPDE.SmoothDependenceCk.exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact
    (X := fun τ y => @raisedGaugeField E _ _ H _ I ∞ M _ _ E _ _ (TangentSpace I : M → Type _)
      (by exact inferInstance) (fun _ => by exact inferInstanceAs (NormedAddCommGroup E))
      (fun _ => by exact inferInstanceAs (NormedSpace ℝ E))
      (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
      (g τ) (om τ) _ _ _ bas y) (fun x => ?_)
  have h0 := @exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection
      E _ _ H _ I ∞ M _ _ E _ _ (TangentSpace I : M → Type _)
      (by exact inferInstance) (fun _ => by exact inferInstanceAs (NormedAddCommGroup E))
      (fun _ => by exact inferInstanceAs (NormedSpace ℝ E))
      (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
      (by exact ‹ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I›) g om _ _ _ bas hg hom x
  obtain ⟨s, hs_open, hxs, hcont⟩ := h0
  exact ⟨s, hs_open, hxs, hcont⟩
/-- **Static (time-independent) specialization of the compact-manifold gauge-flow capstone.**  For a
*time-independent* smooth Riemannian metric `g₀` on the tangent bundle of a compact boundaryless
manifold and a *time-independent* one-form `ω₀` (spatially smooth as a covector section), the
metric-raised gauge field `raisedGaugeField g₀ ω₀ bas` flows: there is `Φ : ℝ → M → M` and an open
interval `Ioo c d ∋ 0` with `Φ 0 = id` and each `Φ t` `C³`.  Obtained from
`exists_gaugeFlow_Ioo_of_timeDependent_raisingData` at the constant families `fun _ ↦ g₀`,
`fun _ ↦ ω₀`, whose joint `(t, x)`-smoothness inputs are discharged by
`contMDiff_constMetricSection_prodSnd` (the metric, unconditionally) and
`contMDiff_constOneFormSection_prodSnd` (the one-form, from its spatial smoothness `hω₀`).  This is the
autonomous-gauge entry point of Item 2 GAP 1: the analytic residual is reduced to the *spatial*
smoothness of the one-form section alone. -/
theorem exists_gaugeFlow_Ioo_of_timeIndependent_raisingData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    (g₀ : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (ω₀ : ∀ y : M, TangentSpace I y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hω₀ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y : M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ (TangentSpace I y →L[ℝ] ℝ)) y (ω₀ y))) :
    ∃ (Φ : ℝ → M → M) (c d : ℝ), (∀ x, Φ 0 x = x) ∧ (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) :=
  exists_gaugeFlow_Ioo_of_timeDependent_raisingData (fun _ => g₀) (fun _ => ω₀) bas
    (g₀.contMDiff.comp contMDiff_snd)
    (hω₀.comp contMDiff_snd)

end PoincareCurvature.ParametrizedInner

/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.ConvexHull

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Pointwise exposed subgradient cluster bridges

This module contains the pointwise exposed-point reduction and the filter/ray wrappers turning
Rockafellar exposed-face outer semicontinuity into membership in the gradient cluster hull.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Rockafellar-style exposed-point reduction for the local subgradient cluster-density
conclusion at one point.

This theorem intentionally keeps the two hard finite-dimensional convex-analysis inputs visible:
first, that the subdifferential is contained in the closed convex hull of its exposed points;
second, that every exposed subgradient is a cluster limit of nearby gradients. -/
theorem mem_closure_convexHull_gradientClusterSet_of_exposedPoint_reduction
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hrepr :
      ∀ ⦃r : E⦄,
        SubgradientOn domain u y r →
          r ∈ closure
            (convexHull ℝ (exposedPoints {q : E | SubgradientOn domain u y q})))
    (hexposed_cluster :
      ∀ ⦃r : E⦄,
        r ∈ exposedPoints {q : E | SubgradientOn domain u y q} →
          r ∈ closure
            (convexHull ℝ
              (HasSubgradientLinearizationOnAt.GradientClusterSet
                (differentiabilitySetOn sample u) (gradient u) y)))
    (hp : SubgradientOn domain u y p) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  let C : Set E :=
    closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y))
  have hclosedC : IsClosed C := isClosed_closure
  have hconvC : Convex ℝ C :=
    (convex_convexHull ℝ
      (HasSubgradientLinearizationOnAt.GradientClusterSet
        (differentiabilitySetOn sample u) (gradient u) y)).closure
  have hsubset :
      {q : E | SubgradientOn domain u y q} ⊆ C :=
    subset_of_subset_closure_convexHull_exposedPoints_of_exposed_subset_closed_convex
      (s := {q : E | SubgradientOn domain u y q}) (C := C)
      hrepr (fun r hr => hexposed_cluster hr) hclosedC hconvC
  exact hsubset hp

/-- An exposed subgradient belongs to the gradient cluster closed convex hull once nearby
differentiability gradients converge to it along the sampling filter.

This is the final filter/metric packaging of Rockafellar's exposed-point argument. The hard
analytic input is the norm convergence hypothesis, which is supplied in Rockafellar 25.6 by
directional outer semicontinuity and the fact that the exposed face is the singleton `{p}`. -/
theorem exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_eventually_norm_sub_lt
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hne : (𝓝[differentiabilitySetOn sample u] y).NeBot)
    (_hexposed : p ∈ exposedPoints {q : E | SubgradientOn domain u y q})
    (hgradient :
      ∀ ε > 0,
        ∀ᶠ w in 𝓝[differentiabilitySetOn sample u] y, ‖gradient u w - p‖ < ε) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  exact subset_closure
    ((subset_convexHull (𝕜 := ℝ)
      (HasSubgradientLinearizationOnAt.GradientClusterSet
        (differentiabilitySetOn sample u) (gradient u) y))
      (HasSubgradientLinearizationOnAt.GradientClusterSet.mem_of_eventually_norm_sub_lt
        hne hgradient))

/-- Exposed-subgradient cluster membership from the outer-semicontinuity shape used by
Rockafellar.

The hypothesis says that for every `ε > 0`, nearby differentiability gradients lie in the
`ε`-thickening of the exposed face selected by `normal`. If `normal` exposes `p`, that exposed
face is `{p}`, so the previous metric bridge applies. -/
theorem exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_eventually_mem_thickening
    {domain sample : Set E} {u : E → ℝ} {y p normal : E}
    (hne : (𝓝[differentiabilitySetOn sample u] y).NeBot)
    (hexposed : ExposesPoint {q : E | SubgradientOn domain u y q} normal p)
    (houter :
      ∀ ε > 0,
        ∀ᶠ w in 𝓝[differentiabilitySetOn sample u] y,
          gradient u w ∈
            normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  refine exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_eventually_norm_sub_lt
    hne ⟨normal, hexposed⟩ ?_
  intro ε hε
  filter_upwards [houter ε hε] with w hw
  have hface : exposedFace {q : E | SubgradientOn domain u y q} normal = {p} :=
    hexposed.exposedFace_eq_singleton
  exact norm_sub_lt_of_mem_normThickening_singleton (by simpa [hface] using hw)

/-- Exposed-subgradient cluster membership from convergence along an auxiliary approach filter.

This is the filter form closest to Rockafellar's exposed-point proof: one constructs
differentiability points approaching `y` in the exposing direction, and proves that their
gradients converge to the exposed subgradient. The approach map only has to tend to `y` through
the differentiability set; it need not be the full ambient `𝓝[D] y` filter. -/
theorem exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_tendsto_norm_sub_lt
    {ι : Type*} {l : Filter ι} {domain sample : Set E} {u : E → ℝ} {y p : E}
    {φ : ι → E}
    (hne : l.NeBot)
    (hφ : Filter.Tendsto φ l (𝓝[differentiabilitySetOn sample u] y))
    (_hexposed : p ∈ exposedPoints {q : E | SubgradientOn domain u y q})
    (hgradient :
      ∀ ε > 0, ∀ᶠ a in l, ‖gradient u (φ a) - p‖ < ε) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  have : Filter.NeBot l := hne
  have htend :
      Filter.Tendsto (fun a => gradient u (φ a)) l (𝓝 p) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hgradient ε hε] with a ha
    simpa [Metric.mem_ball, dist_eq_norm] using ha
  have hcluster :
      MapClusterPt p l (fun a => gradient u (φ a)) := by
    rw [mapClusterPt_def]
    exact ClusterPt.of_le_nhds htend
  exact subset_closure
    ((subset_convexHull (𝕜 := ℝ)
      (HasSubgradientLinearizationOnAt.GradientClusterSet
        (differentiabilitySetOn sample u) (gradient u) y))
      (HasSubgradientLinearizationOnAt.GradientClusterSet.mem_of_mapClusterPt hφ hcluster))

/-- Directional/filter version of the exposed-face outer-semicontinuity bridge.

Instead of requiring all sufficiently nearby differentiability gradients to lie near the exposed
face, it is enough to have one nontrivial approach filter through the differentiability set along
which the outer-semicontinuity estimate holds. -/
theorem exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_tendsto_mem_thickening
    {ι : Type*} {l : Filter ι} {domain sample : Set E} {u : E → ℝ} {y p normal : E}
    {φ : ι → E}
    (hne : l.NeBot)
    (hφ : Filter.Tendsto φ l (𝓝[differentiabilitySetOn sample u] y))
    (hexposed : ExposesPoint {q : E | SubgradientOn domain u y q} normal p)
    (houter :
      ∀ ε > 0,
        ∀ᶠ a in l,
          gradient u (φ a) ∈
            normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  refine exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_tendsto_norm_sub_lt
    hne hφ ⟨normal, hexposed⟩ ?_
  intro ε hε
  filter_upwards [houter ε hε] with a ha
  have hface : exposedFace {q : E | SubgradientOn domain u y q} normal = {p} :=
    hexposed.exposedFace_eq_singleton
  exact norm_sub_lt_of_mem_normThickening_singleton (by simpa [hface] using ha)

/-- Source-ray version of Rockafellar's exposed-subgradient bridge.

This is the wrapper closest to the printed proof of Theorem 25.6. The differentiability samples
`φ a` are chosen within `ε a ^ 2` of the ray point `y + ε a • normal`, with `ε a -> 0` and
`ε a > 0` eventually. The already-proved ray lemmas supply both the approach through the
differentiability set and the normalized-direction convergence required by directional outer
semicontinuity. -/
theorem exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_ray_thickening
    {ι : Type*} {l : Filter ι} {domain sample : Set E} {u : E → ℝ} {y p normal : E}
    {φ : ι → E} {ε : ι → ℝ}
    (hne : l.NeBot)
    (hnormal : ‖normal‖ = 1)
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hεpos : ∀ᶠ a in l, 0 < ε a)
    (hmem : ∀ᶠ a in l, φ a ∈ differentiabilitySetOn sample u)
    (hclose : ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2)
    (hexposed : ExposesPoint {q : E | SubgradientOn domain u y q} normal p)
    (houter :
      Filter.Tendsto (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) →
        ∀ δ > 0,
          ∀ᶠ a in l,
            gradient u (φ a) ∈
              normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) δ) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  have hφ : Filter.Tendsto φ l (𝓝[differentiabilitySetOn sample u] y) :=
    tendsto_nhdsWithin_of_eventually_norm_sub_ray_le_sq hε hmem hclose
  have hdir : Filter.Tendsto (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) :=
    tendsto_unitDirection_sub_of_eventually_norm_sub_ray_le_sq hnormal hε hεpos hclose
  exact exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_tendsto_mem_thickening
    hne hφ hexposed (houter hdir)

end AleksandrovDifferentiability

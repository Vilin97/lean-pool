/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster.Compact

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Local Rockafellar cluster-density assembly

This module turns compact or bounded subdifferentials, Straszewicz approximation, and exposed-face
outer semicontinuity into `LocalSubgradientClusterDensityOn`.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Local cluster density from compact subdifferentials, literal Straszewicz, and the
Rockafellar exposed-face outer-semicontinuity estimate.

This is the local assembly of the two hard inputs in Rockafellar 25.6. The Straszewicz
hypothesis gives the closed-convex-hull representation of each compact subdifferential by its
exposed points; the outer-semicontinuity hypothesis puts every exposed subgradient into the
gradient cluster hull. -/
theorem localSubgradientClusterDensityOn_of_compact_straszewiczClosure_outer
    {domain sample : Set E} {u : E → ℝ}
    (hcompact :
      ∀ ⦃y : E⦄, y ∈ sample → IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (exposedPoints {q : E | SubgradientOn domain u y q}))
    (hne :
      ∀ ⦃y : E⦄, y ∈ sample → (𝓝[differentiabilitySetOn sample u] y).NeBot)
    (houter :
      ∀ ⦃y p normal : E⦄,
        y ∈ sample →
          ExposesPoint {q : E | SubgradientOn domain u y q} normal p →
            ∀ ε > 0,
              ∀ᶠ w in 𝓝[differentiabilitySetOn sample u] y,
                gradient u w ∈
                  normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    LocalSubgradientClusterDensityOn domain sample u := by
  intro y p hy hp
  refine mem_closure_convexHull_gradientClusterSet_of_compact_straszewiczClosure_exposedCluster
    (hcompact hy) (hstrasz hy) ?_ hp
  intro r hr
  rcases hr with ⟨normal, hexposed⟩
  exact exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_eventually_mem_thickening
    (hne hy) hexposed (houter hy hexposed)

/-- Local cluster density from compact subdifferentials, literal Straszewicz, and a directional
outer-semicontinuity input supplied along an auxiliary approach filter.

This is closer to Rockafellar's exposed-point proof than
`localSubgradientClusterDensityOn_of_compact_straszewiczClosure_outer`: for each exposed
subgradient it is enough to construct one nontrivial family of differentiability points tending to
the base point and satisfying the exposed-face estimate. -/
theorem localSubgradientClusterDensityOn_of_compact_straszewiczClosure_directionalOuter
    {domain sample : Set E} {u : E → ℝ}
    (hcompact :
      ∀ ⦃y : E⦄, y ∈ sample → IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (exposedPoints {q : E | SubgradientOn domain u y q}))
    (houter :
      ∀ ⦃y p normal : E⦄,
        y ∈ sample →
          ExposesPoint {q : E | SubgradientOn domain u y q} normal p →
            ∃ (ι : Type*) (l : Filter ι) (φ : ι → E),
              l.NeBot ∧
                Filter.Tendsto φ l (𝓝[differentiabilitySetOn sample u] y) ∧
                  ∀ ε > 0,
                    ∀ᶠ a in l,
                      gradient u (φ a) ∈
                        normThickening
                          (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    LocalSubgradientClusterDensityOn domain sample u := by
  intro y p hy hp
  refine mem_closure_convexHull_gradientClusterSet_of_compact_straszewiczClosure_exposedCluster
    (hcompact hy) (hstrasz hy) ?_ hp
  intro r hr
  rcases hr with ⟨normal, hexposed⟩
  rcases houter hy hexposed with ⟨ι, l, φ, hne, hφ, hthickening⟩
  exact exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_tendsto_mem_thickening
    hne hφ hexposed hthickening

/-- Local cluster density from compact subdifferentials and Rockafellar's concrete ray sequence.

This is the most literal assembly form for the exposed-point part of Theorem 25.6: for every
exposed subgradient one chooses a unit exposing normal, differentiability samples within
`ε^2` of the exposing ray, and the exposed-face thickening estimate supplied by directional
outer semicontinuity along that ray. -/
theorem localSubgradientClusterDensityOn_of_compact_straszewiczClosure_rayOuter
    {domain sample : Set E} {u : E → ℝ}
    (hcompact :
      ∀ ⦃y : E⦄, y ∈ sample → IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (exposedPoints {q : E | SubgradientOn domain u y q}))
    (houter :
      ∀ ⦃y p : E⦄,
        y ∈ sample →
          p ∈ exposedPoints {q : E | SubgradientOn domain u y q} →
            ∃ (normal : E), ‖normal‖ = 1 ∧
              ExposesPoint {q : E | SubgradientOn domain u y q} normal p ∧
                ∃ (ι : Type*) (l : Filter ι) (φ : ι → E) (ε : ι → ℝ),
                  l.NeBot ∧
                    Filter.Tendsto ε l (𝓝 0) ∧
                      (∀ᶠ a in l, 0 < ε a) ∧
                        (∀ᶠ a in l, φ a ∈ differentiabilitySetOn sample u) ∧
                          (∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) ∧
                            (Filter.Tendsto
                              (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) →
                                ∀ δ > 0,
                                  ∀ᶠ a in l,
                                    gradient u (φ a) ∈
                                      normThickening
                                        (exposedFace
                                          {q : E | SubgradientOn domain u y q} normal) δ)) :
    LocalSubgradientClusterDensityOn domain sample u := by
  intro y p hy hp
  refine mem_closure_convexHull_gradientClusterSet_of_compact_straszewiczClosure_exposedCluster
    (hcompact hy) (hstrasz hy) ?_ hp
  intro r hr
  rcases houter hy hr with
    ⟨normal, hnormal, hexposed, ι, l, φ, ε, hne, hε, hεpos, hmem, hclose, hthickening⟩
  exact exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_ray_thickening
    hne hnormal hε hεpos hmem hclose hexposed hthickening

/-- Local cluster density from compact subdifferentials and a Mathlib-shaped Straszewicz
hypothesis. -/
theorem localSubgradientClusterDensityOn_of_compact_mathlibStraszewicz_outer
    {domain sample : Set E} {u : E → ℝ}
    (hcompact :
      ∀ ⦃y : E⦄, y ∈ sample → IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (Set.exposedPoints ℝ {q : E | SubgradientOn domain u y q}))
    (hne :
      ∀ ⦃y : E⦄, y ∈ sample → (𝓝[differentiabilitySetOn sample u] y).NeBot)
    (houter :
      ∀ ⦃y p normal : E⦄,
        y ∈ sample →
          ExposesPoint {q : E | SubgradientOn domain u y q} normal p →
            ∀ ε > 0,
              ∀ᶠ w in 𝓝[differentiabilitySetOn sample u] y,
                gradient u w ∈
                  normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    LocalSubgradientClusterDensityOn domain sample u := by
  intro y p hy hp
  refine mem_closure_convexHull_gradientClusterSet_of_compact_mathlibStraszewicz_exposedCluster
    (hcompact hy) (hstrasz hy) ?_ hp
  intro r hr
  rcases hr with ⟨normal, hexposed⟩
  exact exposedSubgradient_mem_closure_convexHull_gradientClusterSet_of_eventually_mem_thickening
    (hne hy) hexposed (houter hy hexposed)

/-- Bounded-subdifferential version of
`localSubgradientClusterDensityOn_of_compact_straszewiczClosure_outer`.

This is the most source-cube-friendly local Rockafellar assembly theorem: local boundedness of the
subdifferential supplies compactness in a proper metric space, while the remaining two hypotheses
are exactly the literal Straszewicz closure input and the directional outer-semicontinuity input
for exposed faces. -/
theorem localSubgradientClusterDensityOn_of_bounded_straszewiczClosure_outer
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ}
    (hbounded :
      ∀ ⦃y : E⦄, y ∈ sample → Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (exposedPoints {q : E | SubgradientOn domain u y q}))
    (hne :
      ∀ ⦃y : E⦄, y ∈ sample → (𝓝[differentiabilitySetOn sample u] y).NeBot)
    (houter :
      ∀ ⦃y p normal : E⦄,
        y ∈ sample →
          ExposesPoint {q : E | SubgradientOn domain u y q} normal p →
            ∀ ε > 0,
              ∀ᶠ w in 𝓝[differentiabilitySetOn sample u] y,
                gradient u w ∈
                  normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    LocalSubgradientClusterDensityOn domain sample u :=
  localSubgradientClusterDensityOn_of_compact_straszewiczClosure_outer
    (fun {_} hy => isCompact_setOf_subgradientOn_of_isBounded (hbounded hy))
    hstrasz hne houter

/-- Bounded-subdifferential local cluster density from a directional outer-semicontinuity input. -/
theorem localSubgradientClusterDensityOn_of_bounded_straszewiczClosure_directionalOuter
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ}
    (hbounded :
      ∀ ⦃y : E⦄, y ∈ sample → Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (exposedPoints {q : E | SubgradientOn domain u y q}))
    (houter :
      ∀ ⦃y p normal : E⦄,
        y ∈ sample →
          ExposesPoint {q : E | SubgradientOn domain u y q} normal p →
            ∃ (ι : Type*) (l : Filter ι) (φ : ι → E),
              l.NeBot ∧
                Filter.Tendsto φ l (𝓝[differentiabilitySetOn sample u] y) ∧
                  ∀ ε > 0,
                    ∀ᶠ a in l,
                      gradient u (φ a) ∈
                        normThickening
                          (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    LocalSubgradientClusterDensityOn domain sample u :=
  localSubgradientClusterDensityOn_of_compact_straszewiczClosure_directionalOuter
    (fun {_} hy => isCompact_setOf_subgradientOn_of_isBounded (hbounded hy))
    hstrasz houter

/-- Bounded-subdifferential local cluster density from Rockafellar's concrete ray sequence. -/
theorem localSubgradientClusterDensityOn_of_bounded_straszewiczClosure_rayOuter
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ}
    (hbounded :
      ∀ ⦃y : E⦄, y ∈ sample → Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (exposedPoints {q : E | SubgradientOn domain u y q}))
    (houter :
      ∀ ⦃y p : E⦄,
        y ∈ sample →
          p ∈ exposedPoints {q : E | SubgradientOn domain u y q} →
            ∃ (normal : E), ‖normal‖ = 1 ∧
              ExposesPoint {q : E | SubgradientOn domain u y q} normal p ∧
                ∃ (ι : Type*) (l : Filter ι) (φ : ι → E) (ε : ι → ℝ),
                  l.NeBot ∧
                    Filter.Tendsto ε l (𝓝 0) ∧
                      (∀ᶠ a in l, 0 < ε a) ∧
                        (∀ᶠ a in l, φ a ∈ differentiabilitySetOn sample u) ∧
                          (∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) ∧
                            (Filter.Tendsto
                              (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) →
                                ∀ δ > 0,
                                  ∀ᶠ a in l,
                                    gradient u (φ a) ∈
                                      normThickening
                                        (exposedFace
                                          {q : E | SubgradientOn domain u y q} normal) δ)) :
    LocalSubgradientClusterDensityOn domain sample u :=
  localSubgradientClusterDensityOn_of_compact_straszewiczClosure_rayOuter
    (fun {_} hy => isCompact_setOf_subgradientOn_of_isBounded (hbounded hy))
    hstrasz houter

/-- Bounded-subdifferential local cluster density from a Mathlib-shaped Straszewicz hypothesis. -/
theorem localSubgradientClusterDensityOn_of_bounded_mathlibStraszewicz_outer
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ}
    (hbounded :
      ∀ ⦃y : E⦄, y ∈ sample → Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ∀ ⦃y : E⦄, y ∈ sample →
        ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
          closure (Set.exposedPoints ℝ {q : E | SubgradientOn domain u y q}))
    (hne :
      ∀ ⦃y : E⦄, y ∈ sample → (𝓝[differentiabilitySetOn sample u] y).NeBot)
    (houter :
      ∀ ⦃y p normal : E⦄,
        y ∈ sample →
          ExposesPoint {q : E | SubgradientOn domain u y q} normal p →
            ∀ ε > 0,
              ∀ᶠ w in 𝓝[differentiabilitySetOn sample u] y,
                gradient u w ∈
                  normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε) :
    LocalSubgradientClusterDensityOn domain sample u :=
  localSubgradientClusterDensityOn_of_compact_mathlibStraszewicz_outer
    (fun {_} hy => isCompact_setOf_subgradientOn_of_isBounded (hbounded hy))
    hstrasz hne houter

end AleksandrovDifferentiability

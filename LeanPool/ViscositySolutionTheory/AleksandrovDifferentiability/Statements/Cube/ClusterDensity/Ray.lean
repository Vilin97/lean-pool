/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.ClusterDensity.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Source-cube cluster-density ray reductions
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

theorem SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray_one_unitOuter_seq'
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (Set.exposedPoints ℝ
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}))
    (houter :
      ∀ ⦃y p normal : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          p ∈ Set.exposedPoints ℝ
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} →
            ‖normal‖ = 1 →
              ExposesPoint
                {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p →
                ∀ ⦃φ : ℕ → SourceCubeSpace n⦄,
                  (∀ᶠ k in Filter.atTop, φ k ∈ sourceCubeDifferentiabilitySet n 1 u) →
                    (∀ᶠ k in Filter.atTop,
                      ‖φ k - (y + sourceForwardSecantStep k • normal)‖ ≤
                        (sourceForwardSecantStep k) ^ 2) →
                      ∀ δ > 0,
                        ∀ᶠ k in Filter.atTop,
                          frechetGradient u (φ k) ∈
                            normThickening
                              (exposedFace
                                {q : SourceCubeSpace n |
                                  SubgradientOn (sourceOpenCube n 3) u y q}
                                normal) δ) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray_one_unitOuter_seq
    hn hbounded hconvex hstrasz
    (fun {y p normal} hy hp hnormal hexposed {φ} hmem hclose _hdir =>
      houter (y := y) (p := p) (normal := normal) hy hp hnormal hexposed
        (φ := φ) hmem hclose)

/-- Source-cube directional outer semicontinuity along Rockafellar's canonical ray samples.

This is the cube-local version of the analytic input used in the exposed-point part of
Rockafellar 25.6. Boundedness of `u` on `Q_3` supplies a compact ball containing all gradients
at differentiability samples in `Q_1`; the generic compact directional wrapper then puts every
cluster value in the exposed face of the base subdifferential. -/
theorem eventually_frechetGradient_mem_normThickening_exposedFace_of_sourceCube_ray
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {y normal : SourceCubeSpace n}
    {φ : ℕ → SourceCubeSpace n}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hy : y ∈ sourceOpenCube n 1)
    (hnormal : ‖normal‖ = 1)
    (hmem : ∀ᶠ k in Filter.atTop, φ k ∈ sourceCubeDifferentiabilitySet n 1 u)
    (hclose :
      ∀ᶠ k in Filter.atTop,
        ‖φ k - (y + sourceForwardSecantStep k • normal)‖ ≤
          (sourceForwardSecantStep k) ^ 2) :
    ∀ δ > 0,
      ∀ᶠ k in Filter.atTop,
        frechetGradient u (φ k) ∈
          normThickening
            (exposedFace
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}
              normal) δ := by
  intro δ hδ
  let K : Set (SourceCubeSpace n) :=
    Metric.closedBall (0 : SourceCubeSpace n) (sourceCubeOscillation n u)
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_closedBall (0 : SourceCubeSpace n) (sourceCubeOscillation n u)
  have hmemK : ∀ᶠ k in Filter.atTop, gradient u (φ k) ∈ K := by
    filter_upwards [hmem] with k hk
    rcases hk with ⟨hkQ1, hkdiff⟩
    have hle :
        ‖frechetGradient u (φ k)‖ ≤ sourceCubeOscillation n u :=
      ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn
        hconvex hbounded hkQ1 hkdiff
    simpa [K, Metric.mem_closedBall, dist_eq_norm, frechetGradient, gradient] using hle
  have hφWithin :
      Filter.Tendsto φ Filter.atTop
        (𝓝[sourceCubeDifferentiabilitySet n 1 u] y) :=
    tendsto_nhdsWithin_of_eventually_norm_sub_ray_le_sq
      tendsto_sourceForwardSecantStep hmem hclose
  have hφ : Filter.Tendsto φ Filter.atTop (𝓝 y) :=
    hφWithin.mono_right nhdsWithin_le_nhds
  have hy3 : y ∈ sourceOpenCube n 3 :=
    sourceOpenCube_one_subset_three hy
  have hcont : ContinuousAt u y :=
    (hconvex.continuousOn (isOpen_sourceOpenCube (n := n) 3)).continuousAt
      ((isOpen_sourceOpenCube (n := n) 3).mem_nhds hy3)
  have hφ_mem :
      ∀ᶠ k in Filter.atTop, φ k ∈ interior (sourceOpenCube n 3) := by
    filter_upwards [hmem] with k hk
    rcases hk with ⟨hkQ1, _hkdiff⟩
    exact sourceOpenCube_one_subset_interior_three hkQ1
  have hφ_diff : ∀ᶠ k in Filter.atTop, DifferentiableAt ℝ u (φ k) := by
    filter_upwards [hmem] with k hk
    exact hk.2
  have hdir :
      Filter.Tendsto
        (fun k => ‖φ k - y‖⁻¹ • (φ k - y)) Filter.atTop (𝓝 normal) :=
    tendsto_unitDirection_sub_of_eventually_norm_sub_ray_le_sq
      hnormal tendsto_sourceForwardSecantStep
      (Filter.Eventually.of_forall sourceForwardSecantStep_pos) hclose
  have hout :
      ∀ᶠ k in Filter.atTop,
        gradient u (φ k) ∈
          normThickening
            (exposedFace
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}
              normal) δ :=
    ConvexOn.eventually_gradient_mem_normThickening_exposedFace_of_compact_directional
      hconvex hK hmemK hy3 hφ hcont hφ_mem hφ_diff hdir hδ
  simpa [frechetGradient, gradient] using hout

/-- Inner-cube source-cube cluster density from Straszewicz closure and the proved
source-cube directional outer semicontinuity.

Compared with
`SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray_one_unitOuter_seq'`,
this wrapper discharges the `houter` hypothesis using
`eventually_frechetGradient_mem_normThickening_exposedFace_of_sourceCube_ray`. Thus the remaining
mathematical input is the Straszewicz-style approximation of extreme subgradients by exposed
subgradients. -/
theorem SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (Set.exposedPoints ℝ
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q})) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray_one_unitOuter_seq'
    hn hbounded hconvex hstrasz
    (fun {_y _p _normal} hy _hp hnormal _hexposed {_φ} hmem hclose =>
      eventually_frechetGradient_mem_normThickening_exposedFace_of_sourceCube_ray
        hbounded hconvex hy hnormal hmem hclose)

/-- Inner-cube source-cube cluster density from the standard compact-convex Straszewicz theorem.

This is the source-cube bridge from the reusable convex-geometry theorem boundary
`StraszewiczCompactConvexStatement` to the Rockafellar subgradient cluster-density input. -/
theorem SourceCubeSubgradientClusterDensity.of_straszewiczCompactConvex
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz : StraszewiczCompactConvexStatement (SourceCubeSpace n)) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray
    hn hbounded hconvex
    (fun {y} hy => by
      exact hstrasz
        (isCompact_setOf_subgradientOn_of_isBounded
          (sourceCube_subgradient_set_isBounded_of_boundedOn_three_halves hbounded
            (sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
              (by norm_num) hy)))
        convex_setOf_subgradientOn)

/-- Inner-cube source-cube cluster density from the proved compact-convex Straszewicz theorem. -/
theorem SourceCubeSubgradientClusterDensity.of_compactStraszewicz
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_straszewiczCompactConvex
    hn hbounded hconvex
    (straszewiczCompactConvexStatement (E := SourceCubeSpace n))

end AleksandrovDifferentiability

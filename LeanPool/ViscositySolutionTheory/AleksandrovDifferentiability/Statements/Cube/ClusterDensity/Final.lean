/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.ClusterDensity.Ray
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Wrappers

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Source-cube cluster-density final assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

theorem SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_outer_sourceCube_one
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
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
          ExposesPoint
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p →
            ∀ ε > 0,
              ∀ᶠ w in 𝓝[sourceCubeDifferentiabilitySet n 1 u] y,
                frechetGradient u w ∈
                  normThickening
                    (exposedFace
                      {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}
                      normal) ε) :
    SourceCubeSubgradientClusterDensity n u := by
  have hlocal :
      LocalSubgradientClusterDensityOn (sourceOpenCube n 3) (sourceOpenCube n 1) u := by
    refine localSubgradientClusterDensityOn_of_bounded_mathlibStraszewicz_outer
      (domain := sourceOpenCube n 3)
      (sample := sourceOpenCube n 1)
      (u := u)
      ?_ hstrasz ?_ ?_
    · intro y hy
      exact sourceCube_subgradient_set_isBounded_of_boundedOn_three_halves hbounded
        (sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
          (by norm_num) hy)
    · intro y hy
      simpa [differentiabilitySetOn, sourceCubeDifferentiabilitySet,
        firstOrderDifferentiabilitySet] using
        sourceOpenCube_one_nhdsWithin_sourceCubeDifferentiabilitySet_one_neBot_of_convex
          hconvex hy
    · intro y p normal hy hexposed ε hε
      simpa [differentiabilitySetOn, sourceCubeDifferentiabilitySet,
        firstOrderDifferentiabilitySet, frechetGradient, gradient] using
        houter hy hexposed ε hε
  intro x m hxgood
  have hxQ1 : x ∈ sourceOpenCube n 1 :=
    cubeGoodSet_subset_sourceOpenCube_one hxgood
  have hQ1_nhds : sourceOpenCube n 1 ∈ 𝓝 x :=
    (isOpen_sourceOpenCube (n := n) 1).mem_nhds hxQ1
  have hQ1_event_nhds : ∀ᶠ y in 𝓝 x, y ∈ sourceOpenCube n 1 :=
    hQ1_nhds
  have hQ1_event :
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x, y ∈ sourceOpenCube n 1 :=
    hQ1_event_nhds.filter_mono inf_le_left
  filter_upwards [hQ1_event] with y hyQ1 p hp
  have hdensity := hlocal hyQ1 hp
  have hD :
      differentiabilitySetOn (sourceOpenCube n 1) u ⊆
        differentiabilitySetOn (sourceOpenCube n (3 / 2 : ℝ)) u := by
    intro w hw
    exact
      ⟨sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
          (by norm_num) hw.1,
        hw.2⟩
  have hmono :=
    HasSubgradientLinearizationOnAt.GradientClusterSet.mem_closure_convexHull_mono
      (D₁ := differentiabilitySetOn (sourceOpenCube n 1) u)
      (D₂ := differentiabilitySetOn (sourceOpenCube n (3 / 2 : ℝ)) u)
      (G := gradient u) (y := y) (p := p) hD hdensity
  simpa only [differentiabilitySetOn, sourceCubeDifferentiabilitySet,
    firstOrderDifferentiabilitySet, frechetGradient_eq_gradient] using hmono

/-- If the local Rockafellar theorem is available in the source cube space, then the cube-level
cluster-density statement has exactly the quantifiers used by the Aleksandrov assembly. -/
theorem SourceCubeSubgradientClusterDensityStatement.of_rockafellarLocal
    {n : ℕ}
    (hrock :
      RockafellarLocalSubgradientClusterDensityStatement (SourceCubeSpace n)) :
    SourceCubeSubgradientClusterDensityStatement n := by
  intro u hconvex
  exact SourceCubeSubgradientClusterDensity.of_rockafellarLocal
    (hrock
      (domain := sourceOpenCube n 3)
      (sample := sourceOpenCube n (3 / 2 : ℝ))
      (u := u)
      (isOpen_sourceOpenCube (n := n) 3)
      (isOpen_sourceOpenCube (n := n) (3 / 2 : ℝ))
      (sourceOpenCube_subset_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num))
      hconvex)

/-- The normalized source-cube Aleksandrov theorem from the named cluster-density statement.

All other cube-local analytic inputs are now supplied by the concrete convex Stieltjes route and
the second-order assembly in `Statements.Cube.SecondOrder`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_subgradientClusterDensity
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity : SourceCubeSubgradientClusterDensityStatement n) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_convexSourceRightDerivStieltjes
    hn hbounded hconvex (hdensity hconvex)

/-- Normalized source-cube Aleksandrov theorem from the remaining Straszewicz-style
convex-geometry input.

The directional exposed-face outer semicontinuity part of Rockafellar 25.6 is discharged by
`SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray`; the only hypothesis left
here is that the extreme points of each source-cube subdifferential are limits of Mathlib exposed
points. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_mathlibStraszewicz
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (Set.exposedPoints ℝ
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q})) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_convexSourceRightDerivStieltjes
    hn hbounded hconvex
    (SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray
      hn hbounded hconvex hstrasz)

/-- Normalized source-cube Aleksandrov theorem from the standard compact-convex Straszewicz
theorem.

This is now the cleanest source-cube boundary: after the upper-contact/Stieltjes analysis and
Rockafellar directional outer-semicontinuity work, the only remaining external convex-geometry
input is `StraszewiczCompactConvexStatement` for the finite-dimensional source cube space. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_straszewiczCompactConvex
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz : StraszewiczCompactConvexStatement (SourceCubeSpace n)) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_convexSourceRightDerivStieltjes
    hn hbounded hconvex
    (SourceCubeSubgradientClusterDensity.of_straszewiczCompactConvex
      hn hbounded hconvex hstrasz)

/-- Normalized source-cube Aleksandrov theorem for bounded convex functions.

This version discharges the compact-convex Straszewicz input using
`straszewiczCompactConvexStatement`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_straszewiczCompactConvex
    hn hbounded hconvex
    (straszewiczCompactConvexStatement (E := SourceCubeSpace n))

/-- Normalized source-cube Aleksandrov theorem from the local Rockafellar cluster-density theorem.

This is the current source-faithful cube boundary: all analytic and integration work has already
been discharged, and the remaining density input is exactly the local interior consequence of
Rockafellar 25.6. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_rockafellarLocal
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hrock :
      RockafellarLocalSubgradientClusterDensityStatement (SourceCubeSpace n)) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_subgradientClusterDensity
    hn hbounded hconvex
    (SourceCubeSubgradientClusterDensityStatement.of_rockafellarLocal hrock)

end AleksandrovDifferentiability

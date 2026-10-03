/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Envelope
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.EpigraphLineLift
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineIntegral

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Cube-local second-order assembly

This file records the final measure-theoretic assembly step in the source cube proof. The
remaining mathematical work is pointwise: turn the source-route gradient expansion at a good point
into `SecondOrderDifferentiableAt`. Once that pointwise bridge is available, the a.e. cube
statement follows immediately from the countable good-set/envelope theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open Asymptotics
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

/-- At a source good point, every subgradient on the ambient source cube is the Fréchet
gradient.

This is the base-point input in the source subgradient-extension argument. The point `x` belongs
to `Q_1`, hence has a neighborhood inside `Q_3`, and membership in the good set includes
Fréchet differentiability at `x`. -/
theorem cubeGoodSet_subgradient_eq_frechetGradient
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A : ℝ} {x p : SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u A)
    (hp : SubgradientOn (sourceOpenCube n 3) u x p) :
    p = frechetGradient u x := by
  rcases mem_cubeGoodSet.mp hxgood with ⟨hxQ, hdiff, _hopening⟩
  have hxInterior : x ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_one_subset_interior_three hxQ
  have hs : sourceOpenCube n 3 ∈ 𝓝 x :=
    (isOpen_sourceOpenCube (n := n) 3).mem_nhds (interior_subset hxInterior)
  change p = gradient u x
  exact hp.eq_gradient_of_differentiableAt hs hdiff

/-- Cube-local subgradient extension from cluster-gradient density.

This is the source `subgradient-extension` lemma with the hard convex-analysis input exposed as
`hdensity`. The estimate `hgradient` is the moving-base gradient estimate produced from the
good-point gradient expansion in the LaTeX proof. -/
theorem sourceCube_subgradientLinearization_of_clusterConvexHull
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hgradient : ∀ ε > 0,
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ᶠ w in 𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] y,
        ‖frechetGradient u w - (frechetGradient u x + B (y - x))‖ ≤
          ε * ‖y - x‖)
    (hdensity : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y)))
    (hbase : ∀ p : SourceCubeSpace n,
      SubgradientOn (sourceOpenCube n 3) u x p → p = frechetGradient u x) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  HasSubgradientLinearizationOnAt.of_punctured_eventually_gradient_estimates_of_cluster_convexHull
    (domain := sourceOpenCube n 3)
    (D := sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
    (approach := sourceOpenCube n (3 / 2 : ℝ))
    (u := u) (G := frechetGradient u) (x := x) (p₀ := frechetGradient u x)
    (B := B) hgradient hdensity hbase

/-- Good-point version of the cube-local subgradient extension.

The abstract cluster-gradient bridge requires a separate base-point uniqueness hypothesis. At a
good point this is automatic, because the good set records differentiability at the base point. -/
theorem sourceCube_good_subgradientLinearization_of_clusterConvexHull
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hgradient : ∀ ε > 0,
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ᶠ w in 𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] y,
        ‖frechetGradient u w - (frechetGradient u x + B (y - x))‖ ≤
          ε * ‖y - x‖)
    (hdensity : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y))) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_subgradientLinearization_of_clusterConvexHull
    hgradient hdensity (fun _ hp => cubeGoodSet_subgradient_eq_frechetGradient hxgood hp)

/-- Good-point subgradient extension from the source-route gradient little-o expansion.

This is the cube-local form needed after the Lipschitz-envelope step: the envelope argument
produces a little-o expansion of `frechetGradient u` along the dense differentiability set
`D_{3/2}`. The generic moving-base lemma converts that into the punctured estimates required by
the cluster-gradient subgradient bridge. The remaining hypothesis is exactly the source
finite-dimensional density theorem for subgradients. -/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_clusterConvexHull
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hdensity : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y))) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_good_subgradientLinearization_of_clusterConvexHull
    hxgood
    (HasSubgradientLinearizationOnAt.eventually_gradient_estimates_of_isLittleO hgradient)
    hdensity

/-- Good-point subgradient extension from gradient expansion and directional halfspace tests.

This is the current source-facing form of the remaining cluster-density step. Instead of asking
directly for membership in the closed convex hull of gradient cluster values, it asks for the
separating-halfspace consequence: every linear upper bound valid on the gradient cluster set is
valid for each nearby subgradient. The closed-convex-hull membership is then supplied by the
`clusterDensity_of_eventually_forall_inner_le` helper.
-/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_halfspace
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hhalfspace : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        ∀ z : SourceCubeSpace n, ∀ c : ℝ,
          (∀ q ∈
            HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y, inner ℝ q z ≤ c) →
            inner ℝ p z ≤ c) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_good_subgradientLinearization_of_gradientExpansion_and_clusterConvexHull
    hxgood hgradient
    (HasSubgradientLinearizationOnAt.clusterDensity_of_eventually_forall_inner_le hhalfspace)

/-- Good-point subgradient extension from gradient expansion and directional cluster domination.

This is the source-facing form closest to the one-dimensional convex argument: for each nearby
punctured point `y`, every subgradient directional value `p · z` is dominated by some cluster
gradient directional value `q · z`. The halfspace and closed-convex-hull conclusions are then
formal consequences. -/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_directionalCluster
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hdom : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        ∀ z : SourceCubeSpace n,
          ∃ q ∈
            HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y, inner ℝ p z ≤ inner ℝ q z) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_good_subgradientLinearization_of_gradientExpansion_and_clusterConvexHull
    hxgood hgradient
    (HasSubgradientLinearizationOnAt.clusterDensity_of_eventually_directional_dominating_cluster
      hdom)

/-- Good-point subgradient extension from gradient expansion and right-derivative cluster
domination.

This separates the remaining one-dimensional convex-analysis input from the already-formalized
subgradient inequality `p · z <= D_+ (u(y + t z))|_{t = 0}`. It remains to prove that the right
derivative is dominated by a directional value of some nearby gradient cluster value. -/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_lineRightDerivCluster
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hcluster : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ z : SourceCubeSpace n,
        ∃ q ∈
          HasSubgradientLinearizationOnAt.GradientClusterSet
            (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
            (frechetGradient u) y,
          rightDeriv (lineRestriction u y z) 0 ≤ inner ℝ q z) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B := by
  have hInterior :
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
        y ∈ interior (sourceOpenCube n 3) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact sourceOpenCube_subset_interior_of_le
      (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hy.1
  exact
    sourceCube_good_subgradientLinearization_of_gradientExpansion_and_directionalCluster
      hxgood hgradient
      (eventually_directional_dominating_cluster_of_lineRightDeriv_le
        hconvex hInterior hcluster)

/-- Auxiliary good-point wrapper from positive-line gradient clusters.

This theorem is useful as a filter-transport interface, but it is not the active source route.
For a full-measure differentiability set, one should not expect every affine line through every
nearby `y` and direction `z` to contain differentiability points accumulating at `y`.
-/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_posLineCluster
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hlineCluster : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ z : SourceCubeSpace n,
        ∃ q : SourceCubeSpace n,
          MapClusterPt q
            (𝓝[{t : ℝ |
              0 < t ∧ y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
              (0 : ℝ))
            (fun t : ℝ => frechetGradient u (y + t • z)) ∧
          rightDeriv (lineRestriction u y z) 0 ≤ inner ℝ q z) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_good_subgradientLinearization_of_gradientExpansion_and_lineRightDerivCluster
    hxgood hconvex hgradient
    (hlineCluster.mono fun _ hy z =>
      let ⟨q, hqCluster, hqRight⟩ := hy z
      ⟨q, HasSubgradientLinearizationOnAt.GradientClusterSet.mem_of_posLineMapClusterPt
        hqCluster, hqRight⟩)

/-- Auxiliary positive-line wrapper with line right-derivative realization along the same filter.

This is parked as a non-source-route interface: the source proof uses ambient subgradient-density
from gradients approaching `y`, not existence of linewise differentiability clusters for every
direction. -/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_posLineClusterRealization
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hlineCluster : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ z : SourceCubeSpace n,
        ∃ q : SourceCubeSpace n,
          MapClusterPt q
            (𝓝[{t : ℝ |
              0 < t ∧ y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
              (0 : ℝ))
            (fun t : ℝ => frechetGradient u (y + t • z)) ∧
          ∀ᶠ t in 𝓝[{t : ℝ |
              0 < t ∧ y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
              (0 : ℝ),
            rightDeriv (lineRestriction u y z) t =
              inner ℝ (frechetGradient u (y + t • z)) z) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B := by
  have hInterior :
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
        y ∈ interior (sourceOpenCube n 3) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact sourceOpenCube_subset_interior_of_le
      (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hy.1
  refine sourceCube_good_subgradientLinearization_of_gradientExpansion_and_posLineCluster
    hxgood hconvex hgradient ?_
  filter_upwards [hlineCluster, hInterior] with y hyLine hyInterior z
  rcases hyLine z with ⟨q, hqCluster, hqRealize⟩
  exact
    ⟨q, hqCluster,
      ConvexOn.lineRightDeriv_le_inner_of_posLine_gradient_mapClusterPt
        hconvex hyInterior hqCluster hqRealize⟩

/-- Along the source differentiability set, the line-restricted right derivative is eventually
realized by the Fréchet gradient directional component. -/
theorem eventually_lineRightDeriv_eq_inner_frechetGradient_of_sourceCubeDifferentiabilitySet
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {y z : SourceCubeSpace n} :
    ∀ᶠ t in 𝓝[{t : ℝ |
        0 < t ∧ y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
        (0 : ℝ),
      rightDeriv (lineRestriction u y z) t =
        inner ℝ (frechetGradient u (y + t • z)) z := by
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have hdiff : DifferentiableAt ℝ u (y + t • z) := ht.2.2
  calc
    rightDeriv (lineRestriction u y z) t
        = fderiv ℝ u (y + t • z) z :=
          lineRestriction_rightDeriv_eq_fderiv_apply_of_differentiableAt hdiff
    _ = inner ℝ (frechetGradient u (y + t • z)) z :=
          fderiv_apply_eq_inner_frechetGradient u (y + t • z) z

/-- Auxiliary wrapper reducing positive-line cluster realization to positive-line cluster
existence.

The realization part is automatic on the differentiability-set filter, but the remaining
existence hypothesis is generally too strong for the main Aleksandrov route. The source-aligned
boundary remains the ambient closed-convex-hull cluster-density theorem. -/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_posLineClusterExistence
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hlineCluster : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ z : SourceCubeSpace n,
        ∃ q : SourceCubeSpace n,
          MapClusterPt q
            (𝓝[{t : ℝ |
              0 < t ∧ y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
              (0 : ℝ))
            (fun t : ℝ => frechetGradient u (y + t • z))) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_good_subgradientLinearization_of_gradientExpansion_and_posLineClusterRealization
    hxgood hconvex hgradient
    (hlineCluster.mono fun y hyLine z =>
      let ⟨q, hqCluster⟩ := hyLine z
      ⟨q, hqCluster,
        eventually_lineRightDeriv_eq_inner_frechetGradient_of_sourceCubeDifferentiabilitySet
          (n := n) (u := u) (y := y) (z := z)⟩)

/-- Segment form of cube-local subgradient linearization at a good point.

This is the estimate used by the source proof before integrating along
`s ↦ u (x + s • z)`: after shrinking `z`, every point of the segment lies in `Q_{3/2}`, and every
subgradient there is modeled by `frechetGradient u x + B (s • z)` up to
`ε * ‖s • z‖`. -/
theorem cubeGoodSet_eventually_segment_subgradientLinearization
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ∀ p : SourceCubeSpace n,
          SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
            ‖p - (frechetGradient u x + B (t • z))‖ ≤ ε * ‖t • z‖ := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.eventually_segment_estimates hlin
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)

/-- Scalar directional form of cube-local segment subgradient linearization.

This is the estimate that feeds the source proof's right-derivative/integration calculation:
after pairing each segment subgradient with the segment direction `z`, the error from the affine
function `inner (frechetGradient u x) z + t * inner z (B z)` is bounded by
`ε * ‖z‖ ^ 2`. -/
theorem cubeGoodSet_eventually_segment_inner_subgradientLinearization
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ∀ p : SourceCubeSpace n,
          SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
            |inner ℝ p z - (inner ℝ (frechetGradient u x) z + t * inner ℝ z (B z))| ≤
              ε * ‖z‖ ^ 2 := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.eventually_segment_inner_estimates hlin
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)

/-- Good-point Taylor expansion from subgradient linearization and the source line-derivative
bridge.

This packages the final integration step after the segment subgradient estimate. The remaining
line hypotheses are intentionally explicit: convexity supplies the right-derivative integral
representation and integrability, while the source support-function identity supplies
`hrightSubgradient`. -/
theorem cubeGoodSet_hasSecondOrderExpansionAt_of_lineRightDeriv
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B)
    (hrepr : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hrightSubgradient : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n,
          SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
            rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    HasSecondOrderExpansionAt u x (frechetGradient u x) B := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineRightDeriv hlin
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)
      hrepr hint hrightSubgradient

/-- For a good point `x ∈ Q_1`, all sufficiently short source increments have their whole
unit parameter interval inside the interior of the line domain for `Q_3`. -/
theorem cubeGoodSet_eventually_uIcc_subset_interior_lineDomain
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ)) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      Set.uIcc (0 : ℝ) 1 ⊆ interior (lineDomain (sourceOpenCube n 3) x z) := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  filter_upwards [eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ] with
    z hzsegment t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using ht
  have ht_three_halves : x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ) :=
    hzsegment t htIcc
  have htInterior : x + t • z ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
      (by norm_num) ht_three_halves
  have htLine : t ∈ lineDomain (sourceOpenCube n 3) x z := by
    simpa [lineDomain] using interior_subset htInterior
  have hopen : IsOpen (lineDomain (sourceOpenCube n 3) x z) :=
    isOpen_lineDomain (s := sourceOpenCube n 3) (x := x) (v := z)
      (isOpen_sourceOpenCube (n := n) 3)
  exact mem_interior_iff_mem_nhds.mpr (hopen.mem_nhds htLine)

/-- Convex line-restriction right-derivative integrability on the unit segment, eventually in
the source increment. -/
theorem cubeGoodSet_eventually_lineRightDeriv_intervalIntegrable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1 := by
  filter_upwards [cubeGoodSet_eventually_uIcc_subset_interior_lineDomain hxgood] with z hz
  exact ConvexOn.lineRestriction_intervalIntegrable_rightDeriv_of_uIcc_subset_interior
    (x := x) (v := z) hconvex hz

/-- Convex line-restriction right-derivative FTC representation on the unit segment, eventually
in the source increment. -/
theorem cubeGoodSet_eventually_lineRightDeriv_integral_repr
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t := by
  filter_upwards [cubeGoodSet_eventually_uIcc_subset_interior_lineDomain hxgood] with z hz
  exact ConvexOn.lineRestriction_sub_eq_integral_rightDeriv_of_uIcc_subset_interior
    (x := x) (v := z) hconvex hz

/-- For a good point `x ∈ Q_1`, all sufficiently short nontrivial segment parameters lie in the
ambient interior of `Q_3`. -/
theorem cubeGoodSet_eventually_segment_mem_interior_sourceOpenCube_three
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ)) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior (sourceOpenCube n 3) := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  filter_upwards [eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ] with z hzsegment
    t ht
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa using ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
  exact
    sourceOpenCube_subset_interior_of_le
      (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) (hzsegment t htIcc)

/-- Symmetric-operator version of
`cubeGoodSet_hasSecondOrderExpansionAt_of_lineRightDeriv`, yielding the project
`SecondOrderDifferentiableAt` predicate. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_lineRightDeriv
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B)
    (hB : IsSymmetricOperator B)
    (hrepr : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hrightSubgradient : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n,
          SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
            rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (cubeGoodSet_hasSecondOrderExpansionAt_of_lineRightDeriv
      hxgood hlin hrepr hint hrightSubgradient)

/-- Good-point second-order differentiability from subgradient linearization and the source
line-derivative bridge.

This version does not require a separate symmetry proof for `B`; the symmetric part of `B` has
the same quadratic form and is used in the final `SecondOrderDifferentiableAt` witness. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_lineRightDeriv_symmetricPart
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B)
    (hrepr : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hrightSubgradient : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n,
          SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
            rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    SecondOrderDifferentiableAt u x := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineRightDeriv hlin
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)
      hrepr hint hrightSubgradient

/-- Good-point second-order differentiability from subgradient linearization and the
line-subgradient lift interface.

This lower-level compatibility form of the final integration step keeps the vector-valued
line-subgradient lift as an explicit hypothesis. The preferred wrapper below supplies the lift
from strict-epigraph separation. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientLift
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B)
    (hlift : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain (sourceOpenCube n 3) x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient (sourceOpenCube n 3) u x z t q) :
    SecondOrderDifferentiableAt u x := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineSubgradientLift hlin
      hconvex
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)
      (cubeGoodSet_eventually_segment_mem_interior_sourceOpenCube_three hxgood)
      (cubeGoodSet_eventually_lineRightDeriv_integral_repr hxgood hconvex)
      (cubeGoodSet_eventually_lineRightDeriv_intervalIntegrable hxgood hconvex)
      hlift

/-- Good-point second-order differentiability from subgradient linearization and the functional
line-subgradient lift interface.

This lower-level compatibility form keeps the functional line-subgradient lift as an explicit
hypothesis. The preferred wrapper below supplies it from Mathlib Hahn-Banach separation. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientFunctional
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B)
    (hlift : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain (sourceOpenCube n 3) x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional (sourceOpenCube n 3) u x z t q) :
    SecondOrderDifferentiableAt u x := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineSubgradientFunctional hlin
      hconvex
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)
      (cubeGoodSet_eventually_segment_mem_interior_sourceOpenCube_three hxgood)
      (cubeGoodSet_eventually_lineRightDeriv_integral_repr hxgood hconvex)
      (cubeGoodSet_eventually_lineRightDeriv_intervalIntegrable hxgood hconvex)
      hlift

/-- Good-point second-order differentiability from subgradient linearization alone.

The line-subgradient ambient lift is supplied by the strict-epigraph separation theorem in
`ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen`, so no separate Hahn-Banach
hypothesis remains at this point. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_subgradientLinearization
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B) :
    SecondOrderDifferentiableAt u x :=
  cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientFunctional
    hxgood hconvex hlin
    (Filter.Eventually.of_forall fun _z _t _ht _q hq =>
      ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen
        hconvex (isOpen_sourceOpenCube (n := n) 3) hq)

end AleksandrovDifferentiability

/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.SecondOrder.Pointwise

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Cube-local second-order a.e. assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_subgradientLinearization_bridge
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hsubgradientExtension :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            HasSubgradientLinearizationOnAt
              (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
              u x (frechetGradient u x) B)
    (htaylor :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            HasSubgradientLinearizationOnAt
              (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
              u x (frechetGradient u x) B →
            SecondOrderDifferentiableAt u x) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
by
  filter_upwards
    [ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_expansion_three_halves_of_convex
      hfiniteStatement hn hbounded hconvex] with x hx
  rcases hx with ⟨m, hxgood, B, hB⟩
  exact htaylor x m B hxgood hB (hsubgradientExtension x m B hxgood hB)

/-- Source-route a.e. second-order differentiability on `Q_1`, with the subgradient-extension
step reduced to the finite-dimensional cluster-density theorem.

The envelope theorem supplies the good point, the linear map `B`, and the gradient little-o
expansion. The hypothesis `hdensity` is the remaining convex-analysis input identifying nearby
subgradients with the closed convex hull of cluster gradients. The hypothesis `htaylor` is the
last integration step converting subgradient linearization into a second-order Taylor expansion. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y)))
    (htaylor :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            HasSubgradientLinearizationOnAt
              (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
              u x (frechetGradient u x) B →
            SecondOrderDifferentiableAt u x) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_subgradientLinearization_bridge
    hfiniteStatement hn hbounded hconvex
    (fun x m _ hxgood hB =>
      sourceCube_good_subgradientLinearization_of_gradientExpansion_and_clusterConvexHull
        hxgood hB (hdensity x m hxgood))
    htaylor

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the remaining
source-facing pointwise inputs.

At this boundary the envelope theorem and subgradient-extension bridge have already been used.
The remaining hypotheses are the finite-dimensional cluster-density theorem, the
right-derivative/support-function identity along short segments. The symmetric part of the
linear map selected by the gradient-expansion step supplies the symmetric Hessian witness. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_lineRightDeriv
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y)))
    (hrightSubgradient :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
            ∀ t ∈ Set.uIoc (0 : ℝ) 1,
              ∃ p : SourceCubeSpace n,
                SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
                  rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    hfiniteStatement hn hbounded hconvex hdensity
    (fun x m _B hxgood _hgradient hlin =>
      cubeGoodSet_secondOrderDifferentiableAt_of_lineRightDeriv_symmetricPart
        hxgood hlin
        (cubeGoodSet_eventually_lineRightDeriv_integral_repr hxgood hconvex)
        (cubeGoodSet_eventually_lineRightDeriv_intervalIntegrable hxgood hconvex)
        (hrightSubgradient x m hxgood))

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the cluster-density
theorem and the ambient lift theorem for line subgradients.

This is sharper than
`ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_lineRightDeriv`: the
one-dimensional fact that the right derivative is a line subgradient has already been discharged,
so the remaining support-function input is stated as a lift of arbitrary line subgradients to
ambient subgradients with the same directional pairing. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_lineSubgradientLift
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y)))
    (hlift :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
            ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
              SubgradientOn (lineDomain (sourceOpenCube n 3) x z) (lineRestriction u x z) t q →
                LineSubgradientLiftsToAmbient (sourceOpenCube n 3) u x z t q) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    hfiniteStatement hn hbounded hconvex hdensity
    (fun x m _B hxgood _hgradient hlin =>
      cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientLift
        hxgood hconvex hlin (hlift x m hxgood))

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the cluster-density
theorem and an explicit functional ambient lift theorem for line subgradients.

This remains as a compatibility boundary; the direct cluster-density wrapper below supplies the
functional lift from strict-epigraph separation. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_functionalLift
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y)))
    (hlift :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
            ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
              SubgradientOn (lineDomain (sourceOpenCube n 3) x z) (lineRestriction u x z) t q →
                LineSubgradientLiftsToAmbientFunctional (sourceOpenCube n 3) u x z t q) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    hfiniteStatement hn hbounded hconvex hdensity
    (fun x m _B hxgood _hgradient hlin =>
      cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientFunctional
        hxgood hconvex hlin (hlift x m hxgood))

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the finite-dimensional
cluster-density theorem for convex subgradients.

The line-subgradient lift is no longer an external hypothesis: it is supplied by Mathlib
Hahn-Banach separation through `ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y))) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    hfiniteStatement hn hbounded hconvex hdensity
    (fun _x _m _B hxgood _hgradient hlin =>
      cubeGoodSet_secondOrderDifferentiableAt_of_subgradientLinearization
        hxgood hconvex hlin)

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the directional
halfspace form of the finite-dimensional subgradient cluster-density theorem.

This is the most scalar form of the remaining cube-level input: at good points and nearby
punctured points, each subgradient must satisfy every linear upper bound that holds for all
cluster values of the Fréchet gradient along `D_{3/2}`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterHalfspace
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hhalfspace :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              ∀ z : SourceCubeSpace n, ∀ c : ℝ,
                (∀ q ∈
                  HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y, inner ℝ q z ≤ c) →
                  inner ℝ p z ≤ c) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood =>
      HasSubgradientLinearizationOnAt.clusterDensity_of_eventually_forall_inner_le
        (hhalfspace x m hxgood))

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to directional
dominating cluster values.

This is the current closest formal boundary to the scalar convex proof: each directional value
of each nearby subgradient is bounded above by the same directional value of some cluster
gradient along `D_{3/2}`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_directionalCluster
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdom :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              ∀ z : SourceCubeSpace n,
                ∃ q ∈
                  HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y, inner ℝ p z ≤ inner ℝ q z) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood =>
      HasSubgradientLinearizationOnAt.clusterDensity_of_eventually_directional_dominating_cluster
        (hdom x m hxgood))

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the right-derivative
cluster domination theorem along arbitrary directions. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_lineRightDerivCluster
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hcluster :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ z : SourceCubeSpace n,
              ∃ q ∈
                HasSubgradientLinearizationOnAt.GradientClusterSet
                  (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                  (frechetGradient u) y,
                rightDeriv (lineRestriction u y z) 0 ≤ inner ℝ q z) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_directionalCluster
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood => by
      have hInterior :
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            y ∈ interior (sourceOpenCube n 3) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact sourceOpenCube_subset_interior_of_le
          (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hy.1
      exact eventually_directional_dominating_cluster_of_lineRightDeriv_le
        hconvex hInterior (hcluster x m hxgood))

/-- Auxiliary a.e. wrapper reduced to positive-line gradient clusters along arbitrary directions.

This is not the active source route; the linewise cluster hypothesis is stronger than the
ambient cluster-density theorem used by the source proof. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_posLineCluster
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlineCluster :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ z : SourceCubeSpace n,
              ∃ q : SourceCubeSpace n,
                MapClusterPt q
                  (𝓝[{t : ℝ |
                    0 < t ∧
                      y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
                    (0 : ℝ))
                  (fun t : ℝ => frechetGradient u (y + t • z)) ∧
                rightDeriv (lineRestriction u y z) 0 ≤ inner ℝ q z) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_lineRightDerivCluster
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood =>
      (hlineCluster x m hxgood).mono fun _ hy z =>
        let ⟨q, hqCluster, hqRight⟩ := hy z
        ⟨q, HasSubgradientLinearizationOnAt.GradientClusterSet.mem_of_posLineMapClusterPt
          hqCluster, hqRight⟩)

/-- Auxiliary a.e. wrapper with positive-line clusters and line right-derivative realization.

This interface is retained for possible reuse, but the main formalization should proceed through
ambient subgradient cluster-density. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_posLineClusterRealization
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlineCluster :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ z : SourceCubeSpace n,
              ∃ q : SourceCubeSpace n,
                MapClusterPt q
                  (𝓝[{t : ℝ |
                    0 < t ∧
                      y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
                    (0 : ℝ))
                  (fun t : ℝ => frechetGradient u (y + t • z)) ∧
                ∀ᶠ t in 𝓝[{t : ℝ |
                    0 < t ∧
                      y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
                    (0 : ℝ),
                  rightDeriv (lineRestriction u y z) t =
                    inner ℝ (frechetGradient u (y + t • z)) z) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_posLineCluster
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood => by
      have hInterior :
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            y ∈ interior (sourceOpenCube n 3) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact sourceOpenCube_subset_interior_of_le
          (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hy.1
      filter_upwards [hlineCluster x m hxgood, hInterior] with y hyLine hyInterior z
      rcases hyLine z with ⟨q, hqCluster, hqRealize⟩
      exact
        ⟨q, hqCluster,
          ConvexOn.lineRightDeriv_le_inner_of_posLine_gradient_mapClusterPt
            hconvex hyInterior hqCluster hqRealize⟩)

/-- Auxiliary a.e. wrapper reduced to existence of positive-line gradient clusters.

The right-derivative realization is automatic on the differentiability-set filter, but the
linewise cluster-existence hypothesis is not the source theorem and is generally too strong as a
main target. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_posLineClusterExistence
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlineCluster :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ z : SourceCubeSpace n,
              ∃ q : SourceCubeSpace n,
                MapClusterPt q
                  (𝓝[{t : ℝ |
                    0 < t ∧
                      y + t • z ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u}]
                    (0 : ℝ))
                  (fun t : ℝ => frechetGradient u (y + t • z))) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_posLineClusterRealization
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood =>
      (hlineCluster x m hxgood).mono fun y hyLine z =>
        let ⟨q, hqCluster⟩ := hyLine z
        ⟨q, hqCluster,
          eventually_lineRightDeriv_eq_inner_frechetGradient_of_sourceCubeDifferentiabilitySet
            (n := n) (u := u) (y := y) (z := z)⟩)

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the pointwise bridge
from good-set gradient expansion to second-order differentiability.

This is the formal version of the last paragraph of the cube proof before global rescaling:
the countable union of good sets covers `Q_1` up to a null set, the envelope argument supplies a
linearization of the gradient at almost every good point, and a pointwise theorem converts that
linearization into the second-order Taylor expansion. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_goodSet_gradient_expansion
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hpoint :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            SecondOrderDifferentiableAt u x) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x := by
  filter_upwards
    [ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_expansion_three_halves_of_convex
      hfiniteStatement hn hbounded hconvex] with x hx
  rcases hx with ⟨m, hxgood, B, hB⟩
  exact hpoint x m B hxgood hB

end AleksandrovDifferentiability

/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster.Pointwise

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact and bounded Straszewicz cluster reductions

This module packages compact and bounded subdifferential versions of the Rockafellar exposed-point
route, leaving the Straszewicz approximation input explicit.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Compact subdifferential version of the Rockafellar exposed-point route.

For a compact subdifferential, Mathlib's Krein-Milman theorem reduces the closed-convex-hull
representation to a Straszewicz-style hypothesis that extreme points are approximated by exposed
points. If exposed subgradients are already known to lie in the gradient cluster closed convex
hull, then every subgradient has the desired cluster-density conclusion. -/
theorem mem_closure_convexHull_gradientClusterSet_of_compact_straszewicz_exposedCluster
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hcompact : IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
        closure (convexHull ℝ (exposedPoints {q : E | SubgradientOn domain u y q})))
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
  refine mem_closure_convexHull_gradientClusterSet_of_exposedPoint_reduction ?_ hexposed_cluster hp
  exact
    subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_convexHull_exposedPoints
      hcompact convex_setOf_subgradientOn hstrasz

/-- Compact subdifferential version using the literal Straszewicz hypothesis that extreme points
are limits of exposed points. -/
theorem mem_closure_convexHull_gradientClusterSet_of_compact_straszewiczClosure_exposedCluster
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hcompact : IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
        closure (exposedPoints {q : E | SubgradientOn domain u y q}))
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
  refine mem_closure_convexHull_gradientClusterSet_of_exposedPoint_reduction ?_ hexposed_cluster hp
  exact
    subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_exposedPoints
      hcompact convex_setOf_subgradientOn hstrasz

/-- Compact subdifferential version using a Mathlib-shaped literal Straszewicz hypothesis. -/
theorem mem_closure_convexHull_gradientClusterSet_of_compact_mathlibStraszewicz_exposedCluster
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hcompact : IsCompact {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
        closure (Set.exposedPoints ℝ {q : E | SubgradientOn domain u y q}))
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
  refine mem_closure_convexHull_gradientClusterSet_of_exposedPoint_reduction ?_
    hexposed_cluster hp
  exact
    subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_mathlib_exposedPoints
      hcompact convex_setOf_subgradientOn hstrasz

/-- Bounded-subdifferential version of the compact Rockafellar exposed-point route.

In finite-dimensional source-cube applications, boundedness of the subdifferential is usually the
available local input; properness of the ambient metric space turns that bounded closed
subdifferential into a compact set. -/
theorem mem_closure_convexHull_gradientClusterSet_of_bounded_straszewicz_exposedCluster
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hbounded : Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
        closure (convexHull ℝ (exposedPoints {q : E | SubgradientOn domain u y q})))
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
          (differentiabilitySetOn sample u) (gradient u) y)) :=
  mem_closure_convexHull_gradientClusterSet_of_compact_straszewicz_exposedCluster
    (isCompact_setOf_subgradientOn_of_isBounded hbounded) hstrasz hexposed_cluster hp

/-- Bounded-subdifferential version using the literal Straszewicz closure hypothesis. -/
theorem mem_closure_convexHull_gradientClusterSet_of_bounded_straszewiczClosure_exposedCluster
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hbounded : Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
        closure (exposedPoints {q : E | SubgradientOn domain u y q}))
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
          (differentiabilitySetOn sample u) (gradient u) y)) :=
  mem_closure_convexHull_gradientClusterSet_of_compact_straszewiczClosure_exposedCluster
    (isCompact_setOf_subgradientOn_of_isBounded hbounded) hstrasz hexposed_cluster hp

/-- Bounded-subdifferential version using a Mathlib-shaped literal Straszewicz hypothesis. -/
theorem mem_closure_convexHull_gradientClusterSet_of_bounded_mathlibStraszewicz_exposedCluster
    [ProperSpace E]
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hbounded : Bornology.IsBounded {q : E | SubgradientOn domain u y q})
    (hstrasz :
      ({q : E | SubgradientOn domain u y q}.extremePoints ℝ) ⊆
        closure (Set.exposedPoints ℝ {q : E | SubgradientOn domain u y q}))
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
          (differentiabilitySetOn sample u) (gradient u) y)) :=
  mem_closure_convexHull_gradientClusterSet_of_compact_mathlibStraszewicz_exposedCluster
    (isCompact_setOf_subgradientOn_of_isBounded hbounded) hstrasz hexposed_cluster hp

end AleksandrovDifferentiability

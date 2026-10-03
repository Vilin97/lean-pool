/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Basic
public import Mathlib.Analysis.Convex.Exposed

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Exposed faces

This module defines the project-local exposed-face and strictly exposed-point predicates and proves
their basic compactness, convexity, and extremality properties.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A vector `normal` exposes the point `p` of a set `s`.

This is the exact form used in Rockafellar 25.6: the exposed face in direction `normal` is the
singleton `{p}`. -/
def ExposesPoint (s : Set E) (normal p : E) : Prop :=
  p ∈ s ∧ ∀ ⦃r : E⦄, r ∈ s → r ≠ p → inner ℝ normal r < inner ℝ normal p

/-- The exposed face of `s` in the direction `normal`.

This is Rockafellar's notation `∂f(x)_y` in set-theoretic form: the points of `s` where the
linear functional `r ↦ normal · r` attains its supremal value on `s`, written without mentioning
the supremum. -/
def exposedFace (s : Set E) (normal : E) : Set E :=
  {p | p ∈ s ∧ ∀ ⦃r : E⦄, r ∈ s → inner ℝ normal r ≤ inner ℝ normal p}

/-- The project-local exposed face is a Mathlib exposed set. -/
theorem exposedFace_isExposed (s : Set E) (normal : E) :
    IsExposed ℝ s (exposedFace s normal) := by
  intro _hne
  refine ⟨InnerProductSpace.toDual ℝ E normal, ?_⟩
  ext p
  simp [exposedFace]

/-- Exposed faces of compact sets are compact. -/
theorem isCompact_exposedFace
    {s : Set E} (hcompact : IsCompact s) (normal : E) :
    IsCompact (exposedFace s normal) :=
  (exposedFace_isExposed s normal).isCompact hcompact

/-- Exposed faces of convex sets are convex. -/
theorem convex_exposedFace
    {s : Set E} (hconv : Convex ℝ s) (normal : E) :
    Convex ℝ (exposedFace s normal) :=
  (exposedFace_isExposed s normal).convex hconv

/-- Exposed faces are extreme subsets of the original set. -/
theorem exposedFace_isExtreme (s : Set E) (normal : E) :
    IsExtreme ℝ s (exposedFace s normal) :=
  (exposedFace_isExposed s normal).isExtreme

/-- A nonempty compact set has a nonempty exposed face in every direction. -/
theorem IsCompact.exposedFace_nonempty
    {s : Set E} (hcompact : IsCompact s) (hne : s.Nonempty) (normal : E) :
    (exposedFace s normal).Nonempty := by
  let l : StrongDual ℝ E := InnerProductSpace.toDual ℝ E normal
  rcases hcompact.exists_isMaxOn hne l.continuous.continuousOn with ⟨p, hp, hpmax⟩
  refine ⟨p, hp, ?_⟩
  intro r hr
  exact (isMaxOn_iff.mp hpmax) r hr

/-- Extreme points of an exposed face are extreme points of the original set. -/
theorem exposedFace_extremePoints_subset_extremePoints (s : Set E) (normal : E) :
    (exposedFace s normal).extremePoints ℝ ⊆ s.extremePoints ℝ :=
  (exposedFace_isExtreme s normal).extremePoints_subset_extremePoints

/-- If an exposed face is a singleton, its point is a Mathlib exposed point. -/
theorem mem_mathlib_exposedPoints_of_exposedFace_eq_singleton
    {s : Set E} {normal p : E}
    (hface : exposedFace s normal = {p}) :
    p ∈ Set.exposedPoints ℝ s := by
  rw [mem_exposedPoints_iff_exposed_singleton]
  simpa [hface] using exposedFace_isExposed s normal

end AleksandrovDifferentiability

/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Point

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Exposed points and Mathlib bridges

This module defines the project-local exposed-point carrier and relates it to Mathlib
`Set.exposedPoints`.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Recession directions of a set `s` based at `p`.

For a closed convex set this is independent of the base point `p` once `p ∈ s`, but the based
version is enough for the exposed-point step in Rockafellar 25.6. -/
def recessionDirectionsAt (s : Set E) (p : E) : Set E :=
  {q | ∀ ⦃t : ℝ⦄, 0 ≤ t → p + t • q ∈ s}

/-- Directions of affine lines through `p` contained in `s`. -/
def lineDirectionsAt (s : Set E) (p : E) : Set E :=
  {q | ∀ t : ℝ, p + t • q ∈ s}

/-- A set contains no nontrivial affine line. -/
def HasNoAffineLines (s : Set E) : Prop :=
  ∀ ⦃p q : E⦄, p ∈ s → q ∈ lineDirectionsAt s p → q = 0

/-- The exposed points of a set, with the exposing normal existentially packaged.

Rockafellar 25.6 uses Straszewicz's theorem to approximate extreme points by exposed points.
This set is the Lean-facing carrier for that exposed-point reduction. -/
def exposedPoints (s : Set E) : Set E :=
  {p | ∃ normal : E, ExposesPoint s normal p}

omit [CompleteSpace E] in
/-- An exposed point is a point of the original set. -/
theorem exposedPoints_subset {s : Set E} :
    exposedPoints s ⊆ s := by
  intro p hp
  rcases hp with ⟨_normal, hexposed⟩
  exact hexposed.1

omit [CompleteSpace E] in
/-- An exposed point admits a unit exposing normal whenever the ambient space has a unit vector.

This is the existential form used after applying Straszewicz: the exposed-point carrier only
stores some exposing normal, and this lemma recovers Rockafellar's unit normal. -/
theorem exists_unit_exposesPoint_of_mem_exposedPoints_of_exists_unit_vector
    {s : Set E} {p : E} (hp : p ∈ exposedPoints s)
    (hunit : ∃ unitNormal : E, ‖unitNormal‖ = 1) :
    ∃ unitNormal : E, ‖unitNormal‖ = 1 ∧ ExposesPoint s unitNormal p := by
  rcases hp with ⟨normal, hexposed⟩
  exact hexposed.exists_unit_of_exists_unit_vector hunit

/-- A project-local exposed point is a Mathlib exposed point. -/
theorem ExposesPoint.mem_mathlib_exposedPoints
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p) :
    p ∈ Set.exposedPoints ℝ s := by
  refine ⟨hexposed.1, ?_⟩
  refine ⟨InnerProductSpace.toDual ℝ E normal, ?_⟩
  intro y hy
  constructor
  · by_cases h_eq : y = p
    · subst y
      exact le_rfl
    · exact (hexposed.2 hy h_eq).le
  · intro hle
    by_contra hne
    have hlt := hexposed.2 hy hne
    have hdual_y : (InnerProductSpace.toDual ℝ E normal) y = inner ℝ normal y := by
      simp
    have hdual_p : (InnerProductSpace.toDual ℝ E normal) p = inner ℝ normal p := by
      simp
    rw [hdual_y, hdual_p] at hle
    exact (not_le_of_gt hlt) hle

/-- A Mathlib exposed point is a project-local exposed point, using Fréchet-Riesz to represent the
exposing functional by an inner-product normal vector. -/
theorem mem_exposedPoints_of_mem_mathlib_exposedPoints
    {s : Set E} {p : E} (hp : p ∈ Set.exposedPoints ℝ s) :
    p ∈ exposedPoints s := by
  rcases hp with ⟨hps, l, hl⟩
  let normal : E := (InnerProductSpace.toDual ℝ E).symm l
  refine ⟨normal, hps, ?_⟩
  intro r hr hne
  have hlr := hl r hr
  have hnot : ¬ l p ≤ l r := by
    intro hle
    exact hne (hlr.2 hle)
  have hlt_l : l r < l p := lt_of_not_ge hnot
  have hdual_r : inner ℝ normal r = l r := by
    simp [normal]
  have hdual_p : inner ℝ normal p = l p := by
    simp [normal]
  simpa [hdual_r, hdual_p] using hlt_l

/-- In complete real inner product spaces, the project-local exposed points are exactly Mathlib's
exposed points. -/
theorem exposedPoints_eq_mathlib_exposedPoints (s : Set E) :
    exposedPoints s = Set.exposedPoints ℝ s := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨_normal, hexposed⟩
    exact hexposed.mem_mathlib_exposedPoints
  · exact mem_exposedPoints_of_mem_mathlib_exposedPoints

/-- Mathlib exposed points are exactly project-local singleton exposed faces, for some normal. -/
theorem mem_mathlib_exposedPoints_iff_exists_exposedFace_eq_singleton
    {s : Set E} {p : E} :
    p ∈ Set.exposedPoints ℝ s ↔ ∃ normal : E, exposedFace s normal = {p} := by
  constructor
  · intro hp
    rcases mem_exposedPoints_of_mem_mathlib_exposedPoints hp with ⟨normal, hexposed⟩
    exact ⟨normal, hexposed.exposedFace_eq_singleton⟩
  · rintro ⟨normal, hface⟩
    exact mem_mathlib_exposedPoints_of_exposedFace_eq_singleton hface

omit [CompleteSpace E] in
/-- A unique maximizer of a continuous linear functional is a Mathlib exposed point.

This is the basic exposed-point recognition lemma used in the Rockafellar 25.6 route: once a
linear functional has a unique maximizer on a convex set, that maximizer belongs to
`Set.exposedPoints`. No convexity is needed for this definitional bridge. -/
theorem mem_mathlib_exposedPoints_of_unique_isMaxOn
    {s : Set E} {p : E} {l : StrongDual ℝ E}
    (hp : p ∈ s) (hmax : IsMaxOn l s p)
    (hunique : ∀ ⦃q : E⦄, q ∈ s → l q = l p → q = p) :
    p ∈ Set.exposedPoints ℝ s := by
  refine ⟨hp, l, ?_⟩
  intro q hq
  have hq_le : l q ≤ l p := (isMaxOn_iff.mp hmax) q hq
  refine ⟨hq_le, ?_⟩
  intro hle
  exact hunique hq (le_antisymm hq_le hle)

omit [CompleteSpace E] in
/-- A Mathlib exposed point supplies a continuous linear functional with a unique maximum.

This is the unpacked form of `Set.exposedPoints`, phrased with `IsMaxOn` so later
Rockafellar-style arguments can use the standard extremum API. -/
theorem exists_unique_isMaxOn_of_mem_mathlib_exposedPoints
    {s : Set E} {p : E} (hp : p ∈ Set.exposedPoints ℝ s) :
    ∃ l : StrongDual ℝ E,
      IsMaxOn l s p ∧ ∀ ⦃q : E⦄, q ∈ s → l q = l p → q = p := by
  rcases hp with ⟨_hps, l, hl⟩
  refine ⟨l, ?_, ?_⟩
  · intro q hq
    exact (hl q hq).1
  · intro q hq hqp
    exact (hl q hq).2 (le_of_eq hqp.symm)


end AleksandrovDifferentiability

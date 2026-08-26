/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Geometry.Basic

/-!
# The diameter star

The main target of this file is the standard orientation of the seven-cycle
formed by the unit diameter segments.
-/

namespace LeanPool.Erdos132WeiE2.Geometry

/-- Two closed line segments have a common point. -/
def SegmentsMeet (a b c d : Plane) : Prop :=
  ∃ x, x ∈ segment ℝ a b ∧ x ∈ segment ℝ c d

/-- Two open line segments have a common point. -/
def OpenSegmentsMeet (a b c d : Plane) : Prop :=
  ∃ x, x ∈ openSegment ℝ a b ∧ x ∈ openSegment ℝ c d

/-- Two disjoint diameter pairs in a four-point set of diameter one cross properly. -/
theorem four_point_diameter_segments_meet
    {a b c d : Plane}
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : dist a c ≤ 1) (had : dist a d ≤ 1)
    (hbc : dist b c ≤ 1) (hbd : dist b d ≤ 1)
    (hacne : a ≠ c) (hadne : a ≠ d) (hbcne : b ≠ c) (hbdne : b ≠ d) :
    OpenSegmentsMeet a b c d := by
  sorry

/-- All nonincident edges of the labelled diameter cycle cross properly. -/
theorem all_diameter_edges_cross
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) :
    ∀ i j : Fin 7,
      i ≠ j → i ≠ j + 3 → i + 3 ≠ j → i + 3 ≠ j + 3 →
        OpenSegmentsMeet (p i) (p (i + 3)) (p j) (p (j + 3)) := by
  sorry

/-- Along the diameter-cycle walk, every turn has one common orientation. -/
def SameTurnStar (p : Fin 7 → Plane) : Prop :=
  ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ k : Fin 7,
      0 < ε * orientedArea
        (p (walkIndex k)) (p (walkIndex (k + 1))) (p (walkIndex (k + 2)))

/-- The seven unit diameters have the standard star orientation, up to reflection. -/
theorem diameter_star_structure
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) : SameTurnStar p := by
  sorry

end LeanPool.Erdos132WeiE2.Geometry

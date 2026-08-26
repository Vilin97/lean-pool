/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Tactic.Linarith

/-!
# Basic geometry for the Wei E2 configuration

This file fixes the challenge point type, the diameter-star indexing, and the
raw geometric hypotheses used by the angle-parametrization route.
-/

namespace LeanPool.Erdos132WeiE2.Geometry

open EuclideanGeometry

/-- The plane used by the challenge statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The standard real-linear isometry from the complex plane to the challenge plane. -/
noncomputable def complexPlaneEquiv : ℂ ≃ₗᵢ[ℝ] Plane :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Complex coordinates of a point in the challenge plane. -/
noncomputable def toComplex (x : Plane) : ℂ := complexPlaneEquiv.symm x

/-- Signed doubled area, transported through the standard Complex isometry. -/
noncomputable def orientedArea (a b c : Plane) : ℝ :=
  let u := toComplex b - toComplex a
  let v := toComplex c - toComplex a
  u.re * v.im - u.im * v.re

/-- The order in which the seven diameter edges form their cycle. -/
def walkIndex (i : Fin 7) : Fin 7 := 3 * i

/-- The angle between the two unit diameter edges incident at vertex `i`. -/
noncomputable def apexAngle (p : Fin 7 → Plane) (i : Fin 7) : ℝ :=
  ∠ (p (i + 3)) (p i) (p (i + 4))

/-- The geometric and edge-class hypotheses copied from the challenge. -/
structure E2GeometryHypotheses (p : Fin 7 → Plane) : Prop where
  hdiam : ∀ i : Fin 7, dist (p i) (p (i + 3)) = 1
  hshort : ∀ i j : Fin 7, i ≠ j → j ≠ i + 3 → i ≠ j + 3 → dist (p i) (p j) < 1
  hC : dist (p 0) (p 1) = dist (p 3) (p 4)
  hB : dist (p 1) (p 2) = dist (p 2) (p 3)
  hA₁ : dist (p 4) (p 5) = dist (p 5) (p 6)
  hA₂ : dist (p 5) (p 6) = dist (p 6) (p 0)
  hBA : dist (p 1) (p 2) < dist (p 4) (p 5)
  hAC : dist (p 4) (p 5) < dist (p 0) (p 1)

/-- The challenge hypotheses force all seven labelled points to be distinct. -/
theorem pairwise_distinct_of_diameter_pattern
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) : Function.Injective p := by
  sorry

/-- Every distance is bounded by the common diameter. -/
theorem dist_le_one_of_diameter_pattern
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i j : Fin 7) :
    dist (p i) (p j) ≤ 1 := by
  sorry

/-- Every apex triangle is nondegenerate. -/
theorem apex_not_collinear
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    ¬Collinear ℝ ({p (i + 3), p i, p (i + 4)} : Set Plane) := by
  sorry

end LeanPool.Erdos132WeiE2.Geometry

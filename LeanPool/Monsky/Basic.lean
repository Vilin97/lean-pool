/-
Copyright (c) 2026 Monsky contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha et al.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace LeanPool.Monsky

/-!
# Basic Monsky Geometry

This file contains the elementary point, segment, triangle, determinant, and
unit-triangle area declarations used by the Monsky formalization.
-/

/-- A point in the coordinate plane. -/
abbrev Point := Fin 2 → ℝ

/-- A segment is given by its two endpoints. -/
abbrev Segment := Fin 2 → Point

/-- A triangle is given by its three vertices. -/
abbrev Triangle := Fin 3 → Point

/-- The point with coordinates `(x, y)`. -/
def point (x y : ℝ) : Point := fun
  | 0 => x
  | 1 => y

@[simp]
theorem point_zero {x y : ℝ} : point x y 0 = x := rfl

@[simp]
theorem point_one {x y : ℝ} : point x y 1 = y := rfl

/-- The standard unit right triangle with vertices `(0,0)`, `(1,0)`, and `(0,1)`. -/
def unitTriangle : Triangle := fun
  | 0 => point 0 0
  | 1 => point 1 0
  | 2 => point 0 1

/-- The unit square, listed counterclockwise from the origin. -/
def unitSquare : Fin 4 → Point := fun
  | 0 => point 0 0
  | 1 => point 1 0
  | 2 => point 1 1
  | 3 => point 0 1

/-- Twice the signed area of a triangle. -/
def det (T : Triangle) : ℝ :=
  T 0 0 * T 1 1 + T 1 0 * T 2 1 + T 2 0 * T 0 1 -
    T 0 1 * T 1 0 - T 1 1 * T 2 0 - T 2 1 * T 0 0

/-- The determinant-normalized unsigned area of a triangle. -/
noncomputable def triangleArea (T : Triangle) : ℝ := |det T| / 2

theorem det_unitTriangle : det unitTriangle = 1 := by
  norm_num [det, unitTriangle, point]

theorem triangleArea_unitTriangle : triangleArea unitTriangle = 1 / 2 := by
  norm_num [triangleArea, det_unitTriangle]

/-- Reverse the endpoints of a segment. -/
def reverseSegment (L : Segment) : Segment := fun
  | 0 => L 1
  | 1 => L 0

theorem reverseSegment_involutive : Function.Involutive reverseSegment := by
  intro L
  funext i
  fin_cases i <;> rfl

/-- Swap the first two vertices of a triangle. -/
def swapFirstTwoVertices (T : Triangle) : Triangle := fun
  | 0 => T 1
  | 1 => T 0
  | 2 => T 2

theorem det_swap_vertices (T : Triangle) : det (swapFirstTwoVertices T) = -(det T) := by
  simp [swapFirstTwoVertices, det]
  ring

end LeanPool.Monsky

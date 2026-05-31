/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix

/-- Three-dimensional Euclidean space over `ℝ`. -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
/-- Two-dimensional Euclidean space over `ℝ`. -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `n`-dimensional Euclidean space over `ℝ`, indexed by `Fin n`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The special orthogonal group in dimension three over `ℝ`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def proj_xy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as an indexed finite set of vertices. -/
def IsRupert {ι : Type} (vertices : ι → ℝ³) : Prop :=
   ∃ inner_rotation ∈ SO3, ∃ inner_offset : ℝ², ∃ outer_rotation ∈ SO3,
   let hull := convexHull ℝ { vertices i | i }
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow

/-- Alternate formulation of the Rupert Property. This is equivalent to IsRupert and
    should be easier to prove. -/
def IsRupert' {ι : Type} (vertices : ι → ℝ³) : Prop :=
   ∃ inner_rotation ∈ SO3, ∃ inner_offset : ℝ², ∃ outer_rotation ∈ SO3,
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin (vertices i)) | i }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin (vertices i)) | i }
   inner_shadow ⊆ interior (convexHull ℝ outer_shadow)

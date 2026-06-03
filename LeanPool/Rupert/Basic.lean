/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# LeanPool.Rupert.Basic

Imported Lean Pool material for `LeanPool.Rupert.Basic`.
-/

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
def projXy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as an indexed finite set of vertices. -/
def IsRupert {ι : Type} (vertices : ι → ℝ³) : Prop :=
   ∃ innerRotation ∈ SO3, ∃ innerOffset : ℝ², ∃ outerRotation ∈ SO3,
   let hull := convexHull ℝ { vertices i | i }
   let inner_shadow := { innerOffset + projXy (innerRotation.toEuclideanLin p) | p ∈ hull }
   let outerShadow := { projXy (outerRotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outerShadow

/-- Alternate formulation of the Rupert Property. This is equivalent to IsRupert and
    should be easier to prove. -/
def IsRupert' {ι : Type} (vertices : ι → ℝ³) : Prop :=
   ∃ innerRotation ∈ SO3, ∃ innerOffset : ℝ², ∃ outerRotation ∈ SO3,
   let inner_shadow := { innerOffset + projXy (innerRotation.toEuclideanLin (vertices i)) | i }
   let outerShadow := { projXy (outerRotation.toEuclideanLin (vertices i)) | i }
   inner_shadow ⊆ interior (convexHull ℝ outerShadow)

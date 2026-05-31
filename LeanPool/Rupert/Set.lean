/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic

open scoped Matrix

/-- The Rupert Property for a pair of subsets X, Y of ℝ³. X has the
    Rupert property with respect to Y if there such that the shadow of
    X fits "comfortably" within the shadow of Y under affine
    transformations. By "comfortably" we mean the closure of one set is
    a subset of the interior of the other. This definition rules out
    trivial cases of a set fitting inside itself. -/
def IsRupertPair (inner outer : Set ℝ³) : Prop :=
   ∃ inner_rot ∈ SO3, ∃ inner_offset : ℝ², ∃ outer_rot ∈ SO3,
   let inner_shadow := { inner_offset + proj_xy (inner_rot.toEuclideanLin p) | p ∈ inner }
   let outer_shadow := { proj_xy (outer_rot.toEuclideanLin p) | p ∈  outer }
   closure inner_shadow ⊆ interior outer_shadow

/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRupertSet (S : Set ℝ³) : Prop := IsRupertPair S S

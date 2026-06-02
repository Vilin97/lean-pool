/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic

/-!
# LeanPool.Rupert.Set

Imported Lean Pool material for `LeanPool.Rupert.Set`.
-/

open scoped Matrix

/-- The Rupert Property for a pair of subsets X, Y of ℝ³. X has the
    Rupert property with respect to Y if there such that the shadow of
    X fits "comfortably" within the shadow of Y under affine
    transformations. By "comfortably" we mean the closure of one set is
    a subset of the interior of the other. This definition rules out
    trivial cases of a set fitting inside itself. -/
def IsRupertPair (inner outer : Set ℝ³) : Prop :=
   ∃ innerRot ∈ SO3, ∃ innerOffset : ℝ², ∃ outerRot ∈ SO3,
   let inner_shadow := { innerOffset + projXy (innerRot.toEuclideanLin p) | p ∈ inner }
   let outerShadow := { projXy (outerRot.toEuclideanLin p) | p ∈  outer }
   closure inner_shadow ⊆ interior outerShadow

/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRupertSet (S : Set ℝ³) : Prop := IsRupertPair S S

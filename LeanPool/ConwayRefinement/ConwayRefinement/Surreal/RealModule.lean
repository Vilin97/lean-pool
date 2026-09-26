/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Real
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Surreal numbers as an ordered real vector space

The standard ordered embedding of `ℝ` into the surreal field makes `Surreal` an algebra over
`ℝ`. Its scalar multiplication is ordinary multiplication by the embedded real, so it respects
the orders in both arguments.

These instances are natural candidates for CombinatorialGames. They live here rather than in the
pinned dependency so later surreal constructions can use real-linear Archimedean strata without
modifying the dependency revision.
-/

public noncomputable section

namespace Surreal

/-- The surreal field as an algebra over its standard embedded copy of `ℝ`. -/
noncomputable instance instAlgebraReal : Algebra ℝ Surreal :=
  Real.toSurrealRingHom.toRingHom.toAlgebra

/-- Real scalar multiplication on surreal numbers is ordered in both arguments. -/
instance instIsOrderedModuleReal : IsOrderedModule ℝ Surreal where
  smul_le_smul_of_nonneg_left r hr x y hxy := by
    rw [Algebra.smul_def, Algebra.smul_def]
    exact mul_le_mul_of_nonneg_left hxy (Real.toSurreal_nonneg_iff.mpr hr)
  smul_le_smul_of_nonneg_right x hx r s hrs := by
    rw [Algebra.smul_def, Algebra.smul_def]
    exact mul_le_mul_of_nonneg_right (Real.toSurreal_le_iff.mpr hrs) hx

/-- Real scalar multiplication is multiplication by the standard surreal embedding. -/
theorem real_smul_def (r : ℝ) (x : Surreal) :
    r • x = (r : Surreal) * x :=
  Algebra.smul_def r x

end Surreal

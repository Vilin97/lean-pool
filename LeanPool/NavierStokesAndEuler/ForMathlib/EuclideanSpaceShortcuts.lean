/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.NavierStokesAndEuler.ForMathlib.NormedSpaceShortcuts
public import LeanPool.NavierStokesAndEuler.ForMathlib.LinearMapShortcuts
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Shortcut instances for real Euclidean spaces

`EuclideanSpace ℝ (Fin n)` unfolds to `WithLp 2 (Fin n → ℝ)`, whose structures are transported
one class at a time from the function space. The shortcuts below record the normed-space and
inner-product instances, and the normed-space instances of the continuous linear maps between two
such spaces; they apply to the three-dimensional physical space and to the planes used throughout
this development.
-/

public section

noncomputable section

namespace NavierStokesAndEuler

variable {n : ℕ}

real_normed_space_shortcut_instances EuclideanSpaceShortcut : EuclideanSpace ℝ (Fin n)

/-- Shortcut for the inner product space structure of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instInnerProductSpace :
    InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n)) := inferInstance

/-- Shortcut for the inner product of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instInner : Inner ℝ (EuclideanSpace ℝ (Fin n)) := inferInstance

/-- Shortcut for the finite dimensionality of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instFiniteDimensional :
    FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)) := inferInstance

/-- Shortcut for the completeness of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instCompleteSpace : CompleteSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Shortcut for the properness of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instProperSpace : ProperSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

variable {m : ℕ}

real_normed_space_shortcut_instances EuclideanOperatorShortcut :
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)

end NavierStokesAndEuler

end

end

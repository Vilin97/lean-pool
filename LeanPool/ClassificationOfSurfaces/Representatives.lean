/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.LeanEval.ChallengeDeps
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Eval representatives and normal-form indices

The Lean-Eval challenge owns `Complex.ClosedUnitDisc`, `OrientableRel`, and
`NonOrientableRel`; they are imported verbatim from `LeanEval/ChallengeDeps.lean`. This file adds
only the project-owned sphere abbreviation and the index type used by the normal-form reduction.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The sphere branch in the eval theorem. -/
abbrev SphereRepresentative : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The named normal forms that should eventually be realized by quotient spaces. -/
inductive NormalForm where
  | sphere
  | orientable (handles boundaryComponents : ℕ)
  | nonOrientable (crosscaps boundaryComponents : ℕ)
deriving DecidableEq, Repr

/-- The normal forms that actually appear in the Lean Eval conclusion.

The orientable sphere is represented by the separate sphere branch, so an orientable polygonal
normal form must have a handle or a boundary component; nonorientable forms must have at least one
crosscap. -/
def NormalForm.IsEvalAdmissible : NormalForm → Prop
  | NormalForm.sphere => True
  | NormalForm.orientable handles boundaryComponents =>
      1 ≤ handles ∨ 1 ≤ boundaryComponents
  | NormalForm.nonOrientable crosscaps _boundaryComponents => 1 ≤ crosscaps

end ClassificationOfSurfaces
end Topology
end LeanEval

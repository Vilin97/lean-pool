/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProjectiveLine.Charts
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The challenge bridge: `ℙ¹ ≃ₜ` the unit 2-sphere (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.4). Mathlib already contains the
topological homeomorphism from a one-point compactification of a finite-dimensional real vector
space to the unit sphere in a Euclidean space of one higher dimension
(`onePointEquivSphereOfFinrankEq`); specializing it to `V := ℂ` (as a 2-dimensional real vector
space) and `ι := Fin 3` gives exactly the sphere model used by the challenge's
`genus_eq_zero_iff_homeo`.

`homeoSphere` has no closed-form pointwise description (mathlib's construction selects a
`ContinuousLinearEquiv` via `Nonempty.some`); no consumer needs one (see design §3.4).
-/

open scoped ContDiff Manifold OnePoint

namespace RS.P1

/-- `ℙ¹` is homeomorphic to the unit 2-sphere in `EuclideanSpace ℝ (Fin 3)` — the sphere model
used verbatim by the challenge's `genus_eq_zero_iff_homeo`. -/
noncomputable def homeoSphere :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])

end RS.P1

/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SphereHomologyS1BaseMV
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.SphereTopHomologyReduction

/-!
# Branch 1 assembly: the unconditional `SphereSuspensionTower`

This file assembles the two Mayer–Vietoris ingredients proved in the previous
modules into a single concrete, unconditional term of type
`SphereSuspensionTower`:

* the base case `sphereTopHomologyIso_one : SphereTopHomologyIso 1`
 (i.e. `H₁(S¹; ℤ) ≅ ℤ`), from `SphereHomologyS1BaseMV.lean`, and
* the recursive step
 `sphereTopHomology_step_MV : Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)` (`n ≥ 1`),
 from `SphereHomologyMVStep.lean`.

The tower is constructed from the exported Mayer--Vietoris results. Downstream files may
import this file and use `sphereSuspensionTower_from_MV` (or its aliases) to obtain

/-! # Sphere Suspension Tower From MV -/
the full positive-dimensional sphere top-homology family and orientation data.
-/

open CategoryTheory

noncomputable section

namespace SphereOddDegree

/-- **The unconditional sphere suspension tower**, assembled from the
Mayer–Vietoris base case `sphereTopHomologyIso_one` and the Mayer–Vietoris
recursive step `sphereTopHomology_step_MV`. -/
def sphereSuspensionTower_from_MV : SphereSuspensionTower where
  base := sphereTopHomologyIso_one
  step := fun n hn => sphereTopHomology_step_MV n hn

/-- Compatibility alias: the unconditional suspension tower. -/
def sphereSuspensionTower_unconditional : SphereSuspensionTower :=
  sphereSuspensionTower_from_MV

/-- Compatibility alias: the Branch 1 suspension tower. -/
def branch1_sphereSuspensionTower : SphereSuspensionTower :=
  sphereSuspensionTower_from_MV

/-- From the unconditional suspension tower, the genuine positive-dimensional
sphere orientation `SphereOrientationPos`. -/
def sphereOrientationPos_from_MV : SphereOrientationPos :=
  sphereSuspensionTower_from_MV.orientation

end SphereOddDegree

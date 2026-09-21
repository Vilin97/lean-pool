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

* the base case `sphereTopHomologyIsoOne : SphereTopHomologyIso 1`
 (i.e. `H₁(S¹; ℤ) ≅ ℤ`), from `SphereHomologyS1BaseMV.lean`, and
* the recursive step
 `sphereTopHomologyStepMV : Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)` (`n ≥ 1`),
 from `SphereHomologyMVStep.lean`.

The tower is constructed from the exported Mayer--Vietoris results. Downstream files may
import this file and use `sphereSuspensionTowerFromMV` (or its aliases) to obtain

/-! # Sphere Suspension Tower From MV -/
the full positive-dimensional sphere top-homology family and orientation data.
-/

open CategoryTheory

noncomputable section

namespace SphereOddDegree

/-- **The unconditional sphere suspension tower**, assembled from the
Mayer–Vietoris base case `sphereTopHomologyIsoOne` and the Mayer–Vietoris
recursive step `sphereTopHomologyStepMV`. -/
def sphereSuspensionTowerFromMV : SphereSuspensionTower where
  base := sphereTopHomologyIsoOne
  step := fun n hn => sphereTopHomologyStepMV n hn

/-- Compatibility alias: the unconditional suspension tower. -/
def sphereSuspensionTowerUnconditional : SphereSuspensionTower :=
  sphereSuspensionTowerFromMV

/-- Compatibility alias: the Branch 1 suspension tower. -/
def branch1SphereSuspensionTower : SphereSuspensionTower :=
  sphereSuspensionTowerFromMV

/-- From the unconditional suspension tower, the genuine positive-dimensional
sphere orientation `SphereOrientationPos`. -/
def sphereOrientationPosFromMV : SphereOrientationPos :=
  sphereSuspensionTowerFromMV.orientation

end SphereOddDegree

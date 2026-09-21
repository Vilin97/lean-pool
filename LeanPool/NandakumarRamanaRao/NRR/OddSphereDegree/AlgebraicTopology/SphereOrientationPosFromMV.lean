/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SphereSuspensionTowerFromMV

/-!
# Branch 1 finalization: the unconditional `SphereOrientationPos`

the project assembled the unconditional Mayer–Vietoris sphere suspension tower
`sphereSuspensionTower_from_MV : SphereSuspensionTower` and already derived the
positive-dimensional sphere orientation `sphereOrientationPos_from_MV` from it via
`SphereSuspensionTower.orientation`.

This file exposes the **stable final names** that downstream code can
depend on:

* `sphereOrientationPos_unconditional : SphereOrientationPos` — the canonical
 unconditional positive-dimensional sphere orientation, built solely from the
 Mayer–Vietoris suspension tower (no Branch 1 theorem is assumed).
* `sphereTopHomologyIso_unconditional (n : ℕ) (hn : 1 ≤ n) : SphereTopHomologyIso n`
 and its alias `sphereTopHomologyIso_of_pos` — the projection giving the integral
 top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in each dimension `n ≥ 1`.

No `n = 0` case is restored: `SphereTopHomologyIso 0` is genuinely empty
(`sphereTopHomologyIso_zero_isEmpty`), so the only correct object is the
positive-dimensional `SphereOrientationPos`.

The construction is assembled from the Mayer–Vietoris results.
-/

noncomputable section

namespace SphereOddDegree

/-- **The canonical unconditional positive-dimensional sphere orientation.**

This is the stable export of the Branch 1 construction: a genuine, non-vacuous
`SphereOrientationPos` built entirely from the unconditional Mayer–Vietoris
suspension tower `sphereSuspensionTower_from_MV` (no Branch 1 hypothesis is
assumed). -/
def sphereOrientationPos_unconditional : SphereOrientationPos :=
  sphereOrientationPos_from_MV

/-- The unconditional positive-dimensional orientation agrees with the
the project construction `sphereOrientationPos_from_MV`. -/
theorem sphereOrientationPos_unconditional_eq :
    sphereOrientationPos_unconditional = sphereOrientationPos_from_MV := rfl

/-- **Stable projection.** The integral top-homology identification
`Hₙ(Sⁿ; ℤ) ≅ ℤ` for every dimension `n ≥ 1`, read off the unconditional
positive-dimensional orientation. -/
def sphereTopHomologyIso_unconditional (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIso n :=
  sphereOrientationPos_unconditional.iso n hn

/-- Alias for `sphereTopHomologyIso_unconditional`: the positive-dimensional
top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` (`n ≥ 1`). -/
def sphereTopHomologyIso_of_pos (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIso n :=
  sphereTopHomologyIso_unconditional n hn

@[simp]
theorem sphereTopHomologyIso_unconditional_eq (n : ℕ) (hn : 1 ≤ n) :
    sphereTopHomologyIso_unconditional n hn =
      sphereOrientationPos_unconditional.iso n hn := rfl

@[simp]
theorem sphereTopHomologyIso_of_pos_eq (n : ℕ) (hn : 1 ≤ n) :
    sphereTopHomologyIso_of_pos n hn =
      sphereTopHomologyIso_unconditional n hn := rfl

end SphereOddDegree

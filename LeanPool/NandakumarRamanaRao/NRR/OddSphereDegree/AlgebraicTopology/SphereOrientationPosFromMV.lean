/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SphereSuspensionTowerFromMV

/-!
# Branch 1 finalization: the unconditional `SphereOrientationPos`

the project assembled the unconditional Mayer–Vietoris sphere suspension tower
`sphereSuspensionTowerFromMV : SphereSuspensionTower` and already derived the
positive-dimensional sphere orientation `sphereOrientationPosFromMV` from it via
`SphereSuspensionTower.orientation`.

This file exposes the **stable final names** that downstream code can
depend on:

* `sphereOrientationPosUnconditional : SphereOrientationPos` — the canonical
 unconditional positive-dimensional sphere orientation, built solely from the
 Mayer–Vietoris suspension tower (no Branch 1 theorem is assumed).
* `sphereTopHomologyIsoUnconditional (n : ℕ) (hn : 1 ≤ n) : SphereTopHomologyIso n`
 and its alias `sphereTopHomologyIsoOfPos` — the projection giving the integral
 top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in each dimension `n ≥ 1`.

No `n = 0` case is restored: `SphereTopHomologyIso 0` is genuinely empty
(`sphereTopHomologyIso_zero_isEmpty`), so the only correct object is the
positive-dimensional `SphereOrientationPos`.

The construction is assembled from the Mayer–Vietoris results.
-/

@[expose] public section

noncomputable section

namespace SphereOddDegree

/-- **The canonical unconditional positive-dimensional sphere orientation.**

This is the stable export of the Branch 1 construction: a genuine, non-vacuous
`SphereOrientationPos` built entirely from the unconditional Mayer–Vietoris
suspension tower `sphereSuspensionTowerFromMV` (no Branch 1 hypothesis is
assumed). -/
def sphereOrientationPosUnconditional : SphereOrientationPos :=
  sphereOrientationPosFromMV

/-- The unconditional positive-dimensional orientation agrees with the
the project construction `sphereOrientationPosFromMV`. -/
theorem sphereOrientationPos_unconditional_eq :
    sphereOrientationPosUnconditional = sphereOrientationPosFromMV := rfl

/-- **Stable projection.** The integral top-homology identification
`Hₙ(Sⁿ; ℤ) ≅ ℤ` for every dimension `n ≥ 1`, read off the unconditional
positive-dimensional orientation. -/
def sphereTopHomologyIsoUnconditional (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIso n :=
  sphereOrientationPosUnconditional.iso n hn

/-- Alias for `sphereTopHomologyIsoUnconditional`: the positive-dimensional
top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` (`n ≥ 1`). -/
def sphereTopHomologyIsoOfPos (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIso n :=
  sphereTopHomologyIsoUnconditional n hn

@[simp]
theorem sphereTopHomologyIso_unconditional_eq (n : ℕ) (hn : 1 ≤ n) :
    sphereTopHomologyIsoUnconditional n hn =
      sphereOrientationPosUnconditional.iso n hn := rfl

@[simp]
theorem sphereTopHomologyIso_of_pos_eq (n : ℕ) (hn : 1 ≤ n) :
    sphereTopHomologyIsoOfPos n hn =
      sphereTopHomologyIsoUnconditional n hn := rfl

end SphereOddDegree

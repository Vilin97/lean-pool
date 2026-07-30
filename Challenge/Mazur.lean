/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion

/-!
# Mazur's bound on the torsion of an elliptic curve over the rationals

Source: doi:10.1007/BF02684339, url:https://www.numdam.org/item/?id=PMIHES_1977__47__33_0
Proposed by: Kevin Buzzard, Vasily Ilin
Open declarations: `Challenge.Mazur.torsion_ncard_le`
Tags: elliptic-curves, torsion, modular-curves, flt-assumption
MSC: 11G05, 11G18
Estimated size: ~50000 lines of Lean

Informal statement:
* `Challenge.Mazur.torsion_ncard_le` — For every elliptic curve E over the rationals, the torsion
  subgroup of the group of rational points of E, viewed as a set, has at most 16 elements. Set.ncard
  returns 0 on an infinite set, so the statement reads "at most 16, or infinite"; that is the form
  the FLT project assumes, since finiteness of the torsion subgroup is classical and far easier.
-/

namespace Challenge.Mazur

open scoped WeierstrassCurve.Affine

/-- **Mazur's torsion theorem**, in the form the Fermat's Last Theorem project assumes it as
`FLT.Assumptions.Mazur_statement`: the torsion subgroup of the group of rational points of an
elliptic curve over `ℚ` has at most 16 elements. Mazur classified the possible torsion
subgroups — cyclic of order `n ≤ 10` or `n = 12`, or `ℤ/2ℤ × ℤ/nℤ` for `n = 2, 4, 6, 8` — and
16 is the largest resulting size.

`Set.ncard` returns `0` on an infinite set, so this says "at most 16, or infinite". That is
enough for the application, because finiteness of the torsion subgroup is a much easier
classical fact (Mordell--Weil); a solution is welcome to prove finiteness as well. -/
theorem torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := sorry

end Challenge.Mazur

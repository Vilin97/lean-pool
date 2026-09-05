/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Curve

/-!
# The Hessian addition formulas for the Fermat cubic in characteristic two

For two affine Fermat points `(w1,t1)`, `(w2,t2)` the projectivised Hessian addition
formula reads

```text
D  = w1*t1 + w2*t2
Nx = t1^2*w2 + t2^2*w1
Ny = w1^2*t2 + w2^2*t1
```

(for `(w2,t2) = (w^r,t^r)` these are exactly `D0`, `N_x`, `N_y` of the unit).

This file records the three polynomial identities behind the formula; they are all
consequences of the two Fermat equations and of `2 = 0`.
-/

namespace KasamiCyclicAdditive.FermatCubic

variable {K : Type*} [Field K] [CharP K 2]

/-- The denominator `D0` of the Hessian addition formula. -/
def hessD (w1 t1 w2 t2 : K) : K := w1 * t1 + w2 * t2

/-- The first numerator `N_x` of the Hessian addition formula. -/
def hessX (w1 t1 w2 t2 : K) : K := t1 ^ 2 * w2 + t2 ^ 2 * w1

/-- The second numerator `N_y` of the Hessian addition formula. -/
def hessY (w1 t1 w2 t2 : K) : K := w1 ^ 2 * t2 + w2 ^ 2 * t1

variable {w1 t1 w2 t2 : K}

/-- The Hessian numerators and denominator again satisfy the Fermat equation:
`N_x^3 + N_y^3 = D0^3`. -/
theorem hess_cubic (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1) :
    hessX w1 t1 w2 t2 ^ 3 + hessY w1 t1 w2 t2 ^ 3 = hessD w1 t1 w2 t2 ^ 3 := by
  simp only [hessX, hessY, hessD]
  linear_combination (t2^3
    + t2^6
    + (-1) * t1^3
    + (-1) * t1^3 * t2^3
    + 3 * w1 * t1 * w2^2 * t2^2
    + w1^3 * t2^3) * h1
    + ((-1) * t2^3
    + t1^3
    + (-1) * t1^3 * t2^3
    + t1^3 * w2^3
    + t1^6
    + 3 * w1^2 * t1^2 * w2 * t2) * h2 +
    (t2^6 + (-2) * t1^3 * t2^3 + t1^6) * CharTwo.two_eq_zero (R := K)

/-- The `x`-coordinate identity behind the Hessian addition formula. -/
theorem hess_addX_aux (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1) :
    ((w1 * (w2 + t2) + w2 * (w1 + t1)) ^ 2 * ((w1 + t1) * (w2 + t2))
        + ((w1 + t1) + (w2 + t2)) ^ 3) * (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2)
      = hessD w1 t1 w2 t2 * (((w1 + t1) + (w2 + t2)) ^ 2 * ((w1 + t1) * (w2 + t2))) := by
  simp only [hessX, hessY, hessD]
  linear_combination (6 * t2^3
    + 8 * w2 * t2^2
    + 2 * w2^2 * t2
    + 7 * t1 * t2^2
    + t1 * t2^5
    + 2 * t1 * w2 * t2
    + 7 * t1 * w2 * t2^4
    + (-1) * t1 * w2^2
    + 15 * t1 * w2^2 * t2^3
    + 13 * t1 * w2^3 * t2^2
    + 8 * t1 * w2^4 * t2
    + 4 * t1 * w2^5
    + (-2) * t1^2 * w2
    + 3 * t1^2 * w2 * t2^3
    + 12 * t1^2 * w2^2 * t2^2
    + 13 * t1^2 * w2^3 * t2
    + 4 * t1^2 * w2^4
    + 4 * w1 * t2^2
    + w1 * t2^5
    + 3 * w1 * w2 * t2
    + 5 * w1 * w2 * t2^4
    + 8 * w1 * w2^2 * t2^3
    + 4 * w1 * w2^3 * t2^2
    + 2 * w1 * t1 * t2
    + w1 * t1 * t2^4
    + (-1) * w1 * t1 * w2
    + 7 * w1 * t1 * w2 * t2^3
    + 14 * w1 * t1 * w2^2 * t2^2
    + 8 * w1 * t1 * w2^3 * t2
    + w1^2 * t2
    + w1^2 * t2^4
    + 5 * w1^2 * w2 * t2^3
    + 8 * w1^2 * w2^2 * t2^2
    + 4 * w1^2 * w2^3 * t2) * h1
    + (13 * t1 * t2^2
    + 10 * t1 * w2 * t2
    + 5 * t1 * w2^2
    + 20 * t1^2 * t2
    + 8 * t1^2 * w2
    + 6 * t1^3
    + (-13) * t1^4 * t2^2
    + (-7) * t1^4 * w2 * t2
    + (-3) * t1^4 * w2^2
    + (-12) * t1^5 * t2
    + (-3) * t1^5 * w2
    + 2 * w1 * t2^2
    + (-1) * w1 * w2 * t2
    + 10 * w1 * t1 * t2
    + 3 * w1 * t1 * w2
    + 8 * w1 * t1^2
    + (-1) * w1 * t1^3 * t2^2
    + 7 * w1 * t1^3 * w2 * t2
    + 5 * w1 * t1^3 * w2^2
    + (-1) * w1 * t1^4 * t2
    + 5 * w1 * t1^4 * w2
    + 3 * w1^2 * t2
    + 2 * w1^2 * t1
    + 12 * w1^2 * t1^2 * t2^2
    + 14 * w1^2 * t1^2 * w2 * t2
    + 8 * w1^2 * t1^2 * w2^2
    + 11 * w1^2 * t1^3 * t2
    + 8 * w1^2 * t1^3 * w2) * h2 +
    (3 * t2^3
    + 4 * w2 * t2^2
    + w2^2 * t2
    + 10 * t1 * t2^2
    + (-6) * t1 * t2^5
    + 6 * t1 * w2 * t2
    + (-2) * t1 * w2 * t2^4
    + 2 * t1 * w2^2
    + 4 * t1 * w2^2 * t2^3
    + 10 * t1^2 * t2
    + (-10) * t1^2 * t2^4
    + 3 * t1^2 * w2
    + (-3) * t1^2 * w2 * t2^3
    + 7 * t1^2 * w2^2 * t2^2
    + 3 * t1^3
    + (-6) * t1^3 * t2^3
    + (-3) * t1^3 * w2 * t2^2
    + 3 * t1^3 * w2^2 * t2
    + (-10) * t1^4 * t2^2
    + 6 * t1^4 * t2^5
    + (-3) * t1^4 * w2 * t2
    + t1^4 * w2^2
    + (-6) * t1^4 * w2^2 * t2^3
    + (-6) * t1^5 * t2
    + 6 * t1^5 * t2^4
    + (-6) * t1^5 * w2^2 * t2^2
    + 3 * w1 * t2^2
    + w1 * w2 * t2
    + 4 * w1 * w2 * t2^4
    + 4 * w1 * w2^2 * t2^3
    + 6 * w1 * t1 * t2
    + (-3) * w1 * t1 * t2^4
    + w1 * t1 * w2
    + 3 * w1 * t1 * w2 * t2^3
    + 6 * w1 * t1 * w2^2 * t2^2
    + 4 * w1 * t1^2
    + (-3) * w1 * t1^2 * t2^3
    + 3 * w1 * t1^2 * w2^2 * t2
    + (-3) * w1 * t1^3 * t2^2
    + 3 * w1 * t1^3 * w2 * t2
    + (-6) * w1 * t1^3 * w2 * t2^4
    + 6 * w1 * t1^3 * w2^2
    + (-6) * w1 * t1^3 * w2^2 * t2^3
    + (-2) * w1 * t1^4 * t2
    + 4 * w1 * t1^4 * w2
    + (-6) * w1 * t1^4 * w2 * t2^3
    + (-6) * w1 * t1^4 * w2^2 * t2^2
    + 2 * w1^2 * t2
    + w1^2 * t2^4
    + 6 * w1^2 * w2 * t2^3
    + 5 * w1^2 * w2^2 * t2^2
    + w1^2 * t1
    + 3 * w1^2 * t1 * t2^3
    + 3 * w1^2 * t1 * w2 * t2^2
    + 7 * w1^2 * t1^2 * t2^2
    + (-6) * w1^2 * t1^2 * t2^5
    + 6 * w1^2 * t1^2 * w2 * t2
    + (-6) * w1^2 * t1^2 * w2 * t2^4
    + 5 * w1^2 * t1^2 * w2^2
    + 4 * w1^2 * t1^3 * t2
    + (-6) * w1^2 * t1^3 * t2^4
    + 4 * w1^2 * t1^3 * w2
    + (-6) * w1^2 * t1^3 * w2 * t2^3) * CharTwo.two_eq_zero (R := K)

/-- The `y`-coordinate identity behind the Hessian addition formula. -/
theorem hess_addY_aux (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1) :
    (w1 * (w2 + t2) + w2 * (w1 + t1))
          * (hessD w1 t1 w2 t2 * (w1 + t1) + (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2))
        + w1 * ((w1 + t1) + (w2 + t2)) * (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2)
        + ((w1 + t1) + (w2 + t2)) * (w1 + t1) * (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2)
      = hessX w1 t1 w2 t2 * ((w1 + t1) + (w2 + t2)) * (w1 + t1) := by
  simp only [hessX, hessY, hessD]
  linear_combination (4 * t2^2
    + 4 * w2 * t2
    + 4 * t1 * t2
    + 2 * t1 * w2
    + 2 * w1 * t2) * h1
    + (2 * t1^2
    + 4 * w1 * t1) * h2 +
    (2 * t2^2
    + 2 * w2 * t2
    + 2 * t1 * t2
    + t1 * w2
    + t1^2
    + (-1) * t1^2 * t2^3
    + t1^2 * w2^2 * t2
    + (-2) * t1^3 * t2^2
    + (-2) * t1^3 * w2 * t2
    + t1^3 * w2^2
    + (-2) * t1^4 * t2
    + (-1) * t1^4 * w2
    + w1 * t2
    + 2 * w1 * t1
    + (-2) * w1 * t1 * t2^3
    + w1 * t1 * w2 * t2^2
    + 3 * w1 * t1 * w2^2 * t2
    + w1 * t1^2 * w2 * t2
    + 3 * w1 * t1^2 * w2^2
    + (-1) * w1 * t1^3 * t2
    + w1 * t1^3 * w2
    + w1^2 * t2^3
    + 2 * w1^2 * w2 * t2^2
    + w1^2 * w2^2 * t2
    + w1^2 * t1 * t2^2
    + w1^2 * t1 * w2 * t2
    + w1^2 * t1 * w2^2
    + w1^2 * t1^2 * t2
    + 2 * w1^2 * t1^2 * w2) * CharTwo.two_eq_zero (R := K)

end KasamiCyclicAdditive.FermatCubic

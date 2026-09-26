/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Geometry
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# An explicit elliptic model for the weighted trace curve

For the normalized trace equation, the birational coordinate `u = x / y`
gives

`u * (1 - u) * y^2 + sigma * u - 1 = 0`.

On the open set where `sigma * u * (1 - u)` is nonzero, the change

`X = sigma * u`, `Y = sigma * u * (1 - u) * y`

identifies this equation with

`Y^2 = X^3 - (sigma + 1) * X^2 + sigma * X
     = X * (X - 1) * (X - sigma)`.

This module proves the coordinate identity and the exact Weierstrass
discriminant.  It does not disguise the remaining algebraic-geometry wall:
the project still needs an in-repository bridge from this nonsingular
Weierstrass model to the genus and Euler-characteristic data used by
Corvaja--Zannier.
-/

@[expose] public section

namespace BGS.Markoff

variable {K : Type*} [Field K]

/-- The Weierstrass model birational to the normalized weighted trace curve. -/
noncomputable def weightedTraceWeierstrassCurve (sigma : K) :
    WeierstrassCurve K :=
  WeierstrassCurve.mk 0 (-(sigma + 1)) 0 sigma 0

/-- The exact discriminant of the weighted trace Weierstrass model. -/
theorem weightedTraceWeierstrassCurve_discriminant (sigma : K) :
    (weightedTraceWeierstrassCurve sigma).Δ =
      16 * sigma ^ 2 * (sigma - 1) ^ 2 := by
  simp [weightedTraceWeierstrassCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- Away from characteristic two and the degenerate parameters `0, 1`, the
explicit Weierstrass model is elliptic. -/
theorem weightedTraceWeierstrassCurve_isElliptic
    (sigma : K) (htwo : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hnondegenerate : sigma ≠ 1) :
    (weightedTraceWeierstrassCurve sigma).IsElliptic := by
  constructor
  rw [weightedTraceWeierstrassCurve_discriminant]
  apply isUnit_iff_ne_zero.mpr
  have h16 : (16 : K) ≠ 0 := by
    simpa only [show (16 : K) = (2 : K) ^ 4 by norm_num] using
      pow_ne_zero 4 htwo
  exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 2 hsigma))
    (pow_ne_zero 2 (sub_ne_zero.mpr hnondegenerate))

/-- The normalized birational trace equation maps to the explicit
Weierstrass equation. -/
theorem normalizedSplitTraceBirational_to_weightedTraceWeierstrass
    (sigma u y : K)
    (htrace : u * (1 - u) * y ^ 2 + sigma * u - 1 = 0) :
    (sigma * u * (1 - u) * y) ^ 2 =
      (sigma * u) ^ 3 - (sigma + 1) * (sigma * u) ^ 2 +
        sigma * (sigma * u) := by
  linear_combination sigma ^ 2 * u * (1 - u) * htrace

/-- On the natural birational open, the normalized trace equation and the
explicit Weierstrass equation are equivalent. -/
theorem normalizedSplitTraceBirational_iff_weightedTraceWeierstrass
    (sigma u y : K) (hsigma : sigma ≠ 0) (hu : u ≠ 0)
    (huOne : 1 - u ≠ 0) :
    u * (1 - u) * y ^ 2 + sigma * u - 1 = 0 ↔
      (sigma * u * (1 - u) * y) ^ 2 =
        (sigma * u) ^ 3 - (sigma + 1) * (sigma * u) ^ 2 +
          sigma * (sigma * u) := by
  constructor
  · exact normalizedSplitTraceBirational_to_weightedTraceWeierstrass sigma u y
  · intro hWeierstrass
    have hidentity :
        (sigma * u * (1 - u) * y) ^ 2 -
            ((sigma * u) ^ 3 - (sigma + 1) * (sigma * u) ^ 2 +
              sigma * (sigma * u)) =
          sigma ^ 2 * u * (1 - u) *
            (u * (1 - u) * y ^ 2 + sigma * u - 1) := by
      ring
    rw [hWeierstrass, sub_self] at hidentity
    have hcoefficient : sigma ^ 2 * u * (1 - u) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsigma) hu) huOne
    exact (mul_eq_zero.mp hidentity.symm).resolve_left hcoefficient

end BGS.Markoff

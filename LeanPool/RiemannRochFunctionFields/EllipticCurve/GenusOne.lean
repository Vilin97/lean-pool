/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.EllipticCurve.GenusCounting

/-!
# Genus one for elliptic function fields
Shows `g(K) = 1` for a fraction field `K` of an elliptic coordinate ring by counting the
Weierstrass monomials in `L(n·∞)`.  The zero canonical divisor is then obtained by moving an
arbitrary canonical divisor with its unique nonzero Riemann–Roch section.
-/

@[expose] public section

open FunctionField
open FunctionField.Chart

open scoped Polynomial RatFunc

namespace WeierstrassCurve.Affine.Chart

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]

variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]

include W

/-- The divisor of the invariant differential is zero (canonical class is trivial). -/
theorem divOmega_invariant_differential :
    IsCanonical k K (0 : DivisorA k K) := by
  exact zero_isCanonical_of_genus_eq_one K (genus_eq_one_counting W K)

/-- **M7b**: the genus of an elliptic function field is `1`. -/
theorem genus_eq_one : genus k K = 1 := by
  exact genus_eq_one_counting W K

end WeierstrassCurve.Affine.Chart

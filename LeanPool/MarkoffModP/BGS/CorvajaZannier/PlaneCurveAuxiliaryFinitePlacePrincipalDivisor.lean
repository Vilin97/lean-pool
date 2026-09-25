/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlace

/-!
# Actual finite-place auxiliary orders in the exhaustive divisor model

This file keeps the local DVR construction independent of the heavier
exhaustive-place infrastructure, then identifies its normalized order with
the coefficient used by the global principal divisor.
-/

@[expose] public section

open scoped Polynomial
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) auxiliaryFinitePlaceBridgePolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance auxiliaryFinitePlaceBridgePolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  .of_algebraMap_eq' rfl

local instance auxiliaryFinitePlaceBridgeIntegralClosureIsDedekindDomain :
    IsDedekindDomain (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (FunctionField.ringOfIntegers K L)

/-- The actual localized finite-place order is exactly the coefficient in
the exhaustive finite principal divisor. -/
theorem finiteExtensionFinitePlaceLocalOrder_eq_principalDivisor
    (q : PlaneCurveExtensionFinitePlace K L) (x : L) :
    finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q x =
      finiteExtensionFinitePrincipalDivisor K L x q := by
  rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
    finiteExtensionFinitePrincipalDivisor_apply]
  have h := fractionRingAlgEquiv_finitePlaceOrder_eq
    (L := L) q
      ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)
  simpa [ratFuncFiniteIntegralClosureFractionRingEquiv] using h

/-- For a nonzero element, the `WithTop` order appearing in the local
Wronskian inequality is the exhaustive principal-divisor coefficient. -/
theorem finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
    (q : PlaneCurveExtensionFinitePlace K L) (x : L) (hx : x ≠ 0) :
    finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q x =
      (finiteExtensionFinitePrincipalDivisor K L x q : WithTop ℤ) := by
  rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q x hx]
  have horder :=
    finiteExtensionFinitePlaceLocalOrder_eq_principalDivisor K L q x
  rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder] at horder
  exact_mod_cast horder

end

end BGS.CorvajaZannier

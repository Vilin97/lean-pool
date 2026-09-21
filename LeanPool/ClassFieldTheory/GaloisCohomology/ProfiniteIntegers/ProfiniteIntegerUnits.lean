/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerPrimeProduct
import Mathlib.Topology.Algebra.Group.Units
/-!
# Units of the profinite integers

This file upgrades the prime-product Chinese-remainder equivalence for
`ℤ̂` to topological additive, multiplicative, and unit-group equivalences.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

/-- The Chinese-remainder isomorphism as a topological monoid equivalence. -/
noncomputable def zHatContinuousMulEquivPrimeProduct :
    ZHat ≃ₜ* ProfiniteIntegerPrimeProduct :=
  ContinuousMulEquiv.mk'
    (continuous_zHatToProfiniteIntegerPrimeProduct.homeoOfEquivCompactToT2
      (f := zHatRingEquivProfiniteIntegerPrimeProduct.toEquiv))
    zHatRingEquivProfiniteIntegerPrimeProduct.map_mul

/-- The additive form of the topological Chinese-remainder isomorphism. -/
noncomputable def zHatContinuousAddEquivPrimeProduct :
    ZHat ≃ₜ+ ProfiniteIntegerPrimeProduct :=
  { zHatRingEquivProfiniteIntegerPrimeProduct.toAddEquiv with
    continuous_toFun :=
      zHatContinuousMulEquivPrimeProduct.continuous_toFun
    continuous_invFun :=
      zHatContinuousMulEquivPrimeProduct.continuous_invFun }

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The canonical topological Chinese-remainder equivalence on unit
groups. -/
noncomputable def zHatUnitsContinuousMulEquivPrimeProduct :
    ZHatˣ ≃ₜ* ((p : Nat.Primes) → ℤ_[p.1]ˣ) :=
  (Units.mapContinuousMulEquiv
    zHatContinuousMulEquivPrimeProduct).trans
      ContinuousMulEquiv.piUnits

/-- On underlying ring elements, the unit-group Chinese-remainder
equivalence is the canonical `p`-adic coordinate map. -/
@[simp]
theorem zHatUnitsContinuousMulEquivPrimeProduct_coe_apply
    (u : ZHatˣ) (p : Nat.Primes) :
    (zHatUnitsContinuousMulEquivPrimeProduct u p : ℤ_[p.1]) =
      zHatToPadicInt p (u : ZHat) :=
  rfl

end ClassFormation

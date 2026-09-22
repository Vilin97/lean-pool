/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# The equal-characteristic completed-unramified construction: equal-characteristic Frobenius on
  the completed unramified ring

For a finite field `k`, arithmetic Frobenius acts on `AlgebraicClosure k`
by the `#k`-power map and hence coefficientwise on
`(AlgebraicClosure k)[[T]]`.  These definitions belong to the completed
maximal-unramified source used in the equal-characteristic completed-unramified construction;
  the theta construction of the equal-characteristic theta construction
depends on them, not conversely.

This is an equal-characteristic specialization of the general local-field construction, not a
  claim that Lemma the equal-characteristic completed-unramified construction is complete in
  general.
-/

noncomputable section

open scoped PowerSeries

universe u

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

/-- Arithmetic Frobenius on the algebraic closure of the finite coefficient
field. -/
noncomputable def equalCharacteristicCoefficientFrobenius :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := by
  letI : Fintype k := Fintype.ofFinite k
  exact FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)

/-- States the theorem `equalCharacteristicCoefficientFrobenius_apply`. -/
@[simp]
theorem equalCharacteristicCoefficientFrobenius_apply
    (x : AlgebraicClosure k) :
    equalCharacteristicCoefficientFrobenius k x = x ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  simp [equalCharacteristicCoefficientFrobenius,
    Nat.card_eq_fintype_card]

/-- Arithmetic Frobenius on the completed maximal-unramified coefficient
ring, acting coefficientwise and fixing `T`. -/
noncomputable def equalCharacteristicPowerSeriesFrobenius :
    (AlgebraicClosure k)⟦X⟧ →+* (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (equalCharacteristicCoefficientFrobenius k).toRingHom

/-- States the theorem `equalCharacteristicPowerSeriesFrobenius_coeff`. -/
@[simp]
theorem equalCharacteristicPowerSeriesFrobenius_coeff
    (f : (AlgebraicClosure k)⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (equalCharacteristicPowerSeriesFrobenius k f) =
      (PowerSeries.coeff n f) ^ Nat.card k := by
  simp [equalCharacteristicPowerSeriesFrobenius,
    equalCharacteristicCoefficientFrobenius_apply]

/-- States the theorem `equalCharacteristicPowerSeriesFrobenius_X`. -/
@[simp]
theorem equalCharacteristicPowerSeriesFrobenius_X :
    equalCharacteristicPowerSeriesFrobenius k
        (PowerSeries.X : (AlgebraicClosure k)⟦X⟧) =
      PowerSeries.X := by
  simp [equalCharacteristicPowerSeriesFrobenius]

end EqualCharacteristic
end LubinTate

/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
/-!
# The Lubin–Tate endomorphism commutation law: uniqueness source for the first theta identity

This file proves the uniqueness lemma used for the first theta identity in
the equal-characteristic specialization.  The identity
`theta^phi = theta o [u]` itself is a separate required endpoint.
-/

@[expose] public section

noncomputable section

open scoped PowerSeries

namespace LubinTate
namespace EqualCharacteristic


variable {k : Type*} [Field k] [Finite k]

/-- A `q`-additive theta intertwiner is uniquely determined by its linear
coefficient.  This is the uniqueness part of the contracting Frobenius equation specialized to the
coefficient recursion used in the completed theta-intertwining theorem. -/
theorem equalCharacteristicThetaCoefficient_unique
    (u : k⟦X⟧ˣ)
    (c : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hc0 : c 0 = equalCharacteristicThetaCoefficient u 0)
    (hrec : ∀ j : ℕ,
      PowerSeries.X * c (j + 1) -
          equalCharacteristicCompletedSourceUniformizer u ^
              (Nat.card k ^ (j + 1)) *
            equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) =
        equalCharacteristicThetaBetaNumerator (c j)) :
    c = equalCharacteristicThetaCoefficient u := by
  funext j
  induction j with
  | zero => exact hc0
  | succ j ih =>
      have hcleared := hrec j
      rw [ih] at hcleared
      have hgamma := equalCharacteristicThetaGamma_constantCoeff u
        (j + 1) (Nat.zero_lt_succ j)
      have hmul : PowerSeries.X *
          (c (j + 1) -
            equalCharacteristicThetaGamma u (j + 1) *
              equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) -
            equalCharacteristicThetaBeta
              (equalCharacteristicThetaCoefficient u j)) = 0 := by
        rw [mul_sub, mul_sub, ← mul_assoc,
          equalCharacteristicThetaGamma_mul_X u (j + 1)
            (Nat.zero_lt_succ j),
          equalCharacteristicThetaBeta_mul_X]
        exact sub_eq_zero.mpr hcleared
      have hcontract :
          c (j + 1) =
            equalCharacteristicThetaBeta
                (equalCharacteristicThetaCoefficient u j) +
              equalCharacteristicThetaGamma u (j + 1) *
                equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) := by
        apply sub_eq_zero.mp
        apply PowerSeries.X_mul_injective
        simpa [sub_eq_add_neg, add_assoc] using hmul
      have huniq := contractingFrobeniusEquationSolution_unique
        (equalCharacteristicCoefficientFrobenius k).toRingHom
        (equalCharacteristicThetaGamma u (j + 1))
        (equalCharacteristicThetaBeta
          (equalCharacteristicThetaCoefficient u j))
        (c (j + 1)) hgamma
        (by
          simpa [equalCharacteristicPowerSeriesFrobenius] using hcontract)
      simpa [equalCharacteristicThetaCoefficient] using huniq
end EqualCharacteristic
end LubinTate

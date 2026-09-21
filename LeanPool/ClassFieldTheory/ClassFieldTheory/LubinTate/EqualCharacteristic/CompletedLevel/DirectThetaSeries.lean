/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
/-!
# The completed theta-intertwining theorem: the direct-orientation theta series

This file constructs the theta series in the orientation used directly in
the completed theta-intertwining theorem: the source prime is `pi = T` and the target prime is
`bar_pi = uT`.  Thus the second identity is

`theta^φ ∘ e_T = e_(uT) ∘ theta`.

This coefficient recursion is mathematically distinct from the
constructed specialization `u⁻¹T → T`.  The first theta identity and
analytic evaluation at division points are developed in the corresponding
companion modules.
-/

noncomputable section

open scoped PowerSeries


universe u

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} [Field k] [Finite k]

/-- The target prime `bar_pi = uT` in the completed maximal-unramified
coefficient ring. -/
noncomputable def equalCharacteristicDirectCompletedTargetUniformizer
    (u : k⟦X⟧ˣ) : (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
    PowerSeries.X

/-- The direct-orientation contracting coefficient
`gamma_j = u⁻¹ T^(q^j-1)`. -/
noncomputable def equalCharacteristicDirectThetaGamma
    (u : k⟦X⟧ˣ) (j : ℕ) : (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k))
      ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) *
    PowerSeries.X ^ (Nat.card k ^ j - 1)

/-- Positive-index direct theta gamma terms have zero constant coefficient. -/
theorem equalCharacteristicDirectThetaGamma_constantCoeff
    (u : k⟦X⟧ˣ) (j : ℕ) (hj : 0 < j) :
    PowerSeries.coeff 0 (equalCharacteristicDirectThetaGamma u j) = 0 := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpow : 0 < Nat.card k ^ j - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow hj.ne' hq)
  simp [equalCharacteristicDirectThetaGamma, hpow.ne']

/-- Clearing the direct gamma by the target prime `uT` gives
`T^(q^j)`. -/
theorem equalCharacteristicDirectTargetUniformizer_mul_gamma
    (u : k⟦X⟧ˣ) (j : ℕ) (hj : 0 < j) :
    equalCharacteristicDirectCompletedTargetUniformizer u *
        equalCharacteristicDirectThetaGamma u j =
      PowerSeries.X ^ (Nat.card k ^ j) := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpow : 1 ≤ Nat.card k ^ j :=
    (Nat.one_lt_pow hj.ne' hq).le
  have huinv :
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
          PowerSeries.map (algebraMap k (AlgebraicClosure k))
            ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul]
    simp
  rw [equalCharacteristicDirectCompletedTargetUniformizer,
    equalCharacteristicDirectThetaGamma]
  calc
    (PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
          PowerSeries.X) *
        (PowerSeries.map (algebraMap k (AlgebraicClosure k))
            ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) *
          PowerSeries.X ^ (Nat.card k ^ j - 1)) =
      (PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
          PowerSeries.map (algebraMap k (AlgebraicClosure k))
            ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) *
        (PowerSeries.X ^ (Nat.card k ^ j - 1) * PowerSeries.X) := by
          ring
    _ = PowerSeries.X ^ (Nat.card k ^ j) := by
      rw [huinv, one_mul, ← pow_succ, Nat.sub_add_cancel hpow]

/-- The direct right-hand side
`beta(b) = u⁻¹ (phi(b)-b^q)/T` of the contracting recursion. -/
noncomputable def equalCharacteristicDirectThetaBeta
    (u : k⟦X⟧ˣ) (b : (AlgebraicClosure k)⟦X⟧) :
    (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k))
      ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) *
    equalCharacteristicPowerSeriesTail
      (equalCharacteristicPowerSeriesFrobenius k b - b ^ Nat.card k)

/-- Clearing the direct beta by `uT` recovers its numerator
`phi(b)-b^q`. -/
theorem equalCharacteristicDirectTargetUniformizer_mul_beta
    (u : k⟦X⟧ˣ) (b : (AlgebraicClosure k)⟦X⟧) :
    equalCharacteristicDirectCompletedTargetUniformizer u *
        equalCharacteristicDirectThetaBeta u b =
      equalCharacteristicPowerSeriesFrobenius k b - b ^ Nat.card k := by
  have huinv :
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
          PowerSeries.map (algebraMap k (AlgebraicClosure k))
            ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul]
    simp
  rw [equalCharacteristicDirectCompletedTargetUniformizer,
    equalCharacteristicDirectThetaBeta]
  calc
    (PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
          PowerSeries.X) *
        (PowerSeries.map (algebraMap k (AlgebraicClosure k))
            ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) *
          equalCharacteristicPowerSeriesTail
            (equalCharacteristicPowerSeriesFrobenius k b -
              b ^ Nat.card k)) =
      (PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
          PowerSeries.map (algebraMap k (AlgebraicClosure k))
            ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) *
        (PowerSeries.X * equalCharacteristicPowerSeriesTail
          (equalCharacteristicPowerSeriesFrobenius k b -
            b ^ Nat.card k)) := by
          ring
    _ = equalCharacteristicPowerSeriesFrobenius k b - b ^ Nat.card k := by
      rw [huinv, one_mul]
      exact equalCharacteristicThetaBeta_mul_X b

/-- Coefficients of the direct-orientation additive theta series.  Its
linear coefficient solves `phi(b₀)=u b₀`; the later coefficients are the
actual recursively constructed solutions of the contracting equations. -/
noncomputable def equalCharacteristicDirectThetaCoefficient
    (u : k⟦X⟧ˣ) : ℕ → (AlgebraicClosure k)⟦X⟧
  | 0 => equalCharacteristicSemilinearUnit (u : k⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
  | j + 1 =>
      contractingFrobeniusEquationSolution
        (equalCharacteristicCoefficientFrobenius k).toRingHom
        (equalCharacteristicDirectThetaGamma u (j + 1))
        (equalCharacteristicDirectThetaBeta u
          (equalCharacteristicDirectThetaCoefficient u j))

/-- The zeroth direct theta coefficient is the semilinear source unit. -/
@[simp]
theorem equalCharacteristicDirectThetaCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicDirectThetaCoefficient u 0 =
      equalCharacteristicSemilinearUnit (u : k⟦X⟧)
        (by
          intro hzero
          have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
          apply hunit.ne_zero
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero) :=
  rfl

/-- The direct contracting recursion
`b_(j+1) - gamma_(j+1) phi(b_(j+1)) = beta(b_j)`. -/
theorem equalCharacteristicDirectThetaCoefficient_succ_equation
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicDirectThetaCoefficient u (j + 1) -
        equalCharacteristicDirectThetaGamma u (j + 1) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaCoefficient u (j + 1)) =
      equalCharacteristicDirectThetaBeta u
        (equalCharacteristicDirectThetaCoefficient u j) := by
  rw [equalCharacteristicDirectThetaCoefficient]
  have hgamma := equalCharacteristicDirectThetaGamma_constantCoeff u
    (j + 1) (Nat.zero_lt_succ j)
  apply (sub_eq_iff_eq_add).2
  simpa [equalCharacteristicPowerSeriesFrobenius] using
    (contractingFrobeniusEquationSolution_spec
      (equalCharacteristicCoefficientFrobenius k).toRingHom
      (equalCharacteristicDirectThetaGamma u (j + 1))
      (equalCharacteristicDirectThetaBeta u
        (equalCharacteristicDirectThetaCoefficient u j)) hgamma)

/-- The coefficient comparison obtained after clearing `uT`. -/
theorem equalCharacteristicDirectThetaCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicDirectCompletedTargetUniformizer u *
          equalCharacteristicDirectThetaCoefficient u (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaCoefficient u (j + 1)) =
      equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicDirectThetaCoefficient u j) -
        equalCharacteristicDirectThetaCoefficient u j ^ Nat.card k := by
  have hrec := congrArg (fun z : (AlgebraicClosure k)⟦X⟧ ↦
      equalCharacteristicDirectCompletedTargetUniformizer u * z)
    (equalCharacteristicDirectThetaCoefficient_succ_equation u j)
  change equalCharacteristicDirectCompletedTargetUniformizer u *
      (equalCharacteristicDirectThetaCoefficient u (j + 1) -
        equalCharacteristicDirectThetaGamma u (j + 1) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaCoefficient u (j + 1))) =
      equalCharacteristicDirectCompletedTargetUniformizer u *
        equalCharacteristicDirectThetaBeta u
          (equalCharacteristicDirectThetaCoefficient u j) at hrec
  rw [mul_sub, ← mul_assoc,
    equalCharacteristicDirectTargetUniformizer_mul_gamma u
      (j + 1) (Nat.zero_lt_succ j),
    equalCharacteristicDirectTargetUniformizer_mul_beta] at hrec
  exact hrec

/-- The genuine sparse outer theta series for the direct orientation
`T → uT`. -/
noncomputable def equalCharacteristicDirectThetaSeries
    (u : k⟦X⟧ˣ) : ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  equalCharacteristicQAdditiveSeries k
    (equalCharacteristicDirectThetaCoefficient u)

/-- The direct theta coefficient at `q ^ j` is its `j`th recursive coefficient. -/
@[simp]
theorem equalCharacteristicDirectThetaSeries_coeff_pow
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicDirectThetaSeries u) =
      equalCharacteristicDirectThetaCoefficient u j :=
  equalCharacteristicQAdditiveSeries_coeff_pow k
    (equalCharacteristicDirectThetaCoefficient u) j

/-- The direct theta series has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicDirectThetaSeries_constantCoeff
    (u : k⟦X⟧ˣ) :
    PowerSeries.constantCoeff (equalCharacteristicDirectThetaSeries u) = 0 :=
  equalCharacteristicQAdditiveSeries_constantCoeff k _

/-- The direct theta series is valid as a substitution series. -/
theorem equalCharacteristicDirectThetaSeries_hasSubst
    (u : k⟦X⟧ˣ) :
    PowerSeries.HasSubst (equalCharacteristicDirectThetaSeries u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicDirectThetaSeries_constantCoeff u)

/-- Arithmetic Frobenius on every coefficient of the direct theta series. -/
noncomputable def equalCharacteristicDirectThetaSeriesFrobenius
    (u : k⟦X⟧ˣ) : ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
    (equalCharacteristicDirectThetaSeries u)

/-- Frobenius of direct theta is the `q`-additive series of Frobenius coefficients. -/
theorem equalCharacteristicDirectThetaSeriesFrobenius_eq_qAdditiveSeries
    (u : k⟦X⟧ˣ) :
    equalCharacteristicDirectThetaSeriesFrobenius u =
      equalCharacteristicQAdditiveSeries k
        (fun j ↦ equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicDirectThetaCoefficient u j)) := by
  exact equalCharacteristicQAdditiveSeries_map k
    (equalCharacteristicPowerSeriesFrobenius k)
    (equalCharacteristicDirectThetaCoefficient u)

/-- Direct the completed theta-intertwining theorem second identity:
`theta^φ ∘ e_T = e_(uT) ∘ theta`. -/
theorem equalCharacteristicDirectThetaSeries_intertwines
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
        (equalCharacteristicDirectThetaSeriesFrobenius u) =
      PowerSeries.subst (equalCharacteristicDirectThetaSeries u)
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicDirectCompletedTargetUniformizer u)) := by
  rw [equalCharacteristicDirectThetaSeriesFrobenius_eq_qAdditiveSeries,
    equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries,
    equalCharacteristicDirectThetaSeries,
    equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries]
  congr 1
  funext j
  cases j with
  | zero =>
      rw [equalCharacteristicLubinTateSubstitutionCoefficient,
        equalCharacteristicLubinTatePostcompositionCoefficient,
        equalCharacteristicDirectThetaCoefficient_zero,
        equalCharacteristicPowerSeriesFrobenius_semilinearUnit,
        equalCharacteristicDirectCompletedTargetUniformizer]
      ring
  | succ j =>
      rw [equalCharacteristicLubinTateSubstitutionCoefficient,
        equalCharacteristicLubinTatePostcompositionCoefficient]
      have h := equalCharacteristicDirectThetaCoefficient_succ_comparison u j
      linear_combination -h

/-- The direct theta series has the semilinear leading unit as its linear
coefficient. -/
theorem equalCharacteristicDirectThetaSeries_coeff_one
    (u : k⟦X⟧ˣ) :
    PowerSeries.coeff 1 (equalCharacteristicDirectThetaSeries u) =
      equalCharacteristicSemilinearUnit (u : k⟦X⟧)
        (by
          intro hzero
          have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
          apply hunit.ne_zero
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero) := by
  calc
    PowerSeries.coeff 1 (equalCharacteristicDirectThetaSeries u) =
        equalCharacteristicDirectThetaCoefficient u 0 := by
      simpa only [pow_zero] using
        equalCharacteristicDirectThetaSeries_coeff_pow u 0
    _ = _ := equalCharacteristicDirectThetaCoefficient_zero u

end EqualCharacteristic
end LubinTate

/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
/-!
# The completed theta-intertwining theorem: the standard equal-characteristic Lubin--Tate bracket

In the proof of the completed theta-intertwining theorem the standard Lubin--Tate series is

`e_T(Y) = Y^q + T Y`.

For a unit `u`, this file constructs the endomorphism `[u]` of this standard
Lubin--Tate group.  Its linear coefficient is `u`; the higher additive
coefficients are the unique contracting solutions forced by commutation with
`e_T`.  This is the orientation used in the completed theta-intertwining theorem itself, as opposed to the
normalization `u⁻¹T -> T` used in Corollary the Lubin–Tate endomorphism commutation law.
-/

noncomputable section

open scoped PowerSeries


universe u

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} [Field k] [Finite k]

/-- After division by `T`, the contracting coefficient in the recurrence for
the coefficients of the standard bracket `[u]`. -/
noncomputable def equalCharacteristicDirectBracketGamma
    (j : ℕ) : k⟦X⟧ :=
  PowerSeries.X ^ (Nat.card k ^ j - 1)

/-- Positive-index direct bracket gamma terms have zero constant coefficient. -/
theorem equalCharacteristicDirectBracketGamma_constantCoeff
    (j : ℕ) (hj : 0 < j) :
    PowerSeries.coeff 0 (equalCharacteristicDirectBracketGamma (k := k) j) = 0 := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpow : 0 < Nat.card k ^ j - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow hj.ne' hq)
  simp [equalCharacteristicDirectBracketGamma, hpow.ne]

/-- Division of `a-a^q` by the standard prime `T`. -/
noncomputable def equalCharacteristicDirectBracketBeta
    (a : k⟦X⟧) : k⟦X⟧ :=
  equalCharacteristicPowerSeriesTail
    (equalCharacteristicSourceBracketNumerator a)

/-- Additive coefficients of the standard Lubin--Tate endomorphism `[u]`. -/
noncomputable def equalCharacteristicDirectBracketCoefficient
    (u : k⟦X⟧) : ℕ → k⟦X⟧
  | 0 => u
  | j + 1 =>
      contractingFrobeniusEquationSolution (R := k)
        (RingHom.id k)
        (equalCharacteristicDirectBracketGamma (k := k) (j + 1))
        (equalCharacteristicDirectBracketBeta
          (equalCharacteristicDirectBracketCoefficient u j))

omit [Finite k] in
/-- The zeroth direct bracket coefficient is the input power series. -/
@[simp]
theorem equalCharacteristicDirectBracketCoefficient_zero
    (u : k⟦X⟧) :
    equalCharacteristicDirectBracketCoefficient u 0 = u :=
  rfl

/-- Successive direct bracket coefficients satisfy the defining contraction equation. -/
theorem equalCharacteristicDirectBracketCoefficient_succ_equation
    (u : k⟦X⟧) (j : ℕ) :
    equalCharacteristicDirectBracketCoefficient u (j + 1) -
        equalCharacteristicDirectBracketGamma (k := k) (j + 1) *
          equalCharacteristicDirectBracketCoefficient u (j + 1) =
      equalCharacteristicDirectBracketBeta
        (equalCharacteristicDirectBracketCoefficient u j) := by
  rw [equalCharacteristicDirectBracketCoefficient]
  have hgamma := equalCharacteristicDirectBracketGamma_constantCoeff
    (k := k) (j + 1) (Nat.zero_lt_succ j)
  apply (sub_eq_iff_eq_add).2
  simpa using
    (contractingFrobeniusEquationSolution_spec (R := k)
      (RingHom.id k)
      (equalCharacteristicDirectBracketGamma (k := k) (j + 1))
      (equalCharacteristicDirectBracketBeta
        (equalCharacteristicDirectBracketCoefficient u j)) hgamma)

/-- Coefficient comparison equivalent to commutation of `[u]` with
`e_T(Y)=Y^q+TY`. -/
theorem equalCharacteristicDirectBracketCoefficient_succ_comparison
    (u : k⟦X⟧) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicDirectBracketCoefficient u (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicDirectBracketCoefficient u (j + 1) =
      equalCharacteristicDirectBracketCoefficient u j -
        equalCharacteristicDirectBracketCoefficient u j ^ Nat.card k := by
  let qj := Nat.card k ^ (j + 1)
  let a := equalCharacteristicDirectBracketCoefficient u (j + 1)
  let b := equalCharacteristicDirectBracketCoefficient u j
  have hqj : 1 ≤ qj :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Nat.card_pos.ne')
  have hXGamma :
      PowerSeries.X *
          equalCharacteristicDirectBracketGamma (k := k) (j + 1) =
        (PowerSeries.X : k⟦X⟧) ^ qj := by
    rw [equalCharacteristicDirectBracketGamma]
    calc
      PowerSeries.X * (PowerSeries.X : k⟦X⟧) ^ (qj - 1) =
          PowerSeries.X ^ ((qj - 1) + 1) := by
            rw [pow_succ']
      _ = PowerSeries.X ^ qj := by rw [Nat.sub_add_cancel hqj]
  have htail :
      PowerSeries.X *
          equalCharacteristicPowerSeriesTail
            (equalCharacteristicSourceBracketNumerator b) =
        equalCharacteristicSourceBracketNumerator b := by
    have hsplit := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C
      (equalCharacteristicSourceBracketNumerator b)
    rw [equalCharacteristicSourceBracketNumerator_constantCoeff] at hsplit
    simpa only [map_zero, add_zero] using hsplit.symm
  have hrec := congrArg
    (fun z : k⟦X⟧ ↦ PowerSeries.X * z)
    (equalCharacteristicDirectBracketCoefficient_succ_equation u j)
  change PowerSeries.X *
      (a - equalCharacteristicDirectBracketGamma (k := k) (j + 1) * a) =
    PowerSeries.X * equalCharacteristicDirectBracketBeta b at hrec
  rw [mul_sub, ← mul_assoc, hXGamma,
    equalCharacteristicDirectBracketBeta, htail] at hrec
  simpa [a, b, qj, equalCharacteristicSourceBracketNumerator] using hrec

/-- The standard Lubin--Tate endomorphism `[u]` over `k[[T]]`. -/
noncomputable def equalCharacteristicDirectBracket
    (u : k⟦X⟧) : (k⟦X⟧)⟦X⟧ :=
  equalCharacteristicQAdditiveSeries k
    (equalCharacteristicDirectBracketCoefficient u)

/-- The direct bracket coefficient at `q ^ j` is its `j`th recursive coefficient. -/
@[simp]
theorem equalCharacteristicDirectBracket_coeff_pow
    (u : k⟦X⟧) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicDirectBracket u) =
      equalCharacteristicDirectBracketCoefficient u j := by
  exact equalCharacteristicQAdditiveSeries_coeff_pow k _ j

/-- The direct bracket has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicDirectBracket_constantCoeff
    (u : k⟦X⟧) :
    PowerSeries.constantCoeff (equalCharacteristicDirectBracket u) = 0 := by
  exact equalCharacteristicQAdditiveSeries_constantCoeff k _

/-- The direct bracket is valid as a substitution series. -/
theorem equalCharacteristicDirectBracket_hasSubst
    (u : k⟦X⟧) :
    PowerSeries.HasSubst (equalCharacteristicDirectBracket u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicDirectBracket_constantCoeff u)

/-- Coefficients after extension to the completed maximal unramified integer
ring. -/
noncomputable def equalCharacteristicCompletedDirectBracketCoefficient
    (u : k⟦X⟧) (j : ℕ) : (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k))
    (equalCharacteristicDirectBracketCoefficient u j)

/-- The standard bracket over the completed maximal unramified integer ring. -/
noncomputable def equalCharacteristicCompletedDirectBracket
    (u : k⟦X⟧) : ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  equalCharacteristicQAdditiveSeries k
    (equalCharacteristicCompletedDirectBracketCoefficient u)

/-- The completed direct bracket records its `j`th coefficient at exponent `q ^ j`. -/
@[simp]
theorem equalCharacteristicCompletedDirectBracket_coeff_pow
    (u : k⟦X⟧) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicCompletedDirectBracket u) =
      equalCharacteristicCompletedDirectBracketCoefficient u j := by
  exact equalCharacteristicQAdditiveSeries_coeff_pow k _ j

/-- The completed direct bracket has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicCompletedDirectBracket_constantCoeff
    (u : k⟦X⟧) :
    PowerSeries.constantCoeff
        (equalCharacteristicCompletedDirectBracket u) = 0 := by
  exact equalCharacteristicQAdditiveSeries_constantCoeff k _

/-- The completed direct bracket is valid as a substitution series. -/
theorem equalCharacteristicCompletedDirectBracket_hasSubst
    (u : k⟦X⟧) :
    PowerSeries.HasSubst (equalCharacteristicCompletedDirectBracket u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicCompletedDirectBracket_constantCoeff u)

omit [Finite k] in
/-- The zeroth completed direct coefficient is the scalar extension of the input. -/
@[simp]
theorem equalCharacteristicCompletedDirectBracketCoefficient_zero
    (u : k⟦X⟧) :
    equalCharacteristicCompletedDirectBracketCoefficient u 0 =
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) u := by
  simp [equalCharacteristicCompletedDirectBracketCoefficient]

/-- Every coefficient of the standard bracket is defined over `k[[T]]`, so
coefficient Frobenius fixes the bracket. -/
theorem equalCharacteristicCompletedDirectBracket_frobenius
    (u : k⟦X⟧) :
    PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (equalCharacteristicCompletedDirectBracket u) =
      equalCharacteristicCompletedDirectBracket u := by
  rw [equalCharacteristicCompletedDirectBracket,
    equalCharacteristicQAdditiveSeries_map]
  congr 1
  funext j
  exact equalCharacteristicPowerSeriesFrobenius_map_algebraMap
    (equalCharacteristicDirectBracketCoefficient u j)

/-- The standard coefficient recurrence after extension to the completed
maximal unramified integer ring. -/
theorem equalCharacteristicCompletedDirectBracketCoefficient_succ_comparison
    (u : k⟦X⟧) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicCompletedDirectBracketCoefficient u (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicCompletedDirectBracketCoefficient u (j + 1) =
      equalCharacteristicCompletedDirectBracketCoefficient u j -
        equalCharacteristicCompletedDirectBracketCoefficient u j ^ Nat.card k := by
  have h := congrArg
    (PowerSeries.map (algebraMap k (AlgebraicClosure k)))
    (equalCharacteristicDirectBracketCoefficient_succ_comparison u j)
  simpa [equalCharacteristicCompletedDirectBracketCoefficient,
    map_sub, map_mul, map_pow] using h

/-- The standard `[u]` commutes with `e_T(Y)=Y^q+TY`. -/
theorem equalCharacteristicCompletedDirectBracket_commutes
    (u : k⟦X⟧) :
    PowerSeries.subst (equalCharacteristicCompletedDirectBracket u)
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)) =
      PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
        (equalCharacteristicCompletedDirectBracket u) := by
  rw [equalCharacteristicCompletedDirectBracket,
    equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries,
    equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries]
  congr 1
  funext j
  cases j with
  | zero =>
      simp [equalCharacteristicLubinTatePostcompositionCoefficient,
        equalCharacteristicLubinTateSubstitutionCoefficient, mul_comm]
  | succ j =>
      rw [equalCharacteristicLubinTatePostcompositionCoefficient,
        equalCharacteristicLubinTateSubstitutionCoefficient]
      have h :=
        equalCharacteristicCompletedDirectBracketCoefficient_succ_comparison
          u j
      linear_combination h

end EqualCharacteristic
end LubinTate

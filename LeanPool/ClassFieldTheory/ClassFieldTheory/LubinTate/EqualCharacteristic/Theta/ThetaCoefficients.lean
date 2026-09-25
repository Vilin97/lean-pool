/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
/-!
# LubinTate the equal-characteristic theta construction: equal-characteristic theta coefficients

This file constructs the coefficient sources behind the power series
`theta` in the equal-characteristic specialization of the equal-characteristic theta construction.
For a finite field `k`, the completed maximal unramified coefficient ring of
`k((T))` is modeled by `(AlgebraicClosure k)[[T]]`, with arithmetic
Frobenius acting coefficientwise.

The first construction solves the exact semilinear equation

`phi(epsilon) = u * epsilon`

for every unit `u in k[[T]]`.  This is the linear coefficient equation forced
by `theta^phi o e_bar = e o theta` when `pi = u * bar_pi`.
-/

@[expose] public section

noncomputable
section


open scoped PowerSeries Polynomial

universe u

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

private theorem exists_frobenius_eq_mul_add
    (a c : AlgebraicClosure k) :
    ∃ x : AlgebraicClosure k,
      x ^ Nat.card k = a * x + c := by
  let q := Nat.card k
  let P : Polynomial (AlgebraicClosure k) :=
    Polynomial.X ^ q - Polynomial.C a * Polynomial.X - Polynomial.C c
  have hq : 1 < q := Finite.one_lt_card
  have hmain : (Polynomial.X ^ q : Polynomial (AlgebraicClosure k)).Monic :=
    Polynomial.monic_X_pow q
  have hlowerDegree :
      (Polynomial.C a * Polynomial.X + Polynomial.C c :
        Polynomial (AlgebraicClosure k)).degree <
        (Polynomial.X ^ q : Polynomial (AlgebraicClosure k)).degree := by
    rw [Polynomial.degree_X_pow]
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · by_cases ha : a = 0
      · simp [ha]
      · rw [Polynomial.degree_C_mul_X ha]
        exact_mod_cast hq
    · by_cases hc : c = 0
      · simp [hc]
      · rw [Polynomial.degree_C hc]
        exact_mod_cast Nat.zero_lt_one.trans hq
  have hPdegree : P.degree = (q : WithBot ℕ) := by
    dsimp only [P]
    rw [sub_sub]
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlowerDegree,
      Polynomial.degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P (by
    rw [hPdegree]
    exact_mod_cast
      (ne_of_gt (Nat.zero_lt_one.trans hq)))
  refine ⟨x, ?_⟩
  change Polynomial.eval x P = 0 at hx
  have hxc : x ^ q - a * x = c := by
    apply sub_eq_zero.mp
    simpa [P, q] using hx
  calc
    x ^ Nat.card k = c + a * x := sub_eq_iff_eq_add.mp hxc
    _ = a * x + c := add_comm _ _

variable {k}

/-- The constant coefficient chosen for a solution of
`phi(epsilon)=u*epsilon`. -/
noncomputable def chosenEqualCharacteristicSemilinearLeadingCoefficient
    (u : k⟦X⟧) :
    AlgebraicClosure k :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq
      (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u))
      (Nat.sub_pos_of_lt (Finite.one_lt_card : 1 < Nat.card k)))

/-- The chosen leading coefficient is a `(q - 1)`st root of the source constant term. -/
theorem chosenEqualCharacteristicSemilinearLeadingCoefficient_pow
    (u : k⟦X⟧) :
    chosenEqualCharacteristicSemilinearLeadingCoefficient u ^
        (Nat.card k - 1) =
      algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u) :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq
      (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u))
      (Nat.sub_pos_of_lt (Finite.one_lt_card : 1 < Nat.card k)))

/-- A nonzero source constant term gives a nonzero chosen leading coefficient. -/
theorem chosenEqualCharacteristicSemilinearLeadingCoefficient_ne_zero
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) :
    chosenEqualCharacteristicSemilinearLeadingCoefficient u ≠ 0 := by
  intro hzero
  have hpow := chosenEqualCharacteristicSemilinearLeadingCoefficient_pow u
  rw [hzero, zero_pow] at hpow
  · apply hu
    apply (algebraMap k (AlgebraicClosure k)).injective
    simpa using hpow.symm
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card k)

/-- Coefficients of the exact semilinear solution.  At stage `n+1`, the
new coefficient is chosen as a root of the separable additive polynomial
forced by the first `n+1` coefficient equations. -/
noncomputable def chosenEqualCharacteristicSemilinearCoefficient
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) :
    (n : ℕ) → AlgebraicClosure k
  | 0 => chosenEqualCharacteristicSemilinearLeadingCoefficient u
  | n + 1 =>
      Classical.choose
        (exists_frobenius_eq_mul_add k
          (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u))
          (∑ j : Fin (n + 1),
            algebraMap k (AlgebraicClosure k)
                (PowerSeries.coeff (j + 1) u) *
              chosenEqualCharacteristicSemilinearCoefficient u hu (n - j)))
termination_by n => n
decreasing_by
  all_goals exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- The zeroth semilinear coefficient is the chosen leading coefficient. -/
@[simp]
theorem chosenEqualCharacteristicSemilinearCoefficient_zero
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) :
    chosenEqualCharacteristicSemilinearCoefficient u hu 0 =
      chosenEqualCharacteristicSemilinearLeadingCoefficient u := by
  rw [chosenEqualCharacteristicSemilinearCoefficient]

/-- Successive semilinear coefficients satisfy the defining Frobenius recursion. -/
theorem chosenEqualCharacteristicSemilinearCoefficient_succ
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) (n : ℕ) :
    chosenEqualCharacteristicSemilinearCoefficient u hu (n + 1) ^ Nat.card k =
      algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u) *
          chosenEqualCharacteristicSemilinearCoefficient u hu (n + 1) +
        ∑ j : Fin (n + 1),
          algebraMap k (AlgebraicClosure k)
              (PowerSeries.coeff (j + 1) u) *
            chosenEqualCharacteristicSemilinearCoefficient u hu (n - j) := by
  rw [chosenEqualCharacteristicSemilinearCoefficient]
  exact Classical.choose_spec
    (exists_frobenius_eq_mul_add k
      (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u))
      (∑ j : Fin (n + 1),
        algebraMap k (AlgebraicClosure k)
            (PowerSeries.coeff (j + 1) u) *
          chosenEqualCharacteristicSemilinearCoefficient u hu (n - j)))

/-- The exact power-series solution of the semilinear Hilbert--90 equation
in the completed maximal unramified coefficient ring. -/
noncomputable def equalCharacteristicSemilinearUnit
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) :
    (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.mk (chosenEqualCharacteristicSemilinearCoefficient u hu)

/-- The semilinear unit records the recursively chosen coefficients. -/
@[simp]
theorem equalCharacteristicSemilinearUnit_coeff
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (equalCharacteristicSemilinearUnit u hu) =
      chosenEqualCharacteristicSemilinearCoefficient u hu n := by
  simp [equalCharacteristicSemilinearUnit]

/-- The semilinear unit has nonzero constant coefficient. -/
theorem equalCharacteristicSemilinearUnit_constantCoeff_ne_zero
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) :
    PowerSeries.coeff 0 (equalCharacteristicSemilinearUnit u hu) ≠ 0 := by
  rw [equalCharacteristicSemilinearUnit_coeff,
    chosenEqualCharacteristicSemilinearCoefficient_zero]
  exact chosenEqualCharacteristicSemilinearLeadingCoefficient_ne_zero u hu

/-- The completed theta-intertwining theorem, linear theta-coefficient equation:
`phi(epsilon) = u * epsilon`. -/
theorem equalCharacteristicPowerSeriesFrobenius_semilinearUnit
    (u : k⟦X⟧) (hu : PowerSeries.coeff 0 u ≠ 0) :
    equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicSemilinearUnit u hu) =
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) u *
        equalCharacteristicSemilinearUnit u hu := by
  apply PowerSeries.ext
  intro n
  rw [equalCharacteristicPowerSeriesFrobenius_coeff,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    equalCharacteristicSemilinearUnit_coeff]
  simp only [PowerSeries.coeff_map,
    equalCharacteristicSemilinearUnit_coeff]
  cases n with
  | zero =>
      rw [chosenEqualCharacteristicSemilinearCoefficient_zero]
      simp only [Finset.sum_range_one, Nat.zero_sub,
        chosenEqualCharacteristicSemilinearCoefficient_zero]
      calc
        chosenEqualCharacteristicSemilinearLeadingCoefficient u ^ Nat.card k =
            chosenEqualCharacteristicSemilinearLeadingCoefficient u ^
                (Nat.card k - 1) *
              chosenEqualCharacteristicSemilinearLeadingCoefficient u := by
          have hq : 1 < Nat.card k := Finite.one_lt_card
          rw [← pow_succ]
          congr 1
          omega
        _ = algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 u) *
              chosenEqualCharacteristicSemilinearLeadingCoefficient u := by
          rw [chosenEqualCharacteristicSemilinearLeadingCoefficient_pow]
  | succ n =>
      rw [chosenEqualCharacteristicSemilinearCoefficient_succ,
        Finset.sum_range_succ']
      simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
      rw [← Fin.sum_univ_eq_sum_range]
      ac_rfl

section ThetaRecursion

variable (u : k⟦X⟧ˣ)

/-- The image in the completed maximal-unramified coefficient ring of the
unit relating the two prime elements. -/
noncomputable def equalCharacteristicCompletedUnit :
    (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧)

/-- We normalize the target prime to `T`; the source prime is therefore
`bar_pi = u^{-1} T`. -/
noncomputable def equalCharacteristicCompletedSourceUniformizer :
    (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k)) ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) *
    PowerSeries.X

/-- The contracting coefficient
`gamma_j = bar_pi^(q^j) / T` in the `j`-th theta recursion. -/
noncomputable def equalCharacteristicThetaGamma (j : ℕ) :
    (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k)) ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) ^
      (Nat.card k ^ j) *
    PowerSeries.X ^ (Nat.card k ^ j - 1)

/-- Positive-index theta gamma terms have zero constant coefficient. -/
theorem equalCharacteristicThetaGamma_constantCoeff
    (j : ℕ) (hj : 0 < j) :
    PowerSeries.coeff 0 (equalCharacteristicThetaGamma u j) = 0 := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpow : 0 < Nat.card k ^ j - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow hj.ne' hq)
  simp [equalCharacteristicThetaGamma, hpow.ne']

/-- Multiplying theta gamma by `X` gives the corresponding source-uniformizer power. -/
theorem equalCharacteristicThetaGamma_mul_X
    (j : ℕ) (hj : 0 < j) :
    PowerSeries.X * equalCharacteristicThetaGamma u j =
      equalCharacteristicCompletedSourceUniformizer u ^ (Nat.card k ^ j) := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpow : 1 ≤ Nat.card k ^ j :=
    (Nat.one_lt_pow hj.ne' hq).le
  rw [equalCharacteristicThetaGamma,
    equalCharacteristicCompletedSourceUniformizer, mul_pow]
  calc
    PowerSeries.X *
          (PowerSeries.map (algebraMap k (AlgebraicClosure k))
              (((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) ^ (Nat.card k ^ j) *
            PowerSeries.X ^ (Nat.card k ^ j - 1)) =
        PowerSeries.map (algebraMap k (AlgebraicClosure k))
              (((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) ^ (Nat.card k ^ j) *
            (PowerSeries.X ^ (Nat.card k ^ j - 1) * PowerSeries.X) := by
      ac_rfl
    _ = PowerSeries.map (algebraMap k (AlgebraicClosure k))
              (((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) ^ (Nat.card k ^ j) *
            PowerSeries.X ^ ((Nat.card k ^ j - 1) + 1) := by
      rw [pow_succ]
    _ = PowerSeries.map (algebraMap k (AlgebraicClosure k))
              (((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) ^ (Nat.card k ^ j) *
            PowerSeries.X ^ (Nat.card k ^ j) := by
      rw [Nat.sub_add_cancel hpow]

/-- The numerator occurring on the right of the `j`-th theta recursion. -/
noncomputable def equalCharacteristicThetaBetaNumerator
    (b : (AlgebraicClosure k)⟦X⟧) :
    (AlgebraicClosure k)⟦X⟧ :=
  equalCharacteristicPowerSeriesFrobenius k b - b ^ Nat.card k

/-- The theta beta numerator has zero constant coefficient. -/
theorem equalCharacteristicThetaBetaNumerator_constantCoeff
    (b : (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.coeff 0 (equalCharacteristicThetaBetaNumerator b) = 0 := by
  rw [equalCharacteristicThetaBetaNumerator, map_sub,
    equalCharacteristicPowerSeriesFrobenius_coeff]
  simp

/-- The quotient
`beta(b) = (phi(b) - b^q) / T`. -/
noncomputable def equalCharacteristicThetaBeta
    (b : (AlgebraicClosure k)⟦X⟧) :
    (AlgebraicClosure k)⟦X⟧ :=
  equalCharacteristicPowerSeriesTail
    (equalCharacteristicThetaBetaNumerator b)

/-- Multiplying theta beta by `X` recovers its numerator. -/
theorem equalCharacteristicThetaBeta_mul_X
    (b : (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.X * equalCharacteristicThetaBeta b =
      equalCharacteristicThetaBetaNumerator b := by
  have hsplit := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C
    (equalCharacteristicThetaBetaNumerator b)
  rw [equalCharacteristicThetaBetaNumerator_constantCoeff] at hsplit
  simp only [map_zero, add_zero] at hsplit
  exact hsplit.symm

/-- The coefficients `b_j` of the additive theta series
`theta(X)=sum_j b_j X^(q^j)`.  The leading coefficient is the exact
semilinear unit constructed above; every later coefficient is the unique
contracting solution supplied by the contracting Frobenius equation. -/
noncomputable def equalCharacteristicThetaCoefficient :
    ℕ → (AlgebraicClosure k)⟦X⟧
  | 0 => equalCharacteristicSemilinearUnit (u : k⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
  | j + 1 =>
      contractingFrobeniusEquationSolution
        (equalCharacteristicCoefficientFrobenius k).toRingHom
        (equalCharacteristicThetaGamma u (j + 1))
        (equalCharacteristicThetaBeta
          (equalCharacteristicThetaCoefficient j))

/-- The zeroth theta coefficient is the semilinear source unit. -/
@[simp]
theorem equalCharacteristicThetaCoefficient_zero :
    equalCharacteristicThetaCoefficient u 0 =
      equalCharacteristicSemilinearUnit (u : k⟦X⟧)
        (by
          intro hzero
          have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
          apply hunit.ne_zero
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero) :=
  rfl

/-- The canonical contracting recursion for the non-leading theta
coefficients. -/
theorem equalCharacteristicThetaCoefficient_succ_equation (j : ℕ) :
    equalCharacteristicThetaCoefficient u (j + 1) -
        equalCharacteristicThetaGamma u (j + 1) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaCoefficient u (j + 1)) =
      equalCharacteristicThetaBeta
        (equalCharacteristicThetaCoefficient u j) := by
  rw [equalCharacteristicThetaCoefficient]
  have hgamma := equalCharacteristicThetaGamma_constantCoeff u
    (j + 1) (Nat.zero_lt_succ j)
  apply (sub_eq_iff_eq_add).2
  simpa [equalCharacteristicPowerSeriesFrobenius] using
    (contractingFrobeniusEquationSolution_spec
      (equalCharacteristicCoefficientFrobenius k).toRingHom
      (equalCharacteristicThetaGamma u (j + 1))
      (equalCharacteristicThetaBeta
        (equalCharacteristicThetaCoefficient u j)) hgamma)

/-- Clearing the factor `T` gives the coefficient comparison in
`theta^phi o e_bar = e_T o theta`. -/
theorem equalCharacteristicThetaCoefficient_succ_comparison (j : ℕ) :
    PowerSeries.X * equalCharacteristicThetaCoefficient u (j + 1) -
        equalCharacteristicCompletedSourceUniformizer u ^
            (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaCoefficient u (j + 1)) =
      equalCharacteristicThetaBetaNumerator
        (equalCharacteristicThetaCoefficient u j) := by
  have hrec := congrArg (fun z : (AlgebraicClosure k)⟦X⟧ ↦
      PowerSeries.X * z)
    (equalCharacteristicThetaCoefficient_succ_equation u j)
  change PowerSeries.X *
      (equalCharacteristicThetaCoefficient u (j + 1) -
        equalCharacteristicThetaGamma u (j + 1) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaCoefficient u (j + 1))) =
      PowerSeries.X * equalCharacteristicThetaBeta
        (equalCharacteristicThetaCoefficient u j) at hrec
  rw [mul_sub, ← mul_assoc,
    equalCharacteristicThetaGamma_mul_X u (j + 1) (Nat.zero_lt_succ j),
    equalCharacteristicThetaBeta_mul_X] at hrec
  exact hrec

end ThetaRecursion

end EqualCharacteristic
end LubinTate

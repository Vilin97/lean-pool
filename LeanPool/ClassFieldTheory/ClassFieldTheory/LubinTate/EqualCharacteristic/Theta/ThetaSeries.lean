/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
public import Mathlib.RingTheory.PowerSeries.Expand
/-!
# LubinTate the equal-characteristic theta construction: the equal-characteristic theta series

The coefficient recursion of the contracting Frobenius equation produces a sequence `b_j` in the
completed maximal-unramified integer ring.  The series used in the completed theta-intertwining
  theorem is the
genuine sparse power series

`theta(Y) = sum_j b_j Y^(q^j)`.

This file packages that outer series as an actual `PowerSeries`; no
convergence or evaluation hypothesis is inserted into its definition.
-/

@[expose] public section

noncomputable
section

open scoped PowerSeries


universe u v w

namespace LubinTate
namespace EqualCharacteristic

/-- Classical decidability for propositions used in the equal-characteristic theta series. -/
local instance thetaSeriesPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (k : Type u) [Field k] [Finite k]

/-- The predicate saying that a degree is one of the additive exponents
`q^j`, where `q = #k`. -/
def IsEqualCharacteristicAdditiveExponent (n : ℕ) : Prop :=
  ∃ j : ℕ, Nat.card k ^ j = n

/-- The unique index of an additive exponent.  It is only used under a proof
that the degree really has the required form. -/
noncomputable def equalCharacteristicAdditiveExponentIndex
    (n : ℕ) (hn : IsEqualCharacteristicAdditiveExponent k n) : ℕ :=
  Nat.find hn

omit [Field k] [Finite k] in
/-- The chosen additive exponent index realizes `n` as a power of `q`. -/
theorem equalCharacteristicAdditiveExponentIndex_spec
    (n : ℕ) (hn : IsEqualCharacteristicAdditiveExponent k n) :
    Nat.card k ^ equalCharacteristicAdditiveExponentIndex k n hn = n :=
  Nat.find_spec hn

omit [Field k] [Finite k] in
/-- The selected additive-exponent index is no larger than any index
realizing the same exponent. -/
theorem equalCharacteristicAdditiveExponentIndex_min
    (n : ℕ) (hn : IsEqualCharacteristicAdditiveExponent k n)
    (j : ℕ) (hj : Nat.card k ^ j = n) :
    equalCharacteristicAdditiveExponentIndex k n hn ≤ j :=
  Nat.find_min' hn hj

/-- The selected additive-exponent index equals every index representing
the same power.  In particular it is independent of the existence proof
used to define it. -/
theorem equalCharacteristicAdditiveExponentIndex_eq_of_pow_eq
    (n : ℕ) (hn : IsEqualCharacteristicAdditiveExponent k n)
    (j : ℕ) (hj : Nat.card k ^ j = n) :
    equalCharacteristicAdditiveExponentIndex k n hn = j := by
  apply Nat.pow_right_injective
      (Finite.one_lt_card : 2 ≤ Nat.card k)
  exact (equalCharacteristicAdditiveExponentIndex_spec k n hn).trans hj.symm

/-- The chosen index of `q ^ j` is `j`. -/
theorem equalCharacteristicAdditiveExponentIndex_pow (j : ℕ) :
    equalCharacteristicAdditiveExponentIndex k (Nat.card k ^ j) ⟨j, rfl⟩ = j := by
  exact equalCharacteristicAdditiveExponentIndex_eq_of_pow_eq
    k (Nat.card k ^ j) ⟨j, rfl⟩ j rfl

/-- Powers of the cardinality of a nontrivial finite field have unique
exponents. -/
theorem natCard_pow_injective : Function.Injective (Nat.card k ^ ·) :=
  Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card k)

/-- A power of the nontrivial finite-field cardinality is one only at exponent zero. -/
theorem natCard_pow_eq_one_iff (j : ℕ) : Nat.card k ^ j = 1 ↔ j = 0 := by
  rw [← pow_zero (Nat.card k)]
  exact (natCard_pow_injective k).eq_iff

variable {R : Type v} [CommRing R]

/-- The `q`-additive sparse power series attached to a coefficient sequence
`b`: its coefficient at `q^j` is `b_j`, and every other coefficient is zero.
-/
noncomputable def equalCharacteristicQAdditiveSeries (b : ℕ → R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦
    if hn : IsEqualCharacteristicAdditiveExponent k n then
      b (equalCharacteristicAdditiveExponentIndex k n hn)
    else 0

omit [Field k] [Finite k] in
/-- The `n`th coefficient of a `q`-additive series is selected by its power index. -/
theorem equalCharacteristicQAdditiveSeries_coeff
    (b : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (equalCharacteristicQAdditiveSeries k b) =
      if hn : IsEqualCharacteristicAdditiveExponent k n then
        b (equalCharacteristicAdditiveExponentIndex k n hn)
      else 0 := by
  simp [equalCharacteristicQAdditiveSeries]

/-- The coefficient at exponent `q ^ j` is the prescribed coefficient `b j`. -/
@[simp]
theorem equalCharacteristicQAdditiveSeries_coeff_pow
    (b : ℕ → R) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicQAdditiveSeries k b) = b j := by
  rw [equalCharacteristicQAdditiveSeries_coeff]
  split_ifs with h
  · rw [equalCharacteristicAdditiveExponentIndex_pow]
  · exact (h ⟨j, rfl⟩).elim

omit [Field k] [Finite k] in
/-- Coefficients away from powers of `q` vanish in a `q`-additive series. -/
theorem equalCharacteristicQAdditiveSeries_coeff_eq_zero
    (b : ℕ → R) (n : ℕ)
    (hn : ¬ IsEqualCharacteristicAdditiveExponent k n) :
    PowerSeries.coeff n (equalCharacteristicQAdditiveSeries k b) = 0 := by
  rw [equalCharacteristicQAdditiveSeries_coeff]
  simp [hn]

/-- Every `q`-additive series has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicQAdditiveSeries_constantCoeff
    (b : ℕ → R) :
    PowerSeries.constantCoeff (equalCharacteristicQAdditiveSeries k b) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  apply equalCharacteristicQAdditiveSeries_coeff_eq_zero
  rintro ⟨j, hj⟩
  have hpositive : 0 < Nat.card k ^ j := pow_pos Nat.card_pos j
  omega

/-- The linear coefficient of a `q`-additive series is its zeroth parameter. -/
@[simp]
theorem equalCharacteristicQAdditiveSeries_coeff_one
    (b : ℕ → R) :
    PowerSeries.coeff 1 (equalCharacteristicQAdditiveSeries k b) = b 0 := by
  simpa using equalCharacteristicQAdditiveSeries_coeff_pow k b 0

variable {S : Type w} [CommRing S]

omit [Field k] [Finite k] in
/-- Mapping the coefficient ring maps a `q`-additive series coefficientwise.
-/
theorem equalCharacteristicQAdditiveSeries_map
    (f : R →+* S) (b : ℕ → R) :
    PowerSeries.map f (equalCharacteristicQAdditiveSeries k b) =
      equalCharacteristicQAdditiveSeries k (fun j ↦ f (b j)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map,
    equalCharacteristicQAdditiveSeries_coeff,
    equalCharacteristicQAdditiveSeries_coeff]
  split_ifs <;> simp

omit [Field k] [Finite k] in
/-- Multiplication by a constant acts coefficientwise on a `q`-additive
series. -/
theorem equalCharacteristicQAdditiveSeries_C_mul
    (a : R) (b : ℕ → R) :
    PowerSeries.C a * equalCharacteristicQAdditiveSeries k b =
      equalCharacteristicQAdditiveSeries k (fun j ↦ a * b j) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_C_mul,
    equalCharacteristicQAdditiveSeries_coeff,
    equalCharacteristicQAdditiveSeries_coeff]
  split_ifs <;> simp

omit [Field k] [Finite k] in
/-- Addition of `q`-additive series is coefficientwise. -/
theorem equalCharacteristicQAdditiveSeries_add
    (a b : ℕ → R) :
    equalCharacteristicQAdditiveSeries k a +
        equalCharacteristicQAdditiveSeries k b =
      equalCharacteristicQAdditiveSeries k (fun j ↦ a j + b j) := by
  apply PowerSeries.ext
  intro n
  rw [map_add, equalCharacteristicQAdditiveSeries_coeff,
    equalCharacteristicQAdditiveSeries_coeff,
    equalCharacteristicQAdditiveSeries_coeff]
  split_ifs <;> simp

section FrobeniusPowers

variable {A : Type w} [CommRing A] [Algebra k A]

/-- In every algebra over the finite field `k`, raising to a `q^j`-th power
is additive.  This is the characteristic-`p` calculation used when composing
additive power series. -/
theorem add_pow_natCard_pow (a b : A) (j : ℕ) :
    (a + b) ^ (Nat.card k ^ j) =
      a ^ (Nat.card k ^ j) + b ^ (Nat.card k ^ j) := by
  let : Fintype k := Fintype.ofFinite k
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
      simpa only [FiniteField.coe_frobeniusAlgHom,
        Nat.card_eq_fintype_card] using
        map_add (FiniteField.frobeniusAlgHom k A)
          (a ^ Nat.card k ^ j) (b ^ Nat.card k ^ j)

/-- The `q`-power Frobenius on an algebra over the finite field `k`.  Unlike
the completed-unramified Frobenius used above, this raises the whole algebra
element to its `q`-th power. -/
noncomputable def equalCharacteristicCardFrobenius
    {B : Type w} [CommRing B] [Algebra k B] : B →+* B := by
  letI : Fintype k := Fintype.ofFinite k
  exact (FiniteField.frobeniusAlgHom k B).toRingHom

/-- Cardinal Frobenius raises an element to the finite-field cardinality. -/
theorem equalCharacteristicCardFrobenius_apply
    {B : Type w} [CommRing B] [Algebra k B] (x : B) :
    equalCharacteristicCardFrobenius k x = x ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  simp [equalCharacteristicCardFrobenius, Nat.card_eq_fintype_card]

/-- Frobenius on a power-series algebra is coefficient Frobenius followed by
the exponent expansion `Y ↦ Y^q`. -/
theorem powerSeries_pow_natCard_eq_expand_map_cardFrobenius
    {B : Type w} [CommRing B] [Nontrivial B] [Algebra k B]
    (f : B⟦X⟧) :
    f ^ Nat.card k =
      PowerSeries.expand (Nat.card k) Nat.card_pos.ne'
        (PowerSeries.map (equalCharacteristicCardFrobenius k) f) := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hpchar, n, hp, hcard⟩ := FiniteField.card' k
  let : CharP k p := hpchar
  let : ExpChar k p := ExpChar.prime hp
  let : ExpChar B p :=
    expChar_of_injective_algebraMap (algebraMap k B).injective p
  have hiter :
      iterateFrobenius B p (n : ℕ) =
        equalCharacteristicCardFrobenius k := by
    ext x
    rw [equalCharacteristicCardFrobenius_apply]
    rw [Nat.card_eq_fintype_card, hcard]
    rw [show (iterateFrobenius B p (n : ℕ)) x = x ^ p ^ (n : ℕ) by
      rw [congrFun (coe_iterateFrobenius B p (n : ℕ)) x]
      rw [show (⇑(frobenius B p) : B → B) = fun y ↦ y ^ p by
        funext y
        exact frobenius_def p y]
      exact congrFun (pow_iterate p (n : ℕ)) x]
  have hmain := MvPowerSeries.map_iterateFrobenius_expand
    (R := B) p hp.ne_zero (f : MvPowerSeries Unit B) (n : ℕ)
  rw [hiter] at hmain
  change
    PowerSeries.map (equalCharacteristicCardFrobenius k)
        (PowerSeries.expand (p ^ (n : ℕ))
          (pow_ne_zero (n : ℕ) hp.ne_zero) f) =
      f ^ p ^ (n : ℕ) at hmain
  have hcardNat : Nat.card k = p ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hmain' :
      PowerSeries.map (equalCharacteristicCardFrobenius k)
          (PowerSeries.expand (Nat.card k) Nat.card_pos.ne' f) =
        f ^ Nat.card k := by
    simpa only [hcardNat] using hmain
  rw [← hmain']
  exact PowerSeries.map_expand (Nat.card k) Nat.card_pos.ne'
    (equalCharacteristicCardFrobenius k) f

end FrobeniusPowers

/-- Shift of a coefficient sequence induced by `Y ↦ Y^q`. -/
def equalCharacteristicQAdditiveShift (b : ℕ → R) : ℕ → R
  | 0 => 0
  | j + 1 => b j

/-- Expanding exponents by `q` shifts a `q`-additive coefficient sequence by
one place. -/
theorem equalCharacteristicQAdditiveSeries_expand
    (b : ℕ → R) :
    PowerSeries.expand (Nat.card k) Nat.card_pos.ne'
        (equalCharacteristicQAdditiveSeries k b) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicQAdditiveShift b) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : IsEqualCharacteristicAdditiveExponent k n
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
        rw [pow_zero, PowerSeries.coeff_expand,
          equalCharacteristicQAdditiveSeries_coeff_one]
        have hnot : ¬ Nat.card k ∣ 1 := by
          intro h
          have hq : Nat.card k = 1 := Nat.eq_one_of_dvd_one h
          exact (Finite.one_lt_card : 1 < Nat.card k).ne hq.symm
        simp [hnot, equalCharacteristicQAdditiveShift]
    | succ j =>
        rw [equalCharacteristicQAdditiveSeries_coeff_pow]
        change PowerSeries.coeff (Nat.card k ^ (j + 1))
            (PowerSeries.expand (Nat.card k) Nat.card_pos.ne'
              (equalCharacteristicQAdditiveSeries k b)) = b j
        calc
          _ = PowerSeries.coeff (Nat.card k * Nat.card k ^ j)
                (PowerSeries.expand (Nat.card k) Nat.card_pos.ne'
                  (equalCharacteristicQAdditiveSeries k b)) := by
              congr 2
              rw [pow_succ, Nat.mul_comm]
          _ = PowerSeries.coeff (Nat.card k ^ j)
                (equalCharacteristicQAdditiveSeries k b) :=
              PowerSeries.coeff_expand_mul (Nat.card k) Nat.card_pos.ne'
                (equalCharacteristicQAdditiveSeries k b) (Nat.card k ^ j)
          _ = b j := equalCharacteristicQAdditiveSeries_coeff_pow k b j
  · rw [PowerSeries.coeff_expand,
      equalCharacteristicQAdditiveSeries_coeff_eq_zero k _ n hn]
    split_ifs with hdvd
    · obtain ⟨m, hm⟩ := hdvd
      have hmexp : ¬ IsEqualCharacteristicAdditiveExponent k m := by
        rintro ⟨j, hj⟩
        apply hn
        refine ⟨j + 1, ?_⟩
        calc
          Nat.card k ^ (j + 1) = Nat.card k * Nat.card k ^ j := by
            rw [pow_succ, Nat.mul_comm]
          _ = Nat.card k * m := by rw [hj]
          _ = n := hm.symm
      have hdiv : n / Nat.card k = m := by
        rw [hm, Nat.mul_div_cancel_left m Nat.card_pos]
      rw [hdiv,
        equalCharacteristicQAdditiveSeries_coeff_eq_zero k b m hmexp]
    · rfl

/-- Taking a `q`-th power shifts the additive series and raises every
coefficient to its `q`-th power. -/
theorem equalCharacteristicQAdditiveSeries_pow_card
    [Nontrivial R] [Algebra k R] (b : ℕ → R) :
    equalCharacteristicQAdditiveSeries k b ^ Nat.card k =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicQAdditiveShift
          (fun j ↦ b j ^ Nat.card k)) := by
  rw [powerSeries_pow_natCard_eq_expand_map_cardFrobenius k,
    equalCharacteristicQAdditiveSeries_map,
    equalCharacteristicQAdditiveSeries_expand]
  congr 2
  funext j
  exact equalCharacteristicCardFrobenius_apply k (b j)

variable {k}

/-- The actual outer theta series from the completed theta-intertwining theorem. -/
noncomputable def equalCharacteristicThetaSeries
    (u : k⟦X⟧ˣ) : ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  equalCharacteristicQAdditiveSeries k
    (equalCharacteristicThetaCoefficient u)

/-- The theta series coefficient at `q ^ j` is the `j`th theta coefficient. -/
@[simp]
theorem equalCharacteristicThetaSeries_coeff_pow
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicThetaSeries u) =
      equalCharacteristicThetaCoefficient u j := by
  exact equalCharacteristicQAdditiveSeries_coeff_pow k
    (equalCharacteristicThetaCoefficient u) j

/-- The equal-characteristic theta series has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicThetaSeries_constantCoeff
    (u : k⟦X⟧ˣ) :
    PowerSeries.constantCoeff (equalCharacteristicThetaSeries u) = 0 := by
  exact equalCharacteristicQAdditiveSeries_constantCoeff k _

/-- The zero constant coefficient makes theta a valid formal substitution.
-/
theorem equalCharacteristicThetaSeries_hasSubst
    (u : k⟦X⟧ˣ) :
    PowerSeries.HasSubst (equalCharacteristicThetaSeries u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicThetaSeries_constantCoeff u)

/-- Frobenius acts on the completed-unramified coefficients of theta. -/
noncomputable def equalCharacteristicThetaSeriesFrobenius
    (u : k⟦X⟧ˣ) : ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
    (equalCharacteristicThetaSeries u)

/-- Coefficientwise Frobenius of theta is the `q`-additive series of Frobenius coefficients. -/
theorem equalCharacteristicThetaSeriesFrobenius_eq_qAdditiveSeries
    (u : k⟦X⟧ˣ) :
    equalCharacteristicThetaSeriesFrobenius u =
      equalCharacteristicQAdditiveSeries k
        (fun j ↦ equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicThetaCoefficient u j)) := by
  exact equalCharacteristicQAdditiveSeries_map k
    (equalCharacteristicPowerSeriesFrobenius k)
    (equalCharacteristicThetaCoefficient u)

/-- The Frobenius theta coefficient at `q ^ j` is Frobenius of the `j`th coefficient. -/
@[simp]
theorem equalCharacteristicThetaSeriesFrobenius_coeff_pow
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicThetaSeriesFrobenius u) =
      equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicThetaCoefficient u j) := by
  rw [equalCharacteristicThetaSeriesFrobenius_eq_qAdditiveSeries,
    equalCharacteristicQAdditiveSeries_coeff_pow]

/-- The additive Lubin--Tate series `Y^q + pi Y`, now with coefficients in
the completed maximal-unramified integer ring. -/
noncomputable def equalCharacteristicCompletedLubinTateSeries
    (pi : (AlgebraicClosure k)⟦X⟧) :
    ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  PowerSeries.X ^ Nat.card k + PowerSeries.C pi * PowerSeries.X

/-- The completed Lubin–Tate series has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicCompletedLubinTateSeries_constantCoeff
    (pi : (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.constantCoeff
        (equalCharacteristicCompletedLubinTateSeries (k := k) pi) = 0 := by
  have hq : Nat.card k ≠ 0 := Nat.card_pos.ne'
  simp [equalCharacteristicCompletedLubinTateSeries, hq]

/-- A Lubin--Tate series has zero constant coefficient and can therefore be
substituted into theta. -/
theorem equalCharacteristicCompletedLubinTateSeries_hasSubst
    (pi : (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.HasSubst
      (equalCharacteristicCompletedLubinTateSeries (k := k) pi) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicCompletedLubinTateSeries_constantCoeff pi)

/-- A `q^j`-th power of `Y^q + pi Y` has exactly the two expected additive
monomials. -/
theorem equalCharacteristicCompletedLubinTateSeries_pow_card_pow
    (pi : (AlgebraicClosure k)⟦X⟧) (j : ℕ) :
    equalCharacteristicCompletedLubinTateSeries (k := k) pi ^
        (Nat.card k ^ j) =
      PowerSeries.X ^ (Nat.card k ^ (j + 1)) +
        PowerSeries.C (pi ^ (Nat.card k ^ j)) *
          PowerSeries.X ^ (Nat.card k ^ j) := by
  rw [equalCharacteristicCompletedLubinTateSeries,
    add_pow_natCard_pow k, mul_pow, map_pow]
  congr 1
  rw [← pow_mul, pow_succ, Nat.mul_comm]

/-- Coefficient form of the preceding two-monomial calculation. -/
theorem equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff
    (pi : (AlgebraicClosure k)⟦X⟧) (j n : ℕ) :
    PowerSeries.coeff n
        (equalCharacteristicCompletedLubinTateSeries (k := k) pi ^
          (Nat.card k ^ j)) =
      (if n = Nat.card k ^ (j + 1) then 1 else 0) +
        (if n = Nat.card k ^ j then pi ^ (Nat.card k ^ j) else 0) := by
  rw [equalCharacteristicCompletedLubinTateSeries_pow_card_pow]
  simp only [map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul]
  split_ifs <;> simp_all

/-- Coefficients obtained by substituting `Y^q + pi Y` into a `q`-additive
series. -/
def equalCharacteristicLubinTateSubstitutionCoefficient
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧) :
    ℕ → (AlgebraicClosure k)⟦X⟧
  | 0 => b 0 * pi
  | j + 1 => b j + b (j + 1) * pi ^ (Nat.card k ^ (j + 1))

/-- Substitution into an additive series cannot create a non-additive
exponent. -/
theorem equalCharacteristicQAdditiveSeries_subst_coeff_eq_zero
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧)
    (n : ℕ) (hn : ¬ IsEqualCharacteristicAdditiveExponent k n) :
    PowerSeries.coeff n
        (PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k) pi)
          (equalCharacteristicQAdditiveSeries k b)) = 0 := by
  rw [PowerSeries.coeff_subst'
    (equalCharacteristicCompletedLubinTateSeries_hasSubst pi)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : IsEqualCharacteristicAdditiveExponent k d
  · obtain ⟨j, rfl⟩ := hd
    rw [equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff]
    have hnSucc : n ≠ Nat.card k ^ (j + 1) := by
      intro h
      exact hn ⟨j + 1, h.symm⟩
    have hnSelf : n ≠ Nat.card k ^ j := by
      intro h
      exact hn ⟨j, h.symm⟩
    simp [hnSucc, hnSelf]
  · rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hd]
    simp

/-- The linear coefficient after substitution is `b_0 pi`. -/
theorem equalCharacteristicQAdditiveSeries_subst_coeff_one
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.coeff 1
        (PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k) pi)
          (equalCharacteristicQAdditiveSeries k b)) = b 0 * pi := by
  rw [PowerSeries.coeff_subst'
    (equalCharacteristicCompletedLubinTateSeries_hasSubst pi),
    finsum_eq_single _ 1]
  · rw [equalCharacteristicQAdditiveSeries_coeff_one]
    have hpow : (1 : ℕ) = Nat.card k ^ 0 := by simp
    conv_lhs =>
      rhs
      rw [hpow,
        equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff]
    have hq : (1 : ℕ) ≠ Nat.card k :=
      ne_of_lt (Finite.one_lt_card : 1 < Nat.card k)
    simp [hq]
  · intro d hd
    by_cases hde : IsEqualCharacteristicAdditiveExponent k d
    · obtain ⟨j, rfl⟩ := hde
      rw [equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff]
      have hj : j ≠ 0 := by
        intro hj
        subst j
        simp at hd
      have hSelf : (1 : ℕ) ≠ Nat.card k ^ j := by
        intro h
        exact hj ((natCard_pow_eq_one_iff k j).1 h.symm)
      have hSucc : (1 : ℕ) ≠ Nat.card k ^ (j + 1) := by
        intro h
        have : j + 1 = 0 :=
          (natCard_pow_eq_one_iff k (j + 1)).1 h.symm
        omega
      simp [hSelf, hSucc]
    · rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hde]
      simp

/-- At the next additive exponent, substitution receives one contribution
from the preceding `q`-power term and one from the linear term. -/
theorem equalCharacteristicQAdditiveSeries_subst_coeff_pow_succ
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧) (r : ℕ) :
    PowerSeries.coeff (Nat.card k ^ (r + 1))
        (PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k) pi)
          (equalCharacteristicQAdditiveSeries k b)) =
      b r + b (r + 1) * pi ^ (Nat.card k ^ (r + 1)) := by
  rw [PowerSeries.coeff_subst'
    (equalCharacteristicCompletedLubinTateSeries_hasSubst pi)]
  let F : ℕ → (AlgebraicClosure k)⟦X⟧ := fun d ↦
    PowerSeries.coeff d (equalCharacteristicQAdditiveSeries k b) •
      PowerSeries.coeff (Nat.card k ^ (r + 1))
        (equalCharacteristicCompletedLubinTateSeries (k := k) pi ^ d)
  change ∑ᶠ d : ℕ, F d = _
  have hsupport : Function.support F ⊆
      (({Nat.card k ^ r, Nat.card k ^ (r + 1)} : Finset ℕ) : Set ℕ) := by
    intro d hd
    change F d ≠ 0 at hd
    by_cases hde : IsEqualCharacteristicAdditiveExponent k d
    · obtain ⟨j, rfl⟩ := hde
      dsimp only [F] at hd
      rw [equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff] at hd
      by_cases hHigh : Nat.card k ^ (r + 1) = Nat.card k ^ (j + 1)
      · have hrj : r = j := by
          have := natCard_pow_injective k hHigh
          omega
        simp [hrj]
      · by_cases hLow : Nat.card k ^ (r + 1) = Nat.card k ^ j
        · have hj : j = r + 1 :=
            (natCard_pow_injective k hLow).symm
          simp [hj]
        · simp [hHigh, hLow] at hd
    · dsimp only [F] at hd
      rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hde] at hd
      simp at hd
  rw [finsum_eq_sum_of_support_subset F hsupport]
  have hne : Nat.card k ^ r ≠ Nat.card k ^ (r + 1) := by
    intro h
    have := natCard_pow_injective k h
    omega
  rw [Finset.sum_pair hne]
  dsimp only [F]
  rw [equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff,
    equalCharacteristicCompletedLubinTateSeries_pow_card_pow_coeff]
  have hSelf : Nat.card k ^ (r + 1) ≠ Nat.card k ^ r := hne.symm
  have hNext : Nat.card k ^ (r + 1) ≠ Nat.card k ^ (r + 1 + 1) := by
    intro h
    have := natCard_pow_injective k h
    omega
  simp [hSelf, hNext]

/-- Formal substitution formula for a `q`-additive series. -/
theorem equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k) pi)
        (equalCharacteristicQAdditiveSeries k b) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicLubinTateSubstitutionCoefficient pi b) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : IsEqualCharacteristicAdditiveExponent k n
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
        rw [pow_zero,
          equalCharacteristicQAdditiveSeries_subst_coeff_one,
          equalCharacteristicQAdditiveSeries_coeff_one]
        rfl
    | succ j =>
        rw [equalCharacteristicQAdditiveSeries_subst_coeff_pow_succ,
          equalCharacteristicQAdditiveSeries_coeff_pow]
        rfl
  · rw [equalCharacteristicQAdditiveSeries_subst_coeff_eq_zero pi b n hn,
      equalCharacteristicQAdditiveSeries_coeff_eq_zero k _ n hn]

/-- Coefficients obtained by applying `Y^q + pi Y` after a `q`-additive
series. -/
def equalCharacteristicLubinTatePostcompositionCoefficient
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧) :
    ℕ → (AlgebraicClosure k)⟦X⟧
  | 0 => pi * b 0
  | j + 1 => b j ^ Nat.card k + pi * b (j + 1)

/-- Formal postcomposition formula
`(Y^q + pi Y) ∘ (Σ b_j Y^(q^j))`. -/
theorem equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries
    (pi : (AlgebraicClosure k)⟦X⟧)
    (b : ℕ → (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.subst (equalCharacteristicQAdditiveSeries k b)
        (equalCharacteristicCompletedLubinTateSeries (k := k) pi) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicLubinTatePostcompositionCoefficient pi b) := by
  have hsubst : PowerSeries.HasSubst
      (equalCharacteristicQAdditiveSeries k b) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (equalCharacteristicQAdditiveSeries_constantCoeff k b)
  rw [equalCharacteristicCompletedLubinTateSeries,
    ← PowerSeries.smul_eq_C_mul]
  rw [PowerSeries.subst_add hsubst,
    PowerSeries.subst_pow hsubst,
    PowerSeries.subst_smul hsubst,
    PowerSeries.subst_X hsubst,
    equalCharacteristicQAdditiveSeries_pow_card k,
    PowerSeries.smul_eq_C_mul,
    equalCharacteristicQAdditiveSeries_C_mul,
    equalCharacteristicQAdditiveSeries_add]
  congr 2
  funext j
  cases j <;>
    simp [equalCharacteristicQAdditiveShift,
      equalCharacteristicLubinTatePostcompositionCoefficient]

/-- The completed theta-intertwining theorem, the second theta identity
`theta^phi o e_bar_pi = e_T o theta`.

Both sides are genuine formal substitutions.  At the linear coefficient the
claim is the semilinear unit equation `phi(b_0) = u b_0`; at every higher
`q`-power coefficient it is exactly the contracting recursion defining
`b_(j+1)`. -/
theorem equalCharacteristicThetaSeries_intertwines
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicCompletedSourceUniformizer u))
        (equalCharacteristicThetaSeriesFrobenius u) =
      PowerSeries.subst (equalCharacteristicThetaSeries u)
        (equalCharacteristicCompletedLubinTateSeries (k := k) PowerSeries.X) := by
  rw [equalCharacteristicThetaSeriesFrobenius_eq_qAdditiveSeries,
    equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries,
    equalCharacteristicThetaSeries,
    equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries]
  congr 1
  funext j
  cases j with
  | zero =>
      rw [equalCharacteristicLubinTateSubstitutionCoefficient,
        equalCharacteristicLubinTatePostcompositionCoefficient,
        equalCharacteristicThetaCoefficient_zero,
        equalCharacteristicPowerSeriesFrobenius_semilinearUnit,
        equalCharacteristicCompletedSourceUniformizer]
      have huinv :
          PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
              PowerSeries.map (algebraMap k (AlgebraicClosure k))
                ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) = 1 := by
        rw [← map_mul]
        simp
      calc
        _ = (PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) *
              PowerSeries.map (algebraMap k (AlgebraicClosure k))
                ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)) *
              (equalCharacteristicSemilinearUnit (u : k⟦X⟧) _ * PowerSeries.X) := by
            ring
        _ = _ := by rw [huinv]; simp [mul_comm]
  | succ j =>
      rw [equalCharacteristicLubinTateSubstitutionCoefficient,
        equalCharacteristicLubinTatePostcompositionCoefficient]
      have h := equalCharacteristicThetaCoefficient_succ_comparison u j
      rw [equalCharacteristicThetaBetaNumerator] at h
      linear_combination -h

/-- The linear coefficient of theta is the semilinear unit constructed from
`phi(epsilon) = u * epsilon`. -/
theorem equalCharacteristicThetaSeries_coeff_one
    (u : k⟦X⟧ˣ) :
    PowerSeries.coeff 1 (equalCharacteristicThetaSeries u) =
      equalCharacteristicSemilinearUnit (u : k⟦X⟧)
        (by
          intro hzero
          have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
          apply hunit.ne_zero
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero) := by
  calc
    PowerSeries.coeff 1 (equalCharacteristicThetaSeries u) =
        equalCharacteristicThetaCoefficient u 0 := by
      simpa only [pow_zero] using equalCharacteristicThetaSeries_coeff_pow u 0
    _ = _ := equalCharacteristicThetaCoefficient_zero u

end EqualCharacteristic
end LubinTate

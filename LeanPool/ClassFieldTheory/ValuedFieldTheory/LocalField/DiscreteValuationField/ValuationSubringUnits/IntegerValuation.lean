/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.Arithmetic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
public import Mathlib.Data.Int.WithZero
/-!
# Integer valuations induced by `ℤᵐ⁰`-valued valuations

This file constructs the sign-normalized integer valuation on field units and
proves the elementary formulas for powers and natural-number denominators.
-/

@[expose] public section

noncomputable
section

universe u

open WithZero
open scoped NNReal WithZero

namespace LocalFieldTheory.DiscreteValuationField

namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The integer-valued multiplicative valuation attached to a
`ℤᵐ⁰`-valued field valuation.  The sign convention is normalized so that a
uniformizer of value `exp (-1)` has integer value `1`. -/
noncomputable def ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    MultiplicativeIntegerValuation Kˣ where
  val x := -WithZero.log (v (x : K))
  map_one := by
    simp
  map_mul x y := by
    have hx : v (x : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
    have hy : v (y : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 y.ne_zero
    change
      -WithZero.log (v ((x : K) * (y : K))) =
        -WithZero.log (v (x : K)) + -WithZero.log (v (y : K))
    rw [v.map_mul, WithZero.log_mul hx hy]
    ring

/-- Establishes the identity `(ofWithZeroValuation v).val x = -WithZero.log (v (x : K))`. -/
@[simp] theorem ofWithZeroValuation_val
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) :
    (ofWithZeroValuation v).val x = -WithZero.log (v (x : K)) :=
  rfl

/--
`ofWithZeroValuation_val_eq_of_valuation_eq_exp` satisfies the negation formula
`(ofWithZeroValuation v).val x = n`.
-/
theorem ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) {n : ℤ}
    (hx : v (x : K) = WithZero.exp (-n)) :
    (ofWithZeroValuation v).val x = n := by
  rw [ofWithZeroValuation_val, hx, WithZero.log_exp]
  ring

/-- In the normalized `ℤᵐ⁰` convention, a valuation-one unit times the `n`-th
power of an element of value `exp (-1)` has integer value `n`. -/
theorem ofWithZeroValuation_val_unit_mul_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (u π : Kˣ) (n : ℕ)
    (hu : v (u : K) = 1)
    (hπ : v (π : K) = WithZero.exp (-1 : ℤ)) :
    (ofWithZeroValuation v).val (u * π ^ n) = n := by
  refine
    ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
      v (u * π ^ n) ?_
  simp [map_pow, hu, hπ, ← WithZero.exp_nsmul]

/-- The special case of
`ofWithZeroValuation_val_unit_mul_pow` with the valuation-one unit equal to
one. -/
theorem ofWithZeroValuation_val_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (π : Kˣ) (n : ℕ)
    (hπ : v (π : K) = WithZero.exp (-1 : ℤ)) :
    (ofWithZeroValuation v).val (π ^ n) = n := by
  simpa using
    ofWithZeroValuation_val_unit_mul_pow
      v 1 π n (by simp) hπ

/-- Natural-number denominator form of the attached integer valuation.

This is the denominator input for the logarithm-series term
`x^n / n` in the field-unit logarithm theorem. -/
theorem ofWithZeroValuation_val_natCast
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ))) :
    (ofWithZeroValuation v).val (Units.mk0 (n : K) hnK) =
      (padicValNat p n : ℤ) :=
  ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    v (Units.mk0 (n : K) hnK) (by simpa using hnval)

/-- Natural-number denominator form with a ramification-index scale in the
integer valuation.  This is the denominator input for finite extensions where
the normalized field valuation satisfies `v(n) = e * v_p(n)`. -/
theorem ofWithZeroValuation_val_natCast_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (hnK : (n : K) ≠ 0)
    (hnval :
      v (n : K) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n : ℤ)))) :
    (ofWithZeroValuation v).val (Units.mk0 (n : K) hnK) =
      (e : ℤ) * (padicValNat p n : ℤ) :=
  ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    v (Units.mk0 (n : K) hnK)
    (n := (e : ℤ) * (padicValNat p n : ℤ)) (by simpa using hnval)

/-- Valuation of the logarithm-series term `x^n / n`, assuming the natural
number denominator has the expected `p`-adic value. -/
theorem ofWithZeroValuation_val_pow_div_natCast
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (x : Kˣ) (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ))) :
    (ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (padicValNat p n : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast v hnK hnval]

/-- Valuation of the logarithm-series term `x^n / n`, with a fixed
ramification-index scale in the denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (x : Kˣ) (hnK : (n : K) ≠ 0)
    (hnval :
      v (n : K) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n : ℤ)))) :
    (ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (e : ℤ) * (padicValNat p n : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast_scaled v e hnK hnval]

/-- Valuation of the exponential-series term `x^n / n!`, assuming the
factorial denominator has the expected `p`-adic value. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ))) :
    (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (padicValNat p n.factorial : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast v hnK hnval]

/-- Valuation of the exponential-series term `x^n / n!`, with a fixed
ramification-index scale in the factorial denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ)))) :
    (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (e : ℤ) * (padicValNat p n.factorial : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast_scaled
      (v := v) (p := p) (n := n.factorial) e hnK hnval]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

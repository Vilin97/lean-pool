/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms

/-! # Log Exp Additivity -/

@[expose] public section
open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Scaled logarithm additivity for local fields

This file supplies the unconditional summability and regrouping step needed to
evaluate the formal identity
`log ((1 + X) * (1 + Y)) = log (1 + X) + log (1 + Y)` in a complete discretely
valued field whose normalized valuation restricts to `e * v_p` on the natural
numbers.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The scaled field logarithm series, written as evaluation of the positive
coefficients of the formal series `log (1 + X)`. -/
theorem hasSum_powerSeries_log_eval_logOnePlusSeriesField_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff (n + 1) (PowerSeries.log K) *
          x ^ (n + 1))
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  exact hsum.congr_fun fun n =>
    powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
      (K := K) x hnK n

/-- The scaled one-variable formal logarithm evaluation, including its zero
constant coefficient. -/
theorem hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff n (PowerSeries.log K) * x ^ n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let f : ℕ → K := fun n =>
    PowerSeries.coeff n (PowerSeries.log K) * x ^ n
  have htail :
      HasSum (fun n : ℕ => f (n + 1))
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
    simpa only [f] using
      hasSum_powerSeries_log_eval_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnK hnval hvx hcomplete
  have hfull :=
    (hasSum_nat_add_iff
      (f := f)
      (g := logOnePlusSeriesFieldOfWithZeroValuation v x hnK) 1).1 htail
  simpa [f, PowerSeries.coeff_log] using hfull

/-- Scaled evaluation of the left-axis series in the two-variable formal
product formula. -/
theorem hasSum_formalLogOnePlusLeftVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d (formalLogOnePlusLeftVariableLogSubst K) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let term : (Fin 2 →₀ ℕ) → K := fun d =>
    MvPowerSeries.coeff d (formalLogOnePlusLeftVariableLogSubst K) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
  let axis : ℕ → (Fin 2 →₀ ℕ) := fun n => Finsupp.single (0 : Fin 2) n
  have haxis_inj : Function.Injective axis := by
    intro m n h
    have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) h
    simpa [axis] using hcoord
  have haxis :
      HasSum (term ∘ axis)
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
    refine
      (hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnK hnval hvx hcomplete).congr_fun ?_
    intro n
    simp [term, axis, formalLogOnePlusLeftVariableLogSubst_coeff_single,
      mvPowerSeriesMonomialValue]
  have hout : ∀ d, d ∉ Set.range axis → term d = 0 := by
    intro d hd
    have hne : ∀ n : ℕ, d ≠ Finsupp.single (0 : Fin 2) n := by
      intro n h
      exact hd ⟨n, by simpa [axis] using h.symm⟩
    simp [term, formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis K d hne]
  exact (haxis_inj.hasSum_iff (f := term) hout).1 haxis

/-- Scaled evaluation of the right-axis series in the two-variable formal
product formula. -/
theorem hasSum_formalLogOnePlusRightVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d (formalLogOnePlusRightVariableLogSubst K) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let term : (Fin 2 →₀ ℕ) → K := fun d =>
    MvPowerSeries.coeff d (formalLogOnePlusRightVariableLogSubst K) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
  let axis : ℕ → (Fin 2 →₀ ℕ) := fun n => Finsupp.single (1 : Fin 2) n
  have haxis_inj : Function.Injective axis := by
    intro m n h
    have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) h
    simpa [axis] using hcoord
  have haxis :
      HasSum (term ∘ axis)
        (logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
    refine
      (hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e y hnK hnval hvy hcomplete).congr_fun ?_
    intro n
    simp [term, axis, formalLogOnePlusRightVariableLogSubst_coeff_single,
      mvPowerSeriesMonomialValue]
  have hout : ∀ d, d ∉ Set.range axis → term d = 0 := by
    intro d hd
    have hne : ∀ n : ℕ, d ≠ Finsupp.single (1 : Fin 2) n := by
      intro n h
      exact hd ⟨n, by simpa [axis] using h.symm⟩
    simp [term, formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis K d hne]
  exact (haxis_inj.hasSum_iff (f := term) hout).1 haxis

/-- Scaled evaluation of the formal product formula's right-hand side. -/
theorem hasSum_formalLogOnePlusProductRightSide_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d (formalLogOnePlusProductRightSide K) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK +
        logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hleft :=
    hasSum_formalLogOnePlusLeftVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hcomplete
  have hright :=
    hasSum_formalLogOnePlusRightVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvy hcomplete
  refine (hleft.add hright).congr_fun ?_
  intro d
  rw [formalLogOnePlusProductRightSide_coeff]
  ring

/-- Natural-number coefficients have valuation at most one under a scaled
`p`-adic denominator formula. -/
theorem valuation_natCast_le_one_ofWithZeroValuation_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} (e : ℕ)
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (m : ℕ) :
    v (m : K) ≤ 1 := by
  cases m with
  | zero => simp
  | succ n =>
      rw [hnval n]
      calc
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))) ≤
            WithZero.exp (0 : ℤ) :=
          WithZero.exp_le_exp.mpr (by
            apply neg_nonpos.mpr
            exact mul_nonneg (Int.natCast_nonneg e)
              (Int.natCast_nonneg (padicValNat p (n + 1))))
        _ = 1 := WithZero.exp_zero

/-- Evaluation of a two-variable monomial at `(x,y)`. -/
theorem mvPowerSeriesMonomialValue_pair
    (x y : K) (d : Fin 2 →₀ ℕ) :
    mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d =
      x ^ d 0 * y ^ d 1 := by
  rw [mvPowerSeriesMonomialValue, Finsupp.prod_fintype]
  · rw [Fin.prod_univ_two]
    simp
  · intro i
    simp

/-- If the `d`-coefficient of `(X + Y + XY)^q` is nonzero, then its total
degree is at least `q`. -/
theorem formalLogOnePlusProductArgument_pow_coeff_ne_zero_q_le_coord_sum
    (q : ℕ) (d : Fin 2 →₀ ℕ)
    (hcoeff :
      MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) ≠ 0) :
    q ≤ d 0 + d 1 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_card_choices] at hcoeff
  have hcard :
      (formalLogOnePlusProductArgumentBasicFactorChoices q d).card ≠ 0 := by
    intro hzero
    apply hcoeff
    simp [hzero]
  exact
    (formalLogOnePlusProductArgumentBasicFactorChoices_nonempty_q_range
      (Finset.card_ne_zero.mp hcard)).2.2

/-- A monomial occurring in `(X + Y + XY)^q`, evaluated in the open unit ball,
is no larger than the larger of the two pure degree-`q` monomials. -/
theorem valuation_mvPowerSeriesMonomialValue_pair_le_max_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x y : K}
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (q : ℕ) (d : Fin 2 →₀ ℕ) (hq : q ≤ d 0 + d 1) :
    v (mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d) ≤
      max (v x ^ q) (v y ^ q) := by
  rw [mvPowerSeriesMonomialValue_pair, v.map_mul, v.map_pow, v.map_pow]
  let r := max (v x) (v y)
  have hxr : v x ≤ r := le_max_left _ _
  have hyr : v y ≤ r := le_max_right _ _
  have hr : r ≤ 1 := max_le (le_of_lt hvx) (le_of_lt hvy)
  have hprod : v x ^ d 0 * v y ^ d 1 ≤ r ^ (d 0 + d 1) := by
    calc
      v x ^ d 0 * v y ^ d 1 ≤ r ^ d 0 * r ^ d 1 :=
        mul_le_mul (pow_le_pow_left' hxr _) (pow_le_pow_left' hyr _)
          (by simp) (by simp)
      _ = r ^ (d 0 + d 1) := by rw [pow_add]
  have hpow : r ^ (d 0 + d 1) ≤ r ^ q :=
    pow_le_pow_of_le_one (by exact bot_le) hr hq
  calc
    v x ^ d 0 * v y ^ d 1 ≤ r ^ (d 0 + d 1) := hprod
    _ ≤ r ^ q := hpow
    _ = max (v x ^ q) (v y ^ q) := by
      by_cases hxy : v x ≤ v y
      · simp [r, max_eq_right hxy, pow_le_pow_left' hxy]
      · have hyx : v y ≤ v x := le_of_not_ge hxy
        simp [r, max_eq_left hyx, pow_le_pow_left' hyx]

/-- Each nonzero term in the substituted logarithm Sigma-family is bounded by
the larger of the corresponding one-variable logarithm terms. -/
theorem valuation_formalLogOnePlusProductArgument_sigmaTerm_le_max
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} (e : ℕ)
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    {x y : K}
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (q : ℕ) (d : Fin 2 →₀ ℕ) :
    v (PowerSeries.coeff q (PowerSeries.log K) *
        MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) *
        mvPowerSeriesMonomialValue
          (fun i : Fin 2 => if i = 0 then x else y) d) ≤
      max
        (v (PowerSeries.coeff q (PowerSeries.log K) * x ^ q))
        (v (PowerSeries.coeff q (PowerSeries.log K) * y ^ q)) := by
  by_cases hc :
      MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) = 0
  · simp [hc]
  · have hq : q ≤ d 0 + d 1 :=
      formalLogOnePlusProductArgument_pow_coeff_ne_zero_q_le_coord_sum q d hc
    have hcoeff :
        v (MvPowerSeries.coeff d
            ((formalLogOnePlusProductArgument K) ^ q)) ≤ 1 := by
      rw [formalLogOnePlusProductArgument_pow_coeff_eq_card_choices]
      exact valuation_natCast_le_one_ofWithZeroValuation_scaled v e hnval _
    have hmono :=
      valuation_mvPowerSeriesMonomialValue_pair_le_max_pow
        v hvx hvy q d hq
    rw [v.map_mul, v.map_mul, v.map_mul, v.map_mul, v.map_pow, v.map_pow]
    calc
      v (PowerSeries.coeff q (PowerSeries.log K)) *
          v (MvPowerSeries.coeff d
            ((formalLogOnePlusProductArgument K) ^ q)) *
          v (mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d) ≤
        v (PowerSeries.coeff q (PowerSeries.log K)) * 1 *
          max (v x ^ q) (v y ^ q) := by gcongr
      _ = max
          (v (PowerSeries.coeff q (PowerSeries.log K)) * v x ^ q)
          (v (PowerSeries.coeff q (PowerSeries.log K)) * v y ^ q) := by
        simp [mul_max]

/-- The full Sigma-family obtained by expanding every power of
`X + Y + XY` in the scaled logarithm substitution is unconditionally
summable.  No rearrangement hypothesis is exposed: nonzero terms in each
fixed outer degree have finite polynomial support, while their values are
bounded by the convergent one-variable logarithm terms. -/
theorem
  summable_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable
      (fun qd : Sigma fun _ : ℕ => Fin 2 →₀ ℕ =>
        PowerSeries.coeff qd.1 (PowerSeries.log K) *
          MvPowerSeries.coeff qd.2
            ((formalLogOnePlusProductArgument K) ^ qd.1) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) qd.2) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  let term : (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 (PowerSeries.log K) *
      MvPowerSeries.coeff qd.2
        ((formalLogOnePlusProductArgument K) ^ qd.1) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) qd.2
  change Summable term
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [tendsto_def]
  intro s hs
  have hrepr := Valued.mem_nhds_zero.mp hs
  let γ := Classical.choose hrepr
  have hγ := Classical.choose_spec hrepr
  have hball :
      {z : K |
        v z < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ nhds (0 : K) := by
    apply Valued.mem_nhds_zero.mpr
    exact ⟨γ, by
      intro z hz
      change Valued.v.restrict z < γ.1 at hz
      rw [Valuation.restrict_lt_iff_lt_embedding] at hz
      exact hz⟩
  have hxsum :=
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  have hysum :=
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
      (v := v) (p := p) e y hnK hnval hvy hcomplete
  have hxzero :
      Tendsto
        (fun q : ℕ =>
          PowerSeries.coeff q (PowerSeries.log K) * x ^ q)
        atTop (nhds (0 : K)) := by
    have h := hxsum.summable.tendsto_cofinite_zero
    simpa [Nat.cofinite_eq_atTop] using h
  have hyzero :
      Tendsto
        (fun q : ℕ =>
          PowerSeries.coeff q (PowerSeries.log K) * y ^ q)
        atTop (nhds (0 : K)) := by
    have h := hysum.summable.tendsto_cofinite_zero
    simpa [Nat.cofinite_eq_atTop] using h
  have hevent : ∀ᶠ q : ℕ in atTop,
      v (PowerSeries.coeff q (PowerSeries.log K) * x ^ q) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ∧
      v (PowerSeries.coeff q (PowerSeries.log K) * y ^ q) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    (hxzero.eventually hball).and (hyzero.eventually hball)
  have hexN := Filter.eventually_atTop.mp hevent
  let N := Classical.choose hexN
  have hN := Classical.choose_spec hexN
  let P : MvPolynomial (Fin 2) K :=
    formalLogOnePlusProductArgumentPolynomial K
  let E : Finset (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) :=
    (Finset.range N).sigma fun q => (P ^ q).support
  apply Filter.mem_cofinite.mpr
  apply E.finite_toSet.subset
  intro qd hbad
  by_contra hnotE
  have hgood : term qd ∈ s := by
    by_cases hqsmall : qd.1 < N
    · have hdnot : qd.2 ∉ (P ^ qd.1).support := by
        intro hd
        apply hnotE
        exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hqsmall, hd⟩
      have hpoly : (P ^ qd.1).coeff qd.2 = 0 := by
        by_contra hp
        exact hdnot (MvPolynomial.mem_support_iff.mpr hp)
      have hcoeff :
          MvPowerSeries.coeff qd.2
              ((formalLogOnePlusProductArgument K) ^ qd.1) = 0 := by
        rw [formalLogOnePlusProductArgument_eq_coe_polynomial,
          ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe]
        exact hpoly
      have htermzero : term qd = 0 := by simp [term, hcoeff]
      rw [htermzero]
      exact mem_of_mem_nhds hs
    · have hqN : N ≤ qd.1 := Nat.le_of_not_gt hqsmall
      have hcomp := hN qd.1 hqN
      apply hγ
      change Valued.v.restrict (term qd) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      have hbound :=
        valuation_formalLogOnePlusProductArgument_sigmaTerm_le_max
          (v := v) (p := p) e hnval hvx hvy qd.1 qd.2
      exact lt_of_le_of_lt hbound (max_lt hcomp.1 hcomp.2)
  exact hbad hgood

/-- The expanded product-argument Sigma-family has sum equal to the scaled
logarithm of `x + y + xy`. -/
theorem
  hasSum_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_sigma_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun qd : Sigma fun _ : ℕ => Fin 2 →₀ ℕ =>
        PowerSeries.coeff qd.1 (PowerSeries.log K) *
          MvPowerSeries.coeff qd.2
            ((formalLogOnePlusProductArgument K) ^ qd.1) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) qd.2)
      (logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have harg :
      v (x + y + x * y) < (1 : WithZero (Multiplicative ℤ)) :=
    valuation_log_mul_argument_lt_one_of_lt_one v hvx hvy
  have houter :
      HasSum
        (fun q : ℕ =>
          PowerSeries.coeff q (PowerSeries.log K) *
            (x + y + x * y) ^ q)
        (logOnePlusSeriesFieldOfWithZeroValuation v
          (x + y + x * y) hnK) :=
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
      (v := v) (p := p) e (x + y + x * y) hnK hnval harg hcomplete
  have hinner :
      ∀ q : ℕ,
        HasSum
          (fun d : Fin 2 →₀ ℕ =>
            PowerSeries.coeff q (PowerSeries.log K) *
              MvPowerSeries.coeff d
                ((formalLogOnePlusProductArgument K) ^ q) *
              mvPowerSeriesMonomialValue
                (fun i : Fin 2 => if i = 0 then x else y) d)
          (PowerSeries.coeff q (PowerSeries.log K) *
            (x + y + x * y) ^ q) := by
    intro q
    exact
      hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair_mul_left
        K (PowerSeries.coeff q (PowerSeries.log K)) x y q
  have hsigma :=
    summable_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  exact HasSum.sigma_of_hasSum houter hinner hsigma

/-- Regrouping the scaled Sigma-family by monomial exponent evaluates the
substituted formal logarithm itself.  The inner sum is finite for every fixed
monomial, by the degree bound in power-series substitution. -/
theorem
  hasSum_formalLogOnePlusProductArgument_logSubst_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d
            (PowerSeries.subst (formalLogOnePlusProductArgument K) (PowerSeries.log K)) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let sigmaTerm : (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 (PowerSeries.log K) *
      MvPowerSeries.coeff qd.2
        ((formalLogOnePlusProductArgument K) ^ qd.1) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) qd.2
  have hsigma :
      HasSum sigmaTerm
        (logOnePlusSeriesFieldOfWithZeroValuation v
          (x + y + x * y) hnK) := by
    simpa [sigmaTerm] using
      hasSum_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_sigma_ofWithZeroValuation_scaled
        (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  let swap :
      (Sigma fun _ : (Fin 2 →₀ ℕ) => ℕ) ≃
        (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) :=
    { toFun := fun dq => ⟨dq.2, dq.1⟩
      invFun := fun qd => ⟨qd.2, qd.1⟩
      left_inv := by intro dq; cases dq; rfl
      right_inv := by intro qd; cases qd; rfl }
  have hswapped :
      HasSum (sigmaTerm ∘ swap)
        (logOnePlusSeriesFieldOfWithZeroValuation v
          (x + y + x * y) hnK) :=
    (swap.hasSum_iff).2 hsigma
  have hfiber :
      ∀ d : Fin 2 →₀ ℕ,
        HasSum
          (fun q : ℕ => (sigmaTerm ∘ swap) ⟨d, q⟩)
          (MvPowerSeries.coeff d
              (PowerSeries.subst (formalLogOnePlusProductArgument K) (PowerSeries.log K)) *
            mvPowerSeriesMonomialValue
              (fun i : Fin 2 => if i = 0 then x else y) d) := by
    intro d
    let monomial :=
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
    let fiberTerm : ℕ → K := fun q =>
      PowerSeries.coeff q (PowerSeries.log K) *
        MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) * monomial
    have hfinite :
        HasSum fiberTerm
          (∑ q ∈ Finset.range (Finsupp.degree d + 1), fiberTerm q) := by
      apply hasSum_sum_of_ne_finset_zero
      intro q hq
      have hqge : Finsupp.degree d + 1 ≤ q := by
        simpa only [Finset.mem_range, not_lt] using hq
      have hdegree : Finsupp.degree d < q := Nat.lt_of_succ_le hqge
      have hzero :=
        formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
          K q d hdegree
      simp [fiberTerm, hzero]
    have hsum :
        (∑ q ∈ Finset.range (Finsupp.degree d + 1), fiberTerm q) =
          MvPowerSeries.coeff d
              (PowerSeries.subst (formalLogOnePlusProductArgument K)
                (PowerSeries.log K)) *
            monomial := by
      rw [formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ]
      simp only [smul_eq_mul, fiberTerm]
      rw [Finset.sum_mul]
    rw [hsum] at hfinite
    simpa [fiberTerm, monomial, sigmaTerm, swap, Function.comp_def] using hfinite
  exact hswapped.sigma hfiber

/-- Scaled field-level logarithm additivity on the open unit ball, obtained by
evaluating the formal product identity after the unconditional regrouping
above. -/
theorem logOnePlusSeriesField_mul_argument_eq_add_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK =
      logOnePlusSeriesFieldOfWithZeroValuation v x hnK +
        logOnePlusSeriesFieldOfWithZeroValuation v y hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hleft :=
    hasSum_formalLogOnePlusProductArgument_logSubst_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  have hright :=
    hasSum_formalLogOnePlusProductRightSide_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  exact formalLogOnePlusProductFormula_hasSum_monomialValue_eq
    (A := K) hleft hright

/-- Scaled logarithm-series additivity on first principal units.  Unlike the
earlier endpoint reduction, this theorem has no defect-convergence hypothesis. -/
theorem principalUnitLogSeries_mul_eq_add_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  let x := principalUnitSubOneOfWithZeroValuation v u
  let y := principalUnitSubOneOfWithZeroValuation v w
  have hvx : v x < (1 : WithZero (Multiplicative ℤ)) := by
    simpa [x] using principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  have hvy : v y < (1 : WithZero (Multiplicative ℤ)) := by
    simpa [y] using principalUnitSubOne_val_lt_one_ofWithZeroValuation v w
  have hadd :=
    logOnePlusSeriesField_mul_argument_eq_add_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  rw [principalUnitLogSeries_mul_argument_ofWithZeroValuation]
  simpa [principalUnitLogSeriesOfWithZeroValuation, x, y] using hadd

/-- The scaled logarithm series as a genuine homomorphism on first principal
units, with no supplied additivity or defect theorem. -/
noncomputable def principalUnitLogSeriesHomOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1 →*
      Multiplicative K where
  toFun u := Multiplicative.ofAdd
    (principalUnitLogSeriesOfWithZeroValuation v u hnK)
  map_one' := by simp
  map_mul' u w := by
    change
      Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK) =
        Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v u hnK +
            principalUnitLogSeriesOfWithZeroValuation v w hnK)
    rw [principalUnitLogSeries_mul_eq_add_ofWithZeroValuation_scaled
      (v := v) (p := p) e u w hnK hnval hcomplete]

/--
Establishes the identity `Multiplicative.toAdd (principalUnitLogSeriesHomOfWithZeroValuationScaled
(v := v) (p := p) e hnK hnval hcomplete u) = principalUnitLogSeriesOfWithZeroValuation v u hnK`.
-/
@[simp] theorem principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1) :
    Multiplicative.toAdd
        (principalUnitLogSeriesHomOfWithZeroValuationScaled
          (v := v) (p := p) e hnK hnval hcomplete u) =
      principalUnitLogSeriesOfWithZeroValuation v u hnK := by
  rfl

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

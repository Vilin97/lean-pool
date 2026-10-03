/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.LogConvergence
/-!
Develops the valuation estimates showing that logarithm and exponential series are inverse on
their common principal-unit domain.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow →
    mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow


open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable
section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- First-term extraction for the exponential series on the normalized
exponential convergence radius. -/
theorem expSeriesField_eq_one_add_tsum_succ_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    expSeriesFieldOfWithZeroValuation v x hnK =
      1 + ∑' n : ℕ, expSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    expSeriesField_eq_one_add_tsum_succ_of_summable v x hnK
      (summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)

/-- Tail form of the exponential series on the normalized convergence radius:
subtracting the constant term leaves exactly the positive-degree tail. -/
theorem expSeriesField_sub_one_eq_tsum_succ_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    expSeriesFieldOfWithZeroValuation v x hnK - 1 =
      ∑' n : ℕ, expSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [
    expSeriesField_eq_one_add_tsum_succ_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete]
  abel

/-- The positive-degree exponential tail partial sums converge to
`expSeries - 1`. -/
theorem tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1))
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_expSeriesPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1)
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1) =
        fun N : ℕ =>
          ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    funext N
    rw [expSeriesPartialSumField_succ_eq_one_add_tail]
    abel
  simpa [htail] using hsub

/-- First-term extraction for the exponential series under the sharp ramified
threshold. -/
theorem expSeriesField_eq_one_add_tsum_succ_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    expSeriesFieldOfWithZeroValuation v x hnK =
      1 + ∑' n : ℕ, expSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    expSeriesField_eq_one_add_tsum_succ_of_summable v x hnK
      (summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx => by exact_mod_cast hxthreshold hx) hcomplete)

/-- Tail form of the exponential series under the sharp ramified threshold. -/
theorem expSeriesField_sub_one_eq_tsum_succ_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    expSeriesFieldOfWithZeroValuation v x hnK - 1 =
      ∑' n : ℕ, expSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [
    expSeriesField_eq_one_add_tsum_succ_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete]
  abel

/-- The positive-degree exponential tail partial sums converge to
`expSeries - 1` under the sharp ramified threshold. -/
theorem tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1))
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_expSeriesPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx => by exact_mod_cast hxthreshold hx) hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1)
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1) =
        fun N : ℕ =>
          ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    funext N
    rw [expSeriesPartialSumField_succ_eq_one_add_tail]
    abel
  simpa [htail] using hsub

/-- A field-element exponential-series term is nonzero when the input is
nonzero. -/
theorem expSeriesTermField_ne_zero_of_ne_zero
    {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) (n : ℕ) :
    expSeriesTermField x hnK n ≠ 0 := by
  have hpow : x ^ n ≠ 0 := pow_ne_zero n hx
  have hden :
      (((Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K) ≠ 0) :=
    (Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)).ne_zero
  simpa [expSeriesTermField] using div_ne_zero hpow hden

/-- On the normalized exponential convergence ball, every exponential term of
degree at least two has strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_expSeriesTermField_lt_self_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    {n : ℕ} (hn : 2 ≤ n) :
    v (expSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hxoneReal :
      1 < ((ofWithZeroValuation v).val xu : ℝ) :=
    ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
      (v := v) (x := x) hx hvx
  have hxone : 1 < (ofWithZeroValuation v).val xu := by
    exact_mod_cast hxoneReal
  have hxmin : (2 : ℤ) ≤ (ofWithZeroValuation v).val xu := by
    omega
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ n / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_factorial
      (v := v) (p := p) (n := n) xu (hnK n) (hnval n)]
    exact
      exp_higher_term_integer_valuation_gt
        (p := p) hn hxmin
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ n / denom) hval
  simpa [xu, denom, expSeriesTermField] using hlt

/-- Above the sharp ramified `e/(p-1)` threshold, every exponential term of
degree at least two has strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : 2 ≤ n) :
    v (expSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ n / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
      (v := v) (p := p) (e := e) (n := n) xu (hnK n) (hnval n)]
    exact
      exp_higher_term_integer_valuation_gt_scaled
        (p := p) (e := e) (n := n) hn hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ n / denom) hval
  simpa [xu, denom, expSeriesTermField] using hlt

/-- Every finite higher-degree exponential tail has valuation strictly smaller
than the linear term on the normalized convergence ball. -/
theorem valuation_expSeriesHigherTailPartialSumField_lt_self_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ)) (N : ℕ) :
    v (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_expSeriesTermField_lt_self_of_lt_exp_neg_one
          (v := v) (p := p) (x := x) hx hnK hnval hvx
          (by omega))

/-- Every finite higher-degree exponential tail has valuation strictly smaller
than the linear term above the sharp ramified `e/(p-1)` threshold. -/
theorem valuation_expSeriesHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold
          (by omega))

/-- The higher-degree exponential tail partial sums converge to
`expSeries - 1 - x`. -/
theorem tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1))
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
    exact
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1)) - x)
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (N + 1),
          expSeriesTermField x hnK (n + 1)) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2) := by
    funext N
    rw [Finset.sum_range_succ']
    simp [expSeriesTermField]
  simpa [htail] using hsub

/-- The higher-degree exponential tail partial sums converge to
`expSeries - 1 - x` under the sharp ramified threshold. -/
theorem tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1))
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
    exact
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval hxthreshold hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1)) - x)
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (N + 1),
          expSeriesTermField x hnK (n + 1)) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2) := by
    funext N
    rw [Finset.sum_range_succ']
    simp [expSeriesTermField]
  simpa [htail] using hsub

/-- The full higher-degree exponential tail has valuation strictly smaller
than the linear term. -/
theorem valuation_expSeriesHigherTailField_lt_self_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesHigherTailPartialSumField_lt_self_of_lt_exp_neg_one
          (v := v) (p := p) (x := x) hx hnK hnval hvx N)

/-- The full higher-degree exponential tail has valuation strictly smaller
than the linear term above the sharp ramified `e/(p-1)` threshold. -/
theorem valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx' => by
          have hval_eq :
              (ofWithZeroValuation v).val (Units.mk0 x hx') =
                (ofWithZeroValuation v).val (Units.mk0 x hx) := by
            congr
          rw [hval_eq]
          exact hthreshold)
        hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold N)

/-- The exponential-series value is a first principal unit on the normalized
convergence radius: after subtracting the constant term, it lies in the open
unit ball. -/
theorem valuation_expSeriesField_sub_one_lt_one_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) <
      (1 : WithZero (Multiplicative ℤ)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    valuation_limit_lt_one_of_tendsto_of_eventually_lt_one
      (v := v)
      (u := fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      (z := expSeriesFieldOfWithZeroValuation v x hnK - 1)
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesTailPartialSumField_lt_one_of_lt_exp_neg_one
          (v := v) (p := p) x hnK hnval hvx N)

/-- On the normalized convergence ball, `exp(x) - 1` has the same valuation
as the linear term `x`. -/
theorem valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x := by
  have htail :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
        v x :=
    valuation_expSeriesHigherTailField_lt_self_of_lt_exp_neg_one
      (v := v) (p := p) (x := x) hx hnK hnval hvx hcomplete
  have hsplit :
      expSeriesFieldOfWithZeroValuation v x hnK - 1 =
        x + (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

/-- On the sharp ramified exponential convergence ball,
`exp(x) - 1` has the same valuation as the linear term `x`. -/
theorem valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x := by
  have htail :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
        v x :=
    valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hcomplete
  have hsplit :
      expSeriesFieldOfWithZeroValuation v x hnK - 1 =
        x + (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

/-- Above the ramified threshold, the composite `log(exp(x))` is congruent to
`x` to strictly higher valuation.  This is the field-level first-order
inverse estimate; the exact evaluated inverse still requires the full
composition argument. -/
theorem valuation_log_exp_sub_self_lt_of_scaled_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v
          (expSeriesFieldOfWithZeroValuation v x hnKexp - 1) hnKlog - x) <
      v x := by
  let z : K := expSeriesFieldOfWithZeroValuation v x hnKexp - 1
  have hp_sub_pos : 0 < ((p : ℚ) - 1) := by
    have hp_two : (2 : ℕ) ≤ p := (Fact.out : Nat.Prime p).two_le
    have hp_two_rat : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_two
    linarith
  have hthreshold_nonneg :
      0 ≤ (e : ℚ) / ((p : ℚ) - 1) :=
    div_nonneg (Nat.cast_nonneg e) hp_sub_pos.le
  have hxval_pos_rat :
      (0 : ℚ) < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
    lt_of_le_of_lt hthreshold_nonneg hthreshold
  have hxval_pos :
      0 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
    exact_mod_cast hxval_pos_rat
  have hvx_lt_one :
      v x < (1 : WithZero (Multiplicative ℤ)) :=
    valuation_lt_one_of_ofWithZeroValuation_val_pos v (Units.mk0 x hx)
      hxval_pos
  have hvz_eq :
      v z = v x := by
    simpa [z] using
      valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (x := x) hx hnKexp hnvalExp hthreshold
        hcomplete
  have hz : z ≠ 0 := by
    intro hz0
    have hzero : v z = 0 := by simp [hz0]
    have hxzero : v x = 0 := by simpa [hvz_eq] using hzero
    exact ((_root_.Valuation.ne_zero_iff v).2 hx) hxzero
  have hvz_lt_one : v z < (1 : WithZero (Multiplicative ℤ)) := by
    simpa [hvz_eq] using hvx_lt_one
  have hzval_eq :
      (ofWithZeroValuation v).val (Units.mk0 z hz) =
        (ofWithZeroValuation v).val (Units.mk0 x hx) :=
    ofWithZeroValuation_val_eq_of_valuation_eq v hvz_eq
  have hthreshold_z :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 z hz) : ℚ) := by
    rw [hzval_eq]
    exact hthreshold
  have hlog_tail :
      v (logOnePlusSeriesFieldOfWithZeroValuation v z hnKlog - z) <
        v x := by
    have htail :
        v (logOnePlusSeriesFieldOfWithZeroValuation v z hnKlog - z) <
          v z :=
      valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := z) hz hnKlog hnvalLog hvz_lt_one
        hthreshold_z hcomplete
    simpa [hvz_eq] using htail
  have hexp_tail :
      v (z - x) < v x := by
    simpa [z] using
      valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnKexp hnvalExp hthreshold
        hcomplete
  have hsplit :
      logOnePlusSeriesFieldOfWithZeroValuation v z hnKlog - x =
        (logOnePlusSeriesFieldOfWithZeroValuation v z hnKlog - z) +
          (z - x) := by
    abel
  rw [show
      logOnePlusSeriesFieldOfWithZeroValuation v
          (expSeriesFieldOfWithZeroValuation v x hnKexp - 1) hnKlog - x =
        logOnePlusSeriesFieldOfWithZeroValuation v z hnKlog - x by
      simp [z]]
  rw [hsplit]
  exact v.map_add_lt hlog_tail hexp_tail

/-- Above the ramified threshold, the composite `exp(log(1+x)) - 1` is
congruent to `x` to strictly higher valuation.  This is the principal-unit
side first-order inverse estimate. -/
theorem valuation_exp_log_sub_self_lt_of_scaled_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v
          (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) hnKexp -
        1 - x) <
      v x := by
  let y : K := logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog
  have hp_sub_pos : 0 < ((p : ℚ) - 1) := by
    have hp_two : (2 : ℕ) ≤ p := (Fact.out : Nat.Prime p).two_le
    have hp_two_rat : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_two
    linarith
  have hthreshold_nonneg :
      0 ≤ (e : ℚ) / ((p : ℚ) - 1) :=
    div_nonneg (Nat.cast_nonneg e) hp_sub_pos.le
  have hxval_pos_rat :
      (0 : ℚ) < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
    lt_of_le_of_lt hthreshold_nonneg hthreshold
  have hxval_pos :
      0 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
    exact_mod_cast hxval_pos_rat
  have hvx_lt_one :
      v x < (1 : WithZero (Multiplicative ℤ)) :=
    valuation_lt_one_of_ofWithZeroValuation_val_pos v (Units.mk0 x hx)
      hxval_pos
  have hvy_eq :
      v y = v x := by
    simpa [y] using
      valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnKlog hnvalLog hvx_lt_one
        hthreshold hcomplete
  have hy : y ≠ 0 := by
    intro hy0
    have hzero : v y = 0 := by simp [hy0]
    have hxzero : v x = 0 := by simpa [hvy_eq] using hzero
    exact ((_root_.Valuation.ne_zero_iff v).2 hx) hxzero
  have hyval_eq :
      (ofWithZeroValuation v).val (Units.mk0 y hy) =
        (ofWithZeroValuation v).val (Units.mk0 x hx) :=
    ofWithZeroValuation_val_eq_of_valuation_eq v hvy_eq
  have hthreshold_y :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℚ) := by
    rw [hyval_eq]
    exact hthreshold
  have hexp_tail :
      v (expSeriesFieldOfWithZeroValuation v y hnKexp - 1 - y) <
        v x := by
    have htail :
        v (expSeriesFieldOfWithZeroValuation v y hnKexp - 1 - y) <
          v y :=
      valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := y) hy hnKexp hnvalExp hthreshold_y
        hcomplete
    simpa [hvy_eq] using htail
  have hlog_tail :
      v (y - x) < v x := by
    simpa [y] using
      valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnKlog hnvalLog hvx_lt_one
        hthreshold hcomplete
  have hsplit :
      expSeriesFieldOfWithZeroValuation v y hnKexp - 1 - x =
        (expSeriesFieldOfWithZeroValuation v y hnKexp - 1 - y) +
          (y - x) := by
    abel
  rw [show
      expSeriesFieldOfWithZeroValuation v
          (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) hnKexp -
          1 - x =
        expSeriesFieldOfWithZeroValuation v y hnKexp - 1 - x by
      simp [y]]
  rw [hsplit]
  exact v.map_add_lt hexp_tail hlog_tail

/-- On the normalized convergence ball, `exp(x) - 1` is nonzero whenever the
input is nonzero.  This is the kernel-preparation form of the first-term
dominance estimate. -/
theorem expSeriesField_sub_one_ne_zero_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v x hnK - 1 ≠ 0 := by
  intro hzero
  have hv :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x :=
    valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) (x := x) hx hnK hnval hvx hcomplete
  rw [hzero, map_zero] at hv
  exact ((_root_.Valuation.ne_zero_iff v).2 hx) hv.symm

/-- On the normalized convergence ball, the field exponential has trivial
kernel at the identity. -/
theorem expSeriesField_eq_one_iff_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K}
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v x hnK = 1 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact
      (expSeriesField_sub_one_ne_zero_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) (x := x) hx hnK hnval hvx hcomplete)
        (sub_eq_zero.mpr h)
  · intro hx
    subst x
    simp

/-- The exponential-series value itself has valuation one on the normalized
convergence radius.  This is the field-side unit statement used by the
principal-unit exponential. -/
theorem valuation_expSeriesField_eq_one_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK) =
      (1 : WithZero (Multiplicative ℤ)) := by
  have htail :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1) <
        (1 : WithZero (Multiplicative ℤ)) :=
    valuation_expSeriesField_sub_one_lt_one_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  have hrewrite :
      expSeriesFieldOfWithZeroValuation v x hnK =
        1 + (expSeriesFieldOfWithZeroValuation v x hnK - 1) := by
    abel
  rw [hrewrite]
  exact v.map_one_add_of_lt htail

/-- The logarithm-series for the product argument
`(1 + x) * (1 + y) - 1 = x + y + x*y` has the expected topological sum. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_mul_argument
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => signedLogSeriesTermField (x + y + x * y) hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have harg :
      v (x + y + x * y) < (1 : WithZero (Multiplicative ℤ)) :=
    valuation_log_mul_argument_lt_one_of_lt_one v hvx hvy
  exact
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) (x + y + x * y) hnK hnval harg hcomplete

/-- Finite logarithm polynomials for the product argument converge to the
corresponding logarithm-series value. -/
theorem tendsto_logOnePlusPartialSumField_mul_argument
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ => logOnePlusPartialSumField (x + y + x * y) hnK N)
      atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v
        (x + y + x * y) hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_mul_argument
      (v := v) (p := p) x y hnK hnval hvx hvy hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

/-- Product-argument side of the two-variable logarithm formula, arranged as
an outer sum over logarithm degrees and a finite inner monomial sum for each
degree.  The remaining summability hypothesis is exactly the Tonelli/Fubini
input needed before identifying this sigma-indexed family with the substituted
two-variable power-series coefficients. -/
theorem hasSum_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_sigma_of_summable
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hsigma :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Summable
        (fun qd : Sigma fun _ : ℕ => Fin 2 →₀ ℕ =>
          PowerSeries.coeff qd.1 (PowerSeries.log K) *
            MvPowerSeries.coeff qd.2
              ((formalLogOnePlusProductArgument K) ^ qd.1) *
            mvPowerSeriesMonomialValue
              (fun i : Fin 2 => if i = 0 then x else y) qd.2)) :
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
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField
      (v := v) (p := p) (x + y + x * y) hnK hnval harg hcomplete
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
  exact HasSum.sigma_of_hasSum houter hinner hsigma

/-- The complete-DVF package attached to a standard `ℤᵐ⁰`-valued complete
discrete valuation. -/
def completeDVFOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v] :
    CompleteDVF.{u, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := v
  instCompleteDiscrete := inferInstance

/-- For a normalized `ℤᵐ⁰`-valued complete DVF, an integer-valuation lower
bound gives membership in the corresponding maximal-ideal power. -/
theorem mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (hval : ∀ ha : (a : K) ≠ 0,
      (n : ℤ) ≤
        (ofWithZeroValuation v).val (Units.mk0 (a : K) ha)) :
    a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n := by
  by_cases ha0 : (a : K) = 0
  · have ha_zero : a = 0 := Subtype.ext ha0
    simp [ha_zero]
  · have hπpow :
        v (π : K) ^ n =
          WithZero.exp (-(n : ℤ)) := by
      rw [hπval, ← WithZero.exp_nsmul]
      simp
    have hlog :
        WithZero.log (v (a : K)) ≤ -(n : ℤ) := by
      have hNlog :
          (n : ℤ) ≤ -WithZero.log (v (a : K)) := by
        simpa [ofWithZeroValuation_val] using hval ha0
      linarith
    have hva :
        v (a : K) ≤ WithZero.exp (-(n : ℤ)) :=
      WithZero.le_exp_of_log_le hlog
    exact
      (mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
        (val := v) hπ n (x := a)).2 (by
          change v (a : K) ≤ v ((π : K) ^ n)
          rw [map_pow, hπpow]
          exact hva)

/-- A strict integer-valuation lower bound by `n` gives membership in the
next maximal-ideal power. -/
theorem mem_maximalIdeal_pow_succ_ofWithZeroValuation_val_gt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (hval : ∀ ha : (a : K) ≠ 0,
      (n : ℤ) <
        (ofWithZeroValuation v).val (Units.mk0 (a : K) ha)) :
    a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1) := by
  apply
    mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
      (v := v) (π := π) hπ hπval (n + 1) a
  intro ha
  have hgt := hval ha
  omega

/-- Conversely, membership in `m^n` gives the expected lower bound for the
attached integer valuation. -/
theorem ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (ha : a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n)
    (ha_ne : (a : K) ≠ 0) :
    (n : ℤ) ≤
      (ofWithZeroValuation v).val (Units.mk0 (a : K) ha_ne) := by
  have hπpow :
      v (π : K) ^ n =
        WithZero.exp (-(n : ℤ)) := by
    rw [hπval, ← WithZero.exp_nsmul]
    simp
  have hva :
      v (a : K) ≤ WithZero.exp (-(n : ℤ)) := by
    have h :=
      (mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
        (val := v) hπ n (x := a)).1 ha
    change v (a : K) ≤ v ((π : K) ^ n) at h
    rw [map_pow, hπpow] at h
    exact h
  have hv_ne : v (a : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 ha_ne
  have hlog :
      WithZero.log (v (a : K)) ≤ -(n : ℤ) :=
    (WithZero.log_le_iff_le_exp hv_ne).2 hva
  have hneg :
      (n : ℤ) ≤ -WithZero.log (v (a : K)) := by
    simpa using (neg_le_neg hlog)
  simpa [ofWithZeroValuation_val] using hneg

/-- If `a ∈ m^n` lies above the ramified threshold, then the first composite
`log(exp(a))` is congruent to `a` modulo `m^(n+1)`. -/
theorem logOnePlusSeries_expSeries_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a b : (completeDVFOfWithZeroValuation v).valuationSubring)
    (ha : a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n)
    (hb : (b : K) =
      logOnePlusSeriesFieldOfWithZeroValuation v
        (expSeriesFieldOfWithZeroValuation v (a : K) hnKexp - 1) hnKlog -
          (a : K)) :
    b ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let x : K := (a : K)
  apply
    mem_maximalIdeal_pow_succ_ofWithZeroValuation_val_gt
      (v := v) (π := π) hπ hπval n b
  intro hbne
  by_cases hx : x = 0
  · have hbzero : (b : K) = 0 := by
      rw [hb]
      simp [x, hx]
    exact False.elim (hbne hbzero)
  · have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n (a := a) ha hx
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
    have hlt :
        v (logOnePlusSeriesFieldOfWithZeroValuation v
              (expSeriesFieldOfWithZeroValuation v x hnKexp - 1) hnKlog - x) <
          v x :=
      valuation_log_exp_sub_self_lt_of_scaled_threshold
        (v := v) (p := p) e (x := x) hx hnKexp hnvalExp hnKlog
        hnvalLog hthreshold hcomplete
    have hb_lt : v (b : K) < v x := by
      simpa [x, hb] using hlt
    have hval_lt :
        (ofWithZeroValuation v).val (Units.mk0 x hx) <
          (ofWithZeroValuation v).val (Units.mk0 (b : K) hbne) :=
      ofWithZeroValuation_val_lt_of_valuation_lt
        (v := v) (x := Units.mk0 x hx) (y := Units.mk0 (b : K) hbne)
        hb_lt
    exact lt_of_le_of_lt hge hval_lt

/-- If `a ∈ m^n` lies above the ramified threshold, then the second composite
`exp(log(1+a)) - 1` is congruent to `a` modulo `m^(n+1)`. -/
theorem
  expSeries_logOnePlusSeries_sub_one_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a b : (completeDVFOfWithZeroValuation v).valuationSubring)
    (ha : a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n)
    (hb : (b : K) =
      expSeriesFieldOfWithZeroValuation v
        (logOnePlusSeriesFieldOfWithZeroValuation v (a : K) hnKlog) hnKexp -
          1 - (a : K)) :
    b ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let x : K := (a : K)
  apply
    mem_maximalIdeal_pow_succ_ofWithZeroValuation_val_gt
      (v := v) (π := π) hπ hπval n b
  intro hbne
  by_cases hx : x = 0
  · have hbzero : (b : K) = 0 := by
      rw [hb]
      simp [x, hx]
    exact False.elim (hbne hbzero)
  · have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n (a := a) ha hx
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
    have hlt :
        v (expSeriesFieldOfWithZeroValuation v
              (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) hnKexp -
            1 - x) <
          v x :=
      valuation_exp_log_sub_self_lt_of_scaled_threshold
        (v := v) (p := p) e (x := x) hx hnKlog hnvalLog hnKexp
        hnvalExp hthreshold hcomplete
    have hb_lt : v (b : K) < v x := by
      simpa [x, hb] using hlt
    have hval_lt :
        (ofWithZeroValuation v).val (Units.mk0 x hx) <
          (ofWithZeroValuation v).val (Units.mk0 (b : K) hbne) :=
      ofWithZeroValuation_val_lt_of_valuation_lt
        (v := v) (x := Units.mk0 x hx) (y := Units.mk0 (b : K) hbne)
        hb_lt
    exact lt_of_le_of_lt hge hval_lt

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

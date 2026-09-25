/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms
/-!
Establishes convergence and summability of the exponential series on sufficiently deep
nonarchimedean ideals.
-/

@[expose] public section

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The field-unit logarithm theorem, exponential-series valuation estimate:
if `x` has integer valuation strictly bigger than one, then the valuations of
`x^n / n!` tend to `+∞`. -/
theorem ofWithZeroValuation_val_exp_term_tendsto_atTop_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop :=
  ofWithZeroValuation_val_pow_div_natCast_factorial_tendsto_atTop
    (v := v) (p := p) x hnK hnval
    (c := ((ofWithZeroValuation v).val x : ℝ)) hxone le_rfl

/-- Eventually the exponential-series terms have valuation at least any
prescribed integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_exp_term_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ))
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_exp_term_tendsto_atTop_of_one_lt
      (v := v) (p := p) x hnK hnval hxone
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ n /
              Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The exponential-series terms tend to zero in the topology defined by the
given `ℤᵐ⁰`-valued valuation. -/
theorem tendsto_zero_exp_term_ofWithZeroValuation_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        ((x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_exp_term_of_one_lt
      (v := v) (p := p) x hnK hnval hxone (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ n /
      Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  change v.restrict (y : K) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvle (by simpa [γ'] using hNγ)

/-- In a complete nonarchimedean valuation topology, the exponential-series
terms are summable on the radius supplied by the preceding valuation estimate. -/
theorem summable_exp_term_ofWithZeroValuation_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable
      (fun n : ℕ =>
        ((x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto
        (fun n : ℕ =>
          ((x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
        atTop (𝓝 (0 : K)) :=
    tendsto_zero_exp_term_ofWithZeroValuation_of_one_lt
      (v := v) (p := p) x hnK hnval hxone
  have hcofinite :
      Tendsto
        (fun n : ℕ =>
          ((x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
        cofinite (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- The field-unit logarithm theorem, exponential series: the series
`∑ x^n/n!` has the value supplied by `expSeriesOfWithZeroValuation`. -/
theorem hasSum_expSeriesTerm_expSeries_ofWithZeroValuation_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => expSeriesTerm x hnK n)
      (expSeriesOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable
        (fun n : ℕ =>
          ((x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)) :=
    summable_exp_term_ofWithZeroValuation_of_one_lt
      (v := v) (p := p) x hnK hnval hxone hcomplete
  simpa [expSeriesOfWithZeroValuation, expSeriesTerm] using hs.hasSum

/-- The finite exponential polynomials converge to the exponential-series
value on the same radius. -/
theorem tendsto_expSeriesPartialSum_ofWithZeroValuation_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => expSeriesPartialSum x hnK N) atTop
      (𝓝 (expSeriesOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTerm_expSeries_ofWithZeroValuation_of_one_lt
      (v := v) (p := p) x hnK hnval hxone hcomplete
  simpa [expSeriesPartialSum] using hsum.tendsto_sum_nat

/-- Sharp ramified version of the exponential-series valuation estimate:
if `x` has integer valuation strictly bigger than `e/(p-1)`, then the
valuations of `x^n / n!` tend to `+∞`. -/
theorem ofWithZeroValuation_val_exp_term_scaled_tendsto_atTop_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop :=
  ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_tendsto_atTop
    (v := v) (p := p) e x hnK hnval
    (c := ((ofWithZeroValuation v).val x : ℝ)) hxthreshold le_rfl

/-- Eventually the ramified exponential-series terms have valuation at least
any prescribed integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_exp_term_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ))
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_exp_term_scaled_tendsto_atTop_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ n /
              Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The exponential-series terms tend to zero under the sharp ramified
threshold. -/
theorem tendsto_zero_exp_term_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        ((x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_exp_term_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ n /
      Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  change v.restrict (y : K) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvle (by simpa [γ'] using hNγ)

/-- Summability of the exponential series under the sharp ramified threshold. -/
theorem summable_exp_term_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable
      (fun n : ℕ =>
        ((x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto
        (fun n : ℕ =>
          ((x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
        atTop (𝓝 (0 : K)) :=
    tendsto_zero_exp_term_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold
  have hcofinite :
      Tendsto
        (fun n : ℕ =>
          ((x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
        cofinite (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- The exponential series has the same `tsum` value under a sharp ramified
denominator valuation hypothesis. -/
theorem hasSum_expSeriesTerm_expSeries_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => expSeriesTerm x hnK n)
      (expSeriesOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable
        (fun n : ℕ =>
          ((x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)) :=
    summable_exp_term_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  simpa [expSeriesOfWithZeroValuation, expSeriesTerm] using hs.hasSum

/-- Finite exponential polynomials converge under the sharp ramified
threshold. -/
theorem tendsto_expSeriesPartialSum_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => expSeriesPartialSum x hnK N) atTop
      (𝓝 (expSeriesOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTerm_expSeries_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  simpa [expSeriesPartialSum] using hsum.tendsto_sum_nat

/-- Establishes the identity `expSeriesTermField x hnK n = 0`. -/
theorem expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    {n : ℕ} (hn : n ≠ 0) :
    expSeriesTermField x hnK n = 0 := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ n => simp [expSeriesTermField, hx]

/-- The field-element exponential series at zero has value one. -/
@[simp] theorem expSeriesField_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesFieldOfWithZeroValuation v 0 hnK = 1 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  calc
    expSeriesFieldOfWithZeroValuation v 0 hnK =
        ∑' n : ℕ, expSeriesTermField (0 : K) hnK n := by
      rfl
    _ = expSeriesTermField (0 : K) hnK 0 := by
      exact tsum_eq_single 0 fun n hn =>
        expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero rfl hnK hn
    _ = 1 := by
      simp

/-- Field-element exponential-series terms tend to zero under the normalized
radius condition `v x < exp (-1)`.  This version also covers `x = 0`. -/
theorem tendsto_zero_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => expSeriesTermField x hnK n) =ᶠ[atTop]
          fun _ : ℕ => (0 : K) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnzero : n ≠ 0 := by omega
      exact expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero hx hnK hnzero
    exact hconst.tendsto
  · have hxone :
        1 < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
      ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
        (v := v) hx hvx
    have hunit :=
      tendsto_zero_exp_term_ofWithZeroValuation_of_one_lt
        (v := v) (p := p) (Units.mk0 x hx) hnK hnval hxone
    simpa [expSeriesTermField, expSeriesTerm] using hunit

/-- In a complete nonarchimedean valuation topology, the field-element
exponential-series terms are summable under `v x < exp (-1)`. -/
theorem summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
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
    Summable (fun n : ℕ => expSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element exponential series with value supplied by
`expSeriesFieldOfWithZeroValuation`. -/
theorem hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
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
    HasSum (fun n : ℕ => expSeriesTermField x hnK n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [expSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- Field-element exponential-series terms tend to zero under the sharp
ramified threshold.  This version also covers `x = 0`. -/
theorem tendsto_zero_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => expSeriesTermField x hnK n) =ᶠ[atTop]
          fun _ : ℕ => (0 : K) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnzero : n ≠ 0 := by omega
      exact expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero hx hnK hnzero
    exact hconst.tendsto
  · have hunit :=
      tendsto_zero_exp_term_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (Units.mk0 x hx) hnK hnval (hxthreshold hx)
    simpa [expSeriesTermField, expSeriesTerm] using hunit

/-- Summability of the field-element exponential series under the sharp
ramified threshold. -/
theorem summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => expSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold
  have hcofinite :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element exponential series with value supplied by
`expSeriesFieldOfWithZeroValuation`, under the sharp ramified threshold. -/
theorem hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => expSeriesTermField x hnK n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  simpa [expSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- Field-element exponential partial sums converge under the sharp ramified
threshold. -/
theorem tendsto_expSeriesPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => expSeriesPartialSumField x hnK N) atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  simpa [expSeriesPartialSumField] using hsum.tendsto_sum_nat

/-- The local-field exponential series is the convergent evaluation of
mathlib's formal exponential power series on its normalized radius. -/
theorem hasSum_formalExpPowerSeries_eval_expSeriesField
    [Algebra ℚ K]
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
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff n (PowerSeries.exp K) * x ^ n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  exact hsum.congr_fun fun n =>
    formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
      (K := K) x hnK n

/-- The product family of two local exponential series is summable on the
normalized exponential convergence ball.  This uses mathlib's
nonarchimedean Cauchy-product theorem rather than an absolute-convergence
argument. -/
theorem summable_expSeriesTermField_mul_prod_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable
      (fun ij : ℕ × ℕ =>
        expSeriesTermField x hnK ij.1 *
          expSeriesTermField y hnK ij.2) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hxsum :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  have hysum :
      Summable (fun n : ℕ => expSeriesTermField y hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) y hnK hnval hvy hcomplete
  exact hxsum.mul_of_nonarchimedean hysum

/-- The antidiagonal Cauchy product of two local exponential series sums to
the product of their values. -/
theorem
  hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        ∑ ij ∈ Finset.antidiagonal n,
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2)
      (expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hxsum :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  have hysum :
      Summable (fun n : ℕ => expSeriesTermField y hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) y hnK hnval hvy hcomplete
  have hprod :
      Summable
        (fun ij : ℕ × ℕ =>
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2) :=
    hxsum.mul_of_nonarchimedean hysum
  have hcauchy :
      Summable
        (fun n : ℕ =>
          ∑ ij ∈ Finset.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  have htsum :
      expSeriesFieldOfWithZeroValuation v x hnK *
          expSeriesFieldOfWithZeroValuation v y hnK =
        ∑' n : ℕ,
          ∑ ij ∈ Finset.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2 := by
    simpa [expSeriesFieldOfWithZeroValuation] using
      hxsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hysum hprod
  exact htsum.symm ▸ hcauchy.hasSum

/-- Local exponential multiplicativity on the normalized convergence ball. -/
theorem expSeriesField_add_eq_mul_ofWithZeroValuation_of_lt_exp_neg_one
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v (x + y) hnK =
      expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hxy :
      v (x + y) < WithZero.exp (-1 : ℤ) :=
    valuation_add_lt_exp_neg_one_of_lt_exp_neg_one v hvx hvy
  have hsumAdd :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) (x + y) hnK hnval hxy hcomplete
  have hsumCauchyAdd :
      HasSum
        (fun n : ℕ =>
          ∑ ij ∈ Finset.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2)
        (expSeriesFieldOfWithZeroValuation v (x + y) hnK) :=
    hsumAdd.congr_fun fun n =>
      (expSeriesTermField_add_eq_sum_antidiagonal
        (K := K) x y hnK n).symm
  have hsumProduct :=
    hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x y hnK hnval hvx hvy hcomplete
  exact hsumCauchyAdd.unique hsumProduct

/-- The product family of two local exponential series is summable under the
sharp ramified threshold. -/
theorem summable_expSeriesTermField_mul_prod_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable
      (fun ij : ℕ × ℕ =>
        expSeriesTermField x hnK ij.1 *
          expSeriesTermField y hnK ij.2) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hxsum :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  have hysum :
      Summable (fun n : ℕ => expSeriesTermField y hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e y hnK hnval hythreshold hcomplete
  exact hxsum.mul_of_nonarchimedean hysum

/-- The antidiagonal Cauchy product of two local exponential series sums to
the product of their values under the sharp ramified threshold. -/
theorem
  hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        ∑ ij ∈ Finset.antidiagonal n,
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2)
      (expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hxsum :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  have hysum :
      Summable (fun n : ℕ => expSeriesTermField y hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e y hnK hnval hythreshold hcomplete
  have hprod :
      Summable
        (fun ij : ℕ × ℕ =>
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2) :=
    hxsum.mul_of_nonarchimedean hysum
  have hcauchy :
      Summable
        (fun n : ℕ =>
          ∑ ij ∈ Finset.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  have htsum :
      expSeriesFieldOfWithZeroValuation v x hnK *
          expSeriesFieldOfWithZeroValuation v y hnK =
        ∑' n : ℕ,
          ∑ ij ∈ Finset.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2 := by
    simpa [expSeriesFieldOfWithZeroValuation] using
      hxsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hysum hprod
  exact htsum.symm ▸ hcauchy.hasSum

/-- Local exponential multiplicativity under the sharp ramified threshold. -/
theorem expSeriesField_add_eq_mul_ofWithZeroValuation_scaled_of_threshold
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v (x + y) hnK =
      expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hxythreshold : ∀ hxy : x + y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) : ℝ) := by
    intro hxy
    by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        intro hy
        exact hxy (by simp [hx, hy])
      simpa [hx] using hythreshold hy
    · by_cases hy : y = 0
      · simpa [hy] using hxthreshold hx
      · have hmin :
            min ((ofWithZeroValuation v).val (Units.mk0 x hx))
                ((ofWithZeroValuation v).val (Units.mk0 y hy)) ≤
              (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) :=
          ofWithZeroValuation_val_add_ge_min v hx hy hxy
        have hminR :
            ((min ((ofWithZeroValuation v).val (Units.mk0 x hx))
                ((ofWithZeroValuation v).val (Units.mk0 y hy)) : ℤ) : ℝ) ≤
              ((ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) : ℝ) := by
          exact_mod_cast hmin
        have hthresholdMin :
            (e : ℝ) / ((p : ℝ) - 1) <
              ((min ((ofWithZeroValuation v).val (Units.mk0 x hx))
                  ((ofWithZeroValuation v).val (Units.mk0 y hy)) : ℤ) : ℝ) := by
          rw [Int.cast_min]
          exact lt_min (hxthreshold hx) (hythreshold hy)
        exact lt_of_lt_of_le hthresholdMin hminR
  have hsumAdd :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e (x + y) hnK hnval hxythreshold hcomplete
  have hsumCauchyAdd :
      HasSum
        (fun n : ℕ =>
          ∑ ij ∈ Finset.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2)
        (expSeriesFieldOfWithZeroValuation v (x + y) hnK) :=
    hsumAdd.congr_fun fun n =>
      (expSeriesTermField_add_eq_sum_antidiagonal
        (K := K) x y hnK n).symm
  have hsumProduct :=
    hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x y hnK hnval hxthreshold hythreshold
      hcomplete
  exact hsumCauchyAdd.unique hsumProduct

/-- The negative additive parameter gives a left inverse for the local
exponential series. -/
theorem expSeriesField_neg_mul_self_eq_one_ofWithZeroValuation_of_lt_exp_neg_one
    [Algebra ℚ K]
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
    expSeriesFieldOfWithZeroValuation v (-x) hnK *
        expSeriesFieldOfWithZeroValuation v x hnK = 1 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hneg :
      v (-x) < WithZero.exp (-1 : ℤ) := by
    simpa using hvx
  have hmul :=
    expSeriesField_add_eq_mul_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) (-x) x hnK hnval hneg hvx hcomplete
  simpa [neg_add_cancel] using hmul.symm

/-- The negative additive parameter gives a right inverse for the local
exponential series. -/
theorem expSeriesField_mul_neg_self_eq_one_ofWithZeroValuation_of_lt_exp_neg_one
    [Algebra ℚ K]
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
    expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v (-x) hnK = 1 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hneg :
      v (-x) < WithZero.exp (-1 : ℤ) := by
    simpa using hvx
  have hmul :=
    expSeriesField_add_eq_mul_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x (-x) hnK hnval hvx hneg hcomplete
  simpa [add_neg_cancel] using hmul.symm

/-- Field-side inverse form of the local exponential identity:
`exp(-x) = exp(x)⁻¹`. -/
theorem expSeriesField_neg_eq_inv_self_ofWithZeroValuation_of_lt_exp_neg_one
    [Algebra ℚ K]
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
    expSeriesFieldOfWithZeroValuation v (-x) hnK =
      (expSeriesFieldOfWithZeroValuation v x hnK)⁻¹ := by
  exact
    eq_inv_of_mul_eq_one_left
      (expSeriesField_neg_mul_self_eq_one_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)

/-- Field-side inverse form of the local exponential identity:
`exp(x)⁻¹ = exp(-x)`. -/
theorem expSeriesField_inv_eq_neg_self_ofWithZeroValuation_of_lt_exp_neg_one
    [Algebra ℚ K]
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
    (expSeriesFieldOfWithZeroValuation v x hnK)⁻¹ =
      expSeriesFieldOfWithZeroValuation v (-x) hnK := by
  exact
    inv_eq_of_mul_eq_one_right
      (expSeriesField_mul_neg_self_eq_one_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)

/-- Field-element exponential partial sums converge to the exponential-series
value under `v x < exp (-1)`. -/
theorem tendsto_expSeriesPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
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
    Tendsto (fun N : ℕ => expSeriesPartialSumField x hnK N) atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [expSeriesPartialSumField] using hsum.tendsto_sum_nat

/-- Zero lies in the normalized exponential convergence ball. -/
theorem valuation_zero_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    v (0 : K) < WithZero.exp (-1 : ℤ) := by
  simp

/-- The additive ball on which the local exponential series converges. -/
def expConvergenceAddSubgroupOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    AddSubgroup K where
  carrier := {x : K | v x < WithZero.exp (-1 : ℤ)}
  zero_mem' := valuation_zero_lt_exp_neg_one (K := K) v
  add_mem' := by
    intro x y hx hy
    exact valuation_add_lt_exp_neg_one_of_lt_exp_neg_one v hx hy
  neg_mem' := by
    intro x hx
    simpa using hx

/--
Characterizes `x ∈ expConvergenceAddSubgroupOfWithZeroValuation v` by the equivalent condition `v
x < WithZero.exp (-1 : ℤ)`.
-/
@[simp] theorem mem_expConvergenceAddSubgroupOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x : K} :
    x ∈ expConvergenceAddSubgroupOfWithZeroValuation v ↔
      v x < WithZero.exp (-1 : ℤ) :=
  Iff.rfl

/-- Every positive-degree exponential-series term lies in the open unit ball
on the normalized exponential convergence radius. -/
theorem valuation_expSeriesTermField_lt_one_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    {n : ℕ} (hn : n ≠ 0) :
    v (expSeriesTermField x hnK n) <
      (1 : WithZero (Multiplicative ℤ)) := by
  by_cases hx : x = 0
  · have hterm :
        expSeriesTermField x hnK n = 0 :=
      expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero hx hnK hn
    simp [hterm]
  · let y : Kˣ :=
      (Units.mk0 x hx) ^ n /
        Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
    have hxoneReal :
        1 < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
      ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
        (v := v) hx hvx
    have hxone : 1 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      exact_mod_cast hxoneReal
    have hpos :
        0 < (ofWithZeroValuation v).val y :=
      ofWithZeroValuation_val_pow_div_natCast_factorial_pos_of_one_lt
        (v := v) (p := p) (n := n) (Units.mk0 x hx)
        (hnK n) (hnval n) hxone hn
    have hlt :
        v (y : K) < (1 : WithZero (Multiplicative ℤ)) :=
      valuation_lt_one_of_ofWithZeroValuation_val_pos v y hpos
    simpa [y, expSeriesTermField, expSeriesTerm] using hlt

/-- Exponential partial sums split into the constant term and the positive
degree tail. -/
theorem expSeriesPartialSumField_succ_eq_one_add_tail
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (N : ℕ) :
    expSeriesPartialSumField x hnK (N + 1) =
      1 + ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
  calc
    expSeriesPartialSumField x hnK (N + 1) =
        (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1)) +
          expSeriesTermField x hnK 0 := by
      rw [expSeriesPartialSumField, Finset.sum_range_succ']
    _ = 1 + ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
      simp [add_comm]

/-- Every finite positive-degree tail of the exponential series lies in the
open unit ball on the normalized exponential convergence radius. -/
theorem valuation_expSeriesTailPartialSumField_lt_one_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ)) (N : ℕ) :
    v (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1)) <
      (1 : WithZero (Multiplicative ℤ)) := by
  exact
    v.map_sum_lt' (show (0 : WithZero (Multiplicative ℤ)) < 1 from zero_lt_one)
      (fun n _hn =>
        valuation_expSeriesTermField_lt_one_of_lt_exp_neg_one
          (v := v) (p := p) x hnK hnval hvx (Nat.succ_ne_zero n))

/-- The finite exponential partial sums are principal units after subtracting
the constant term. -/
theorem valuation_expSeriesPartialSumField_sub_one_lt_one_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ)) (N : ℕ) :
    v (expSeriesPartialSumField x hnK (N + 1) - 1) <
      (1 : WithZero (Multiplicative ℤ)) := by
  have hsplit :=
    expSeriesPartialSumField_succ_eq_one_add_tail x hnK N
  have htail :
      expSeriesPartialSumField x hnK (N + 1) - 1 =
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    rw [hsplit]
    abel
  rw [htail]
  exact
    valuation_expSeriesTailPartialSumField_lt_one_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx N

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

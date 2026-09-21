/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ExpConvergence
/-!
Establishes convergence and summability of the logarithm series on the nonarchimedean open unit
ball.
-/

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

/-- A summable logarithm series splits into its first term and the remaining
tail.  This is the algebraic first-term extraction used before proving the
logarithm identities. -/
theorem logOnePlusSeriesField_eq_self_add_tsum_succ_of_summable
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hs :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
      x + ∑' n : ℕ, signedLogSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs' : Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := hs
  calc
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
        ∑' n : ℕ, signedLogSeriesTermField x hnK n := by
      rfl
    _ = signedLogSeriesTermField x hnK 0 +
        ∑' n : ℕ, signedLogSeriesTermField x hnK (n + 1) :=
      hs'.tsum_eq_zero_add
    _ = x + ∑' n : ℕ, signedLogSeriesTermField x hnK (n + 1) := by
      simp

/-- A summable exponential series splits into the constant term `1` and the
positive-degree tail. -/
theorem expSeriesField_eq_one_add_tsum_succ_of_summable
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hs :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Summable (fun n : ℕ => expSeriesTermField x hnK n)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    expSeriesFieldOfWithZeroValuation v x hnK =
      1 + ∑' n : ℕ, expSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs' : Summable (fun n : ℕ => expSeriesTermField x hnK n) := hs
  calc
    expSeriesFieldOfWithZeroValuation v x hnK =
        ∑' n : ℕ, expSeriesTermField x hnK n := by
      rfl
    _ = expSeriesTermField x hnK 0 +
        ∑' n : ℕ, expSeriesTermField x hnK (n + 1) :=
      hs'.tsum_eq_zero_add
    _ = 1 + ∑' n : ℕ, expSeriesTermField x hnK (n + 1) := by
      simp

/-- Establishes the identity `logSeriesTermField x hnK n = 0`. -/
theorem logSeriesTermField_eq_zero_of_eq_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    logSeriesTermField x hnK n = 0 := by
  have hpow : (0 : K) ^ (n + 1) = 0 := by
    cases n with
    | zero => simp
    | succ n => simp
  simp [logSeriesTermField, hx, hpow]

/-- Establishes the identity `signedLogSeriesTermField x hnK n = 0`. -/
theorem signedLogSeriesTermField_eq_zero_of_eq_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    signedLogSeriesTermField x hnK n = 0 := by
  simp [signedLogSeriesTermField,
    logSeriesTermField_eq_zero_of_eq_zero hx hnK n]

/-- Establishes the identity `logOnePlusSeriesFieldOfWithZeroValuation v 0 hnK = 0`. -/
@[simp] theorem logOnePlusSeriesField_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logOnePlusSeriesFieldOfWithZeroValuation v 0 hnK = 0 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hzero :
      (fun n : ℕ => signedLogSeriesTermField (0 : K) hnK n) =
        fun _ : ℕ => (0 : K) := by
    funext n
    exact signedLogSeriesTermField_eq_zero_of_eq_zero rfl hnK n
  simp [logOnePlusSeriesFieldOfWithZeroValuation, hzero]

/-- Field-element logarithm-series terms tend to zero when `v x < 1`.  This is
the principal-unit form of the convergence estimate: unlike the unit-valued
version, it also covers `x = 0`. -/
theorem tendsto_zero_logSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => logSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => logSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact logSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_log_term_ofWithZeroValuation_of_pos
        (v := v) (p := p) (Units.mk0 x hx) hnK hnval hxpos
    simpa [logSeriesTermField, logSeriesTerm] using hunit

/-- Signed field-element logarithm-series terms tend to zero when `v x < 1`. -/
theorem tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => signedLogSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact signedLogSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_signed_log_term_ofWithZeroValuation_of_pos
        (v := v) (p := p) (Units.mk0 x hx) hnK hnval hxpos
    simpa [signedLogSeriesTermField, logSeriesTermField] using hunit

/-- In a complete nonarchimedean valuation topology, the field-element
logarithm-series terms are summable under the principal-unit condition
`v x < 1`. -/
theorem summable_logSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => logSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => logSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_logSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => logSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Summability of the signed field-element logarithm series under the
principal-unit condition `v x < 1`. -/
theorem summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element principal-unit logarithm series: the signed series has the
value supplied by `logOnePlusSeriesFieldOfWithZeroValuation`. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => signedLogSeriesTermField x hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) :=
    summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [logOnePlusSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- The formal power series `log(1+X)`, evaluated term by term at a
principal-unit parameter `x`, has sum equal to the local logarithm series. -/
theorem hasSum_powerSeries_log_eval_logOnePlusSeriesField
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
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
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  exact hsum.congr_fun fun n =>
    powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
      (K := K) x hnK n

/-- The one-variable formal logarithm, including the zero coefficient, has
the same field-valued sum as the local logarithm series. -/
theorem hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
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
      hasSum_powerSeries_log_eval_logOnePlusSeriesField
        (v := v) (p := p) x hnK hnval hvx hcomplete
  have hfull :=
    (hasSum_nat_add_iff
      (f := f)
      (g := logOnePlusSeriesFieldOfWithZeroValuation v x hnK) 1).1 htail
  simpa [f, PowerSeries.coeff_log] using hfull

/-- The left-axis part of the two-variable product-formula right side sums
to the field logarithm of the left input. -/
theorem hasSum_formalLogOnePlusLeftVariableLogSubst_monomialValue_pair
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
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
      (hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField
        (v := v) (p := p) x hnK hnval hvx hcomplete).congr_fun ?_
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

/-- The right-axis part of the two-variable product-formula right side sums
to the field logarithm of the right input. -/
theorem hasSum_formalLogOnePlusRightVariableLogSubst_monomialValue_pair
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
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
      (hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField
        (v := v) (p := p) y hnK hnval hvy hcomplete).congr_fun ?_
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

/-- The right-hand side `log(1+X)+log(1+Y)` of the formal product formula,
read as a field-valued monomial sum at `(x,y)`, sums to
`log(1+x)+log(1+y)`. -/
theorem hasSum_formalLogOnePlusProductRightSide_monomialValue_pair
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
    hasSum_formalLogOnePlusLeftVariableLogSubst_monomialValue_pair
      (v := v) (p := p) x y hnK hnval hvx hcomplete
  have hright :=
    hasSum_formalLogOnePlusRightVariableLogSubst_monomialValue_pair
      (v := v) (p := p) x y hnK hnval hvy hcomplete
  refine (hleft.add hright).congr_fun ?_
  intro d
  rw [formalLogOnePlusProductRightSide_coeff]
  ring

/-- The field-element finite logarithm polynomials converge to the
principal-unit logarithm-series value. -/
theorem tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => logOnePlusPartialSumField x hnK N) atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

/-- Signed field-element logarithm-series terms tend to zero under a
ramified denominator valuation hypothesis. -/
theorem tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => signedLogSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact signedLogSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_signed_log_term_ofWithZeroValuation_scaled_of_pos
        (v := v) (p := p) e (Units.mk0 x hx) hnK hnval hxpos
    simpa [signedLogSeriesTermField, logSeriesTermField] using hunit

/-- Summability of the signed field-element logarithm series under a
ramified denominator valuation hypothesis. -/
theorem summable_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
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
    Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element logarithm series has the same `tsum` value under a
ramified denominator valuation hypothesis. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
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
    HasSum (fun n : ℕ => signedLogSeriesTermField x hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) :=
    summable_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  simpa [logOnePlusSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- Field-element finite logarithm polynomials converge to the logarithm
series under a ramified denominator valuation hypothesis. -/
theorem tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
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
    Tendsto (fun N : ℕ => logOnePlusPartialSumField x hnK N) atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

/-- Termwise addition of two convergent field-element logarithm series.  This
is the right-hand analytic side of the product formula
`log((1 + x) * (1 + y)) = log(1 + x) + log(1 + y)`. -/
theorem hasSum_signedLogSeriesTermField_add_logOnePlusSeriesField
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
    HasSum
      (fun n : ℕ =>
        signedLogSeriesTermField x hnK n +
          signedLogSeriesTermField y hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK +
        logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    (hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete).add
      (hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
        (v := v) (p := p) y hnK hnval hvy hcomplete)

/-- Finite logarithm polynomials for two inputs add term by term. -/
theorem logOnePlusPartialSumField_add_eq_sum_add_terms
    (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    logOnePlusPartialSumField x hnK N +
        logOnePlusPartialSumField y hnK N =
      ∑ n ∈ Finset.range N,
        (signedLogSeriesTermField x hnK n +
          signedLogSeriesTermField y hnK n) := by
  simp [logOnePlusPartialSumField, Finset.sum_add_distrib]

/-- The sum of two finite field logarithm polynomials converges to the sum of
their logarithm-series values. -/
theorem tendsto_logOnePlusPartialSumField_add
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
      (fun N : ℕ =>
        logOnePlusPartialSumField x hnK N +
          logOnePlusPartialSumField y hnK N)
      atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK +
        logOnePlusSeriesFieldOfWithZeroValuation v y hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hx :=
    tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  have hy :=
    tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) y hnK hnval hvy hcomplete
  exact hx.add hy

/-- First-term extraction for the logarithm series on the principal-unit
convergence radius. -/
theorem logOnePlusSeriesField_eq_self_add_tsum_succ_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
      x + ∑' n : ℕ, signedLogSeriesTermField x hnK (n + 1) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    logOnePlusSeriesField_eq_self_add_tsum_succ_of_summable v x hnK
      (summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)

/-- A field-element logarithm-series term is nonzero when the input is
nonzero. -/
theorem logSeriesTermField_ne_zero_of_ne_zero
    {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    logSeriesTermField x hnK n ≠ 0 := by
  have hpow : x ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hx
  have hden :
      (((Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K) ≠ 0) :=
    (Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)).ne_zero
  simpa [logSeriesTermField] using div_ne_zero hpow hden

/-- Above the usual `1/(p-1)` threshold, each higher logarithm term has
strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_logSeriesTermField_lt_self_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (logSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ (n + 1) / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast
      (v := v) (p := p) (n := n + 1) xu (hnK n) (hnval n)]
    exact
      log_higher_term_integer_valuation_gt
        (p := p) (n := n + 1) (by omega) hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ (n + 1) / denom) hval
  simpa [xu, denom, logSeriesTermField] using hlt

/-- The signed higher logarithm terms have the same valuation estimate as the
unsigned terms. -/
theorem valuation_signedLogSeriesTermField_lt_self_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (signedLogSeriesTermField x hnK n) < v x := by
  have hlog :
      v (logSeriesTermField x hnK n) < v x :=
    valuation_logSeriesTermField_lt_self_of_inv_sub_one_lt
      (v := v) (p := p) (x := x) hx hnK hnval hthreshold hn
  have hval :
      v (signedLogSeriesTermField x hnK n) =
        v (logSeriesTermField x hnK n) := by
    rw [signedLogSeriesTermField, v.map_mul]
    simp
  rw [hval]
  exact hlog

/-- Every finite higher-degree logarithm tail has valuation strictly smaller
than the linear term above the `1/(p-1)` threshold. -/
theorem valuation_logHigherTailPartialSumField_lt_self_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_signedLogSeriesTermField_lt_self_of_inv_sub_one_lt
          (v := v) (p := p) (x := x) hx hnK hnval hthreshold
          (Nat.succ_ne_zero n))

/-- The higher-degree logarithm tail partial sums converge to
`log(1+x) - x`. -/
theorem tendsto_logHigherTailPartialSumField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1))
        atTop (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
        (v := v) (p := p) x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x)
        atTop
        (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1) := by
    funext N
    rw [logOnePlusPartialSumField, Finset.sum_range_succ']
    simp
  simpa [htail] using hsub

/-- The full higher-degree logarithm tail has valuation strictly smaller than
the linear term above the `1/(p-1)` threshold. -/
theorem valuation_logHigherTailField_lt_self_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_logHigherTailPartialSumField_ofWithZeroValuation_of_lt_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_logHigherTailPartialSumField_lt_self_of_inv_sub_one_lt
          (v := v) (p := p) (x := x) hx hnK hnval hthreshold N)

/-- Above the usual `1/(p-1)` threshold, `log(1+x)` has the same valuation as
the linear term `x`. -/
theorem valuation_logOnePlusSeriesField_eq_self_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x := by
  have htail :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
        v x :=
    valuation_logHigherTailField_lt_self_of_inv_sub_one_lt
      (v := v) (p := p) (x := x) hx hnK hnval hvx hthreshold hcomplete
  have hsplit :
      logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
        x + (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

/-- Above the usual `1/(p-1)` threshold, `log(1 + x)` is nonzero for
nonzero `x`. -/
theorem logOnePlusSeriesField_ne_zero_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK ≠ 0 := by
  intro hzero
  have hv :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x :=
    valuation_logOnePlusSeriesField_eq_self_of_inv_sub_one_lt
      (v := v) (p := p) (x := x) hx hnK hnval hvx hthreshold hcomplete
  rw [hzero, map_zero] at hv
  exact ((_root_.Valuation.ne_zero_iff v).2 hx) hv.symm

/-- On any part of the open unit ball satisfying the `1/(p-1)` threshold away
from zero, the field logarithm has trivial kernel. -/
theorem logOnePlusSeriesField_eq_zero_iff_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] {x : K}
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold : ∀ hx : x ≠ 0,
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK = 0 ↔ x = 0 := by
  constructor
  · intro hlog
    by_contra hx
    exact
      (logOnePlusSeriesField_ne_zero_of_inv_sub_one_lt
        (v := v) (p := p) (x := x) hx hnK hnval hvx (hthreshold hx)
        hcomplete) hlog
  · intro hx
    subst x
    simp

/-- Above the ramified threshold `e/(p-1)`, each higher logarithm term has
strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_logSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (logSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ (n + 1) / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_scaled
      (v := v) (p := p) (e := e) (n := n + 1) xu (hnK n) (hnval n)]
    exact
      log_higher_term_integer_valuation_gt_scaled
        (p := p) (e := e) (n := n + 1) (by omega) hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ (n + 1) / denom) hval
  simpa [xu, denom, logSeriesTermField] using hlt

/-- The signed higher logarithm terms have the same ramified valuation
estimate as the unsigned terms. -/
theorem valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (signedLogSeriesTermField x hnK n) < v x := by
  have hlog :
      v (logSeriesTermField x hnK n) < v x :=
    valuation_logSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hn
  have hval :
      v (signedLogSeriesTermField x hnK n) =
        v (logSeriesTermField x hnK n) := by
    rw [signedLogSeriesTermField, v.map_mul]
    simp
  rw [hval]
  exact hlog

/-- Every finite higher-degree logarithm tail has valuation strictly smaller
than the linear term above the ramified `e/(p-1)` threshold. -/
theorem valuation_logHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold
          (Nat.succ_ne_zero n))

/-- The higher-degree logarithm tail partial sums converge to
`log(1+x) - x` under a ramified denominator valuation hypothesis. -/
theorem tendsto_logHigherTailPartialSumField_ofWithZeroValuation_scaled_of_lt_one
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
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1))
        atTop (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (v := v) (p := p) e x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x)
        atTop
        (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1) := by
    funext N
    rw [logOnePlusPartialSumField, Finset.sum_range_succ']
    simp
  simpa [htail] using hsub

/-- The full higher-degree logarithm tail has valuation strictly smaller than
the linear term above the ramified `e/(p-1)` threshold. -/
theorem valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_logHigherTailPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (v := v) (p := p) e x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_logHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold N)

/-- Above the ramified `e/(p-1)` threshold, `log(1+x)` has the same valuation
as the linear term `x`. -/
theorem valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x := by
  have htail :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
        v x :=
    valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
  have hsplit :
      logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
        x + (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

/-- Above the ramified `e/(p-1)` threshold, `log(1 + x)` is nonzero for
nonzero `x`. -/
theorem logOnePlusSeriesField_ne_zero_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK ≠ 0 := by
  intro hzero
  have hv :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x :=
    valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
  rw [hzero, map_zero] at hv
  exact ((_root_.Valuation.ne_zero_iff v).2 hx) hv.symm

/-- On any part of the open unit ball satisfying the ramified `e/(p-1)`
threshold away from zero, the field logarithm has trivial kernel. -/
theorem logOnePlusSeriesField_eq_zero_iff_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    logOnePlusSeriesFieldOfWithZeroValuation v x hnK = 0 ↔ x = 0 := by
  constructor
  · intro hlog
    by_contra hx
    exact
      (logOnePlusSeriesField_ne_zero_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnK hnval hvx (hthreshold hx)
        hcomplete) hlog
  · intro hx
    subst x
    simp

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

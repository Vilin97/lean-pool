/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog
/-!
Packages the convergent logarithm and exponential series as additive and multiplicative
homomorphisms on their natural nonarchimedean domains.
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

/-- Finite logarithm polynomials of a first principal unit. -/
noncomputable def principalUnitLogPartialSumOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) : K :=
  logOnePlusPartialSumField (principalUnitSubOneOfWithZeroValuation v u) hnK N

/-- Establishes the identity `principalUnitLogPartialSumOfWithZeroValuation v u hnK 0 = 0`. -/
@[simp] theorem principalUnitLogPartialSum_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogPartialSumOfWithZeroValuation v u hnK 0 = 0 := by
  simp [principalUnitLogPartialSumOfWithZeroValuation]

/--
Establishes the identity `principalUnitLogPartialSumOfWithZeroValuation v u hnK 1 =
principalUnitSubOneOfWithZeroValuation v u`.
-/
@[simp] theorem principalUnitLogPartialSum_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogPartialSumOfWithZeroValuation v u hnK 1 =
      principalUnitSubOneOfWithZeroValuation v u := by
  simp [principalUnitLogPartialSumOfWithZeroValuation]

/--
Establishes the identity `principalUnitLogSeriesOfWithZeroValuation v (1 :
(CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) hnK = 0`.
-/
@[simp] theorem principalUnitLogSeries_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v
        (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (completeDVFOfWithZeroValuation v)) 1)
        hnK = 0 := by
  simp [principalUnitLogSeriesOfWithZeroValuation]

/-- Above the usual `1/(p-1)` threshold, the principal-unit logarithm has the
same valuation as the additive parameter `u - 1`. -/
theorem principalUnitLogSeries_valuation_eq_subOne_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0)
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (principalUnitLogSeriesOfWithZeroValuation v u hnK) =
      v (principalUnitSubOneOfWithZeroValuation v u) := by
  have hvx :
      v (principalUnitSubOneOfWithZeroValuation v u) <
        (1 : WithZero (Multiplicative ℤ)) :=
    principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  simpa [principalUnitLogSeriesOfWithZeroValuation] using
    valuation_logOnePlusSeriesField_eq_self_of_inv_sub_one_lt
      (v := v) (p := p)
      (x := principalUnitSubOneOfWithZeroValuation v u) hne
      hnK hnval hvx hthreshold hcomplete

/-- Above the usual `1/(p-1)` threshold, the principal-unit logarithm is
nonzero away from the identity. -/
theorem principalUnitLogSeries_ne_zero_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0)
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v u hnK ≠ 0 := by
  intro hzero
  have hv :
      v (principalUnitLogSeriesOfWithZeroValuation v u hnK) =
        v (principalUnitSubOneOfWithZeroValuation v u) :=
    principalUnitLogSeries_valuation_eq_subOne_of_inv_sub_one_lt
      (v := v) (p := p) u hnK hnval hne hthreshold hcomplete
  rw [hzero, map_zero] at hv
  exact ((_root_.Valuation.ne_zero_iff v).2 hne) hv.symm

/-- On a threshold-controlled principal-unit domain, the logarithm has kernel
exactly the identity element. -/
theorem principalUnitLogSeries_eq_zero_iff_subOne_eq_zero_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hthreshold : ∀ hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0,
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v u hnK = 0 ↔
      principalUnitSubOneOfWithZeroValuation v u = 0 := by
  constructor
  · intro hlog
    by_contra hne
    exact
      (principalUnitLogSeries_ne_zero_of_inv_sub_one_lt
        (v := v) (p := p) u hnK hnval hne (hthreshold hne) hcomplete)
        hlog
  · intro hsub
    simp [principalUnitLogSeriesOfWithZeroValuation, hsub]

/-- On a threshold-controlled principal-unit domain, the logarithm has kernel
exactly the identity. -/
theorem principalUnitLogSeries_eq_zero_iff_eq_one_of_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hthreshold : ∀ hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0,
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v u hnK = 0 ↔
      u = (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1) := by
  rw [principalUnitLogSeries_eq_zero_iff_subOne_eq_zero_of_inv_sub_one_lt
    (v := v) (p := p) u hnK hnval hthreshold hcomplete]
  exact principalUnitSubOne_eq_zero_iff_ofWithZeroValuation v u

/-- If `u - 1` lies in the normalized exponential convergence ball and the
logarithm threshold holds, then `Log(u)` also lies in the exponential
convergence ball. -/
theorem principalUnitLogSeries_val_lt_exp_neg_one_of_subOne_val_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0)
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ))
    (hsubExp :
      v (principalUnitSubOneOfWithZeroValuation v u) <
        WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (principalUnitLogSeriesOfWithZeroValuation v u hnK) <
      WithZero.exp (-1 : ℤ) := by
  have hv :
      v (principalUnitLogSeriesOfWithZeroValuation v u hnK) =
        v (principalUnitSubOneOfWithZeroValuation v u) :=
    principalUnitLogSeries_valuation_eq_subOne_of_inv_sub_one_lt
      (v := v) (p := p) u hnK hnval hne hthreshold hcomplete
  rw [hv]
  exact hsubExp

/-- On a threshold-controlled domain where `Log(u)` lies in the exponential
convergence ball, the composite `Exp(Log(u))` has kernel exactly the identity. -/
theorem principalUnitExpSeries_logSeries_eq_one_iff_eq_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvlogExp :
      v (principalUnitLogSeriesOfWithZeroValuation v u hnKlog) <
        WithZero.exp (-1 : ℤ))
    (hthreshold : ∀ hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0,
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p)
        (principalUnitLogSeriesOfWithZeroValuation v u hnKlog)
        hnKexp hnvalExp hvlogExp hcomplete =
        (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (completeDVFOfWithZeroValuation v)) 1) ↔
      u = (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1) := by
  rw [principalUnitExpSeries_eq_one_iff_ofWithZeroValuation
    (v := v) (p := p)
    (x := principalUnitLogSeriesOfWithZeroValuation v u hnKlog)
    hnKexp hnvalExp hvlogExp hcomplete]
  exact
    principalUnitLogSeries_eq_zero_iff_eq_one_of_inv_sub_one_lt
      (v := v) (p := p) u hnKlog hnvalLog hthreshold hcomplete

/-- On the common convergence and threshold domain, the composite
`Log(Exp(x))` has the same valuation as `x`. -/
theorem principalUnitLogSeries_expSeries_valuation_eq_self_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (principalUnitLogSeriesOfWithZeroValuation v
      (principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) x hnKexp hnvalExp hvx hcomplete) hnKlog) =
      v x := by
  let u :=
    principalUnitExpSeriesOfWithZeroValuation
      (v := v) (p := p) x hnKexp hnvalExp hvx hcomplete
  have hne : principalUnitSubOneOfWithZeroValuation v u ≠ 0 := by
    dsimp [u]
    exact
      principalUnitSubOne_expSeries_ne_zero_ofWithZeroValuation
        (v := v) (p := p) (x := x) hx hnKexp hnvalExp hvx hcomplete
  have hthresholdSub :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val
          (Units.mk0 (principalUnitSubOneOfWithZeroValuation v u) hne) :
          ℚ) := by
    dsimp [u]
    exact
      principalUnitSubOne_expSeries_threshold_ofWithZeroValuation
        (v := v) (p := p) (x := x) hx hnKexp hnvalExp hvx hthreshold
        hcomplete hne
  have hvlog :
      v (principalUnitLogSeriesOfWithZeroValuation v u hnKlog) =
        v (principalUnitSubOneOfWithZeroValuation v u) :=
    principalUnitLogSeries_valuation_eq_subOne_of_inv_sub_one_lt
      (v := v) (p := p) u hnKlog hnvalLog hne hthresholdSub hcomplete
  have hvsub :
      v (principalUnitSubOneOfWithZeroValuation v u) = v x := by
    dsimp [u]
    exact
      principalUnitSubOne_expSeries_valuation_eq_self_ofWithZeroValuation
        (v := v) (p := p) (x := x) hx hnKexp hnvalExp hvx hcomplete
  exact hvlog.trans hvsub

/-- On the common convergence and threshold domain, `Log(Exp(x))` is nonzero
for nonzero `x`. -/
theorem principalUnitLogSeries_expSeries_ne_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ≠ 0)
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hthreshold :
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v
      (principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) x hnKexp hnvalExp hvx hcomplete) hnKlog ≠ 0 := by
  intro hzero
  have hv :
      v (principalUnitLogSeriesOfWithZeroValuation v
        (principalUnitExpSeriesOfWithZeroValuation
          (v := v) (p := p) x hnKexp hnvalExp hvx hcomplete) hnKlog) =
        v x :=
    principalUnitLogSeries_expSeries_valuation_eq_self_ofWithZeroValuation
      (v := v) (p := p) (x := x) hx hnKexp hnvalExp hnKlog hnvalLog
      hvx hthreshold hcomplete
  rw [hzero, map_zero] at hv
  exact ((_root_.Valuation.ne_zero_iff v).2 hx) hv.symm

/-- On the common convergence and threshold domain, the composite
`Log ∘ Exp` has trivial kernel. -/
theorem principalUnitLogSeries_expSeries_eq_zero_iff_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] {x : K}
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hthreshold : ∀ hx : x ≠ 0,
      1 / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v
      (principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) x hnKexp hnvalExp hvx hcomplete) hnKlog = 0 ↔
      x = 0 := by
  constructor
  · intro hlog
    by_contra hx
    exact
      (principalUnitLogSeries_expSeries_ne_zero_ofWithZeroValuation
        (v := v) (p := p) (x := x) hx hnKexp hnvalExp hnKlog hnvalLog
        hvx (hthreshold hx) hcomplete) hlog
  · intro hx
    subst x
    have hExp :
        principalUnitExpSeriesOfWithZeroValuation
          (v := v) (p := p) (0 : K) hnKexp hnvalExp hvx hcomplete =
          (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            (completeDVFOfWithZeroValuation v)) 1) :=
      (principalUnitExpSeries_eq_one_iff_ofWithZeroValuation
        (v := v) (p := p) (x := (0 : K)) hnKexp hnvalExp hvx hcomplete).2 rfl
    simp [hExp]

/-- Product of principal units, rewritten as the `log(1 + z)` argument for
`z = (u - 1) + (w - 1) + (u - 1)(w - 1)`. -/
theorem principalUnitLogSeries_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      logOnePlusSeriesFieldOfWithZeroValuation v
        (principalUnitSubOneOfWithZeroValuation v u +
          principalUnitSubOneOfWithZeroValuation v w +
            principalUnitSubOneOfWithZeroValuation v u *
              principalUnitSubOneOfWithZeroValuation v w) hnK := by
  simp [principalUnitLogSeriesOfWithZeroValuation,
    principalUnitSubOne_mul_ofWithZeroValuation]

/-- Finite-logarithm-polynomial version of
`principalUnitLogSeries_mul_argument_ofWithZeroValuation`. -/
theorem principalUnitLogPartialSum_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N =
      logOnePlusPartialSumField
        (principalUnitSubOneOfWithZeroValuation v u +
          principalUnitSubOneOfWithZeroValuation v w +
            principalUnitSubOneOfWithZeroValuation v u *
              principalUnitSubOneOfWithZeroValuation v w) hnK N := by
  simp [principalUnitLogPartialSumOfWithZeroValuation,
    principalUnitSubOne_mul_ofWithZeroValuation]

/-- The logarithm series for a product of first principal units, written with
the explicit product argument `(u - 1) + (w - 1) + (u - 1)(w - 1)`. -/
theorem hasSum_principalUnitLogSeries_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        signedLogSeriesTermField
          (principalUnitSubOneOfWithZeroValuation v u +
            principalUnitSubOneOfWithZeroValuation v w +
              principalUnitSubOneOfWithZeroValuation v u *
                principalUnitSubOneOfWithZeroValuation v w) hnK n)
      (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hvu :
      v (principalUnitSubOneOfWithZeroValuation v u) <
        (1 : WithZero (Multiplicative ℤ)) :=
    principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  have hvw :
      v (principalUnitSubOneOfWithZeroValuation v w) <
        (1 : WithZero (Multiplicative ℤ)) :=
    principalUnitSubOne_val_lt_one_ofWithZeroValuation v w
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_mul_argument
      (v := v) (p := p)
      (principalUnitSubOneOfWithZeroValuation v u)
      (principalUnitSubOneOfWithZeroValuation v w)
      hnK hnval hvu hvw hcomplete
  simpa [principalUnitLogSeries_mul_argument_ofWithZeroValuation] using hsum

/-- Finite logarithm polynomials for a product of first principal units
converge to the product logarithm-series value, in the explicit
`(u - 1) + (w - 1) + (u - 1)(w - 1)` argument form. -/
theorem tendsto_principalUnitLogPartialSum_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        logOnePlusPartialSumField
          (principalUnitSubOneOfWithZeroValuation v u +
            principalUnitSubOneOfWithZeroValuation v w +
              principalUnitSubOneOfWithZeroValuation v u *
                principalUnitSubOneOfWithZeroValuation v w) hnK N)
      atTop (𝓝 (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_principalUnitLogSeries_mul_argument_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

/-- The principal-unit logarithm series has the value
`principalUnitLogSeriesOfWithZeroValuation`. -/
theorem hasSum_principalUnitLogSeries_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        signedLogSeriesTermField
          (principalUnitSubOneOfWithZeroValuation v u) hnK n)
      (principalUnitLogSeriesOfWithZeroValuation v u hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hvx :
      v (principalUnitSubOneOfWithZeroValuation v u) <
        (1 : WithZero (Multiplicative ℤ)) :=
    principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  simpa [principalUnitLogSeriesOfWithZeroValuation] using
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p)
      (principalUnitSubOneOfWithZeroValuation v u) hnK hnval hvx hcomplete

/-- The finite logarithm polynomials of a first principal unit converge to the
principal-unit logarithm-series value. -/
theorem tendsto_principalUnitLogPartialSum_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        principalUnitLogPartialSumOfWithZeroValuation v u hnK N)
      atTop (𝓝 (principalUnitLogSeriesOfWithZeroValuation v u hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hvx :
      v (principalUnitSubOneOfWithZeroValuation v u) <
        (1 : WithZero (Multiplicative ℤ)) :=
    principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  simpa [principalUnitLogPartialSumOfWithZeroValuation,
    principalUnitLogSeriesOfWithZeroValuation] using
    tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p)
      (principalUnitSubOneOfWithZeroValuation v u) hnK hnval hvx hcomplete

/-- The termwise sum of the two principal-unit logarithm series has value
`Log(u) + Log(w)`. -/
theorem hasSum_principalUnitLogSeries_add_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        signedLogSeriesTermField
            (principalUnitSubOneOfWithZeroValuation v u) hnK n +
          signedLogSeriesTermField
            (principalUnitSubOneOfWithZeroValuation v w) hnK n)
      (principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    (hasSum_principalUnitLogSeries_ofWithZeroValuation
      (v := v) (p := p) u hnK hnval hcomplete).add
      (hasSum_principalUnitLogSeries_ofWithZeroValuation
        (v := v) (p := p) w hnK hnval hcomplete)

/-- Finite logarithm polynomials for two principal units add term by term. -/
theorem principalUnitLogPartialSum_add_eq_sum_add_terms_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
        principalUnitLogPartialSumOfWithZeroValuation v w hnK N =
      ∑ n ∈ Finset.range N,
        (signedLogSeriesTermField
            (principalUnitSubOneOfWithZeroValuation v u) hnK n +
          signedLogSeriesTermField
            (principalUnitSubOneOfWithZeroValuation v w) hnK n) := by
  simpa [principalUnitLogPartialSumOfWithZeroValuation] using
    logOnePlusPartialSumField_add_eq_sum_add_terms
      (principalUnitSubOneOfWithZeroValuation v u)
      (principalUnitSubOneOfWithZeroValuation v w) hnK N

/-- The sum of two finite principal-unit logarithm polynomials converges to
`Log(u) + Log(w)`. -/
theorem tendsto_principalUnitLogPartialSum_add_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
          principalUnitLogPartialSumOfWithZeroValuation v w hnK N)
      atTop
      (𝓝 (principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hu :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) u hnK hnval hcomplete
  have hw :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) w hnK hnval hcomplete
  exact hu.add hw

/-- If two convergent field-valued sequences differ by a sequence converging
to zero, then their limits agree.  This is the topological endpoint used to
turn the formal logarithm product defect into actual additivity of the local
logarithm. -/
theorem eq_of_tendsto_sub_zero
    [TopologicalSpace K] [T2Space K] [ContinuousAdd K]
    {f g : ℕ → K} {a b : K}
    (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b))
    (hsub : Tendsto (fun n => f n - g n) atTop (𝓝 0)) :
    a = b := by
  have hfg :
      Tendsto (fun n => (f n - g n) + g n) atTop (𝓝 (0 + b)) :=
    hsub.add hg
  have hf' : Tendsto f atTop (𝓝 b) := by
    simpa [sub_eq_add_neg, add_assoc] using hfg
  exact tendsto_nhds_unique hf hf'

/-- The principal-unit logarithm product defect is the same as the field-level
defect for the two additive parameters `u - 1` and `w - 1`. -/
theorem principalUnitLogPartialSum_product_defect_eq_field_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N -
        (principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
          principalUnitLogPartialSumOfWithZeroValuation v w hnK N) =
      logOnePlusPartialSumField
          (principalUnitSubOneOfWithZeroValuation v u +
            principalUnitSubOneOfWithZeroValuation v w +
              principalUnitSubOneOfWithZeroValuation v u *
                principalUnitSubOneOfWithZeroValuation v w) hnK N -
        (logOnePlusPartialSumField
            (principalUnitSubOneOfWithZeroValuation v u) hnK N +
          logOnePlusPartialSumField
            (principalUnitSubOneOfWithZeroValuation v w) hnK N) := by
  rw [principalUnitLogPartialSum_mul_argument_ofWithZeroValuation]
  simp [principalUnitLogPartialSumOfWithZeroValuation]

/-- Principal-unit logarithm additivity reduced to the one remaining analytic
bridge: the difference between the product logarithm partial sums and the
sum of the two logarithm partial sums tends to zero.  The formal identity
proved above supplies the coefficient cancellation for this defect; this
lemma records the exact topological endpoint needed by the field-unit logarithm theorem. -/
theorem principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto
        (fun N : ℕ =>
          principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N -
            (principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
              principalUnitLogPartialSumOfWithZeroValuation v w hnK N))
        atTop (𝓝 (0 : K))) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hprod :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) (u * w) hnK hnval hcomplete
  have hadd :=
    tendsto_principalUnitLogPartialSum_add_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete
  exact
    eq_of_tendsto_sub_zero
      (K := K) hprod hadd hdefect

/-- Field-level version of
`principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation`.
After this reduction, the remaining analytic work for the field-unit logarithm theorem is to
prove that the displayed field-level defect tends to zero from the formal
coefficient identity. -/
theorem principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto
        (fun N : ℕ =>
          logOnePlusPartialSumField
              (principalUnitSubOneOfWithZeroValuation v u +
                principalUnitSubOneOfWithZeroValuation v w +
                  principalUnitSubOneOfWithZeroValuation v u *
                    principalUnitSubOneOfWithZeroValuation v w) hnK N -
            (logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u) hnK N +
              logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v w) hnK N))
        atTop (𝓝 (0 : K))) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  apply principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation
    (v := v) (p := p) u w hnK hnval hcomplete
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  simpa [principalUnitLogPartialSum_product_defect_eq_field_defect_ofWithZeroValuation
    (v := v) u w hnK] using hdefect

/-- Principal-unit logarithm as a multiplicative homomorphism, conditional only
on the remaining field-level defect convergence.  The codomain is written as
`Multiplicative K`, so multiplication there is addition in the local field. -/
noncomputable def principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K))) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1 →*
      Multiplicative K where
  toFun u := Multiplicative.ofAdd
    (principalUnitLogSeriesOfWithZeroValuation v u hnK)
  map_one' := by
    simp
  map_mul' u w := by
    change
      Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK) =
        Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v u hnK +
            principalUnitLogSeriesOfWithZeroValuation v w hnK)
    rw [principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete (hdefect u w)]

/--
Establishes the identity `Multiplicative.toAdd
(principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation (v := v) (p := p) hnK hnval
hcomplete hdefect u) = principalUnitLogSeriesOfWithZeroValuation v u hnK`.
-/
@[simp] theorem principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K)))
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1) :
    Multiplicative.toAdd
        (principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
          (v := v) (p := p) hnK hnval hcomplete hdefect u) =
      principalUnitLogSeriesOfWithZeroValuation v u hnK := by
  rfl

/-- A homomorphism on first principal units extends to the three-factor
decomposition of `Kˣ` by killing the Teichmuller root factor and the
uniformizer factor.  This is the algebraic extension shape used in the field-unit logarithm
  theorem after the principal-unit logarithm has been proved additive. -/
noncomputable def fieldUnitDecompositionLogHomOfPrincipalUnitHom
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →*
      Multiplicative A where
  toFun z := φ z.1.2
  map_one' := by
    simp
  map_mul' z w := by
    simp

/--
The defining evaluation formula for `fieldUnitDecompositionLogHomOfPrincipalUnitHom` is
`fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ z = φ z.1.2`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (z : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ z = φ z.1.2 :=
  rfl

/--
Establishes the identity `fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ ((ζ, 1), (1 :
Multiplicative ℤ)) = 1`.
-/
theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_root
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (ζ : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ
        ((ζ, 1), (1 : Multiplicative ℤ)) = 1 := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u), (1 : Multiplicative ℤ)) = φ
u`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ
        (((1 :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
          (1 : Multiplicative ℤ)) = φ u := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), (1 :
(CompleteDVF.higherPrincipalUnitGroup F) 1)), Multiplicative.ofAdd m) = 1`.
-/
theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (m : ℤ) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ
        (((1 :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
              F) 1)),
          Multiplicative.ofAdd m) = 1 := by
  simp

/-- A field-unit logarithm homomorphism obtained from a chosen the
uniformizer–residue–principal-unit decomposition
three-factor decomposition and a principal-unit logarithm homomorphism. -/
noncomputable def fieldUnitLogHomOfPrincipalUnitHom
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A) :
    Kˣ →* Multiplicative A :=
  (fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ).comp
    e.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomOfPrincipalUnitHom` is
`fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ ((e.symm x).1.2)`.
-/
@[simp] theorem fieldUnitLogHomOfPrincipalUnitHom_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A) (x : Kˣ) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x =
      φ ((e.symm x).1.2) :=
  rfl

/-- Establishes the identity `fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ z.1.2`. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_apply_of_decomposition_eq
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (z : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F)
    {x : Kˣ} (hx : e z = x) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ z.1.2 := by
  subst x
  simp

/-- Establishes the identity `fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = 1`. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_root_decomposition
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (ζ : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
    {x : Kˣ}
    (hx : e ((ζ, 1), (1 : Multiplicative ℤ)) = x) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = 1 := by
  simpa using
    fieldUnitLogHomOfPrincipalUnitHom_apply_of_decomposition_eq
      (F := F) e φ ((ζ, 1), (1 : Multiplicative ℤ)) hx

/-- Establishes the identity `fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ u`. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_eq_of_principal_decomposition
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) {x
      : Kˣ}
    (hx :
      e (((1 :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
          u), (1 : Multiplicative ℤ)) = x) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ u := by
  simpa using
    fieldUnitLogHomOfPrincipalUnitHom_apply_of_decomposition_eq
      (F := F) e φ
      (((1 :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
        (1 : Multiplicative ℤ)) hx

/-- Establishes the identity `fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = 1`. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_uniformizer_decomposition
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (m : ℤ) {x : Kˣ}
    (hx :
      e (((1 :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
          (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)),
        Multiplicative.ofAdd m) = x) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = 1 := by
  simpa using
    fieldUnitLogHomOfPrincipalUnitHom_apply_of_decomposition_eq
      (F := F) e φ
      (((1 :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
          (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)),
        Multiplicative.ofAdd m) hx

/-- public root-factor value of the field-unit logarithm constructed from
the complete-DVF uniformizer decomposition. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_completeDVF_root
    (F : CompleteDVF K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (ζ : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    fieldUnitLogHomOfPrincipalUnitHom
        (F := F)
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ) φ
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ)) = 1 := by
  apply fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_root_decomposition
    (F := F)
    (e :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ)
    (φ := φ) (ζ := ζ)
  simp [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]

/-- public principal-unit value of the field-unit logarithm constructed
from the complete-DVF uniformizer decomposition. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_eq_of_completeDVF_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitLogHomOfPrincipalUnitHom
        (F := F)
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ) φ
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (u : F.valuationSubringˣ)) = φ u := by
  apply fieldUnitLogHomOfPrincipalUnitHom_eq_of_principal_decomposition
    (F := F)
    (e :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ)
    (φ := φ) (u := u)
  simp [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]

/-- public uniformizer value of the field-unit logarithm constructed from
the complete-DVF uniformizer decomposition: the selected uniformizer is sent to
zero, written as `1` in `Multiplicative A`. -/
theorem fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_completeDVF_uniformizer
    (F : CompleteDVF K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative A) :
    fieldUnitLogHomOfPrincipalUnitHom
        (F := F)
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ) φ
        (Units.mk0 (π : K) hπ.ne_zero) = 1 := by
  apply fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_uniformizer_decomposition
    (F := F)
    (e :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ)
    (φ := φ) (m := 1)
  simp [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]

/-- Conditional field-unit logarithm for the field-unit logarithm theorem: once the remaining
field-level defect convergence proves additivity on `U¹`, the resulting
principal-unit logarithm extends over a chosen field-unit decomposition by
sending the root and uniformizer factors to zero. -/
noncomputable def fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    (e :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors
          (completeDVFOfWithZeroValuation v) ≃* Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K))) :
    Kˣ →* Multiplicative K :=
  fieldUnitLogHomOfPrincipalUnitHom
    (F := completeDVFOfWithZeroValuation v) e
    (principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
      (v := v) (p := p) hnK hnval hcomplete hdefect)

/-- public conditional logarithm on `Kˣ`, using the complete-DVF
uniformizer decomposition supplied by
  the uniformizer–residue–principal-unit decomposition.  This is the same
construction as `fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation`,
with the decomposition chosen canonically from a uniformizer. -/
noncomputable def fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K))) :
    Kˣ →* Multiplicative K :=
  fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
    (v := v) (p := p)
    (e :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        (completeDVFOfWithZeroValuation v) hπ)
    hnK hnval hcomplete hdefect

/-- On first principal units, the public conditional field-unit logarithm
agrees with the principal-unit logarithm. -/
theorem fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_principal
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K)))
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1) :
    fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
        (v := v) (p := p) hπ hnK hnval hcomplete hdefect
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom
          (completeDVFOfWithZeroValuation v) (u : _)) =
      principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
        (v := v) (p := p) hnK hnval hcomplete hdefect u := by
  simpa [fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer,
    fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation] using
    fieldUnitLogHomOfPrincipalUnitHom_eq_of_completeDVF_principal
      (F := completeDVFOfWithZeroValuation v) hπ
      (principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
        (v := v) (p := p) hnK hnval hcomplete hdefect) u

/-- Additive-value form of the preceding principal-unit evaluation: on `U¹`,
the public field-unit logarithm is the principal-unit logarithm series. -/
theorem fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_principal_toAdd
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K)))
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1) :
    Multiplicative.toAdd
        (fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
          (v := v) (p := p) hπ hnK hnval hcomplete hdefect
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom
            (completeDVFOfWithZeroValuation v) (u : _))) =
      principalUnitLogSeriesOfWithZeroValuation v u hnK := by
  rw [fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_principal
    (v := v) (p := p) hπ hnK hnval hcomplete hdefect u]
  rfl

/-- Teichmuller root factors have logarithm zero for the public
conditional field-unit logarithm. -/
theorem fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_root
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K)))
    (ζ :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup
        (completeDVFOfWithZeroValuation v)) :
    fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
        (v := v) (p := p) hπ hnK hnval hcomplete hdefect
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom
          (completeDVFOfWithZeroValuation v) (ζ : _)) = 1 := by
  simpa [fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer,
    fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation] using
    fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_completeDVF_root
      (F := completeDVFOfWithZeroValuation v) hπ
      (principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
        (v := v) (p := p) hnK hnval hcomplete hdefect) ζ

/-- Additive-value form of the Teichmuller-root evaluation: root factors have
field-unit logarithm `0`. -/
theorem fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_root_toAdd
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K)))
    (ζ :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup
        (completeDVFOfWithZeroValuation v)) :
    Multiplicative.toAdd
        (fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
          (v := v) (p := p) hπ hnK hnval hcomplete hdefect
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom
            (completeDVFOfWithZeroValuation v) (ζ : _))) = 0 := by
  rw [fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_root
    (v := v) (p := p) hπ hnK hnval hcomplete hdefect ζ]
  rfl

/-- The selected uniformizer has logarithm zero for the public conditional
field-unit logarithm. -/
theorem fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_uniformizer
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K))) :
    fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
        (v := v) (p := p) hπ hnK hnval hcomplete hdefect
        (Units.mk0 (π : K) hπ.ne_zero) = 1 := by
  simpa [fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer,
    fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation] using
    fieldUnitLogHomOfPrincipalUnitHom_eq_one_of_completeDVF_uniformizer
      (F := completeDVFOfWithZeroValuation v) hπ
      (principalUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuation
        (v := v) (p := p) hnK hnval hcomplete hdefect)

/-- Additive-value form of the uniformizer evaluation: the selected
uniformizer has field-unit logarithm `0`. -/
theorem fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_uniformizer_toAdd
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    [Finite (completeDVFOfWithZeroValuation v).residueField]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K))) :
    Multiplicative.toAdd
        (fieldUnitLogSeriesHomOfTendstoFieldDefectOfWithZeroValuationUniformizer
          (v := v) (p := p) hπ hnK hnval hcomplete hdefect
          (Units.mk0 (π : K) hπ.ne_zero)) = 0 := by
  rw [fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer_uniformizer
    (v := v) (p := p) hπ hnK hnval hcomplete hdefect]
  rfl

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

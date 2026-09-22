/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog.Core
/-!
Packages inverse exponential and logarithm series as equivalences of deep principal units.
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

/-- Endpoint package for the deep exponential–logarithm equivalence from the exact inverse
equalities:
once the two evaluated composites are proved to be identities on `m^n` and
`U^n`, the exponential and logarithm maps give the underlying equivalence
between the two source and target groups.  The group-homomorphism structure is supplied
separately by the logarithm additivity and exponential additivity results. -/
noncomputable def principalUnitExpLogEquivOfExactOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (hlog_exp :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) =
        a)
    (hexp_log :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hcomplete u) =
        u) :
    ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n where
  toFun a :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete a
  invFun u :=
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKlog hnvalLog hcomplete u
  left_inv a := hlog_exp a
  right_inv u := hexp_log u

/-- Endpoint package for the deep exponential–logarithm equivalence as the actual group isomorphism:
if the evaluated composites are identities, then the source and target groups are
multiplicatively isomorphic after wrapping the additive ideal by
`Multiplicative`.  The multiplicativity of the forward map is supplied by the
scaled exponential additivity proved above. -/
noncomputable def principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Algebra ℚ K]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (hlog_exp :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) =
        a)
    (hexp_log :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hcomplete u) =
        u) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n where
  toFun a :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete a.toAdd
  invFun u :=
    Multiplicative.ofAdd
      (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hcomplete u)
  left_inv a := by
    apply Multiplicative.ext
    simpa using hlog_exp a.toAdd
  right_inv u := by
    simpa using hexp_log u
  map_mul' a b := by
    simpa using
      principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hcomplete a.toAdd b.toAdd

/-- Endpoint package for the deep exponential–logarithm equivalence from finite quotient
identities: if the
two evaluated composites agree with the identity in every quotient
`O / m^r` for `r ≥ n`, then the underlying source and target groups `m^n` and `U^n` are
equivalent. -/
noncomputable def principalUnitExpLogEquivOfIdealQuotientGeOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (hlog_exp_quot :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        ∀ r : ℕ, n ≤ r →
          Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKlog hnvalLog hcomplete
                (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKexp hnvalExp hcomplete a) :
                (completeDVFOfWithZeroValuation v).valuationSubring) =
            Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (a : (completeDVFOfWithZeroValuation v).valuationSubring))
    (hexp_log_quot :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n,
        ∀ r : ℕ, n ≤ r →
          Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKexp hnvalExp hcomplete
                  (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                    (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                    hnKlog hnvalLog hcomplete u) :
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                  (completeDVFOfWithZeroValuation v)) n) :
                (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
                (completeDVFOfWithZeroValuation v).valuationSubring) =
            Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
                (completeDVFOfWithZeroValuation v).valuationSubring))) :
    ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n :=
  principalUnitExpLogEquivOfExactOfWithZeroValuationScaled
    (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
    hnKexp hnvalExp hnKlog hnvalLog hcomplete
    (fun a =>
      principalUnitLogSeries_expSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hnKlog hnvalLog hcomplete a (hlog_exp_quot a))
    (fun u =>
      principalUnitExpSeries_logSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hnKexp hnvalExp hcomplete u (hexp_log_quot u))

/-- Endpoint package for the deep exponential–logarithm equivalence as a multiplicative
equivalence, from
finite quotient identities for both evaluated composites. -/
noncomputable def principalUnitExpLogMulEquivOfIdealQuotientGeOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Algebra ℚ K]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (hlog_exp_quot :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        ∀ r : ℕ, n ≤ r →
          Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKlog hnvalLog hcomplete
                (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKexp hnvalExp hcomplete a) :
                (completeDVFOfWithZeroValuation v).valuationSubring) =
            Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (a : (completeDVFOfWithZeroValuation v).valuationSubring))
    (hexp_log_quot :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n,
        ∀ r : ℕ, n ≤ r →
          Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKexp hnvalExp hcomplete
                  (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                    (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                    hnKlog hnvalLog hcomplete u) :
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                  (completeDVFOfWithZeroValuation v)) n) :
                (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
                (completeDVFOfWithZeroValuation v).valuationSubring) =
            Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
              (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
                (completeDVFOfWithZeroValuation v).valuationSubring))) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n :=
  principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled
    (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
    hnKexp hnvalExp hnKlog hnvalLog hcomplete
    (fun a =>
      principalUnitLogSeries_expSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hnKlog hnvalLog hcomplete a (hlog_exp_quot a))
    (fun u =>
      principalUnitExpSeries_logSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hnKexp hnvalExp hcomplete u (hexp_log_quot u))

/-- Endpoint package for the deep exponential–logarithm equivalence from direct all-level defect
membership:
if the two evaluated formal composites differ from the identity by elements of
every finite maximal-ideal power `m^r` for `r ≥ n`, then the underlying source and target groups
  `m^n` and `U^n` are equivalent. -/
noncomputable def principalUnitExpLogEquivOfSubMemGeOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (hlog_exp_mem :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        ∀ r : ℕ, n ≤ r →
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKlog hnvalLog hcomplete
                (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKexp hnvalExp hcomplete a) :
              (completeDVFOfWithZeroValuation v).valuationSubring) -
            (a : (completeDVFOfWithZeroValuation v).valuationSubring) ∈
              (completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
    (hexp_log_mem :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n,
        ∀ r : ℕ, n ≤ r →
          (((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKexp hnvalExp hcomplete
                (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKlog hnvalLog hcomplete u) :
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                (completeDVFOfWithZeroValuation v)) n) :
              (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
              (completeDVFOfWithZeroValuation v).valuationSubring) -
            (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
              (completeDVFOfWithZeroValuation v).valuationSubring)) ∈
              (completeDVFOfWithZeroValuation v).maximalIdeal ^ r) :
    ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n :=
  principalUnitExpLogEquivOfExactOfWithZeroValuationScaled
    (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
    hnKexp hnvalExp hnKlog hnvalLog hcomplete
    (fun a =>
      principalUnitLogSeries_expSeries_eq_self_of_sub_mem_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hnKlog hnvalLog hcomplete a (hlog_exp_mem a))
    (fun u =>
      principalUnitExpSeries_logSeries_eq_self_of_sub_mem_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hnKexp hnvalExp hcomplete u (hexp_log_mem u))

/-- Endpoint package for the deep exponential–logarithm equivalence as a multiplicative
equivalence, from the
same all-level defect-membership hypotheses.  This is the final reusable shape
for the principal-unit exponential/logarithm isomorphism once the remaining analytic
defect estimates are available. -/
noncomputable def principalUnitExpLogMulEquivOfSubMemGeOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Algebra ℚ K]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (hlog_exp_mem :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        ∀ r : ℕ, n ≤ r →
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKlog hnvalLog hcomplete
                (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKexp hnvalExp hcomplete a) :
              (completeDVFOfWithZeroValuation v).valuationSubring) -
            (a : (completeDVFOfWithZeroValuation v).valuationSubring) ∈
              (completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
    (hexp_log_mem :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n,
        ∀ r : ℕ, n ≤ r →
          (((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKexp hnvalExp hcomplete
                (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                  (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                  hnKlog hnvalLog hcomplete u) :
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                (completeDVFOfWithZeroValuation v)) n) :
              (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
              (completeDVFOfWithZeroValuation v).valuationSubring) -
            (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
              (completeDVFOfWithZeroValuation v).valuationSubring)) ∈
              (completeDVFOfWithZeroValuation v).maximalIdeal ^ r) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) n :=
  principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled
    (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
    hnKexp hnvalExp hnKlog hnvalLog hcomplete
    (fun a =>
      principalUnitLogSeries_expSeries_eq_self_of_sub_mem_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hnKlog hnvalLog hcomplete a (hlog_exp_mem a))
    (fun u =>
      principalUnitExpSeries_logSeries_eq_self_of_sub_mem_ge_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hnKexp hnvalExp hcomplete u (hexp_log_mem u))

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

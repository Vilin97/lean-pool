/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitExp
/-!
Restricts the logarithm series to principal units and places its values in the corresponding
additive ideal.
-/

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitOneAddOfMemPowSubgroup_val →
    principalUnitOneAddOfMemPowSubgroup_val

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitOneAddOfMemPow_val →
    principalUnitOneAddOfMemPow_val

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotMk →
    principalUnitSuccQuotMk

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotOfIdealPow →
    principalUnitSuccQuotOfIdealPow

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotOfIdealPow_apply →
    principalUnitSuccQuotOfIdealPow_apply

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ →
    principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ


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

/-- The logarithm-series value of a first principal unit `u`, defined as the
series for `log(1 + (u - 1))`. -/
noncomputable def principalUnitLogSeriesOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) : K :=
  logOnePlusSeriesFieldOfWithZeroValuation v
    (principalUnitSubOneOfWithZeroValuation v u) hnK

/-- Sharp ramified endpoint form of the logarithm: if `u ∈ U^n` and
`n > e/(p-1)`, then `Log(u)` lies in `m^n`. -/
noncomputable def principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) n) :
    ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation v).valuationSubring) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let aSub : F.valuationSubring :=
    ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  let x : K := (aSub : K)
  have haMem : aSub ∈ F.maximalIdeal ^ n := by
    simpa [aSub] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) n (u : F.valuationSubringˣ)).1 u.property
  have hxthreshold :
      ∀ hx : x ≠ 0,
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
    intro hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n aSub haMem hx
    exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
  have haMemOne : aSub ∈ F.maximalIdeal := by
    have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ 1 :=
      Ideal.pow_le_pow_right hn
    simpa [pow_one] using hle haMem
  have hxlt : v x < (1 : WithZero (Multiplicative ℤ)) := by
    have hbound := (CompleteDVF.mem_maximalIdeal_iff F aSub).1 haMemOne
    change v (aSub : K) < 1 at hbound
    exact hbound
  have hbLe :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) ≤
        (1 : WithZero (Multiplicative ℤ)) := by
    by_cases hx : x = 0
    · simp [x, hx]
    · have hv :
          v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x :=
        valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval
          hxlt (hxthreshold hx) hcomplete
      have hxInt : v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
        le_of_lt hxlt
      simpa [hv] using hxInt
  let b : F.valuationSubring :=
    ⟨logOnePlusSeriesFieldOfWithZeroValuation v x hnK,
      (CompleteDVF.mem_valuationSubring_iff F
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)).2
        (by
          change v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) ≤ 1
          exact hbLe)⟩
  have hbmem : b ∈ F.maximalIdeal ^ n := by
    apply
      mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
        (v := v) (π := π) hπ hπval n b
    intro hbne
    by_cases hx : x = 0
    · have hbzero : (b : K) = 0 := by
        simp [b, x, hx]
      exact False.elim (hbne hbzero)
    · have hv :
          v (b : K) = v x := by
        simpa [b] using
          valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
            (v := v) (p := p) e (x := x) hx hnK hnval
            hxlt (hxthreshold hx) hcomplete
      have hge :
          (n : ℤ) ≤
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simpa [F, x] using
          ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
            (v := v) (π := π) hπ hπval n aSub haMem hx
      have hvaleq :
          (ofWithZeroValuation v).val (Units.mk0 (b : K) hbne) =
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simp [ofWithZeroValuation_val, hv]
      rw [hvaleq]
      exact hge
  exact ⟨b, hbmem⟩

/-- On the successive additive quotient `m^n/m^(n+1)`, the composite
`Log ∘ Exp` induced by the ramified endpoint maps is the identity. -/
theorem principalUnitLogSeries_expSeries_maximalIdealPowSuccQuot_eq_self_ofWithZeroValuationScaled
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
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    (completeDVFOfWithZeroValuation v).toDVF.maximalIdealPowSuccQuotMk n
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a)) =
      (completeDVFOfWithZeroValuation v).toDVF.maximalIdealPowSuccQuotMk n a := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let expu : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete a
  let l : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKlog hnvalLog hcomplete expu
  rw [DVF.maximalIdealPowSuccQuotMk_eq_iff]
  change ((l : F.valuationSubring) - (a : F.valuationSubring)) ∈
    F.maximalIdeal ^ (n + 1)
  refine
    logOnePlusSeries_expSeries_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow
      (v := v) (p := p) e n (π := π) hπ hπval hlevel
      hnKexp hnvalExp hnKlog hnvalLog hcomplete
      (a := (a : F.valuationSubring))
      (b := (l : F.valuationSubring) - (a : F.valuationSubring))
      a.property ?_
  simp [l, expu, principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled,
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled, F]

/-- On the successive principal-unit quotient `U^n/U^(n+1)`, the composite
`Exp ∘ Log` induced by the ramified endpoint maps is the identity. -/
theorem principalUnitExpSeries_logSeries_principalUnitSuccQuot_eq_self_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) n) :
    principalUnitSuccQuotMk
        (completeDVFOfWithZeroValuation v) n
        (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hcomplete u)) =
      principalUnitSuccQuotMk
        (completeDVFOfWithZeroValuation v) n u := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let loga : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKlog hnvalLog hcomplete u
  let expLogu : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
    n :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete loga
  have class_eq_subOne :
      ∀ (w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n)
        (w0 : F.valuationSubring),
        w0 = ((w : F.valuationSubringˣ) : F.valuationSubring) - 1 →
        ∀ hw0 : w0 ∈ F.maximalIdeal ^ n,
        principalUnitSuccQuotMk F n w =
          principalUnitSuccQuotOfIdealPow
            F n hn ⟨w0, hw0⟩ := by
    intro w w0 hw0eq hw0
    subst w0
    rw [principalUnitSuccQuotOfIdealPow_apply]
    congr 1
    dsimp
    apply Subtype.ext
    rw [principalUnitOneAddOfMemPowSubgroup_val]
    apply Units.ext
    rw [principalUnitOneAddOfMemPow_val]
    ring
  let a0 : F.valuationSubring :=
    ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  have ha0 : a0 ∈ F.maximalIdeal ^ n := by
    dsimp [a0]
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
      (F := F) n (u : F.valuationSubringˣ)).1 u.property
  let a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
    ⟨a0, ha0⟩
  let b0 : F.valuationSubring :=
    ((expLogu : F.valuationSubringˣ) : F.valuationSubring) - 1
  have hb0 : b0 ∈ F.maximalIdeal ^ n := by
    dsimp [b0]
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
      (F := F) n (expLogu : F.valuationSubringˣ)).1 expLogu.property
  let b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
    ⟨b0, hb0⟩
  have hdiff : (b : F.valuationSubring) - (a : F.valuationSubring) ∈
      F.maximalIdeal ^ (n + 1) := by
    change b0 - a0 ∈ F.maximalIdeal ^ (n + 1)
    refine
      expSeries_logOnePlusSeries_sub_one_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow
        (v := v) (p := p) e n (π := π) hπ hπval hlevel
        hnKlog hnvalLog hnKexp hnvalExp hcomplete
        (a := a0) (b := b0 - a0) ha0 ?_
    simp [a0, b0, expLogu, loga,
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled,
      principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled, F]
  rw [class_eq_subOne expLogu b0 rfl hb0, class_eq_subOne u a0 rfl ha0]
  exact
    principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
      F n hn b a hdiff

/-- The deep exponential–logarithm equivalence, additive finite-level defect: the evaluated
composite
`Log ∘ Exp` differs from the identity by an element of `m^(n+1)`.  This is the
first nontrivial finite quotient identity behind the separatedness endpoint. -/
theorem
  principalUnitLogSeries_expSeries_sub_self_mem_maximalIdeal_pow_succ_ofWithZeroValuationScaled
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
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) :
        (completeDVFOfWithZeroValuation v).valuationSubring) -
      (a : (completeDVFOfWithZeroValuation v).valuationSubring) ∈
        (completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let expu : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete a
  let l : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKlog hnvalLog hcomplete expu
  change ((l : F.valuationSubring) - (a : F.valuationSubring)) ∈
    F.maximalIdeal ^ (n + 1)
  refine
    logOnePlusSeries_expSeries_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow
      (v := v) (p := p) e n (π := π) hπ hπval hlevel
      hnKexp hnvalExp hnKlog hnvalLog hcomplete
      (a := (a : F.valuationSubring))
      (b := (l : F.valuationSubring) - (a : F.valuationSubring))
      a.property ?_
  simp [l, expu, principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled,
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled, F]

/-- The deep exponential–logarithm equivalence, additive finite quotient identity at level `n+1`:
`Log ∘ Exp` is the identity in `O / m^(n+1)`. -/
theorem principalUnitLogSeries_expSeries_idealQuotient_succ_eq_self_ofWithZeroValuationScaled
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
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1))
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) :
          (completeDVFOfWithZeroValuation v).valuationSubring) =
      Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1))
        (a : (completeDVFOfWithZeroValuation v).valuationSubring) := by
  exact
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1))
      (x :=
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) :
          (completeDVFOfWithZeroValuation v).valuationSubring))
      (y := (a : (completeDVFOfWithZeroValuation v).valuationSubring))).2
      (principalUnitLogSeries_expSeries_sub_self_mem_maximalIdeal_pow_succ_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hnKlog hnvalLog hcomplete a)

/-- The deep exponential–logarithm equivalence, multiplicative finite-level defect: the evaluated
composite `Exp ∘ Log` differs from the identity by an element of `m^(n+1)` on
underlying valuation-ring units. -/
theorem
  principalUnitExpSeries_logSeries_sub_self_mem_maximalIdeal_pow_succ_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) n) :
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
        (completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let loga : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKlog hnvalLog hcomplete u
  let expLogu : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
    n :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete loga
  let a0 : F.valuationSubring :=
    ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  have ha0 : a0 ∈ F.maximalIdeal ^ n := by
    dsimp [a0]
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
      (F := F) n (u : F.valuationSubringˣ)).1 u.property
  let b0 : F.valuationSubring :=
    ((expLogu : F.valuationSubringˣ) : F.valuationSubring) - 1
  have hdiff : b0 - a0 ∈ F.maximalIdeal ^ (n + 1) := by
    refine
      expSeries_logOnePlusSeries_sub_one_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow
        (v := v) (p := p) e n (π := π) hπ hπval hlevel
        hnKlog hnvalLog hnKexp hnvalExp hcomplete
        (a := a0) (b := b0 - a0) ha0 ?_
    simp [a0, b0, expLogu, loga,
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled,
      principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled, F]
  have hsub :
      ((expLogu : F.valuationSubringˣ) : F.valuationSubring) -
        ((u : F.valuationSubringˣ) : F.valuationSubring) =
      b0 - a0 := by
    simp [a0, b0]
  simpa [F, expLogu] using hsub ▸ hdiff

/-- The deep exponential–logarithm equivalence, multiplicative finite quotient identity at level
`n+1`:
`Exp ∘ Log` is the identity in `O / m^(n+1)` after forgetting to
valuation-ring units. -/
theorem principalUnitExpSeries_logSeries_idealQuotient_succ_eq_self_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) n) :
    Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1))
        ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete
            (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
              (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
              hnKlog hnvalLog hcomplete u) :
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            (completeDVFOfWithZeroValuation v)) n) :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring)) =
      Ideal.Quotient.mk ((completeDVFOfWithZeroValuation v).maximalIdeal ^ (n + 1))
        (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring)) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let lhs : F.valuationSubring :=
    (((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete
      (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hcomplete u) :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n) :
        F.valuationSubringˣ) : F.valuationSubring)
  let rhs : F.valuationSubring :=
    ((u : F.valuationSubringˣ) : F.valuationSubring)
  change Ideal.Quotient.mk (F.maximalIdeal ^ (n + 1)) lhs =
    Ideal.Quotient.mk (F.maximalIdeal ^ (n + 1)) rhs
  exact
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := F.maximalIdeal ^ (n + 1)) lhs rhs).2
      (by
        simpa [F, lhs, rhs] using
          principalUnitExpSeries_logSeries_sub_self_mem_maximalIdeal_pow_succ_ofWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hnKexp hnvalExp hcomplete u)

/-- Separatedness endpoint for the additive side of the deep exponential–logarithm equivalence: two
elements of a fixed maximal-ideal power are equal if all finite
maximal-ideal quotient coordinates agree. -/
theorem maximalIdealPowSubtype_eq_of_idealQuotient_eq_all
    (F : CompleteDVF.{u, 0} K) {n : ℕ}
    {a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)}
    (h :
      ∀ r : ℕ,
        Ideal.Quotient.mk (F.maximalIdeal ^ r) (a : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ r) (b : F.valuationSubring)) :
    a = b := by
  apply Subtype.ext
  have hsub :
      ∀ r : ℕ,
        (a : F.valuationSubring) - (b : F.valuationSubring) ∈
          F.maximalIdeal ^ r := by
    intro r
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ r)
        (x := (a : F.valuationSubring))
        (y := (b : F.valuationSubring))).1 (h r)
  exact sub_eq_zero.mp (F.eq_zero_of_mem_maximalIdeal_pow_all hsub)

/-- Variant of `maximalIdealPowSubtype_eq_of_idealQuotient_eq_all` tailored
to elements already known to lie in `m^n`: quotient equality only has to be
checked at levels `r ≥ n`; the lower levels are automatic. -/
theorem maximalIdealPowSubtype_eq_of_idealQuotient_eq_ge
    (F : CompleteDVF.{u, 0} K) {n : ℕ}
    {a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)}
    (h :
      ∀ r : ℕ, n ≤ r →
        Ideal.Quotient.mk (F.maximalIdeal ^ r) (a : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ r) (b : F.valuationSubring)) :
    a = b := by
  apply maximalIdealPowSubtype_eq_of_idealQuotient_eq_all F
  intro r
  by_cases hr : n ≤ r
  · exact h r hr
  · have hrle : r ≤ n := Nat.le_of_not_ge hr
    apply
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ r)
        (x := (a : F.valuationSubring))
        (y := (b : F.valuationSubring))).2
    have ha : (a : F.valuationSubring) ∈ F.maximalIdeal ^ r :=
      Ideal.pow_le_pow_right hrle a.property
    have hb : (b : F.valuationSubring) ∈ F.maximalIdeal ^ r :=
      Ideal.pow_le_pow_right hrle b.property
    exact (F.maximalIdeal ^ r).sub_mem ha hb

/-- Separatedness endpoint for the multiplicative principal-unit side of
the deep exponential–logarithm equivalence: higher principal units are equal if their underlying
  units
have the same image in every finite maximal-ideal quotient. -/
theorem higherPrincipalUnitGroup_eq_of_idealQuotient_eq_all
    (F : CompleteDVF.{u, 0} K) {n : ℕ}
    {u₁ u₂ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n}
    (h :
      ∀ r : ℕ,
        Ideal.Quotient.mk (F.maximalIdeal ^ r)
            ((u₁ : F.valuationSubringˣ) : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ r)
            ((u₂ : F.valuationSubringˣ) : F.valuationSubring)) :
    u₁ = u₂ := by
  apply Subtype.ext
  exact F.unit_eq_of_idealQuotient_eq_all h

/-- Variant of `higherPrincipalUnitGroup_eq_of_idealQuotient_eq_all` for two
elements of the same `U^n`: it is enough to compare finite quotient
coordinates at levels `r ≥ n`. -/
theorem higherPrincipalUnitGroup_eq_of_idealQuotient_eq_ge
    (F : CompleteDVF.{u, 0} K) {n : ℕ}
    {u₁ u₂ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n}
    (h :
      ∀ r : ℕ, n ≤ r →
        Ideal.Quotient.mk (F.maximalIdeal ^ r)
            ((u₁ : F.valuationSubringˣ) : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ r)
            ((u₂ : F.valuationSubringˣ) : F.valuationSubring)) :
    u₁ = u₂ := by
  apply higherPrincipalUnitGroup_eq_of_idealQuotient_eq_all F
  intro r
  by_cases hr : n ≤ r
  · exact h r hr
  · have hrle : r ≤ n := Nat.le_of_not_ge hr
    apply
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ r)
        (x := ((u₁ : F.valuationSubringˣ) : F.valuationSubring))
        (y := ((u₂ : F.valuationSubringˣ) : F.valuationSubring))).2
    have hu₁n :
        ((u₁ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
          F.maximalIdeal ^ n :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) n (u₁ : F.valuationSubringˣ)).1 u₁.property
    have hu₂n :
        ((u₂ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
          F.maximalIdeal ^ n :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) n (u₂ : F.valuationSubringˣ)).1 u₂.property
    have hu₁r :
        ((u₁ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
          F.maximalIdeal ^ r :=
      Ideal.pow_le_pow_right hrle hu₁n
    have hu₂r :
        ((u₂ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
          F.maximalIdeal ^ r :=
      Ideal.pow_le_pow_right hrle hu₂n
    have hsub :
        ((u₁ : F.valuationSubringˣ) : F.valuationSubring) -
            ((u₂ : F.valuationSubringˣ) : F.valuationSubring) =
          (((u₁ : F.valuationSubringˣ) : F.valuationSubring) - 1) -
            (((u₂ : F.valuationSubringˣ) : F.valuationSubring) - 1) := by
      ring
    rw [hsub]
    exact (F.maximalIdeal ^ r).sub_mem hu₁r hu₂r

/-- Exact `Log ∘ Exp` endpoint reduced to finite quotient coordinates.  This
is the separatedness step for the additive side of the deep exponential–logarithm equivalence
  after the
analytic/formal proof supplies equality in every quotient `O/m^r` for
`r ≥ n`. -/
theorem principalUnitLogSeries_expSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
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
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring))
    (hquot :
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
            (a : (completeDVFOfWithZeroValuation v).valuationSubring)) :
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hcomplete
        (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete a) =
      a := by
  exact
    maximalIdealPowSubtype_eq_of_idealQuotient_eq_ge
      (completeDVFOfWithZeroValuation v) hquot

/-- Exact `Exp ∘ Log` endpoint reduced to finite quotient coordinates.  This
is the separatedness step for the multiplicative side of the deep exponential–logarithm equivalence
after the analytic/formal proof supplies equality in every quotient `O/m^r`
for `r ≥ n`. -/
theorem principalUnitExpSeries_logSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) n)
    (hquot :
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
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hcomplete
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete u) =
      u := by
  exact
    higherPrincipalUnitGroup_eq_of_idealQuotient_eq_ge
      (completeDVFOfWithZeroValuation v) hquot

/-- Exact `Log ∘ Exp` endpoint from direct membership of the defect in every
finite maximal-ideal power at levels `r ≥ n`. -/
theorem principalUnitLogSeries_expSeries_eq_self_of_sub_mem_ge_ofWithZeroValuationScaled
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
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring))
    (hmem :
      ∀ r : ℕ, n ≤ r →
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
              (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
              hnKlog hnvalLog hcomplete
              (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKexp hnvalExp hcomplete a) :
            (completeDVFOfWithZeroValuation v).valuationSubring) -
          (a : (completeDVFOfWithZeroValuation v).valuationSubring) ∈
            (completeDVFOfWithZeroValuation v).maximalIdeal ^ r) :
    principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hcomplete
        (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete a) =
      a := by
  apply
    principalUnitLogSeries_expSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hnKlog hnvalLog hcomplete a
  intro r hr
  exact
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
      (x :=
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hcomplete
            (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
              (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
              hnKexp hnvalExp hcomplete a) :
          (completeDVFOfWithZeroValuation v).valuationSubring))
      (y := (a : (completeDVFOfWithZeroValuation v).valuationSubring))).2
      (hmem r hr)

/-- Exact `Exp ∘ Log` endpoint from direct membership of the multiplicative
defect in every finite maximal-ideal power at levels `r ≥ n`. -/
theorem principalUnitExpSeries_logSeries_eq_self_of_sub_mem_ge_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
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
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v)) n)
    (hmem :
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
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hcomplete
        (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete u) =
      u := by
  apply
    principalUnitExpSeries_logSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKlog hnvalLog hnKexp hnvalExp hcomplete u
  intro r hr
  exact
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (completeDVFOfWithZeroValuation v).maximalIdeal ^ r)
      (x :=
        (((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
              (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
              hnKexp hnvalExp hcomplete
              (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
                (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
                hnKlog hnvalLog hcomplete u) :
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
              (completeDVFOfWithZeroValuation v)) n) :
            (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
            (completeDVFOfWithZeroValuation v).valuationSubring))
      (y :=
        (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring)))).2
      (hmem r hr)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end

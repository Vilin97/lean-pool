/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog
/-!
# Topology of exponential and logarithm

This file supplies the topological part of the deep exponential–logarithm equivalence at the sharp
ramified endpoint `n > e / (p - 1)`.  The algebraic construction of the maps is supplied by
  the preceding modules;
here we prove that the endpoint
exponential and logarithm maps are continuous for the valuation topology.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

open Filter
open WithZeroValuation
open scoped Topology

variable {K : Type u} [Field K]

/-- The endpoint exponential of the deep exponential–logarithm equivalence, as a homomorphism
from the
additive ideal (written multiplicatively) to the higher principal units. -/
noncomputable def principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) →*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v) n := by
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  exact
    { toFun := fun a =>
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete a.toAdd
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        apply Subtype.ext
        simp [principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled]
      map_mul' := by
        intro a b
        simpa using
          principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnK hnval hcomplete a.toAdd b.toAdd }

/--
The defining evaluation formula for `principalUnitExpSeriesHomOfMaximalIdealPow` is
`principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled (v := v) (p := p) e n (π :=
π) hπval hn hlevel hnK hnval hcomplete a =
principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled (v := v) (p := p) e n (π := π)
(isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval) hπval hn hlevel hnK hnval hcomplete
a.toAdd`.
-/
@[simp] theorem principalUnitExpSeriesHomOfMaximalIdealPow_apply
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a : Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete a =
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π)
        (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
        hπval hn hlevel
        hnK hnval hcomplete a.toAdd :=
  rfl

/-- The field value of the endpoint exponential is continuous at the origin.
The proof is the valuation estimate `v(Exp(a) - 1) = v(a)`: membership in `m^n`
puts every nonzero `a` above the ramified convergence threshold. -/
theorem continuousAt_zero_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousAt
      (fun a :
          ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
            Ideal (completeDVFOfWithZeroValuation v).valuationSubring) =>
        ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnK hnval hcomplete a :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            (completeDVFOfWithZeroValuation v) n) :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring) : K))
      0 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    completeDVFOfWithZeroValuation v
  let E :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnK hnval hcomplete
  have hcoe : Continuous
      (fun a : (F.maximalIdeal ^ n : Ideal F.valuationSubring) =>
        ((a : F.valuationSubring) : K)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hEzero : ((((E 0 :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) : F.valuationSubring) : K) = 1 := by
    simp [E, principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled]
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  rw [hEzero, Valued.mem_nhds] at hs
  obtain ⟨γ, hγ⟩ := hs
  have hball : {x : K |
      v x < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈
      𝓝 (0 : K) := by
    apply Valued.mem_nhds_zero.mpr
    exact ⟨γ, by
      intro x hx
      change v.restrict x < γ.1 at hx
      rw [Valuation.restrict_lt_iff_lt_embedding] at hx
      exact hx⟩
  have hpre :
      {a : (F.maximalIdeal ^ n : Ideal F.valuationSubring) |
        v (((a : F.valuationSubring) : K)) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ 𝓝 0 := by
    have ht := (hcoe.tendsto
      (0 : (F.maximalIdeal ^ n : Ideal F.valuationSubring))) hball
    simpa using ht
  refine Filter.mem_of_superset hpre ?_
  intro a ha
  change v (((a : F.valuationSubring) : K)) <
    MonoidWithZeroHom.ValueGroup₀.embedding γ.1 at ha
  apply hγ
  change v.restrict
    (((((E a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) : F.valuationSubring) : K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  let x : K := ((a : F.valuationSubring) : K)
  by_cases hx : x = 0
  · simpa [E, principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled,
      x, hx] using
        (MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ)
  · have hge :
        (n : ℤ) ≤ (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (a : F.valuationSubring)) a.property hx
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
      lt_of_lt_of_le hlevel (by exact_mod_cast hge)
    have hv :=
      valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hcomplete
    rw [principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled,
      hv]
    simpa [x] using ha

/-- The field value of the endpoint exponential is continuous everywhere.
Translation in `m^n`, exponential additivity, and continuity of multiplication
reduce this to the preceding continuity statement at zero. -/
theorem continuous_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (fun a :
          ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
            Ideal (completeDVFOfWithZeroValuation v).valuationSubring) =>
        ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnK hnval hcomplete a :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            (completeDVFOfWithZeroValuation v) n) :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring) : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    completeDVFOfWithZeroValuation v
  let E :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnK hnval hcomplete
  let f : (F.maximalIdeal ^ n : Ideal F.valuationSubring) → K :=
    fun a => ((((E a :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) : F.valuationSubring) : K)
  have hzero : ContinuousAt f 0 := by
    simpa [F, E, f] using
      continuousAt_zero_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete
  rw [continuous_iff_continuousAt]
  intro a
  have hshiftContinuous : Continuous
      (fun b : (F.maximalIdeal ^ n : Ideal F.valuationSubring) => b - a) := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_subtype_val).sub
        continuous_const
  have hshift : ContinuousAt
      (fun b : (F.maximalIdeal ^ n : Ideal F.valuationSubring) => b - a) a :=
    hshiftContinuous.continuousAt
  have hshiftExp : ContinuousAt (fun b => f (b - a)) a :=
    hzero.comp_of_eq hshift (sub_self a)
  have htranslated : ContinuousAt (fun b => f a * f (b - a)) a :=
    continuousAt_const.mul hshiftExp
  convert htranslated using 1
  funext b
  have hadd :=
    principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnK hnval hcomplete a (b - a)
  have hfield := congrArg
    (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n =>
      ((((u : F.valuationSubringˣ) : F.valuationSubring) : K))) hadd
  simpa [f, E, add_sub_cancel_right] using hfield

/-- The exponential endpoint `m^n → U^n` of the deep exponential–logarithm equivalence is
continuous.
The unit topology records both a unit and its inverse; the inverse component is
the same continuous exponential evaluated at `-a`. -/
theorem continuous_principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    completeDVFOfWithZeroValuation v
  let I : Type u := (F.maximalIdeal ^ n : Ideal F.valuationSubring)
  let H : Multiplicative I →*
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n :=
    principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπval hn hlevel
      hnK hnval hcomplete
  have hFieldAdd : Continuous
      (fun a : I => ((((H (Multiplicative.ofAdd a) :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
          F.valuationSubringˣ) :
        F.valuationSubring) : K)) := by
    simpa [F, I, H] using
      continuous_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete
  have hField : Continuous
      (fun a : Multiplicative I => ((((H a :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
        F.valuationSubringˣ) : F.valuationSubring) : K)) := by
    convert hFieldAdd.comp continuous_toAdd using 1
    rfl
  have hVal : Continuous
      (fun a : Multiplicative I =>
        (((H a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F
          n) : F.valuationSubringˣ) :
          F.valuationSubring)) := by
    apply Continuous.subtype_mk
    exact hField
  have hNegI : Continuous (fun a : I => -a) := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).neg
  have hNeg : Continuous (fun a : Multiplicative I => -(a.toAdd)) :=
    hNegI.comp continuous_toAdd
  let Hinv : Multiplicative I → F.valuationSubringˣ :=
    fun a => ((H a : F.valuationSubringˣ)⁻¹)
  have hFieldInv : Continuous
      (fun a : Multiplicative I => ((Hinv a : F.valuationSubring) : K)) := by
    have hnegexp := hFieldAdd.comp hNeg
    convert hnegexp using 1
    funext a
    simp [Hinv]
  have hInvVal : Continuous
      (fun a : Multiplicative I => (Hinv a : F.valuationSubring)) := by
    apply Continuous.subtype_mk
    exact hFieldInv
  have hUnits : Continuous
      (fun a : Multiplicative I =>
        ((H a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F
          n) : F.valuationSubringˣ)) := by
    rw [Units.continuous_iff]
    exact ⟨hVal, by simpa [Hinv] using hInvVal⟩
  change Continuous H
  apply Continuous.subtype_mk
  exact hUnits

/-- The logarithm endpoint `U^n → m^n` of the deep exponential–logarithm equivalence is continuous.
It is the restriction of the continuous logarithm on `U^1`; the two subtype
lifts merely record the already-proved fact that its value lies in `m^n`. -/
theorem continuous_principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π)
        (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
        hπval hn hlevel
        hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    completeDVFOfWithZeroValuation v
  let ι : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n →
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1 :=
    fun u => ⟨(u : F.valuationSubringˣ),
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone F hn
        u.property⟩
  have hι : Continuous ι := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  let L : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1 →*
    Multiplicative K :=
    principalUnitLogSeriesHomOfWithZeroValuationScaled
      (v := v) (p := p) e hnK hnval hcomplete
  have hL : Continuous L := by
    simpa [F, L] using
      continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled
        (v := v) (p := p) e hnK hnval hcomplete
  have hfield : Continuous
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n
        => (L (ι u)).toAdd) :=
    continuous_toAdd.comp (hL.comp hι)
  have hfieldEndpoint : Continuous
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n =>
        (((principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete u :
            (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring) : K)) := by
    convert hfield using 1
    funext u
    change principalUnitLogSeriesOfWithZeroValuation v (ι u) hnK =
      Multiplicative.toAdd (L (ι u))
    exact
      (principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd
        (v := v) (p := p) e hnK hnval hcomplete (ι u)).symm
  have hValEndpoint : Continuous
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n =>
        ((principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete u :
            (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring)) := by
    apply Continuous.subtype_mk
    exact hfieldEndpoint
  apply Continuous.subtype_mk
  exact hValEndpoint

/-- The deep exponential–logarithm equivalence as a topological group isomorphism, once the two
exact
series-composition identities have been supplied.  Continuity of both maps is
not an assumption: it is furnished by the endpoint theorems above. -/
noncomputable def principalUnitExpLogContinuousMulEquivOfExactOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
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
          (v := v) (p := p) e n (π := π)
          (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
          hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnKexp hnvalExp hcomplete a) = a)
    (hexp_log :
      ∀ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v) n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π)
          (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
          hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnKlog hnvalLog hcomplete u) = u) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v) n := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  exact
    { __ :=
        principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hnKlog hnvalLog hcomplete hlog_exp hexp_log
      continuous_toFun :=
        continuous_principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπval hn hlevel
          hnKexp hnvalExp hcomplete
      continuous_invFun :=
        continuous_ofAdd.comp
          (continuous_principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπval hn hlevel
            hnKlog hnvalLog hcomplete) }

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

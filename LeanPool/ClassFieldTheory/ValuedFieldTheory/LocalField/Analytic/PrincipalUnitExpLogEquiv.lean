/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpComposition
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpContinuity
/-!
# Exponential and logarithm on deep principal units

This file combines the two evaluated formal composition identities with the
valuation-theoretic endpoint maps and their continuity.  No finite-quotient
or defect-membership hypothesis remains in the public result.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The local-field structure theory, the deep exponential–logarithm equivalence.  If the normalized valuation has
ramification index `e`, then for every `n > e/(p-1)` the exponential and
logarithm series give mutually inverse topological group isomorphisms
`m^n ≃ U^n` (with the additive source written multiplicatively).
Surjectivity onto the standard value group `ℤᵐ⁰` is the formal normalization
condition; a normalized uniformizer is chosen internally. -/
noncomputable def chosenExpLogContinuousMulEquiv
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (LocalField.ramificationIndexOfWithZeroValuation v : ℚ) /
          (((LocalField.ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let LF : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let hnormalized :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π : (completeDVFOfWithZeroValuation v).valuationSubring :=
    Classical.choose hnormalized
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hnormalized
  let hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  let p : ℕ := LF.residueCharacteristic
  let e : ℕ := LocalField.ramificationIndexOfWithZeroValuation v
  haveI : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  letI : Fact p.Prime := by
    dsimp [p, LF]
    infer_instance
  have hlevel' : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ) := by
    simpa [e, p, LF] using hlevel
  have hpden : (0 : ℚ) < (p : ℚ) - 1 := by
    have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
    exact sub_pos.mpr (by exact_mod_cast hp)
  have hepos : (0 : ℚ) < (e : ℚ) := by
    exact_mod_cast LocalField.ramificationIndexOfWithZeroValuation_pos v
  have hnpos : 0 < n := by
    have hnq : (0 : ℚ) < (n : ℚ) :=
      lt_trans (div_pos hepos hpden) hlevel'
    exact_mod_cast hnq
  have hn : 1 ≤ n := hnpos
  let hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0) :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  let hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0) :=
    fun m => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  let hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))) := by
    intro m
    simpa [e, p, LF] using
      LocalField.valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat
        v m
  let hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))) := by
    intro m
    simpa [e, p, LF] using
      LocalField.valuation_natCast_succ_eq_exp_neg_ramificationIndex_mul_padicValNat
        v m
  have hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K :=
    WithZeroValuationTopology.completeSpace_ofWithZeroValuation v
  have hlevelR : (e : ℝ) / ((p : ℝ) - 1) < (n : ℝ) := by
    exact_mod_cast hlevel'
  have hthreshold_of_mem :
      ∀ (a : F.valuationSubring), a ∈ F.maximalIdeal ^ n →
        ∀ hx : (a : K) ≠ 0,
          (e : ℝ) / ((p : ℝ) - 1) <
            ((ofWithZeroValuation v).val (Units.mk0 (a : K) hx) : ℝ) := by
    intro a ha hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 (a : K) hx) := by
      simpa [F] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n a ha hx
    exact lt_of_lt_of_le hlevelR (by exact_mod_cast hge)
  have hlog_exp :
      ∀ a : (F.maximalIdeal ^ n : Ideal F.valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
            hnKexp hnvalExp hcomplete a) = a := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    simpa [principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled,
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled, F] using
      logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (((a : F.valuationSubring) : K))
        hnKexp hnvalExp hnKlog hnvalLog
        (hthreshold_of_mem (a : F.valuationSubring) a.property) hcomplete
  have hexp_log :
      ∀ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
            hnKlog hnvalLog hcomplete u) = u := by
    intro u
    let a : F.valuationSubring :=
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
    have ha : a ∈ F.maximalIdeal ^ n := by
      simpa [a] using
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
          (F := F) n (u : F.valuationSubringˣ)).1 u.property
    have hexact :=
      expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (a : K) hnKlog hnvalLog hnKexp hnvalExp
        (hthreshold_of_mem a ha) hcomplete
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    simpa [a,
      principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled,
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled, F] using hexact
  exact
    principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπval hn hlevel'
      hnKexp hnvalExp hnKlog hnvalLog hcomplete hlog_exp hexp_log

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

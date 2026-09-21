/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval

/-!
# The eventual value cut for translated truncations

For a series of ordinal value above one, every sufficiently high translated truncation has
ordinal value at most `v_J^r(b) * α` for some `α < v_J^p(b)`, with ordinary ordinal
multiplication. This is the upper half of Berarducci, Lemma 6.8, in the quantitative form used by
the value estimates of Berarducci, Lemma 7.7 and Lemma 8.2, and it is the statement that lets a
truncation value be absorbed strictly below `v_J(b)`.

On a stable tail the ordinary order type is exactly `v_J(b) = v_J^r(b) * v_J^p(b)`. Cutting at `γ`
leaves a relative upper set of the support below `γ` whose order type is bounded by that of a
proper initial segment of the tail, hence strictly below `v_J(b)`; continuity of ordinary ordinal
multiplication in its second argument at the successor-limit `v_J^p(b)` then supplies `α`.

When the support has no point in `(η, γ)` the truncation is a constant modulo `J`, its value is at
most one, and `α = 1` works because the residual value is at least one and the principal value is
above one.
-/

universe v

public noncomputable section

open HahnSeries

namespace Berarducci

variable {K : Type v} [Field K]

theorem exists_ordinalValue_translatedTruncation_le (b : SeriesWithOrdinalValueAboveOne K) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      ∃ α < b.principalValue.val,
        (ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ)).val ≤ b.residualValue.val * α := by
  obtain ⟨η, hη, hstable⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue b.1 b.2
  obtain ⟨η', hηη', hη'0⟩ := exists_between hη
  have hone : (1 : Ordinal) < b.principalValue.val := by
    simpa using NatOrdinal.val.lt_iff_lt.mpr b.one_lt_principalValue
  have hρ : (1 : Ordinal) ≤ b.residualValue.val := by
    rw [Order.one_le_iff_ne_zero]
    intro h
    exact b.residualValue_ne_zero (NatOrdinal.val.injective (by simpa using h))
  refine ⟨η', hη'0, fun γ hη'γ hγ ↦ ?_⟩
  by_cases hne : ((b.1 : K⟦ℝ⟧).support ∩ Set.Ioo η' γ).Nonempty
  · set C := (b.1 : K⟦ℝ⟧).support ∩ Set.Ioo η' γ with hCdef
    have hC : IsRelUpperSet C (· ∈ (b.1 : K⟦ℝ⟧).support ∩ Set.Iio γ) := by
      rintro a ⟨haSupport, haLow, haHigh⟩
      refine ⟨⟨haSupport, haHigh⟩, ?_⟩
      rintro d had ⟨hdSupport, hdHigh⟩
      exact ⟨hdSupport, lt_of_lt_of_le haLow had, hdHigh⟩
    have hbound :=
      ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow
        (b.1 : K⟦ℝ⟧) γ hC hne
    have htailLUB :=
      isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue b.1 b.2 hη'0
    obtain ⟨x, hxTail, hγx, _⟩ := htailLUB.exists_between hγ
    have htailPWO : (negativeSupportTail b.1 η').IsPWO :=
      (b.1 : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b.1 η')
    have hsub : C ⊆ negativeSupportTail b.1 η' ∩ Set.Iio x := by
      rintro y ⟨hySupport, hyLow, hyHigh⟩
      exact ⟨mem_negativeSupportTail_iff.mpr ⟨hySupport, hyLow, hyHigh.trans hγ⟩,
        hyHigh.trans hγx⟩
    have hlt : ((b.1 : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType <
        (ordinalValue b.1).val := by
      calc
        ((b.1 : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType
            ≤ (htailPWO.mono (s := negativeSupportTail b.1 η' ∩ Set.Iio x)
              Set.inter_subset_left).orderType :=
          Set.IsPWO.orderType_mono _ _ hsub
        _ < htailPWO.orderType := htailPWO.orderType_inter_Iio_lt hxTail
        _ = (ordinalValue b.1).val := hstable η' hηη' hη'0
    rw [← b.residualValue_val_mul_principalValue_val] at hlt
    obtain ⟨α, hα, hαlt⟩ :=
      (Ordinal.lt_mul_iff_of_isSuccLimit
        b.principalValue_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp hlt
    exact ⟨α, hα, hbound.trans hαlt.le⟩
  · refine ⟨1, hone, ?_⟩
    rw [mul_one]
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hmem : translatedTruncation (b.1 : K⟦ℝ⟧) γ ∈ nearConstantSubgroup K := by
      refine mem_nearConstantSubgroup_iff_exists_germ_eq_constant.mpr
        ⟨(b.1 : K⟦ℝ⟧).coeff γ, ?_⟩
      refine toGerm_eq_toGerm_iff_exists_coeff_eq.mpr
        ⟨η' - γ, by linarith, fun δ hδlow hδ0 ↦ ?_⟩
      rw [coeff_translatedTruncation, if_pos hδ0, HahnSeries.Nonpositive.coe_C]
      rcases hδ0.eq_or_lt with rfl | hδneg
      · simp
      · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by linarith : δ ≠ (0 : ℝ))]
        by_contra hcoeff
        have hmemSupport : γ + δ ∈ (b.1 : K⟦ℝ⟧).support ∩ Set.Ioo η' γ :=
          ⟨(HahnSeries.mem_support _ _).mpr hcoeff, by linarith, by linarith⟩
        rw [hne] at hmemSupport
        exact hmemSupport
    have hle : ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) ≤ 1 :=
      le_of_not_gt fun h ↦ (one_lt_ordinalValue_iff.mp h) hmem
    exact (NatOrdinal.val.monotone hle).trans hρ

end Berarducci

/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SeriesTruncations
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.ProductValues
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition

/-!
# Shifted series, sums of series of bounded support, and principal representatives

Three small tools for the induction over degrees:

* the shift `t^ξ u` of a nonpositive series by `ξ ≤ 0`, its translated truncations
  `(t^ξ u)^{|ζ} = u^{|ζ - ξ}` and its support order type;
* a finite sum of series whose supports have order type below `ω^e` has support of order type
  below `ω^e`;
* every element of `P_β` is represented by a principal series of degree `β` or by `0`: a series
  of support order type at most `ω^β` whose translated truncations at cutoffs `ζ < 0` have
  ordinal value below `ω^β`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-! ### Shifts -/

/-- The shift `t^ξ u` of a nonpositive series by `ξ ≤ 0` (and `0` for `ξ > 0`). -/
def shift (ξ : ℝ) (u : Series K) : Series K :=
  if h : ξ ≤ 0 then Nonpositive.single ξ (1 : K) h * u else 0

theorem coe_shift_of_le {ξ : ℝ} (hξ : ξ ≤ 0) (u : Series K) :
    ((shift ξ u : Series K) : K⟦ℝ⟧) = translate ξ (u : K⟦ℝ⟧) := by
  rw [shift, dif_pos hξ, Subring.coe_mul, Nonpositive.coe_single, single_one_mul_eq_translate]

theorem shift_mul {ξ : ℝ} (hξ : ξ ≤ 0) (u v : Series K) :
    shift ξ u * v = shift ξ (u * v) := by
  rw [shift, shift, dif_pos hξ, dif_pos hξ, mul_assoc]

/-- The translated truncation of a shift: `(t^ξ u)^{|ζ} = u^{|ζ - ξ}`. -/
theorem translatedTruncation_shift {ξ : ℝ} (hξ : ξ ≤ 0) (u : Series K) (ζ : ℝ) :
    translatedTruncation ((shift ξ u : Series K) : K⟦ℝ⟧) ζ =
      translatedTruncation (u : K⟦ℝ⟧) (ζ - ξ) := by
  rw [coe_shift_of_le hξ, translatedTruncation_translate]

theorem supportOrderType_shift {ξ : ℝ} (hξ : ξ ≤ 0) (u : Series K) :
    ((shift ξ u : Series K) : K⟦ℝ⟧).supportOrderType = (u : K⟦ℝ⟧).supportOrderType := by
  rw [coe_shift_of_le hξ, supportOrderType_translate]

/-! ### Sums -/

/-- A finite sum of series whose supports have order type below `ω^e` has support of order type
below `ω^e`. -/
theorem supportOrderType_sum_lt_wpow {ι' : Type*} (s : Finset ι') (f : ι' → Series K)
    {e : NatOrdinal} (h : ∀ i ∈ s, ((f i : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ e).val) :
    ((∑ i ∈ s, f i : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ e).val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Subring.coe_zero, supportOrderType_eq_setOrderType]
    simp only [HahnSeries.support_zero]
    rw [(Set.isPWO_empty.orderType_eq_zero).mpr rfl]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Subring.coe_add]
    refine (supportOrderType_add_le_naturalAdd _ _).trans_lt ?_
    have h1 : NatOrdinal.of ((f a : Series K) : K⟦ℝ⟧).supportOrderType < ω^ e := by
      rw [← NatOrdinal.of_val (ω^ e)]
      exact NatOrdinal.of.lt_iff_lt.mpr (h a (Finset.mem_insert_self a s))
    have h2 : NatOrdinal.of ((∑ i ∈ s, f i : Series K) : K⟦ℝ⟧).supportOrderType < ω^ e := by
      rw [← NatOrdinal.of_val (ω^ e)]
      exact NatOrdinal.of.lt_iff_lt.mpr (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    exact NatOrdinal.val.lt_iff_lt.mpr (NatOrdinal.add_lt_wpow h1 h2)

/-! ### Representatives -/

theorem Represents.of_eq {u : Series K} {β β' : NatOrdinal} {e : PrincipalSubring K} (h : β = β')
    (hu : Represents u β e) : Represents u β' e := by
  subst h; exact hu

/-- A finite sum of representatives represents the sum. -/
theorem represents_sum {ι' : Type*} (s : Finset ι') (f : ι' → Series K) (β : NatOrdinal)
    (e : ι' → PrincipalSubring K) (h : ∀ i ∈ s, Represents (f i) β (e i)) :
    Represents (∑ i ∈ s, f i) β (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact represents_zero β
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- **Principal representatives.** Every element of `P_β ⊆ P̂` is represented by a series of
support order type at most `ω^β` whose translated truncations at cutoffs `ζ < 0` have ordinal
value below `ω^β`: a principal series of degree `β`, or `0`. -/
theorem exists_represents_of_mem_principalGrading {β : NatOrdinal} {e : PrincipalSubring K}
    (he : e ∈ principalGrading K β) :
    ∃ p : Series K, Represents p β e ∧ (p : K⟦ℝ⟧).supportOrderType ≤ (ω^ β).val ∧
      ∀ ζ : ℝ, ζ < 0 → ordinalValue (translatedTruncation (p : K⟦ℝ⟧) ζ) < ω^ β := by
  obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ β e).mp he
  rw [DirectSum.lof_eq_of]
  rcases eq_or_ne a 0 with rfl | ha
  · refine ⟨0, by rw [map_zero]; exact represents_zero β, ?_, fun ζ _ ↦ ?_⟩
    · rw [Subring.coe_zero, supportOrderType_eq_setOrderType]
      simp only [HahnSeries.support_zero]
      rw [(Set.isPWO_empty.orderType_eq_zero).mpr rfl]
      exact bot_le
    · rw [Subring.coe_zero, translatedTruncation_zero_input, ordinalValue_zero]
      exact NatOrdinal.wpow_pos β
  · obtain ⟨p, hp, hprin, hdeg, hpa⟩ := exists_principal_representative_of_ne_zero β a ha
    exact ⟨p, represents_iff.mpr ⟨hp, by rw [hpa]⟩,
      (hprin.supportOrderType_eq_wpow_of_degree_eq hdeg).le,
      fun ζ hζ ↦ ordinalValue_translatedTruncation_lt_of_isPrincipal hprin hdeg hζ⟩

end Berarducci

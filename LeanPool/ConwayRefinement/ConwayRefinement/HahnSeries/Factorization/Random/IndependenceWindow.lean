/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.ReducibleSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import Mathlib.Tactic.Linarith

/-!
# The support of a vanishing relation among classes

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Propositions 3.4 and 3.6, both start from a relation `∑ k_i rv_J(b_i) = 0`, that is
`r := ∑ k_i b_i ∈ J_{deg_J(b_1)}`, and compare the supports of the `b_i` with that of `r` near
zero: the support of each `b_i` in `(η, 0)` has order type `v_J(b_i)`, while that of `r` has
order type at most `v_J(r) < v_J(b_i)`, so each `b_i` has infinitely many support points in
`(η, 0)` outside the support of `r`. This module proves these two facts and the coefficient
formula for `r`; the two propositions then differ only in how they exploit such a point.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- A vanishing `K`-linear relation among the classes `rv_J(c k)` of series of a common ordinal
value `ω^d` puts the corresponding combination of the `c k` into `J_{ω^d}`. -/
theorem ordinalValue_sum_C_mul_lt_of_sum_smul_rvJ_eq_zero {κ : Type*} [Fintype κ]
    {c : κ → Series K} {d : NatOrdinal} (hc : ∀ k, ordinalValue (c k) = ω^ d) (g : κ → K)
    (hrel : ∑ k, g k • rvJ (c k) = 0) :
    ordinalValue (∑ k, (HahnSeries.Nonpositive.C : K →+* Series K) (g k) * c k) < ω^ d := by
  have hcut : ∀ k ∈ (Finset.univ : Finset κ), ordinalValue (c k) < ω^ (d + 1) := fun k _ ↦ by
    rw [hc k]; exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one d)
  have hCcut : ∀ k ∈ (Finset.univ : Finset κ),
      ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) (g k) * c k) < ω^ (d + 1) :=
    fun k hk ↦ by
      simpa only [zero_add] using
        ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one (g k)) (hcut k hk)
  rw [← gradeClass_eq_zero_iff (ordinalValue_sum_lt_wpow_add_one _ _ hCcut),
    gradeClass_sum _ _ hCcut, ← hrel]
  exact Finset.sum_congr rfl fun k hk ↦ by
    rw [gradeClass_C_mul (g k) (hcut k hk), rvJ_eq_gradeClass (hc k)]

/-- The coefficient of a `K`-linear combination of series. -/
theorem coeff_sum_C_mul {κ : Type*} [Fintype κ] (c : κ → Series K) (g : κ → K) (x : ℝ) :
    (((∑ k, (HahnSeries.Nonpositive.C : K →+* Series K) (g k) * c k : Series K)) :
      K⟦ℝ⟧).coeff x = ∑ k, g k * ((c k : Series K) : K⟦ℝ⟧).coeff x := by
  rw [AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Subring.coe_mul, HahnSeries.Nonpositive.coe_C, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul]

/-- Near zero, the support of a series in `(η, 0)` has order type at most its ordinal value:
equality holds on a stable tail when `1 < v_J`, and the support is empty in `(η, 0)` when the
series lies in `J + K`. -/
theorem exists_forall_orderType_negativeSupportTail_le (r : Series K) :
    ∃ η₀ < (0 : ℝ), ∀ η, η₀ < η → η < 0 →
      NatOrdinal.of ((r : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support r η)).orderType ≤ ordinalValue r := by
  by_cases hone : 1 < ordinalValue r
  · obtain ⟨η₀, hη₀, h⟩ :=
      exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue r hone
    refine ⟨η₀, hη₀, fun η hη₀η hη ↦ ?_⟩
    rw [h η hη₀η hη, NatOrdinal.of_val]
  · have hnear : r ∈ nearConstantSubgroup K := not_not.mp (mt one_lt_ordinalValue_iff.mpr hone)
    have hJ := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hnear
    set j := r - HahnSeries.Nonpositive.C (HahnSeries.Nonpositive.constantCoeff r) with hj
    -- Every nonzero support point of `r` lies in the support of `j`, which is bounded below
    -- zero.
    have hsupp : (j : K⟦ℝ⟧).support = (r : K⟦ℝ⟧).support \ {0} := support_sub_C_constantCoeff r
    obtain ⟨η₀, hη₀, hbound⟩ : ∃ η₀ < (0 : ℝ), ∀ x ∈ (j : K⟦ℝ⟧).support, x ≤ η₀ := by
      rcases eq_or_ne j 0 with hj0 | hj0
      · exact ⟨-1, by norm_num, fun x hx ↦ by
          rw [hj0] at hx
          simp at hx⟩
      · have hlt := mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mp hJ
        rw [supportSup_of_ne hj0] at hlt
        exact ⟨sSup (j : K⟦ℝ⟧).support, WithBot.coe_lt_coe.mp hlt,
          fun x hx ↦ le_csSup (bddAbove_support j) hx⟩
    refine ⟨η₀, hη₀, fun η hη₀η hη ↦ ?_⟩
    have hempty : negativeSupportTail r η = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨hxsupp, hηx, hx0⟩ := mem_negativeSupportTail_iff.mp hx
      have hxj : x ∈ (j : K⟦ℝ⟧).support := by
        rw [hsupp]; exact ⟨hxsupp, hx0.ne⟩
      exact absurd (hbound x hxj) (not_le.mpr (by linarith))
    rw [(Set.IsPWO.orderType_eq_zero _).mpr hempty]
    simp

/-- FLLM24, proofs of Propositions 3.4 and 3.6: if `v_J(c) = ω^d > 1` and `v_J(r) < ω^d`, then
on every interval `(η, 0)` close to zero the support of `c` has infinitely many points outside
the support of `r`. -/
theorem exists_forall_infinite_support_diff {c r : Series K} {d : NatOrdinal} (hd : 0 < d)
    (hc : ordinalValue c = ω^ d) (hr : ordinalValue r < ω^ d) :
    ∃ η₀ < (0 : ℝ), ∀ η, η₀ < η → η < 0 →
      (((c : K⟦ℝ⟧).support ∩ Set.Ioo η 0) \ (r : K⟦ℝ⟧).support).Infinite := by
  have hone : 1 < ordinalValue c := by
    rw [hc, ← NatOrdinal.wpow_zero]
    exact NatOrdinal.wpow_lt_wpow.mpr hd
  obtain ⟨η₁, hη₁, hstable⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue c hone
  obtain ⟨η₂, hη₂, hbound⟩ := exists_forall_orderType_negativeSupportTail_le r
  refine ⟨max η₁ η₂, max_lt hη₁ hη₂, fun η hη₀η hη hfin ↦ ?_⟩
  have hη₁η : η₁ < η := (le_max_left _ _).trans_lt hη₀η
  have hη₂η : η₂ < η := (le_max_right _ _).trans_lt hη₀η
  -- The tail of `c` is covered by the tail of `r` and a finite set.
  set E := ((c : K⟦ℝ⟧).support ∩ Set.Ioo η 0) \ (r : K⟦ℝ⟧).support with hE
  have hcover : negativeSupportTail c η ⊆ negativeSupportTail r η ∪ E := by
    intro x hx
    obtain ⟨hxc, hηx, hx0⟩ := mem_negativeSupportTail_iff.mp hx
    by_cases hxr : x ∈ (r : K⟦ℝ⟧).support
    · exact Or.inl (mem_negativeSupportTail_iff.mpr ⟨hxr, hηx, hx0⟩)
    · exact Or.inr ⟨⟨hxc, hηx, hx0⟩, hxr⟩
  have hcPWO := (c : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support c η)
  have hrPWO := (r : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support r η)
  have hEPWO : E.IsPWO := hfin.isPWO
  have hle := Set.IsPWO.orderType_mono hcPWO (hrPWO.union hEPWO) hcover
  have hunion := Set.IsPWO.orderType_union_le_naturalAdd hrPWO hEPWO
  have hEfin : NatOrdinal.of hEPWO.orderType < ω^ d := by
    have h1 : hEPWO.orderType < Ordinal.omega0 := (hEPWO.finite_iff_orderType_lt_omega).mp hfin
    have h2 : NatOrdinal.of hEPWO.orderType < ω^ (1 : NatOrdinal) := by
      rw [NatOrdinal.wpow_def, NatOrdinal.of.lt_iff_lt]
      simpa using h1
    exact h2.trans_le (NatOrdinal.wpow_le_wpow.mpr (Order.one_le_iff_pos.mpr hd))
  have hrlt : NatOrdinal.of hrPWO.orderType < ω^ d := (hbound η hη₂η hη).trans_lt hr
  have hsum : NatOrdinal.of hrPWO.orderType + NatOrdinal.of hEPWO.orderType < ω^ d :=
    NatOrdinal.add_lt_wpow hrlt hEfin
  have hcval : NatOrdinal.of hcPWO.orderType = ω^ d := by
    rw [hstable η hη₁η hη, NatOrdinal.of_val, hc]
  have : NatOrdinal.of hcPWO.orderType ≤ NatOrdinal.of hrPWO.orderType +
      NatOrdinal.of hEPWO.orderType := by
    rw [← NatOrdinal.val.le_iff_le, NatOrdinal.val_of]
    exact hle.trans hunion
  rw [hcval] at this
  exact absurd this (not_le.mpr hsum)

end FLLM24

end

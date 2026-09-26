/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonValue
public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Additive laws for the Cantor–Bendixson value

Binary union commutes with every transfinite derivative. The support of a sum is contained in
the union of the factor supports, so the value of a sum is bounded by their maximum. If the
values differ, the larger value survives. A difference of value zero preserves the value.
These statements use the given order topology, with no completeness hypothesis.
-/

public noncomputable section

open Set Topology TopologicalSpace

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type v} [LinearOrder G] [TopologicalSpace G]
  [OrderTopology G] [Zero G]

section AddMonoid

variable [AddMonoid R]

/-- The value of a sum is bounded by the maximum of the summand values. -/
theorem cantorBendixsonValue_add_le (b d : HahnSeries G R) :
    (b + d).cantorBendixsonValue ≤ max b.cantorBendixsonValue d.cantorBendixsonValue := by
  by_cases hm : 0 ∈ closure (b + d).support
  · have hsub : (b + d).closedSupport ≤ b.closedSupport ⊔ d.closedSupport := by
      change ((b + d).closedSupport : Set G) ⊆
        (b.closedSupport : Set G) ∪ (d.closedSupport : Set G)
      rw [coe_closedSupport, coe_closedSupport, coe_closedSupport, ← closure_union]
      exact closure_mono (support_add_subset b d)
    have hh := Closeds.cantorBendixson_mono hsub ((b + d).cantorBendixsonRank 0)
      (((b + d).mem_support_derivative_iff 0 _).mpr ⟨hm, le_rfl⟩)
    rw [Closeds.cantorBendixson_sup] at hh
    rcases hh with hb | hd
    · obtain ⟨hb0, hr⟩ := (b.mem_support_derivative_iff 0 _).mp hb
      apply le_max_of_le_left
      rw [(b + d).cantorBendixsonValue_of_mem hm, b.cantorBendixsonValue_of_mem hb0]
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos hr
    · obtain ⟨hd0, hr⟩ := (d.mem_support_derivative_iff 0 _).mp hd
      apply le_max_of_le_right
      rw [(b + d).cantorBendixsonValue_of_mem hm, d.cantorBendixsonValue_of_mem hd0]
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos hr
  · rw [(b + d).cantorBendixsonValue_of_notMem hm]
    exact zero_le

/-- Repeated addition cannot increase the value. -/
theorem cantorBendixsonValue_nsmul_le (b : HahnSeries G R) (n : ℕ) :
    (n • b).cantorBendixsonValue ≤ b.cantorBendixsonValue := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact (cantorBendixsonValue_add_le _ _).trans (max_le ih le_rfl)

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid R]

/-- A finite sum preserves a strict positive upper bound on the values. -/
theorem cantorBendixsonValue_sum_lt {ι : Type*} (s : Finset ι) (f : ι → HahnSeries G R)
    {ρ : Ordinal.{u}} (hρ : 0 < ρ) (h : ∀ i ∈ s, (f i).cantorBendixsonValue < ρ) :
    (∑ i ∈ s, f i).cantorBendixsonValue < ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, cantorBendixsonValue_zero] using hρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (cantorBendixsonValue_add_le _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

/-- A finite sum of value-zero terms has value zero. -/
theorem cantorBendixsonValue_sum_eq_zero {ι : Type*} (s : Finset ι) (f : ι → HahnSeries G R)
    (h : ∀ i ∈ s, (f i).cantorBendixsonValue = 0) :
    (∑ i ∈ s, f i).cantorBendixsonValue = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cantorBendixsonValue_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply le_antisymm _ zero_le
    exact (cantorBendixsonValue_add_le _ _).trans (by
      rw [h a (Finset.mem_insert_self a s),
        ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)), max_self])

end AddCommMonoid

section AddGroup

variable [AddGroup R]

/-- Negation preserves the value. -/
theorem cantorBendixsonValue_neg (b : HahnSeries G R) :
    (-b).cantorBendixsonValue = b.cantorBendixsonValue :=
  cantorBendixsonValue_congr_support support_neg

/-- Subtraction is bounded by the maximum of the two values. -/
theorem cantorBendixsonValue_sub_le (b d : HahnSeries G R) :
    (b - d).cantorBendixsonValue ≤ max b.cantorBendixsonValue d.cantorBendixsonValue := by
  simpa only [sub_eq_add_neg, cantorBendixsonValue_neg] using
    b.cantorBendixsonValue_add_le (-d)

/-- When two values differ, their sum has the larger value. -/
theorem cantorBendixsonValue_add_eq_max_of_ne (b d : HahnSeries G R)
    (hne : b.cantorBendixsonValue ≠ d.cantorBendixsonValue) :
    (b + d).cantorBendixsonValue = max b.cantorBendixsonValue d.cantorBendixsonValue := by
  apply le_antisymm (b.cantorBendixsonValue_add_le d)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [max_eq_right hlt.le]
    have hd := (-b).cantorBendixsonValue_add_le (b + d)
    rw [neg_add_cancel_left, cantorBendixsonValue_neg] at hd
    exact (le_max_iff.mp hd).resolve_left (not_le_of_gt hlt)
  · rw [max_eq_left hgt.le]
    have hb := (b + d).cantorBendixsonValue_add_le (-d)
    rw [add_neg_cancel_right, cantorBendixsonValue_neg] at hb
    exact (le_max_iff.mp hb).resolve_right (not_le_of_gt hgt)

/-- An error of value zero does not change the value. -/
theorem cantorBendixsonValue_eq_of_sub_value_eq_zero (b d : HahnSeries G R)
    (h : (b - d).cantorBendixsonValue = 0) :
    b.cantorBendixsonValue = d.cantorBendixsonValue := by
  have hbd := (b - d).cantorBendixsonValue_add_le d
  rw [sub_add_cancel, h, max_eq_right zero_le] at hbd
  have hdb := (d - b).cantorBendixsonValue_add_le b
  rw [sub_add_cancel, ← neg_sub b d, cantorBendixsonValue_neg, h,
    max_eq_right zero_le] at hdb
  exact hbd.antisymm hdb

/-- Value one means a nonzero ordinary coefficient with a remainder of value zero. -/
theorem cantorBendixsonValue_eq_one_iff (b : HahnSeries G R) :
    b.cantorBendixsonValue = 1 ↔
      b.coeff 0 ≠ 0 ∧ (b - single 0 (b.coeff 0)).cantorBendixsonValue = 0 := by
  classical
  constructor
  · intro hv
    have hm : 0 ∈ closure b.support := by
      by_contra hn
      have he := b.cantorBendixsonValue_of_notMem hn
      rw [hv] at he
      exact one_ne_zero he
    have hr : b.cantorBendixsonRank 0 = 0 := by
      rw [b.cantorBendixsonValue_of_mem hm, Ordinal.opow_eq_one_iff] at hv
      exact hv.resolve_left Ordinal.one_lt_omega0.ne'
    have hn : (0 : G) ∉ derivedSet (closure b.support) := by
      have he := b.closedSupport.notMem_cantorBendixson_rank_add_one b.closedSupport_isPWO 0
      rw [← cantorBendixsonRank_eq, hr, zero_add,
        show (1 : Ordinal.{u}) = 0 + 1 by simp,
        Closeds.cantorBendixson_add_one, Closeds.cantorBendixson_zero] at he
      simpa only [Closeds.coe_derived, coe_closedSupport] using he
    have hcoeff : b.coeff 0 ≠ 0 := by
      rw [closure_eq_self_union_derivedSet] at hm
      exact hm.resolve_right (fun ha ↦ hn (derivedSet_mono _ _ subset_closure ha))
    refine ⟨hcoeff, cantorBendixsonValue_of_notMem _ ?_⟩
    rw [mem_closure_iff_frequently, Filter.not_frequently]
    rw [mem_derivedSet, accPt_iff_frequently, Filter.not_frequently] at hn
    filter_upwards [hn] with x hx
    change ¬ (b - single 0 (b.coeff 0)).coeff x ≠ 0
    rw [coeff_sub]
    by_cases hx0 : x = 0
    · subst x
      simp
    · have hbx : b.coeff x = 0 := by
        by_contra hnonzero
        exact hx ⟨hx0, subset_closure hnonzero⟩
      simp [hbx, hx0]
  · rintro ⟨hc, hz⟩
    rw [b.cantorBendixsonValue_eq_of_sub_value_eq_zero _ hz]
    apply cantorBendixsonValue_of_finite_of_coeff_ne_zero
    · exact (finite_singleton _).subset support_single_subset
    · simpa using hc

end AddGroup

section Ring

variable [Ring R] [NoZeroDivisors R]

/-- A natural scalar that is nonzero in the coefficient domain preserves the value. -/
theorem cantorBendixsonValue_nsmul (b : HahnSeries G R) (n : ℕ) (hn : (n : R) ≠ 0) :
    (n • b).cantorBendixsonValue = b.cantorBendixsonValue := by
  apply cantorBendixsonValue_congr_support
  ext x
  simp only [mem_support]
  rw [coeff_nsmul]
  simp [nsmul_eq_mul, hn]

end Ring

end HahnSeries

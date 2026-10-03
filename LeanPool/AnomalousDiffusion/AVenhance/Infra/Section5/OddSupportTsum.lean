/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportSums

/-! The odd cutoff `tsum` as an integer sum on its filtered finite support. -/

@[expose] public section

namespace AVenhance.Infra.Section5

open AVenhance

/-- Convert an odd-subtype cutoff `tsum` to the corresponding finite sum over
the integer support filtered to odd indices. -/
theorem xiMK_odd_tsum_eq_integer_filtered_sum
    {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [Module ℝ α]
    (F : ℤ → α) :
    ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t • F q.1 =
      ∑ k ∈ (I.xiMK_support_finite m t).toFinset.filter Odd,
        I.xiMK m k t • F k := by
  classical
  let S := (I.xiMK_support_finite m t).toFinset.filter Odd
  have hsupport := xiMK_odd_tsum_eq_support_sum I m hm t
    (fun q => F q.1)
  calc
    _ = ∑ q ∈ S.attach, I.xiMK m q.1 t • F q.1 := by
      simpa [S] using hsupport
    _ = ∑ k ∈ S, I.xiMK m k t • F k :=
      Finset.sum_attach S (fun k => I.xiMK m k t • F k)

/-- Reindex an odd-filtered integer support sum to the finite odd-subtype
support. -/
theorem xiMK_odd_integer_support_sum_eq_subtype_sum
    {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [Module ℝ α]
    (F : ℤ → α) :
    ∑ k ∈ (I.xiMK_support_finite m t).toFinset.filter Odd,
        I.xiMK m k t • F k =
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • F q.1 := by
  classical
  let S := (I.xiMK_support_finite m t).toFinset.filter Odd
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have htsum := xiMK_odd_tsum_eq_integer_filtered_sum I m hm t F
  have hsupport := xiMK_odd_tsum_eq_support_sum I m hm t
    (fun q => F q.1)
  have hreindex := xiMK_odd_support_sum_reindex I m hm t
    (F := fun q => I.xiMK m q.1 t • F q.1)
  calc
    _ = ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t • F q.1 := htsum.symm
    _ = ∑ q ∈ S.attach, I.xiMK m q.1 t • F q.1 := by
      simpa [S] using hsupport
    _ = ∑ q ∈ U, I.xiMK m q.1 t • F q.1 := by
      simpa [S, U] using hreindex

/-- The odd cutoff `tsum` directly as a sum over the finite odd-subtype
support. -/
theorem xiMK_odd_tsum_eq_subtype_support_sum
    {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [Module ℝ α]
    (F : {k : ℤ // Odd k} → α) :
    ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t • F q =
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • F q := by
  classical
  let S := (I.xiMK_support_finite m t).toFinset.filter Odd
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hattach := xiMK_odd_tsum_eq_support_sum I m hm t F
  have hreindex := xiMK_odd_support_sum_reindex I m hm t
    (F := fun q => I.xiMK m q.1 t • F q)
  calc
    _ = ∑ q ∈ S.attach, I.xiMK m q.1 t • F ⟨q.1,
        (Finset.mem_filter.mp q.2).2⟩ := by
      simpa [S] using hattach
    _ = ∑ q ∈ U, I.xiMK m q.1 t • F q := by
      simpa [S, U] using hreindex

end AVenhance.Infra.Section5

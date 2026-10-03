/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy

/-! Reindex finite sums between the odd-integer support and its odd subtype,
and identify the corresponding locally finite `tsum`. -/

@[expose] public section

namespace AVenhance.Infra.Section5

open AVenhance

/-- Reindex the odd support of `xiMK` from the filtered integer support to the
source's odd subtype. -/
theorem xiMK_odd_support_sum_reindex
    {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    {α : Type*} [AddCommMonoid α]
    (F : {k : ℤ // Odd k} → α) :
    (let S := (I.xiMK_support_finite m t).toFinset.filter Odd
     ∑ q ∈ S.attach,
       F ⟨q.1, (Finset.mem_filter.mp q.2).2⟩) =
      ∑ k ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset, F k := by
  classical
  let S₀ := (I.xiMK_support_finite m t).toFinset
  let S := S₀.filter Odd
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  change (∑ q ∈ S.attach,
      F ⟨q.1, (Finset.mem_filter.mp q.2).2⟩) = ∑ k ∈ U, F k
  refine Finset.sum_bij
    (fun q _ => (⟨q.1, (Finset.mem_filter.mp q.2).2⟩ : {k : ℤ // Odd k}))
    ?_ ?_ ?_ ?_
  · intro q hq
    have hxi : I.xiMK m q.1 t ≠ 0 := by
      have hqS₀ : q.1 ∈ S₀ := (Finset.mem_filter.mp q.2).1
      exact (I.xiMK_support_finite m t).mem_toFinset.mp hqS₀
    exact (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mpr hxi
  · intro q₁ hq₁ q₂ hq₂ heq
    have hval : q₁.1 = q₂.1 :=
      congrArg (fun k : {k : ℤ // Odd k} => k.1) heq
    exact Subtype.ext hval
  · intro k hk
    have hxi : I.xiMK m k.1 t ≠ 0 :=
      (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mp hk
    have hkS₀ : k.1 ∈ S₀ := (I.xiMK_support_finite m t).mem_toFinset.mpr hxi
    let q : {z : ℤ // z ∈ S} := ⟨k.1, Finset.mem_filter.mpr ⟨hkS₀, k.2⟩⟩
    refine ⟨q, Finset.mem_attach S q, ?_⟩
    exact Subtype.ext rfl
  · intro q hq
    rfl

/-- A compact form of `tsum_eq_sum` for the odd cutoff support. -/
theorem xiMK_odd_tsum_eq_support_sum
    {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [Module ℝ α]
    (F : {k : ℤ // Odd k} → α) :
    ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t • F k =
      (let S := (I.xiMK_support_finite m t).toFinset.filter Odd
       ∑ q ∈ S.attach,
         I.xiMK m q.1 t • F ⟨q.1, (Finset.mem_filter.mp q.2).2⟩) := by
  classical
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  let S := (I.xiMK_support_finite m t).toFinset.filter Odd
  have hfinite :
      (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t • F k) =
        ∑ k ∈ U, I.xiMK m k.1 t • F k := by
    apply tsum_eq_sum (s := U)
    intro k hk
    have hzero : I.xiMK m k.1 t = 0 := by
      by_contra hne
      exact hk ((AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mpr hne)
    simp [hzero]
  calc
    _ = ∑ k ∈ U, I.xiMK m k.1 t • F k := hfinite
    _ = ∑ q ∈ S.attach,
        I.xiMK m q.1 t • F ⟨q.1, (Finset.mem_filter.mp q.2).2⟩ := by
      symm
      exact xiMK_odd_support_sum_reindex I m hm t
        (F := fun k => I.xiMK m k.1 t • F k)

end AVenhance.Infra.Section5

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic

/-!
# Measure Theory Helpers for Residue Theory

Countability of isolated point sets and measure-zero results for
preimages of singletons under piecewise C¹ immersions.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

theorem Set.countable_setOf_isolated_points'
    {S : Set ℝ}
    (h : ∀ t ∈ S, ∃ ε > 0,
      ∀ s ∈ S, s ≠ t → |s - t| ≥ ε) :
    S.Countable := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  · have h_radii : ∀ t : S, ∃ ε > 0,
        ∀ s ∈ S, s ≠ t.val → |s - t.val| ≥ ε :=
      fun t => h t.val t.prop
    choose r hr_pos hr_sep using h_radii
    let ball : S → Set ℝ := fun t =>
      Metric.ball t.val (r t / 2)
    have h_disj :
        Pairwise (Function.onFun Disjoint ball) := by
      intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h_ne
      simp only [Function.onFun, Set.disjoint_iff,
        ball]
      intro x ⟨hx₁, hx₂⟩
      simp only [Metric.mem_ball,
        Real.dist_eq] at hx₁ hx₂
      have h_ne' : t₁ ≠ t₂ :=
        fun heq => h_ne (by simp [heq])
      have h1 : |t₁ - t₂| ≤ |t₁ - x| + |x - t₂| :=
        abs_sub_le t₁ x t₂
      have h2 : |t₁ - x| < r ⟨t₁, ht₁⟩ / 2 := by
        rw [abs_sub_comm]; exact hx₁
      have h3 : |x - t₂| < r ⟨t₂, ht₂⟩ / 2 := hx₂
      have h4' :=
        hr_sep ⟨t₁, ht₁⟩ t₂ ht₂ (Ne.symm h_ne')
      have h4 : r ⟨t₁, ht₁⟩ ≤ |t₁ - t₂| := by
        rw [abs_sub_comm]; exact h4'
      have h5' :=
        hr_sep ⟨t₂, ht₂⟩ t₁ ht₁ h_ne'
      have h5 : r ⟨t₂, ht₂⟩ ≤ |t₂ - t₁| := by
        rw [abs_sub_comm]; exact h5'
      rw [abs_sub_comm] at h5
      linarith [hr_pos ⟨t₁, ht₁⟩, hr_pos ⟨t₂, ht₂⟩]
    have h_open : ∀ t : S, IsOpen (ball t) :=
      fun _ => Metric.isOpen_ball
    have h_nonempty : ∀ t : S, (ball t).Nonempty :=
      fun t =>
        ⟨t.val,
          Metric.mem_ball_self (by linarith [hr_pos t])⟩
    have h_countable_S : Countable S :=
      Pairwise.countable_of_isOpen_disjoint
        h_disj h_open h_nonempty
    exact Set.countable_coe_iff.mp h_countable_S

/-- Preimage of a singleton under a piecewise C¹
immersion has measure zero. -/
theorem preimage_singleton_measure_zero_of_deriv_ne_zero
    {γ : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (z₀ : ℂ)
    (_hγ : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Icc a b, t ∉ P →
      DifferentiableAt ℝ γ t)
    (hγ'_ne : ∀ t ∈ Icc a b, t ∉ P →
      deriv γ t ≠ 0) :
    volume ({t ∈ Icc a b | γ t = z₀}) = 0 := by
  let S := {t ∈ Icc a b | γ t = z₀}
  have h_isolated : ∀ t₀ ∈ S, t₀ ∉ P →
      ∃ ε > 0, ∀ t ∈ S, t ≠ t₀ → |t - t₀| ≥ ε := by
    intro t₀ ⟨ht₀_Icc, ht₀_eq⟩ ht₀_nP
    have h_diff : DifferentiableAt ℝ γ t₀ :=
      hγ_diff t₀ ht₀_Icc ht₀_nP
    have h_deriv_ne : deriv γ t₀ ≠ 0 :=
      hγ'_ne t₀ ht₀_Icc ht₀_nP
    have h_ev :=
      HasDerivAt.eventually_ne h_diff.hasDerivAt
        h_deriv_ne (c := z₀)
    rw [eventually_nhdsWithin_iff,
      Metric.eventually_nhds_iff] at h_ev
    obtain ⟨ε, hε_pos, h_ball⟩ := h_ev
    use ε, hε_pos
    intro t ⟨_, ht_eq⟩ ht_ne
    by_contra h_lt
    push Not at h_lt
    have h_in_ball : dist t t₀ < ε := by
      simp only [Real.dist_eq]; exact h_lt
    have h_ne' : t ∈ ({t₀} : Set ℝ)ᶜ := by
      simp [ht_ne]
    exact h_ball h_in_ball h_ne' ht_eq
  have h_countable : S.Countable := by
    have h_eq : S = (S ∩ ↑P) ∪ (S \ ↑P) :=
      (Set.inter_union_sdiff S ↑P).symm
    rw [h_eq]
    apply Set.Countable.union
    · exact (P.finite_toSet.subset
        Set.inter_subset_right).countable
    · have h_iso : ∀ t ∈ S \ ↑P, ∃ ε > 0,
          ∀ s ∈ S \ ↑P, s ≠ t → |s - t| ≥ ε := by
        intro t ⟨ht_S, ht_nP⟩
        obtain ⟨ε, hε_pos, h_sep⟩ :=
          h_isolated t ht_S ht_nP
        exact ⟨ε, hε_pos,
          fun s ⟨hs_S, _⟩ hs_ne =>
            h_sep s hs_S hs_ne⟩
      exact Set.countable_setOf_isolated_points' h_iso
  exact h_countable.measure_zero _

end

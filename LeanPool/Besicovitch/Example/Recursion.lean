/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SumOverResidueClass

/-!
# A recursion that forces a sequence to zero

If `u (n+1) ≤ (1 - a (n+1)) * u n + e (n+1)` with `0 ≤ a n ≤ 1`, the partial sums of `a`
unbounded and `e` summable, then `u n → 0`.  This drives the hole argument: the measure of what
survives the level-`n` holes contracts by a factor `1 - c/n` at each level, up to a summable
error, and `∑ 1/n = ∞`.
-/

@[expose] public section

open Filter Finset Topology

namespace LeanPool.Besicovitch.Example

variable {u a e : ℕ → ℝ}

/-- Unrolling the recursion from level `N` to level `n`. -/
theorem le_prod_mul_add_sum_of_recursive (hu : ∀ n, 0 ≤ u n) (ha : ∀ n, 0 ≤ a n)
    (ha1 : ∀ n, a n ≤ 1) (he : ∀ n, 0 ≤ e n)
    (h : ∀ n, u (n + 1) ≤ (1 - a (n + 1)) * u n + e (n + 1)) (N : ℕ) :
    ∀ n, N ≤ n →
      u n ≤ (∏ k ∈ Ioc N n, (1 - a k)) * u N + ∑ k ∈ Ioc N n, e k := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hNn ih =>
    have hprod : 0 ≤ ∏ k ∈ Ioc N n, (1 - a k) := prod_nonneg fun k _ ↦ by linarith [ha1 k]
    have h1a : 0 ≤ 1 - a (n + 1) := by linarith [ha1 (n + 1)]
    rw [Finset.prod_Ioc_succ_top hNn, Finset.sum_Ioc_succ_top hNn]
    calc u (n + 1) ≤ (1 - a (n + 1)) * u n + e (n + 1) := h n
      _ ≤ (1 - a (n + 1)) * ((∏ k ∈ Ioc N n, (1 - a k)) * u N + ∑ k ∈ Ioc N n, e k) +
            e (n + 1) := by gcongr
      _ ≤ (∏ k ∈ Ioc N n, (1 - a k)) * (1 - a (n + 1)) * u N +
            (∑ k ∈ Ioc N n, e k + e (n + 1)) := by
          have hsum : 0 ≤ ∑ k ∈ Ioc N n, e k := sum_nonneg fun k _ ↦ he k
          have : (1 - a (n + 1)) * ∑ k ∈ Ioc N n, e k ≤ ∑ k ∈ Ioc N n, e k :=
            mul_le_of_le_one_left hsum (by linarith [ha (n + 1)])
          nlinarith [hu N]

/-- A product of `1 - a k` is at most `exp (-∑ a k)`. -/
theorem prod_one_sub_le_exp_neg_sum (ha1 : ∀ n, a n ≤ 1) (s : Finset ℕ) :
    ∏ k ∈ s, (1 - a k) ≤ Real.exp (-∑ k ∈ s, a k) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine prod_le_prod (fun k _ ↦ by linarith [ha1 k]) fun k _ ↦ ?_
  have := Real.add_one_le_exp (-a k)
  linarith

/-- The sums `∑_{k ∈ Ioc N n} a k` tend to infinity when the partial sums of `a` do. -/
theorem tendsto_sum_Ioc_atTop (ha : ∀ n, 0 ≤ a n)
    (hasum : Tendsto (fun n ↦ ∑ k ∈ range n, a k) atTop atTop) (N : ℕ) :
    Tendsto (fun n ↦ ∑ k ∈ Ioc N n, a k) atTop atTop := by
  have hsplit : ∀ n, N ≤ n →
      ∑ k ∈ Ioc N n, a k = ∑ k ∈ range (n + 1), a k - ∑ k ∈ range (N + 1), a k := by
    intro n hn
    have hIoc : Ioc N n = Ico (N + 1) (n + 1) := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sub _ (by omega)]
  have h1 : Tendsto (fun n ↦ ∑ k ∈ range (n + 1), a k - ∑ k ∈ range (N + 1), a k)
      atTop atTop := by
    have h0 : Tendsto (fun n ↦ ∑ k ∈ range (n + 1), a k) atTop atTop :=
      hasum.comp (tendsto_add_atTop_nat 1)
    have := tendsto_atTop_add_const_right atTop (-∑ k ∈ range (N + 1), a k) h0
    exact this.congr fun n ↦ (sub_eq_add_neg _ _).symm
  exact h1.congr' ((eventually_ge_atTop N).mono fun n hn ↦ (hsplit n hn).symm)

/-- The main recursion lemma. -/
theorem tendsto_zero_of_recursive (hu : ∀ n, 0 ≤ u n) (ha : ∀ n, 0 ≤ a n)
    (ha1 : ∀ n, a n ≤ 1)
    (he : ∀ n, 0 ≤ e n) (hasum : Tendsto (fun n ↦ ∑ k ∈ range n, a k) atTop atTop)
    (hesum : Summable e)
    (h : ∀ n, u (n + 1) ≤ (1 - a (n + 1)) * u n + e (n + 1)) :
    Tendsto u atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb ↦ Eventually.of_forall fun n ↦ hb.trans_le (hu n), fun ε hε ↦ ?_⟩
  -- choose `N` with the tail of `e` from `N` on at most `ε / 2`
  obtain ⟨N, hN⟩ : ∃ N, ∑' k, e (k + N) ≤ ε / 2 :=
    ((tendsto_sum_nat_add e).eventually (ge_mem_nhds (half_pos hε))).exists
  -- the product from `N` on decays to zero
  have hprod : Tendsto (fun n ↦ ∏ k ∈ Ioc N n, (1 - a k)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun n ↦ Real.exp (-∑ k ∈ Ioc N n, a k)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_sum_Ioc_atTop ha hasum N))
    exact squeeze_zero (fun n ↦ prod_nonneg fun k _ ↦ by linarith [ha1 k])
      (fun n ↦ prod_one_sub_le_exp_neg_sum ha1 _) hexp
  -- the tail of `e` over `Ioc N n` is at most the tail sum from `N`
  have htail : ∀ n, ∑ k ∈ Ioc N n, e k ≤ ∑' k, e (k + N) := by
    intro n
    have hsub : Ioc N n ⊆ (range (n + 1)).image (· + N) := by
      intro k hk
      rw [Finset.mem_Ioc] at hk
      exact Finset.mem_image.mpr ⟨k - N, Finset.mem_range.mpr (by omega), by omega⟩
    calc ∑ k ∈ Ioc N n, e k ≤ ∑ k ∈ (range (n + 1)).image (· + N), e k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ ↦ he k
      _ = ∑ k ∈ range (n + 1), e (k + N) :=
          Finset.sum_image fun _ _ _ _ hxy ↦ by omega
      _ ≤ ∑' k, e (k + N) :=
          Summable.sum_le_tsum _ (fun k _ ↦ he _) ((summable_nat_add_iff N).mpr hesum)
  -- combine
  have hbound := le_prod_mul_add_sum_of_recursive hu ha ha1 he h N
  have hsmall : ∀ᶠ n in atTop, (∏ k ∈ Ioc N n, (1 - a k)) * u N < ε / 2 := by
    rcases (hu N).eq_or_lt with hN0 | hN0
    · exact Eventually.of_forall fun n ↦ by rw [← hN0, mul_zero]; exact half_pos hε
    · have := hprod.eventually (gt_mem_nhds (div_pos (half_pos hε) hN0))
      exact this.mono fun n hn ↦ by rwa [lt_div_iff₀ hN0] at hn
  filter_upwards [hsmall, eventually_ge_atTop N] with n hn hNn
  calc u n ≤ (∏ k ∈ Ioc N n, (1 - a k)) * u N + ∑ k ∈ Ioc N n, e k := hbound n hNn
    _ < ε / 2 + ε / 2 := by linarith [htail n]
    _ = ε := by ring

end LeanPool.Besicovitch.Example

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.BlockAnalysis

/-!
# Selecting the good blocks

This file formalizes the implication from eventual avoidance of the bad-value
slalom to a common zero-sum witness. All hypotheses describe the concrete finite
blocks and the chosen functions; no cardinal-invariant inequality is assumed.
-/

open Filter Finset Topology

namespace NonMRR

/-- Choose block `e n` if it is available, and use the zero block otherwise. -/
def selectedBlock (u : ℕ → ℕ → ℕ → ℝ) (e g : ℕ → ℕ) (n i : ℕ) : ℝ :=
  if e n < g n then u n (e n) i else 0

/-- Values with a large prefix in the natural or the permuted order. -/
noncomputable def badValues (u : ℕ → ℕ → ℕ → ℝ) (g : ℕ → ℕ)
    (π : Equiv.Perm ℕ) (b : ℕ → ℝ) (n : ℕ) : Finset ℕ := by
  classical
  exact (range (g n)).filter (fun k ↦
    (∃ j, b n < ‖rearrangedPartialSum (u n k) (Equiv.refl ℕ) j‖) ∨
    (∃ j, b n < ‖rearrangedPartialSum (u n k) π j‖))

/-- Avoiding a bad value bounds every prefix in both orders. -/
theorem prefix_bounds_of_not_mem_badValues
    (u : ℕ → ℕ → ℕ → ℝ) (g : ℕ → ℕ) (π : Equiv.Perm ℕ) (b : ℕ → ℝ)
    (n k : ℕ) (hk : k < g n) (hgood : k ∉ badValues u g π b n) :
    (∀ j, ‖rearrangedPartialSum (u n k) (Equiv.refl ℕ) j‖ ≤ b n) ∧
    (∀ j, ‖rearrangedPartialSum (u n k) π j‖ ≤ b n) := by
  classical
  constructor
  · intro j
    by_contra h
    exact hgood (mem_filter.mpr ⟨mem_range.mpr hk, Or.inl ⟨j, lt_of_not_ge h⟩⟩)
  · intro j
    by_contra h
    exact hgood (mem_filter.mpr ⟨mem_range.mpr hk, Or.inr ⟨j, lt_of_not_ge h⟩⟩)

/-- Infinitely many selected blocks and eventual avoidance of the bad-value
slalom produce a conditionally convergent series with natural and permuted sum zero. -/
theorem selected_blocks_give_zero_witness
    (u : ℕ → ℕ → ℕ → ℝ) (I : ℕ → Finset ℕ) (e g : ℕ → ℕ)
    (π : Equiv.Perm ℕ)
    (hdisjoint : Pairwise (fun n m ↦ Disjoint (I n) (I m)))
    (hsupport : ∀ n k, k < g n → ∀ i, i ∉ I n → u n k i = 0)
    (hbalance : ∀ n k, k < g n → ∑ i ∈ I n, u n k i = 0)
    (hmass : ∀ n k, k < g n → 1 ≤ ∑ i ∈ I n, ‖u n k i‖)
    (b : ℕ → ℝ) (hb : Summable b) (hbnonneg : ∀ n, 0 ≤ b n)
    (hinfinite : ∃ᶠ n in atTop, e n < g n)
    (havoid : ∀ᶠ n in atTop, e n ∉ badValues u g π b n) :
    let a : ℕ → ℝ := fun i ↦ ∑' n, selectedBlock u e g n i
    Tendsto (rearrangedPartialSum a (Equiv.refl ℕ)) atTop (𝓝 0) ∧
    Tendsto (rearrangedPartialSum a π) atTop (𝓝 0) ∧
    ¬ Summable (fun i ↦ ‖a i‖) := by
  classical
  apply conditional_series_of_disjoint_balanced_blocks
    (selectedBlock u e g) I {n | e n < g n} π hdisjoint
  · intro n i hi
    by_cases hn : e n < g n
    · exact (ite_eq_left hn).trans (hsupport n (e n) hn i hi)
    · exact ite_eq_right hn
  · intro n
    by_cases hn : e n < g n
    · simpa only [selectedBlock, ite_eq_left hn] using hbalance n (e n) hn
    · simp [selectedBlock, hn]
  · exact Nat.frequently_atTop_iff_infinite.mp hinfinite
  · intro n hn
    change e n < g n at hn
    simpa only [selectedBlock, ite_eq_left hn] using hmass n (e n) hn
  · exact hb
  · filter_upwards [havoid] with n hn j
    by_cases he : e n < g n
    · simpa only [rearrangedPartialSum, selectedBlock, ite_eq_left he] using
        (prefix_bounds_of_not_mem_badValues u g π b n (e n) he hn).1 j
    · simpa [rearrangedPartialSum, selectedBlock, he] using hbnonneg n
  · filter_upwards [havoid] with n hn j
    by_cases he : e n < g n
    · simpa only [rearrangedPartialSum, selectedBlock, ite_eq_left he] using
        (prefix_bounds_of_not_mem_badValues u g π b n (e n) he hn).2 j
    · simpa [rearrangedPartialSum, selectedBlock, he] using hbnonneg n

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.FiniteAnalytic
import LeanPool.RearrangementNumber.NonMRR.Walsh

/-! Finite vector constructions. -/

open scoped BigOperators

noncomputable section

namespace NonMRR

@[simp] theorem prefix_zero {L : ℕ} (v : Fin L → ℝ) : vectorPrefix v 0 = 0 := by
  simp [vectorPrefix]

@[simp] theorem prefix_length {L : ℕ} (v : Fin L → ℝ) :
    vectorPrefix v L = ∑ i, v i := by
  simp [vectorPrefix]

theorem prefix_succ_sub {L i : ℕ} (v : Fin L → ℝ) (hi : i < L) :
    vectorPrefix v (i + 1) - vectorPrefix v i = v ⟨i, hi⟩ := by
  classical
  have hs : (Finset.univ.filter fun k : Fin L => k.val < i + 1) =
      insert ⟨i, hi⟩ (Finset.univ.filter fun k : Fin L => k.val < i) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hki : k.val = i
      · exact Or.inl (Fin.ext hki)
      · exact Or.inr (by omega)
    · rintro (rfl | h)
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  unfold vectorPrefix
  rw [hs, Finset.sum_insert (by simp)]
  ring

/-- The counting estimate for every ordering of a family satisfying the Walsh identities. -/
theorem card_bad_prefixes_le {m L q : ℕ} (hL : 0 < L) (hq : 0 < q)
    (v : Fin m → Fin L → ℝ)
    (hbalanced : ∀ k, ∑ i, v k i = 0)
    (habs : ∀ k i, |v k i| = 1 / (L : ℝ))
    (hprefix : ∀ (σ : Equiv.Perm (Fin L)) (j : ℕ),
      ∑ k, (vectorPrefix (v k ∘ σ) j) ^ 2 ≤ 1)
    (σ : Equiv.Perm (Fin L)) :
    (Finset.univ.filter fun k : Fin m =>
      ∃ j ≤ L, 1 / (q : ℝ) < |vectorPrefix (v k ∘ σ) j|).card ≤ 4 * q ^ 4 := by
  classical
  apply card_badWalks_le hL hq (fun k j => vectorPrefix (v k ∘ σ) j)
  · intro k
    exact prefix_zero _
  · intro k
    rw [prefix_length]
    exact (Equiv.sum_comp σ (v k)).trans (hbalanced k)
  · intro k i hi
    rw [prefix_succ_sub _ hi]
    exact (habs k (σ ⟨i, hi⟩)).le
  · intro j _hj
    exact hprefix σ j

/-- For each `m` and positive `q`, there are balanced sign vectors such that every
permutation has at most `4*q^4` vectors with a vectorPrefix exceeding `1/q`.
This is the finite counting estimate in Section 3 of
`Determining the Rearrangement Number`. -/
theorem finite_counting_estimate (m : ℕ) {q : ℕ} (hq : 0 < q) :
    ∃ L : ℕ, 0 < L ∧ ∃ v : Fin m → Fin L → ℝ,
      (∀ k, ∑ i, v k i = 0) ∧
      (∀ k i, |v k i| = 1 / (L : ℝ)) ∧
      (∀ σ : Equiv.Perm (Fin L),
        (Finset.univ.filter fun k : Fin m =>
          ∃ j ≤ L, 1 / (q : ℝ) < |vectorPrefix (v k ∘ σ) j|).card ≤ 4 * q ^ 4) := by
  classical
  obtain ⟨L, hL, v, hbalanced, habs, hprefix⟩ := exists_walsh_vectors m
  exact ⟨L, hL, v, hbalanced, habs,
    fun σ => card_bad_prefixes_le hL hq v hbalanced habs hprefix σ⟩

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

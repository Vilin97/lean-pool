/-
Copyright (c) 2026 Jose Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Fonollosa
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PicardGroup

/-!
# Elementary abelian 2-groups attain the optimal bound

If `g : Fin n → (Fin k → ZMod 2)` has unique multiset sums — the only
multiset of size `n` whose weighted sum of the `g i` equals `∑ i, g i` is
the all-ones multiset — then `n - 1 ≤ k`
(`elementaryAbelianTwoGroups_optimal`). This is the optimality half of
the elementary-abelian case of the minimum-modulus problem.
-/

namespace MinModulus

open scoped BigOperators
open Module

/-- `g` has unique multiset sums: the only multiset of size `n` whose
weighted sum of the `g i` equals `∑ i, g i` is the all-ones multiset. -/
def UniqueMultisetSums {n k : ℕ} (g : Fin n → (Fin k → ZMod 2)) : Prop :=
  ∀ m : Fin n → ℕ,
    (∑ i, m i = n) →
    (∑ i, ((m i : ℕ) : ZMod 2) • g i = ∑ i, g i) →
    ∀ i, m i = 1

/-- A vector in the kernel of the weighted-sum map whose coordinates also
sum to zero must vanish: otherwise its (even-sized) support yields a
multiset of size `n` with the same weighted sum as the all-ones multiset,
contradicting `UniqueMultisetSums`. -/
private lemma eq_zero_of_sum_eq_zero {n k : ℕ} (g : Fin n → (Fin k → ZMod 2))
    (huniq : UniqueMultisetSums g) (u : Fin n → ZMod 2)
    (h_sum : ∑ i, u i = 0) (hu : ∑ i, u i • g i = 0) : u = 0 := by
  have h_ZMod2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  ext i
  by_contra h_nz
  -- Contradiction assumption: u ≠ 0
  let S := Finset.univ.filter (fun j => u j ≠ 0)
  have h_u_one : ∀ j ∈ S, u j = 1 := by
    intro j hj
    have hj_ne : u j ≠ 0 := (Finset.mem_filter.mp hj).2
    rcases h_ZMod2 (u j) with h0 | h1
    · contradiction
    · exact h1
  have h_sum_S : ∑ j, u j = S.card := by
    have eq1 : ∑ j, u j = ∑ j ∈ S, u j + ∑ j ∈ Finset.univ \ S, u j :=
      (Finset.sum_add_sum_compl S _).symm
    rw [eq1]
    have hz : ∑ j ∈ Finset.univ \ S, u j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_contra h_nz_j
      have : j ∈ S := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, h_nz_j⟩
      have h1 : j ∉ S := (Finset.mem_sdiff.mp hj).2
      exact h1 this
    have ho : ∑ j ∈ S, u j = S.card := by
      have : ∑ j ∈ S, u j = ∑ j ∈ S, (1 : ZMod 2) := Finset.sum_congr rfl h_u_one
      rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hz, ho, add_zero]
  have h_even : Even S.card := by
    rw [even_iff_two_dvd]
    have h_cast : (S.card : ZMod 2) = 0 := by rw [← h_sum_S, h_sum]
    exact (CharP.cast_eq_zero_iff (ZMod 2) 2 S.card).mp h_cast
  have h_S_pos : 0 < S.card := by
    apply Finset.card_pos.mpr
    use i
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, h_nz⟩
  obtain ⟨w, hw_eq⟩ := h_even
  have hw_le : w ≤ S.card := by omega
  obtain ⟨S₁, hS₁_sub, hS₁_card⟩ := Finset.exists_subset_card_eq hw_le
  let m : Fin n → ℕ := fun j => if j ∈ S₁ then 2 else if j ∈ S \ S₁ then 0 else 1
  have h_sum_m : ∑ j, m j = n := by
    have eq1 : ∑ j, m j = ∑ j ∈ S, m j + ∑ j ∈ Finset.univ \ S, m j :=
      (Finset.sum_add_sum_compl S m).symm
    have eq2 : ∑ j ∈ S, m j = ∑ j ∈ S₁, m j + ∑ j ∈ S \ S₁, m j := by
      rw [← Finset.sum_sdiff hS₁_sub, add_comm]
    rw [eq1, eq2]
    have hs1 : ∑ j ∈ S₁, m j = S₁.card * 2 := by
      have : ∑ j ∈ S₁, m j = ∑ j ∈ S₁, 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [m]
        rw [ite_eq_left hj]
      rw [this, Finset.sum_const]
      simp
    have hs2 : ∑ j ∈ S \ S₁, m j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      dsimp [m]
      have h1 : j ∉ S₁ := (Finset.mem_sdiff.mp hj).2
      rw [ite_eq_right h1, ite_eq_left hj]
    have hs3 : ∑ j ∈ Finset.univ \ S, m j = (Finset.univ \ S).card := by
      have : ∑ j ∈ Finset.univ \ S, m j = ∑ j ∈ Finset.univ \ S, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [m]
        have h1 : j ∉ S := (Finset.mem_sdiff.mp hj).2
        have h2 : j ∉ S₁ := fun h => h1 (hS₁_sub h)
        have h3 : j ∉ S \ S₁ := fun h => h1 (Finset.mem_sdiff.mp h).1
        rw [ite_eq_right h2, ite_eq_right h3]
      rw [this, Finset.sum_const]
      simp
    rw [hs1, hs2, hs3, hS₁_card]
    have h_card_compl : (Finset.univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [h_card_compl, hw_eq]
    have hS_le_n : S.card ≤ n := by
      have h_le := Finset.card_le_univ S
      rw [Fintype.card_fin] at h_le
      exact h_le
    omega
  have h_sum_g : ∑ j, ((m j : ℕ) : ZMod 2) • g j = ∑ j, g j := by
    have eq1 : ∑ j, ((m j : ℕ) : ZMod 2) • g j
        = ∑ j ∈ S, ((m j : ℕ) : ZMod 2) • g j
          + ∑ j ∈ Finset.univ \ S, ((m j : ℕ) : ZMod 2) • g j :=
      (Finset.sum_add_sum_compl S _).symm
    have eq2 : ∑ j ∈ S, ((m j : ℕ) : ZMod 2) • g j
        = ∑ j ∈ S₁, ((m j : ℕ) : ZMod 2) • g j
          + ∑ j ∈ S \ S₁, ((m j : ℕ) : ZMod 2) • g j := by
      rw [← Finset.sum_sdiff hS₁_sub, add_comm]
    rw [eq1, eq2]
    have hs1 : ∑ j ∈ S₁, ((m j : ℕ) : ZMod 2) • g j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      dsimp [m]
      rw [ite_eq_left hj]
      have : ((2 : ℕ) : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
      rw [this, zero_smul]
    have hs2 : ∑ j ∈ S \ S₁, ((m j : ℕ) : ZMod 2) • g j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      dsimp [m]
      have h1 : j ∉ S₁ := (Finset.mem_sdiff.mp hj).2
      rw [ite_eq_right h1, ite_eq_left hj]
      have : ((0 : ℕ) : ZMod 2) = 0 := Nat.cast_zero
      rw [this, zero_smul]
    have hs3 : ∑ j ∈ Finset.univ \ S, ((m j : ℕ) : ZMod 2) • g j
        = ∑ j ∈ Finset.univ \ S, g j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [m]
      have h1 : j ∉ S := (Finset.mem_sdiff.mp hj).2
      have h2 : j ∉ S₁ := fun h => h1 (hS₁_sub h)
      have h3 : j ∉ S \ S₁ := fun h => h1 (Finset.mem_sdiff.mp h).1
      rw [ite_eq_right h2, ite_eq_right h3]
      have : ((1 : ℕ) : ZMod 2) = 1 := Nat.cast_one
      rw [this, one_smul]
    rw [hs1, hs2, hs3, zero_add, zero_add]
    have h_S_zero : ∑ j ∈ S, g j = 0 := by
      have h_full : ∑ j, u j • g j = 0 := hu
      have eq3 : ∑ j, u j • g j
          = ∑ j ∈ S, u j • g j + ∑ j ∈ Finset.univ \ S, u j • g j :=
        (Finset.sum_add_sum_compl S _).symm
      rw [eq3] at h_full
      have h_out : ∑ j ∈ Finset.univ \ S, u j • g j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hj_zero : u j = 0 := by
          by_contra h_nz_j
          have : j ∈ S := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ j, h_nz_j⟩
          have h1 : j ∉ S := (Finset.mem_sdiff.mp hj).2
          exact h1 this
        rw [hj_zero, zero_smul]
      rw [h_out, add_zero] at h_full
      have h_in : ∑ j ∈ S, u j • g j = ∑ j ∈ S, g j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [h_u_one j hj, one_smul]
      rw [← h_in]
      exact h_full
    have h_final : ∑ j, g j = ∑ j ∈ S, g j + ∑ j ∈ Finset.univ \ S, g j :=
      (Finset.sum_add_sum_compl S _).symm
    rw [h_final, h_S_zero, zero_add]
  have m_ne_ones : m i ≠ 1 := by
    have hi_mem : i ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, h_nz⟩
    by_cases hi1 : i ∈ S₁
    · dsimp [m]
      rw [ite_eq_left hi1]
      decide
    · have hi2 : i ∈ S \ S₁ := Finset.mem_sdiff.mpr ⟨hi_mem, hi1⟩
      dsimp [m]
      rw [ite_eq_right hi1, ite_eq_left hi2]
      decide
  have h_all_ones := huniq m h_sum_m h_sum_g i
  exact m_ne_ones h_all_ones

theorem elementaryAbelianTwoGroups_optimal
    {n k : ℕ} (g : Fin n → (Fin k → ZMod 2))
    (huniq : UniqueMultisetSums g) : n - 1 ≤ k := by
  -- 1. Define Λ_mod directly as a linear map to avoid all Finsupp overhead
  let Λ_mod : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := {
    toFun := fun f => ∑ i, f i • g i,
    map_add' := fun x y => by
      dsimp
      have : ∑ i, (x i + y i) • g i = ∑ i, (x i • g i + y i • g i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [add_smul]
      rw [this, Finset.sum_add_distrib]
    map_smul' := fun r x => by
      dsimp
      have : ∑ i, (r * x i) • g i = ∑ i, r • (x i • g i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_smul r (x i) (g i)
      rw [this, ← Finset.smul_sum]
  }
  -- 2. Define sum_map natively
  let sum_map : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := {
    toFun := fun f => ∑ i, f i,
    map_add' := fun x y => by
      dsimp
      exact Finset.sum_add_distrib
    map_smul' := fun r x => by
      dsimp
      rw [← Finset.mul_sum]
  }
  -- 3. Restrict sum_map to the kernel of Λ_mod
  let sum_map_ker := sum_map.comp (LinearMap.ker Λ_mod).subtype
  have h_ker_triv : LinearMap.ker sum_map_ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro ⟨u, hu_ker⟩ h_sum_map
    have h_sum : ∑ i, u i = 0 := h_sum_map
    have hu : ∑ i, u i • g i = 0 := hu_ker
    exact Subtype.ext (eq_zero_of_sum_eq_zero g huniq u h_sum hu)
  -- Rank-nullity wrap up
  have h_rn := LinearMap.finrank_range_add_finrank_ker sum_map_ker
  rw [h_ker_triv, finrank_bot, add_zero] at h_rn
  have h_top_dim : finrank (ZMod 2) (ZMod 2) = 1 := finrank_self (ZMod 2)
  have h_range_le : finrank (ZMod 2) (LinearMap.range sum_map_ker) ≤ 1 := by
    have h1 := Submodule.finrank_le (LinearMap.range sum_map_ker)
    rw [finrank_self (ZMod 2)] at h1
    exact h1
  have h_ker_le_1 : finrank (ZMod 2) (LinearMap.ker Λ_mod) ≤ 1 := by
    omega
  have h_rank_nullity := LinearMap.finrank_range_add_finrank_ker Λ_mod
  rw [finrank_fintype_fun_eq_card, Fintype.card_fin] at h_rank_nullity
  have h_target_dim : finrank (ZMod 2) (Fin k → ZMod 2) = k := by
    rw [finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h_range_le_k : finrank (ZMod 2) (LinearMap.range Λ_mod) ≤ k := by
    have h1 := Submodule.finrank_le (LinearMap.range Λ_mod)
    omega
  omega

end MinModulus

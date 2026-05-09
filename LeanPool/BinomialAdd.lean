/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Mathlib

open Real PMF BigOperators ENNReal NNReal Finset

lemma PMF.binomial_add_binomial (p : NNReal) (hp : p ≤ 1) (m₁ m₂ : ℕ) :
    (do
      let k ← PMF.binomial p hp (m₁ + m₂)
      return (k : ℕ))
    =
    (do
      let k ← PMF.binomial p hp m₁
      let l ← PMF.binomial p hp m₂
      return (k + l : ℕ) ):= by
  ext n
  show ((PMF.binomial p hp (m₁ + m₂)).bind (fun k => PMF.pure (k : ℕ))) n =
       ((PMF.binomial p hp m₁).bind (fun k =>
         (PMF.binomial p hp m₂).bind (fun l => PMF.pure (k + l : ℕ)))) n
  simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
  by_cases hn : n ≤ m₁ + m₂
  · have hn' : n < m₁ + m₂ + 1 := Nat.lt_succ_of_le hn
    have lhs_eq : (∑ x : Fin (m₁ + m₂ + 1), if n = ↑x then (binomial p hp (m₁ + m₂)) x else 0) =
        (binomial p hp (m₁ + m₂)) ⟨n, hn'⟩ := by
      rw [Finset.sum_eq_single ⟨n, hn'⟩]
      · simp only [↓reduceIte]
      · intro b _ hne
        have hne' : n ≠ (b : ℕ) := by
          intro heq
          apply hne
          ext
          exact heq.symm
        simp only [hne', ↓reduceIte]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [lhs_eq]
    simp only [PMF.binomial_apply, Fin.val_last]
    conv_rhs =>
      arg 2
      ext x
      rw [show (∑ x_1 : Fin (m₂ + 1), if n = ↑x + ↑x_1 then
            (p : ENNReal) ^ ↑x_1 * (1 - (p : ENNReal)) ^ (m₂ - ↑x_1) * ↑(m₂.choose ↑x_1) else 0) =
          if (x : ℕ) ≤ n ∧ n - (x : ℕ) ≤ m₂ then
            (p : ENNReal) ^ (n - (x : ℕ)) * (1 - (p : ENNReal)) ^ (m₂ - (n - (x : ℕ))) * ↑(m₂.choose (n - (x : ℕ)))
          else 0 by
        split_ifs with hcond
        · obtain ⟨hxn, hnxm⟩ := hcond
          rw [Finset.sum_eq_single ⟨n - (x : ℕ), Nat.lt_succ_of_le hnxm⟩]
          · simp only [add_tsub_cancel_of_le hxn, ↓reduceIte]
          · intro b _ hne
            have hne' : n ≠ ↑x + ↑b := by
              intro heq
              apply hne
              ext
              have : n - (x : ℕ) = (b : ℕ) := by omega
              simp only [this]
            simp only [hne', ↓reduceIte]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        · push_neg at hcond
          apply Finset.sum_eq_zero
          intro y _
          simp only [ite_eq_right_iff]
          intro heq
          specialize hcond (by omega : (x : ℕ) ≤ n)
          have hy : (y : ℕ) ≤ m₂ := Fin.is_le y
          omega
      ]
    simp only [mul_ite, mul_zero]
    rw [Nat.add_choose_eq m₁ m₂ n, Nat.cast_sum]
    erw [Finset.mul_sum]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    have lhs_filter : ∑ i ∈ antidiagonal n, (p : ENNReal) ^ n * (1 - (p : ENNReal)) ^ (m₁ + m₂ - n) *
        ↑(m₁.choose i.1 * m₂.choose i.2) =
        ∑ i ∈ (antidiagonal n).filter (fun ij => ij.1 ≤ m₁ ∧ ij.2 ≤ m₂),
        (p : ENNReal) ^ n * (1 - (p : ENNReal)) ^ (m₁ + m₂ - n) *
        ↑(m₁.choose i.1 * m₂.choose i.2) := by
      symm
      apply Finset.sum_filter_of_ne
      intro ⟨i, j⟩ hij hne
      simp only at hne
      constructor
      · by_contra hi
        push_neg at hi
        simp only [Nat.choose_eq_zero_of_lt hi, zero_mul, Nat.cast_zero, mul_zero,
          ne_eq, not_true_eq_false] at hne
      · by_contra hj
        push_neg at hj
        simp only [Nat.choose_eq_zero_of_lt hj, mul_zero, Nat.cast_zero, mul_zero,
          ne_eq, not_true_eq_false] at hne
    rw [lhs_filter]
    symm
    refine Finset.sum_bij' (fun x _ => (↑x, n - ↑x))
        (fun ij hij => ⟨ij.1, Nat.lt_succ_of_le (Finset.mem_filter.mp hij).2.1⟩)
        ?hi ?hj ?left_inv ?right_inv ?h
    case hi =>
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      obtain ⟨_, hxn, hnxm₂⟩ := hx
      simp only
      constructor
      · rw [mem_antidiagonal]
        omega
      · exact ⟨Fin.is_le x, hnxm₂⟩
    case hj =>
      intro ⟨i, j⟩ hij
      rw [Finset.mem_filter] at hij ⊢
      obtain ⟨hij_mem, hi_le, hj_le⟩ := hij
      rw [mem_antidiagonal] at hij_mem
      constructor
      · exact Finset.mem_univ _
      · simp only
        constructor
        · omega
        · omega
    case left_inv =>
      intro x hx
      ext
      simp
    case right_inv =>
      intro ⟨i, j⟩ hij
      rw [Finset.mem_filter] at hij
      rw [mem_antidiagonal] at hij
      simp only [Prod.mk.injEq, true_and]
      omega
    case h =>
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨_, hxn, hnxm₂⟩ := hx
      simp only [Nat.cast_mul]
      have pow_p : (p : ENNReal) ^ (x : ℕ) * (p : ENNReal) ^ (n - (x : ℕ)) = (p : ENNReal) ^ n := by
        rw [← pow_add]
        congr 1
        omega
      have pow_q : (1 - (p : ENNReal)) ^ (m₁ - (x : ℕ)) * (1 - (p : ENNReal)) ^ (m₂ - (n - (x : ℕ))) =
          (1 - (p : ENNReal)) ^ (m₁ + m₂ - n) := by
        rw [← pow_add]
        congr 1
        omega
      ring_nf
      calc (p : ENNReal) ^ (x : ℕ) * (p : ENNReal) ^ (n - (x : ℕ)) *
           (1 - (p : ENNReal)) ^ (m₁ - (x : ℕ)) * (1 - (p : ENNReal)) ^ (m₂ - (n - (x : ℕ))) *
           ↑(m₁.choose (x : ℕ)) * ↑(m₂.choose (n - (x : ℕ)))
        _ = (p : ENNReal) ^ n * ((1 - (p : ENNReal)) ^ (m₁ - (x : ℕ)) *
            (1 - (p : ENNReal)) ^ (m₂ - (n - (x : ℕ)))) * ↑(m₁.choose (x : ℕ)) *
            ↑(m₂.choose (n - (x : ℕ))) := by rw [pow_p]; ring
        _ = (p : ENNReal) ^ n * (1 - (p : ENNReal)) ^ (m₁ + m₂ - n) *
            ↑(m₁.choose (x : ℕ)) * ↑(m₂.choose (n - (x : ℕ))) := by rw [pow_q]
  · push_neg at hn
    have lhs_zero : (∑ x : Fin (m₁ + m₂ + 1), if n = ↑x then (binomial p hp (m₁ + m₂)) x else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      have : (x : ℕ) ≤ m₁ + m₂ := Fin.is_le x
      omega
    have rhs_zero : (∑ x : Fin (m₁ + 1), (binomial p hp m₁) x *
        ∑ x_1 : Fin (m₂ + 1), if n = ↑x + ↑x_1 then (binomial p hp m₂) x_1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have inner_zero : (∑ x_1 : Fin (m₂ + 1), if n = ↑x + ↑x_1 then (binomial p hp m₂) x_1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        simp only [ite_eq_right_iff]
        intro h
        have hx : (x : ℕ) ≤ m₁ := Fin.is_le x
        have hy : (y : ℕ) ≤ m₂ := Fin.is_le y
        omega
      simp [inner_zero]
    rw [lhs_zero, rhs_zero]

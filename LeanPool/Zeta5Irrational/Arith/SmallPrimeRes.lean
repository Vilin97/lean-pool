/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.Pullback
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Small primes: products over the poles `±1, …, ±K`

* `∏_{s ∈ PlK K} (m - s) = (K!)² C(m-1, K) C(m+K, K)` for `m > K`;
* the residue denominators `∏_{s ≠ r} (r - s)` at `r = ±j`, and
  `v_p((K!)² / ∏_{s ≠ r} (r - s)) ≥ -log_p (2K)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma prod_Icc_sub_mul_factorial (a : ℕ) :
    ∀ c : ℕ,
      c < a →
        (∏ i ∈ Icc 1 c, ((a : ℚ) - i)) * ((a - 1 - c).factorial : ℚ) = ((a - 1).factorial : ℚ) := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    rw [Finset.prod_Icc_succ_top (by omega), ← ih (by omega)]
    have e : a - 1 - c = (a - 1 - (c + 1)) + 1 := by omega
    rw [e, Nat.factorial_succ]
    push_cast [show c + 1 ≤ a by omega, show 1 ≤ a by omega]
    rw [show ((a - 1 - (c + 1) : ℕ) : ℚ) = (a : ℚ) - 1 - (c + 1) by
        push_cast [show c + 1 ≤ a - 1 by omega, show 1 ≤ a by omega]; ring]
    ring

lemma prod_Icc_add_mul_factorial (a c : ℕ) :
    (∏ i ∈ Icc 1 c, ((a : ℚ) + i)) * (a.factorial : ℚ) = ((a + c).factorial : ℚ) := by
  induction c with
  | zero => simp
  | succ c
    ih =>
    rw [Finset.prod_Icc_succ_top (by omega), mul_right_comm, ih, ← add_assoc, Nat.factorial_succ]
    push_cast; ring

lemma prod_Ioc_sub (j t : ℕ) :
    ∏ i ∈ Ioc j (j + t), ((j : ℚ) - i) = (-1) ^ t * (t.factorial : ℚ) := by
  induction t with
  | zero => simp
  | succ t
    ih =>
    rw [← add_assoc, Finset.prod_Ioc_succ_top (by omega), ih, Nat.factorial_succ, pow_succ]
    push_cast; ring

/-- `∏_{j ≤ K} (m - j) = K! C(m-1, K)` for `m > K`. -/
lemma prod_Icc_sub_eq_choose {m K : ℕ} (h : K < m) :
    ∏ j ∈ Icc 1 K, ((m : ℚ) - j) = (K.factorial : ℚ) * ((m - 1).choose K : ℚ) := by
  have h1 := prod_Icc_sub_mul_factorial m K h
  have h2 :
    ((m - 1).choose K : ℚ) * (K.factorial : ℚ) * ((m - 1 - K).factorial : ℚ) =
      ((m - 1).factorial : ℚ) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : K ≤ m - 1)
  have hne : ((m - 1 - K).factorial : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  rw [h1, ← h2]; ring

/-- `∏_{j ≤ K} (m + j) = K! C(m+K, K)`. -/
lemma prod_Icc_add_eq_choose (m K : ℕ) :
    ∏ j ∈ Icc 1 K, ((m : ℚ) + j) = (K.factorial : ℚ) * ((m + K).choose K : ℚ) := by
  have h1 := prod_Icc_add_mul_factorial m K
  have h2 :
    ((m + K).choose K : ℚ) * (K.factorial : ℚ) * (m.factorial : ℚ) = ((m + K).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : K ≤ m + K)
    rw [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hne : (m.factorial : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  rw [h1, ← h2]; ring

/-- The pole product at a point `m > K`. -/
lemma prod_PlK_sub {m K : ℕ} (h : K < m) :
    ∏ s ∈ PlK K, ((m : ℚ) - s) =
      (K.factorial : ℚ) ^ 2 * ((m - 1).choose K : ℚ) * ((m + K).choose K : ℚ) := by
  rw [prod_PlK, Finset.prod_mul_distrib]
  simp only [Int.cast_natCast, Int.cast_neg, sub_neg_eq_add]
  rw [prod_Icc_sub_eq_choose h, prod_Icc_add_eq_choose]; ring

/-- The product `∏_{i ≤ K, i ≠ j} (j - i)`. -/
lemma prod_Icc_ite_sub {j K : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ∏ i ∈ Icc 1 K, (if i = j then (1 : ℚ) else (j : ℚ) - i) =
      (-1) ^ (K - j) * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) := by
  have hsplit : Icc 1 K = Icc 1 j ∪ Ioc j K := by
    ext i;
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 j) (Ioc j K) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  rw [hsplit, Finset.prod_union hdisj]
  have hA : ∏ i ∈ Icc 1 j, (if i = j then (1 : ℚ) else (j : ℚ) - i) = ((j - 1).factorial : ℚ) := by
    obtain ⟨c, rfl⟩ : ∃ c, j = c + 1 := ⟨j - 1, by omega⟩
    rw [Finset.prod_Icc_succ_top (by omega), ite_eq_left rfl, mul_one]
    rw [Finset.prod_congr rfl
        (fun i hi => ite_eq_right (by have := Finset.mem_Icc.mp hi; omega) :
          ∀ i ∈ Icc 1 c,
            (if i = c + 1 then (1 : ℚ) else ((c + 1 : ℕ) : ℚ) - i) = ((c + 1 : ℕ) : ℚ) - i)]
    have := prod_Icc_sub_mul_factorial (c + 1) c (by omega)
    rw [show c + 1 - 1 - c = 0 by omega, Nat.factorial_zero, Nat.cast_one, mul_one] at this
    rw [this]
  have hB :
    ∏ i ∈ Ioc j K, (if i = j then (1 : ℚ) else (j : ℚ) - i) =
      (-1) ^ (K - j) * ((K - j).factorial : ℚ) := by
    rw [Finset.prod_congr rfl
        (fun i hi => ite_eq_right (by have := Finset.mem_Ioc.mp hi; omega) :
          ∀ i ∈ Ioc j K, (if i = j then (1 : ℚ) else (j : ℚ) - i) = (j : ℚ) - i)]
    have := prod_Ioc_sub j (K - j)
    rwa [show j + (K - j) = K by omega] at this
  rw [hA, hB]; ring

/-- Residue denominator at `r = ±j`, up to sign. -/
lemma prod_erase_PlK {j K : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ σ : ℚ,
      (σ = 1 ∨ σ = -1) ∧
        ∏ s ∈ (PlK K).erase (ε * j), (((ε * j : ℤ) : ℚ) - s) =
          σ * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) * ((K + j).factorial : ℚ) /
            (j.factorial : ℚ) := by
  classical
  set r : ℤ := ε * j with hr
  have hrmem : r ∈ PlK K := by
    rcases hε with rfl | rfl
    · simp only [hr, one_mul, PlK, Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjK⟩, rfl⟩
    · simp only [hr, neg_one_mul, PlK, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjK⟩, rfl⟩
  set f : ℤ → ℚ := fun s => if s = r then 1 else (r : ℚ) - s with hf
  have e1 : ∏ s ∈ (PlK K).erase r, ((r : ℚ) - s) = ∏ s ∈ PlK K, f s := by
    rw [← Finset.prod_erase_mul _ _ hrmem]
    simp only [hf, ite_eq_left rfl, mul_one]
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [ite_eq_right (Finset.mem_erase.mp hs).1]
  rw [e1, prod_PlK]
  have hPj := prod_Icc_ite_sub hj1 hjK
  have hjf : (j.factorial : ℚ) ≠ 0 := by positivity
  have hA' : ∏ i ∈ Icc 1 K, ((j : ℚ) + i) = ((K + j).factorial : ℚ) / (j.factorial : ℚ) := by
    rw [eq_div_iff hjf, prod_Icc_add_mul_factorial j K, add_comm]
  rcases hε with hε | hε
  · refine ⟨(-1) ^ (K - j), by rcases neg_one_pow_eq_or ℚ (K - j) with h | h <;> simp [h], ?_⟩
    have e2 :
      ∀ i ∈ Icc 1 K,
        f (i : ℤ) * f (-(i : ℤ)) = (if i = j then (1 : ℚ) else (j : ℚ) - i) * ((j : ℚ) + i) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      simp only [hf, hr, hε, one_mul]
      rw [ite_eq_right (by omega : -(i : ℤ) ≠ (j : ℤ))]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right (by exact_mod_cast hij), ite_eq_right hij]; push_cast; ring
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, hPj, hA']
    ring
  · refine ⟨(-1) ^ (K - j) * (-1) ^ (2 * K - 1), ?_, ?_⟩
    · rcases neg_one_pow_eq_or ℚ (K - j) with h | h <;>
          rcases neg_one_pow_eq_or ℚ (2 * K - 1) with h' | h' <;>
        simp [h, h']
    have e2 :
      ∀ i ∈ Icc 1 K,
        f (i : ℤ) * f (-(i : ℤ)) =
          ((-1) * ((j : ℚ) + i)) * ((-1) * (if i = j then (-1 : ℚ) else (j : ℚ) - i)) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      simp only [hf, hr, hε, neg_one_mul]
      rw [ite_eq_right (by omega : (i : ℤ) ≠ -(j : ℤ))]
      by_cases hij : i = j
      · subst hij; simp; ring
      · rw [ite_eq_right (by intro h; exact hij (by exact_mod_cast neg_injective h)),
          ite_eq_right hij]
        push_cast; ring
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    have hPj' :
      ∏ i ∈ Icc 1 K, (if i = j then (-1 : ℚ) else (j : ℚ) - i) =
        -((-1) ^ (K - j) * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ)) := by
      rw [← hPj, ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.mpr ⟨hj1, hjK⟩), ←
        Finset.mul_prod_erase (Icc 1 K) (fun i => if i = j then (1 : ℚ) else (j : ℚ) - i)
          (Finset.mem_Icc.mpr ⟨hj1, hjK⟩),
        ite_eq_left rfl, ite_eq_left rfl]
      rw [Finset.prod_congr rfl (fun i hi => by rw [ite_eq_right (Finset.mem_erase.mp hi).1]),
        Finset.prod_congr rfl
          (fun i hi => by rw [ite_eq_right (Finset.mem_erase.mp hi).1] :
            ∀ i ∈ (Icc 1 K).erase j, (if i = j then (1 : ℚ) else (j : ℚ) - i) = (j : ℚ) - i)]
      ring
    rw [hPj', hA']
    have h2K : (-1 : ℚ) ^ (2 * K - 1) * (-1) = 1 := by
      rw [← pow_succ, show 2 * K - 1 + 1 = 2 * K by omega, pow_mul]; norm_num
    have hodd : (-1 : ℚ) ^ (2 * K - 1) = -1 := by linear_combination (-1 : ℚ) * h2K
    have hK2 : (-1 : ℚ) ^ K * (-1) ^ K = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [hodd]
    linear_combination
      (-((-1 : ℚ) ^ (K - j) * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) *
            (((K + j).factorial : ℚ) / (j.factorial : ℚ)))) *
        hK2

end Zeta5Irrational

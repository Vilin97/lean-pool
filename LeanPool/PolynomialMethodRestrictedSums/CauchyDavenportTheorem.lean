/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Prime.Factorial
import LeanPool.PolynomialMethodRestrictedSums.ANRPolynomialMethod

/-!
# The Cauchy-Davenport theorem

Derives the Cauchy-Davenport theorem `cauchy_davenport` on sumsets in `ZMod p`
from the Alon-Nathanson-Ruzsa polynomial method.
-/

open Finsupp
open scoped Finset
open MvPolynomial
open BigOperators

-- 2.1
variable {R : Type*} [CommRing R]
-- variable {p : ℕ} [Fact p.Prime]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

--
-- 1.  Fin 2
lemma sum_fin_two {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    ∑ i, f i = f 0 + f 1 := by
  rw [Fin.sum_univ_two]



-- 2.  ZMod p
lemma binomial_coeff_ne_zero_mod_p (n k : ℕ) (hp : p.Prime) (h_k : k ≤ n) (h_n : n < p) :
    (Nat.choose n k : ZMod p) ≠ 0 := by
  -- 1.  ≠   ... = ...
  rw [ne_eq]
  -- 2.  ZMod p  = 0  (p ∣ n.choose k)
  rw [CharP.cast_eq_zero_iff (ZMod p) p]
  -- 3.  p  n.choose k
  intro h_dvd
  -- 4.  p ∣ n.choose k → p ∣ n!
  have key : n.choose k ∣ n.factorial := by
    have h_eq := Nat.choose_mul_factorial_mul_factorial h_k
    rw [mul_assoc] at h_eq
    rw [mul_comm] at h_eq
    rw [← h_eq]
    exact Nat.dvd_mul_left _ _
  have h_dvd_fact : p ∣ n.factorial := dvd_trans h_dvd key
  -- 5.  p ∣ n!  p ≤ n
  rw [Nat.Prime.dvd_factorial] at h_dvd_fact
  · linarith
  exact hp



/-- The sumset `A + B = { a + b | a ∈ A, b ∈ B }` as a `Finset`. -/
def sumset {α : Type*} [Add α] [DecidableEq α] (A B : Finset α) : Finset α :=
  (A ×ˢ B).image (fun x => x.1 + x.2)

variable {A B : Finset (ZMod p)}

-- 3.  "Case 1" ()
lemma cauchy_davenport_small_sum (A B S : Finset (ZMod p)) (hp : p.Prime)
    (hA : A.Nonempty) (hB : B.Nonempty) (h_sum : A.card + B.card ≤ p + 1)
    (hS : S = sumset A B) : S.card ≥ A.card + B.card - 1 := by
  let k_val := 1 --k=1
  let As : Fin 2 → Finset (ZMod p) := ![A, B]  --Fin 2  {0,1} A0,A1
  let cs : Fin 2 → ℕ := ![A.card - 1, B.card - 1]
  let h_poly : MvPolynomial (Fin 2) (ZMod p) := 1
  let m := A.card + B.card - 2
  have h_card : ∀ i, (As i).card = cs i + 1 := by -- |Ai|ci+1
    intro i; fin_cases i
    · simp only [As, cs]
      exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hA.card_pos)).symm
    · simp only [As, cs]
      exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hB.card_pos)).symm
  have h_deg : m + h_poly.totalDegree = ∑ i, cs i := by -- m∑cideg(h)
    simp only [h_poly, m, cs, MvPolynomial.totalDegree_one, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
    rw [show 2 = 1 + 1 by rfl]
    rw [Nat.sub_add_eq]-- x - (y + z) = x - y - z
    have h_A_neg_zero : 1 ≤ A.card := by exact Finset.one_le_card.mpr hA
    have h_B_neg_zero : 1 ≤ B.card := by exact Finset.one_le_card.mpr hB
    rw [Nat.add_comm, Nat.add_sub_assoc h_A_neg_zero, add_comm,← Nat.add_sub_assoc h_B_neg_zero]
  have h_coeff_ne_zero : coeff (equivFunOnFinite.symm cs) ((∑ i : Fin 2, X i) ^ m * h_poly) ≠ 0 :=
      by
    simp only [h_poly, mul_one, Fin.sum_univ_two]
    rw [add_pow]
    rw [coeff_sum]
    rw [Finset.sum_eq_single (cs 0)] --  (m_1 = cs 0)
    · --  1  ()
      have h_exp : m - cs 0 = cs 1 := by
        dsimp [m, cs]
        aesop
      rw [h_exp] --  m - cs 0  cs 1
      rw [mul_comm]
      rw [show (↑(m.choose (cs 0)) : MvPolynomial (Fin 2) (ZMod p)) =
              C (m.choose (cs 0) : ZMod p) by simp]
      rw [MvPolynomial.coeff_C_mul]
      apply mul_ne_zero
      · apply binomial_coeff_ne_zero_mod_p
        · exact hp
        · dsimp [m, cs]; aesop --  cs 0 ≤ m
        · --  m < p
          dsimp [m]
          have : A.card + B.card ≤ p + 1 := h_sum
          have h1 : A.card + B.card - 2 ≤ p - 1 := by omega
          have h2 : 0 < p := hp.pos
          have h3 : p - 1 < p := by exact Nat.sub_lt (h2) (Nat.zero_lt_one)
          exact lt_of_le_of_lt h1 h3
      · simp only [X, monomial_pow, monomial_mul]
        rw [coeff_monomial]
        rw [if_pos]
        · rw [one_pow, one_pow, one_mul]; exact one_ne_zero
        · --
          ext i; fin_cases i
          · simp [cs]
          · simp [cs]
    · --  2  (b ≠ cs 0)  0
      intro b hb_range h_ne
      rw [show (↑(m.choose b) : MvPolynomial (Fin 2) (ZMod p)) = C (m.choose b : ZMod p) by simp]
      rw [mul_comm, coeff_C_mul]
      simp only [X, monomial_pow, monomial_mul]
      rw [coeff_monomial]
      rw [if_neg]
      · simp -- 0 *  = 0
      · --  b = cs 0
        intro h_eq
        rw [Finsupp.ext_iff] at h_eq
        specialize h_eq 0
        simp only [Finsupp.add_apply] at h_eq
        simp [cs] at h_eq
        contradiction
    · --  3  cs 0  (cs 0 < m + 1)
      intro h_notin
      exfalso --
      apply h_notin
      rw [Finset.mem_range]
      dsimp [m, cs]
      have hA_pos : 1 ≤ A.card := Finset.one_le_card.mpr hA
      have hB_pos : 1 ≤ B.card := Finset.one_le_card.mpr hB
      omega
  have h_ANR := ANR_polynomial_method h_poly As cs h_card m h_deg h_coeff_ne_zero
  let S_ANR :=
      (Fintype.piFinset As).filter (fun f => h_poly.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
  have h_card_ge : S_ANR.card ≥ m + 1 := h_ANR.1
  have h_set_eq : S = S_ANR := by
    rw [hS]
    dsimp [S_ANR, sumset]
    have h_eval_ne_zero : ∀ f ∈ Fintype.piFinset As, h_poly.eval f ≠ 0 := by
      intro f _
      simp [h_poly]
    ext z
    simp only [Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      let f : Fin 2 → ZMod p := ![a, b]
      refine ⟨f, ?_, ?_⟩
      · rw [Finset.mem_filter, Fintype.mem_piFinset]
        constructor
        · intro i
          fin_cases i
          · simp only [f, As, Fin.zero_eta, Fin.isValue]; exact ha
          · simp only [f, As, Fin.mk_one, Fin.isValue]; exact hb
        · simp [h_poly] -- h_poly  1
      · rw [sum_fin_two]
        simp [f]
    · --  2: z ∈ S_ANR → z ∈ sumset A B
      rintro ⟨f, hf, rfl⟩
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
      use (f 0, f 1)
      constructor
      · --  1:  (f 0, f 1) ∈ A  B
        dsimp
        constructor
        · --  f 0 ∈ A
          have hf0 := hf.1 0
          simp only [As, Matrix.cons_val_zero] at hf0
          exact hf0
        · --  f 1 ∈ B
          have hf1 := hf.1 1
          simp only [As, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hf1
          exact hf1
      · --  2:  (f 0) + (f 1) = z
        rw [sum_fin_two] --  ∑ f i = f 0 + f 1
  rw [h_set_eq]
  dsimp [m] at h_card_ge
  have hA_ge_1 : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hB_ge_1 : 1 ≤ B.card := Finset.one_le_card.mpr hB
  omega


-- 4.  ( Case 2 )
theorem cauchy_davenport (A B S : Finset (ZMod p)) (hp : p.Prime)
    (hA : A.Nonempty) (hB : B.Nonempty) (hS : S = sumset A B) :
    min p (A.card + B.card - 1) ≤ S.card := by
  by_cases h : A.card + B.card ≤ p + 1
  {
    -- === Case 1:  ===
    rw [min_eq_right (Nat.sub_le_iff_le_add.mpr h)]
    apply cauchy_davenport_small_sum
    · exact hp
    · exact hA
    · exact hB
    · exact h
    · omega
  }
  {
    -- === Case 2: (Subset Reduction) ===
    rw [not_le] at h -- h : A.card + B.card > p + 1
    rw [min_eq_left]
    · let target := p + 1 - A.card
      --  target ≤ |B| B  B'
      have h_target_le_B : target ≤ B.card := by omega
      --  B'  ( |A| ≤ p)
      have h_target_pos : target > 0 := by
         apply Nat.sub_pos_of_lt
         apply Nat.lt_succ_of_le
         have h_le : A.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ A
         rw [ZMod.card p] at h_le
         exact h_le
      obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq h_target_le_B
      have hB'_ne : B'.Nonempty := by rw [←Finset.card_pos, hB'_card]; exact h_target_pos
      have h_sum_exact : A.card + B'.card = p + 1 := by
        rw [hB'_card]
        dsimp [target]
        omega
      have h_new_sum_le : A.card + B'.card ≤ p + 1 := le_of_eq h_sum_exact
      have h_lower_bound : (sumset A B').card ≥ p := by
        have step1 :=
            cauchy_davenport_small_sum A B' (sumset A B') Fact.out hA hB'_ne h_new_sum_le rfl
        rw [h_sum_exact] at step1
        norm_num at step1
        exact step1
      have h_subset_sum : sumset A B' ⊆ sumset A B := Finset.add_subset_add_left hB'_sub
      apply Nat.le_trans h_lower_bound
      rw [hS]
      apply Finset.card_le_card h_subset_sum
    · omega
  }

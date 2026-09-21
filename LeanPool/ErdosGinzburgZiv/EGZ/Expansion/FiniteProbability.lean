/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Elementary uniform probabilities on finite sample spaces

These lemmas keep the sampling estimates for exchanges finite and explicit.
-/

open scoped BigOperators

namespace EGZ.Expansion

noncomputable def finiteProb {A : Type*} [Fintype A] (P : A → Prop) : ℝ := by
  classical
  exact 𝔼 a, if P a then 1 else 0

theorem finiteProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ finiteProb P := by
  classical
  exact Finset.expect_nonneg (by intro a _; split_ifs <;> norm_num)

theorem finiteProb_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : finiteProb P ≤ finiteProb Q := by
  classical
  apply Finset.expect_le_expect
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

@[simp] theorem finiteProb_true {A : Type*} [Fintype A] [Nonempty A] :
    finiteProb (fun _ : A ↦ True) = 1 := by
  simp [finiteProb]

@[simp] theorem finiteProb_false {A : Type*} [Fintype A] :
    finiteProb (fun _ : A ↦ False) = 0 := by
  simp [finiteProb]

theorem finiteProb_le_one {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    finiteProb P ≤ 1 := by
  simpa using finiteProb_mono (P := P) (Q := fun _ ↦ True) (by simp)

theorem finiteProb_not {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    finiteProb (fun a ↦ ¬P a) = 1 - finiteProb P := by
  classical
  unfold finiteProb
  rw [← Fintype.expect_const (ι := A) (1 : ℝ), ← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro a _
  by_cases h : P a <;> simp [h]

theorem finiteProb_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (P : I → A → Prop) :
    finiteProb (fun a ↦ ∃ i, P i a) ≤ ∑ i, finiteProb (P i) := by
  classical
  unfold finiteProb
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro a _
  by_cases h : ∃ i, P i a
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    exact (by simp [hi] : (1 : ℝ) ≤ if P i a then 1 else 0).trans
      (Finset.single_le_sum (f := fun j ↦ if P j a then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ i))
  · simp only [h, ↓reduceIte]
    positivity

theorem exists_forall_not_of_sum_finiteProb_lt_one {A I : Type*}
    [Fintype A] [Nonempty A] [Fintype I] (P : I → A → Prop)
    (h : (∑ i, finiteProb (P i)) < 1) : ∃ a, ∀ i, ¬P i a := by
  by_contra! hn
  have hp : finiteProb (fun a ↦ ∃ i, P i a) = 1 := by
    have heq : (fun a ↦ ∃ i, P i a) = (fun _ : A ↦ True) := by
      funext a
      exact propext ⟨fun _ ↦ trivial, fun _ ↦ hn a⟩
    rw [heq, finiteProb_true]
  have := finiteProb_exists_le P
  linarith

theorem finiteProb_prod {A B : Type*} [Fintype A] [Fintype B]
    (P : A × B → Prop) :
    finiteProb P = 𝔼 a, finiteProb (fun b ↦ P (a, b)) := by
  classical
  simpa only [finiteProb, Finset.univ_product_univ] using
    Finset.expect_product Finset.univ Finset.univ (fun x : A × B ↦ if P x then (1 : ℝ) else 0)

theorem expect_pi_split {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] (i : I) (f : (∀ i, A i) → ℝ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b : ∀ j : {j // j ≠ i}, A j,
      f ((Equiv.piSplitAt i A).symm (a, b)) := by
  rw [Fintype.expect_equiv (Equiv.piSplitAt i A) f
    (fun x ↦ f ((Equiv.piSplitAt i A).symm x))
    (by intro x; exact congrArg f ((Equiv.piSplitAt i A).symm_apply_apply x).symm)]
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product Finset.univ Finset.univ
      (fun x ↦ f ((Equiv.piSplitAt i A).symm x))

theorem expect_pi_eval {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (i : I) (f : A i → ℝ) : (𝔼 x : ∀ i, A i, f (x i)) = 𝔼 a, f a := by
  classical
  rw [expect_pi_split A i]
  simp [Equiv.piSplitAt]

theorem finiteProb_pi_eval {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (i : I) (P : A i → Prop) :
    finiteProb (fun x : ∀ i, A i ↦ P (x i)) = finiteProb P := by
  classical
  exact expect_pi_eval A i (fun a ↦ if P a then 1 else 0)

theorem finiteProb_eq_card {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] :
    finiteProb P = ((Finset.univ.filter P).card : ℝ) / Fintype.card A := by
  classical
  rw [finiteProb, Fintype.expect_eq_sum_div_card]
  congr 1
  have h : (∑ a : A, if P a then (1 : ℕ) else 0) = (Finset.univ.filter P).card :=
    Finset.sum_boole _ _
  exact_mod_cast h

@[simp] theorem finiteProb_eq {A : Type*} [Fintype A] (a : A) :
    finiteProb (fun x ↦ x = a) = 1 / (Fintype.card A : ℝ) := by
  classical
  simp [finiteProb]

/-- The two samples at distinct coordinates of a finite product are
independent, including when the coordinate types differ. -/
theorem expect_pi_pair {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    {i j : I} (hij : j ≠ i) (f : A i → A j → ℝ) :
    (𝔼 x : ∀ k, A k, f (x i) (x j)) = 𝔼 a, 𝔼 b, f a b := by
  rw [expect_pi_split A i]
  apply Finset.expect_congr rfl
  intro a _
  simpa only [Equiv.piSplitAt_symm_apply, ↓reduceDIte, dite_eq_right hij] using
    expect_pi_eval (fun k : {k // k ≠ i} ↦ A k) ⟨j, hij⟩ (f a)

theorem finiteProb_pi_pair {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    {i j : I} (hij : j ≠ i) (P : A i → A j → Prop) :
    finiteProb (fun x : ∀ k, A k ↦ P (x i) (x j)) =
      𝔼 a, finiteProb (P a) := by
  classical
  exact expect_pi_pair A hij (fun a b ↦ if P a b then 1 else 0)

/-- A collision after injectively encoding the two coordinate types has
probability at most the reciprocal size of the second coordinate type. -/
theorem finiteProb_pi_collision_le {I B : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (v : ∀ i, A i → B) (hv : ∀ i, Function.Injective (v i))
    {i j : I} (hij : j ≠ i) :
    finiteProb (fun x : ∀ k, A k ↦ v i (x i) = v j (x j)) ≤
      1 / (Fintype.card (A j) : ℝ) := by
  rw [finiteProb_pi_pair A hij (fun a b ↦ v i a = v j b)]
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  by_cases he : ∃ b, v i a = v j b
  · obtain ⟨b, hb⟩ := he
    have hp : (fun x ↦ v i a = v j x) = (fun x ↦ x = b) := by
      funext x
      exact propext (by rw [hb, (hv j).eq_iff, eq_comm])
    rw [hp, finiteProb_eq]
  · have hp : (fun x ↦ v i a = v j x) = (fun _ : A j ↦ False) := by
      funext x
      exact propext ⟨fun h ↦ he ⟨x, h⟩, False.elim⟩
    rw [hp, finiteProb_false]
    positivity

/-- A union bound controls all repeated positions in an independent
sample. The deliberately loose square bound avoids ordering the indices. -/
theorem finiteProb_not_injective_le {I B : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (v : ∀ i, A i → B) (hv : ∀ i, Function.Injective (v i))
    {M : ℝ} (hM : 0 < M) (hsize : ∀ i, M ≤ Fintype.card (A i)) :
    finiteProb (fun x : ∀ i, A i ↦ ¬Function.Injective (fun i ↦ v i (x i))) ≤
      (Fintype.card I : ℝ) ^ 2 / M := by
  classical
  let bad : I × I → (∀ i, A i) → Prop := fun ij x ↦
    ij.1 ≠ ij.2 ∧ v ij.1 (x ij.1) = v ij.2 (x ij.2)
  have hpoint (ij : I × I) : finiteProb (bad ij) ≤ 1 / M := by
    by_cases h : ij.1 = ij.2
    · have heq : bad ij = fun _ ↦ False := by
        funext x
        simp [bad, h]
      rw [heq, finiteProb_false]
      positivity
    · calc
        finiteProb (bad ij) ≤ finiteProb (fun x ↦ v ij.1 (x ij.1) = v ij.2 (x ij.2)) :=
          finiteProb_mono (fun _ hx ↦ hx.2)
        _ ≤ 1 / (Fintype.card (A ij.2) : ℝ) :=
          finiteProb_pi_collision_le A v hv (Ne.symm h)
        _ ≤ 1 / M := one_div_le_one_div_of_le hM (hsize ij.2)
  calc
    finiteProb (fun x : ∀ i, A i ↦ ¬Function.Injective (fun i ↦ v i (x i))) ≤
        finiteProb (fun x ↦ ∃ ij, bad ij x) := by
      apply finiteProb_mono
      intro x hx
      by_contra! hn
      apply hx
      intro i j hij
      by_contra hne
      exact hn (i, j) ⟨hne, hij⟩
    _ ≤ ∑ ij, finiteProb (bad ij) := finiteProb_exists_le bad
    _ ≤ ∑ _ij : I × I, 1 / M := Finset.sum_le_sum (fun ij _ ↦ hpoint ij)
    _ = (Fintype.card I : ℝ) ^ 2 / M := by
      simp [Fintype.card_prod, Nat.cast_mul, pow_two, div_eq_mul_inv]

end EGZ.Expansion

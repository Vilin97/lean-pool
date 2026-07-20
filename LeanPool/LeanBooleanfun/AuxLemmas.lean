/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic

/-!
General lemmas not specific to analysis of Boolean functions.
-/

namespace LeanPool.LeanBooleanfun.BooleanFun

open Finset Pi

variable {α : Type*}

variable {ι : Type*} [Fintype ι]

-- not to be confused with `Finset.sum_singleton`
lemma sum_singletons [AddCommMonoid α] {F : Finset ι → α} {G : ι → α} (h : ∀ i, F {i} = G i) :
    ∑ S ∈ {S | S.card = 1}, F S = ∑ i, G i := by
  symm
  apply sum_of_injOn (e := fun i ↦ {i})
  · intro j _ l _ h'
    simp only at h'
    exact Finset.singleton_inj.mp h'
  · intro j _
    simp
  · intro S hS hS'
    simp only [mem_filter, mem_univ, true_and] at hS
    obtain ⟨i, hi⟩ := card_eq_one.mp hS
    simp only [coe_univ, Set.image_univ, Set.mem_range, not_exists] at hS'
    exact absurd hi.symm (hS' i)
  · intro i _
    symm
    exact h i

lemma sum_singletons' [AddCommMonoid α] {F : Finset ι → α} :
    ∑ S ∈ {S | S.card = 1}, F S = ∑ i, F {i} := by apply sum_singletons; intro i; rfl

variable {P : Prop} [Decidable P] {a b c : α}

lemma ite_ite_same (a b c : α) :
    ite P (ite P a b) c = ite P a c := by split_ifs <;> rfl

lemma rw_ite_left (h : P → a = c) :
    ite P a b = ite P c b := by
  split_ifs with hp
  · rw [h hp]
  · rfl

lemma rw_ite_right (h : ¬P → a = c) :
    ite P b a = ite P b c := by
  split_ifs with hp
  · rfl
  · rw [h hp]

lemma ite_add_ite {α : Type*} [AddCommMonoid α] (a₁ b₁ a₂ b₂ : α) :
    ite P a₁ b₁ + ite P a₂ b₂ = ite P (a₁ + a₂) (b₁ + b₂) := by split_ifs <;> simp

lemma ite_ite_not (P : Prop) [Decidable P] (a b c : α) :
    ite P (ite (¬P) a b) c = ite P b c := by split_ifs <;> rfl

lemma ite_ite_not' (P : Prop) [Decidable P] (a b c : α) :
    ite (¬P) (ite P a b) c = ite (¬P) b c := by split_ifs <;> rfl

variable {p q : Prop}

/-- Real-valued `0-1` indicator testing a proposition. We prefer this over using `Set.indicator`
and we don't call it indicator to avoid overloading the Mathlib definition. -/
noncomputable abbrev oneOn (p : Prop) : ℝ := ite (h := Classical.propDecidable p) p 1 0

lemma oneOn_true (h : p) : oneOn p = 1 := by simpa

lemma oneOn_false (h : ¬p) : oneOn p = 0 := by simpa

lemma oneOn_and : oneOn (p ∧ q) = (oneOn p) * (oneOn q) := by
  unfold oneOn
  split_ifs <;> simp_all

lemma oneOn_not : oneOn (¬p) = 1 - oneOn p := by
  unfold oneOn; split_ifs <;> simp

lemma oneOn_prod {p : ι → Prop} : ∏ i, oneOn (p i) = oneOn (∀ i, p i) := by
  classical
  unfold oneOn
  split_ifs with h
  · simp [h]
  · rw [not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [← Finset.prod_erase_mul (a := i) (s := Finset.univ) (h := Finset.mem_univ i)]
    simp [hi]

/-- Solutions of the equation `ρᵏ = ρ` in real numbers. -/
lemma pow_eq_self_imp {ρ : ℝ} {k : ℕ} :
    ρ ^ k = ρ → (k = 1 ∨ ρ = 0 ∨ ρ = 1 ∨ ρ = -1) := by
  intro h
  cases k with
  | zero => right; right; left; symm; rwa [pow_zero] at h
  | succ k =>
    by_cases hρ : ρ = 0
    · right; left; assumption
    · rw [pow_succ] at h
      nth_rewrite 3 [← one_mul ρ] at h
      have h := mul_right_cancel₀ hρ h
      obtain h'|h'|⟨h', _⟩ := pow_eq_one_iff_cases.mp h
      · left; omega
      · right; right; left; assumption
      · right; right; right; assumption

end LeanPool.LeanBooleanfun.BooleanFun

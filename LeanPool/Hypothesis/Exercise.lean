/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Data.ENNReal.Basic

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!

# Exercises from Grinstead and Snell
-/

namespace Exercise124

/-- "Heads", encoded as `true`. -/
def H := true
/-- "Tails", encoded as `false`. -/
def T := false

lemma part_1 :
    {![H,H,H], ![H,H,T], ![H,T,H], ![H,T,T]} = {x | x 0 = H} := by
    apply subset_antisymm
    · intro v hv
      simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      cases hv with
      | inl h => subst h;simp
      | inr h => cases h with
      | inl h => subst h;simp
      | inr h => cases h with
      | inl h => subst h;simp
      | inr h => subst h;simp
    · intro v hv
      simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hv ⊢
      by_cases H₁ : v 1 = H
      · by_cases H₂ : v 2 = H
        · left;ext i;fin_cases i <;> tauto
        · have H₂ : v 2 = T := eq_false_of_ne_true H₂
          right;left;ext i;fin_cases i <;> tauto
      · have H₁ : v 1 = T := eq_false_of_ne_true H₁
        by_cases H₂ : v 2 = H
        · right;right;left;ext i;fin_cases i <;> tauto
        · have H₂ : v 2 = T := eq_false_of_ne_true H₂
          right;right;right;ext i;fin_cases i <;> tauto

lemma part_2 :
    {![H,H,H], ![T,T,T]} = {x | ∀ i, x i = x 0} := by
    apply subset_antisymm
    · intro v hv
      simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      cases hv with
      | inl h => subst h;intro i;fin_cases i <;> tauto
      | inr h => subst h;intro i;fin_cases i <;> tauto
    · intro v hv
      simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hv ⊢
      by_cases H₁ : v 0 = H
      · left; ext i; fin_cases i <;> simp_all
      · have : v 0 = T := eq_false_of_ne_true H₁
        rw [this] at hv
        right;ext i; fin_cases i <;> (simp; tauto)


lemma part_3 :
    {![H,H,T], ![H,T,H], ![T,H,H]} = {x | ∃! i, x i = T} := by
  apply subset_antisymm
  · intro v hv
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    cases hv with
    | inl h =>
      subst h;simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_setOf_eq]
      use 2
      constructor
      · simp
      · intro i hi
        fin_cases i
        · simp [H,T] at hi
        · simp [H,T] at hi
        · simp
    | inr h => cases h with
    | inl h =>
      subst h
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_setOf_eq]
      use 1
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, true_and]
      intro i hi
      fin_cases i
      · simp [H,T] at hi
      · simp
      · simp [H,T] at hi
    | inr h =>
      subst h
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_setOf_eq]
      use 0
      simp only [Fin.isValue, Matrix.cons_val_zero, true_and]
      intro i hi
      fin_cases i
      · simp
      · simp [H,T] at hi
      · simp [H,T] at hi
  · intro v hv
    obtain ⟨i,hi⟩ := hv
    fin_cases i
    · simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi ⊢
      right;right;ext j
      fin_cases j
      · simp;tauto
      · simp only [
          Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        have := hi.2 1
        simp only [Fin.isValue, one_ne_zero, imp_false] at this
        exact Bool.not_eq_not.mp this
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue,
          Matrix.cons_val]
        have := hi.2 2
        simp only [Fin.isValue, Fin.reduceEq, imp_false] at this
        exact Bool.not_eq_not.mp this
    · simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi ⊢
      right;left;ext j
      fin_cases j
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero]
        have := hi.2 0
        simp only [Fin.isValue, zero_ne_one, imp_false] at this
        exact Bool.not_eq_not.mp this
      · simp;tauto
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue,
          Matrix.cons_val]
        have := hi.2 2
        simp only [Fin.isValue, Fin.reduceEq, imp_false] at this
        exact Bool.not_eq_not.mp this
    · simp only [
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi ⊢
      left;ext j
      fin_cases j
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero]
        have := hi.2 0
        simp only [Fin.isValue, Fin.reduceEq, imp_false] at this
        exact Bool.not_eq_not.mp this
      · simp only [
          Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        have := hi.2 1
        simp only [Fin.isValue, Fin.reduceEq, imp_false] at this
        exact Bool.not_eq_not.mp this
      · simp;tauto



end Exercise124

-- inductive omega
-- | a : omega
-- | b : omega
-- | c : omega

-- def m (s : omega) : ℚ := match s with
-- | omega.a => 1/2
-- | _ => 0


-- example : ({omega.a, omega.c} : Set omega)
--   ∈ (Set.univ : Set omega).powerset := by
--   simp
-- -- #check Set omega

-- def a : Fin 3 := 0
-- def b : Fin 3 := 1
-- def c : Fin 3 := 2
-- def mm (s : Fin 3) : ℚ := match s with
-- | 0 => 1/2
-- | 1 => 1/3
-- | 2 => 1/6

open MeasureTheory ENNReal

lemma arithmetic_for_exercise_1_2_7 :
    (1:ℝ≥0∞) / 2 + 1 = 11 / 12 + 1 / 4 + 1 / 3 := by
  rw [show (11 : ℝ≥0∞) = 4+4 + 3 by norm_num, show (12 : ℝ≥0∞) = 3 * 4 by norm_num]
  repeat rw [ENNReal.add_div]
  have : 4 / (3 * 4) = 1 / (3 : ℝ≥0∞) := by
    nth_rewrite 1 [← one_mul 4]
    apply ENNReal.mul_div_mul_right 1 3 <;> simp
  rw [this]
  have : 3 / (3 * 4) = 1 / (4 : ℝ≥0∞) := by
    nth_rewrite 1 [← mul_one 3]
    apply ENNReal.mul_div_mul_left 1 4 <;> simp
  rw [this]
  simp only [one_div]
  rw [← inv_three_add_inv_three]
  ring_nf
  rw [add_comm]
  congr
  rw [show (4 :ENNReal) = 2 * 2 by norm_num]
  rw [ENNReal.mul_inv, mul_assoc, ENNReal.inv_mul_cancel]
  all_goals simp

/-- Exercise 1.2.7:
  Let A and B be events such that P(A ∩ B) = 1/4, P(Aᶜ) = 1/3, and P(B) =
  1/2. What is P(A ∪ B)? -/
lemma exercise_1_2_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [i : IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A)
    (h₀ : μ (A ∩ B) = 1 / 4) (h₁ : μ Aᶜ = 1 / 3) (h₂ : μ B = 1 / 2) :
    μ (A ∪ B) = 11/12 := by
  apply (add_left_inj (show μ (A ∩ B) ≠ ⊤ by simp)).mp
  rw [measure_union_add_inter' hA, h₂, h₀]
  nth_rewrite 1 [add_comm]
  apply (add_left_inj (show μ Aᶜ ≠ ⊤ by simp)).mp
  nth_rewrite 1 [add_assoc]
  rw [← measure_union' (Set.disjoint_compl_right_iff_subset.mpr (by simp)) hA]
  rw [Set.union_compl_self A, measure_univ, h₁]
  exact arithmetic_for_exercise_1_2_7

lemma exercise_1_2_6 (μ : Measure (Fin 6)) [i : IsProbabilityMeasure μ]
  (h : μ {2} = 2 * μ {1} -- Have to be careful since (6 : Fin 6) = 0.
     ∧ μ {3} = 3 * μ {1}
     ∧ μ {4} = 4 * μ {1}
     ∧ μ {5} = 5 * μ {1}
     ∧ μ {6} = 6 * μ {1}) : μ {2,4,6} = 12 / 21 := by
  have h₀ : μ {2,4,6} = 12 * μ {1} := by
    rw [show {2,4,6} = ({2} ∪ ({4} ∪ {6}) : Set (Fin 6)) by rfl]
    repeat rw [measure_union (by simp) (by simp)]
    rw [h.1, h.2.2.1, h.2.2.2.2]
    ring_nf
  have h₂ : μ Set.univ = 1 := by simp
  have h₃ : (Set.univ : Set (Fin 6)) = {1,2,3,4,5,6} := by
    ext j; fin_cases j <;> tauto
  have h₅ : (1:Real) + 2 + 3 + 4 + 5 + 6 = 21 := by linarith
  have h₆ : (1:ENNReal) + 2 + 3 + 4 + 5 + 6 = 21 :=
      (toReal_eq_toReal_iff' (by simp) (by simp)).mp h₅
  have h₄ : μ {1} + μ {2} + μ {3} + μ {4} + μ {5} + μ {6} = μ {1,2,3,4,5,6} := by
    have h₇ : ({1,2,3,4,5,6} : Set (Fin 6)) = {1} ∪ {2} ∪ {3} ∪ {4} ∪ {5} ∪ {6}:= by
      ext j; fin_cases j <;> simp
    rw [h₇]
    repeat rw [measure_union (by simp) (by simp)]
  have h₂ : μ {1} = 1/21 := by
    rw [ENNReal.eq_div_iff (by simp) (by simp)]
    rw [← h₂, h₃, ← h₄, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    ring_nf
  rw [h₀, h₂, mul_div]
  simp

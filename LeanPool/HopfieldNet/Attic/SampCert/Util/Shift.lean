/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Shift Util

This file contains lemmas about invariance of sums under integer shifts.
-/

open Summable

/--
A series is right-ℕ-shift-invariant provided its shifted positive and negative parts are summable.
-/
theorem tsum_shift₁ (f : ℤ → ℝ) (μ : ℕ)
  (h2 : ∀ μ : ℕ, Summable fun x : ℕ => f (x + μ))
  (h3 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) + μ))
  :
  (∑' x : ℤ, f x) = ∑' x : ℤ, f (x + μ) := by
  have h1 : Summable fun x : ℕ => f x := by
    apply h2 0
  have h4 : Summable fun x : ℕ => f (- (x + 1)) := by
    apply h3 0
  rw [tsum_of_nat_of_neg_add_one h1]
  · rw [← sum_add_tsum_nat_add μ h1]
    rw [add_rotate]
    conv =>
      left
      rw [add_assoc]
      right
      rw [add_comm]
    conv =>
      right
      rw [@tsum_of_nat_of_neg_add_one ℝ _ _ _ _ (fun x : ℤ => f (x + μ)) (h2 μ) (h3 μ)]
    congr 1
    conv =>
      right
      rw [← sum_add_tsum_nat_add μ (h3 μ)]
    conv =>
      right
      right
      right
      intro i
      ring_nf
      simp
      ring_nf
      rw [← neg_add']
      rw [add_comm]
    congr 1
    induction μ
    · simp
    · rename_i n IH
      rw [Finset.sum_range_succ]
      rw [IH]
      clear IH
      rw [Finset.sum_range_succ']
      simp
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ring_nf
  · exact h4


/--
A series is left-ℕ-shift-invariant provided its shifted positive and negative parts are summable.
-/
theorem tsum_shift₂ (f : ℤ → ℝ) (μ : ℕ)
  (h2 : ∀ μ : ℕ, Summable fun x : ℕ => f (x - μ))
  (h3 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) - μ)) :
  ∑' x : ℤ, f (x - μ) = (∑' x : ℤ, f x) := by
  have h1 : Summable fun x : ℕ => f x := by
    apply h2 0
  have h4 : Summable fun x : ℕ => f (- (x + 1)) := by
    apply h3 0
  rw [tsum_of_nat_of_neg_add_one]
  · rw [← sum_add_tsum_nat_add μ (h2 μ)]
    rw [add_rotate]
    conv =>
      left
      rw [add_assoc]
      right
      rw [add_comm]
    conv =>
      right
      rw [tsum_of_nat_of_neg_add_one h1 h4]
    congr 1
    · apply tsum_congr
      intro b
      congr 1
      simp
    · conv =>
        right
        rw [← sum_add_tsum_nat_add μ h4]
      congr 1
      · induction μ
        · simp
        · rename_i μ IH
          rw [Finset.sum_range_succ']
          rw [Finset.sum_range_succ]
          rw [← IH]
          simp
      · apply tsum_congr
        intro b
        congr 1
        simp
        ring_nf
  · exact (h2 μ)
  · exact (h3 μ)

/--
A series is invariant under integer shifts provided its shifted positive and negative parts are summable.
-/
theorem tsum_shift (f : ℤ → ℝ) (μ : ℤ)
  (h₀ : ∀ μ : ℤ, Summable fun x : ℤ => f (x + μ)) :
  ∑' x : ℤ, f (x + μ) = (∑' x : ℤ, f x) := by
  have h : ∀ μ : ℤ, Summable fun x : ℕ => f (x + μ) := by
    intro μ
    have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun x => f (x + μ))
    replace A := A.1 (h₀ μ)
    cases A
    rename_i X Y
    exact X
  have h' : ∀ μ : ℤ, Summable fun x : ℕ => f (-(x + 1) + μ) := by
    intro μ
    have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun x => f (x + μ))
    replace A := A.1 (h₀ μ)
    cases A
    rename_i X Y
    exact Y
  have h1 : ∀ μ : ℕ, Summable fun x : ℕ => f (x + μ) := by
    intro μ
    apply h
  have h2 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) + μ) := by
    intro μ
    apply h'
  have h3 : ∀ μ : ℕ, Summable fun x : ℕ => f (x - μ) := by
    intro μ
    apply h
  have h4 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) - μ) := by
    intro μ
    apply h'
  cases μ
  · rename_i μ
    rw [tsum_shift₁ f μ h1 h2]
    simp
  · rename_i μ
    rw [← tsum_shift₂ f (μ + 1) h3 h4]
    apply tsum_congr
    intro b
    congr

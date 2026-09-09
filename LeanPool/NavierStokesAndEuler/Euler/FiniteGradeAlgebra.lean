/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Exact finite graded identities for the literal packet residual. -/

noncomputable section

namespace EulerFiniteGrades

open Finset

variable {V W Q : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Q] [Module ℝ Q]

def evaluate (M : ℕ) (κ : ℝ) (u : ℕ → V) : V :=
  ∑ n ∈ range (M+1), κ^n • u n

def truncate (M : ℕ) (u : ℕ → V) (n : ℕ) : V := if n ≤ M then u n else 0

def convolution (M : ℕ) (B : V →ₗ[ℝ] W →ₗ[ℝ] Q) (u : ℕ → V) (v : ℕ → W) (n : ℕ) : Q :=
  ∑ i ∈ range (M+1), ∑ j ∈ range (M+1), if i+j=n then B (u i) (v j) else 0

theorem evaluate_add (M : ℕ) (κ : ℝ) (u v : ℕ → V) :
    evaluate M κ (fun n => u n+v n) = evaluate M κ u+evaluate M κ v := by
  simp only [evaluate, smul_add, sum_add_distrib]

theorem map_evaluate (M : ℕ) (κ : ℝ) (L : V →ₗ[ℝ] W) (u : ℕ → V) :
    L (evaluate M κ u) = evaluate M κ (fun n => L (u n)) := by
  simp only [evaluate, map_sum, map_smul]

/-- Bilinearity expands the actual finite evaluated packet into its exact grades. -/
theorem bilinear_evaluate (M : ℕ) (κ : ℝ) (B : V →ₗ[ℝ] W →ₗ[ℝ] Q)
    (u : ℕ → V) (v : ℕ → W) :
    B (evaluate M κ u) (evaluate M κ v) = evaluate (2*M) κ (convolution M B u v) := by
  calc
    _ = ∑ i ∈ range (M+1), ∑ j ∈ range (M+1), κ^(i+j) • B (u i) (v j) := by
      simp only [evaluate, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_sum, smul_smul, pow_add]
      rw [sum_comm]
      simp only [mul_comm]
    _ = ∑ i ∈ range (M+1), ∑ j ∈ range (M+1),
        ∑ n ∈ range (2*M+1), κ^n • (if i+j=n then B (u i) (v j) else 0) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      have hmem : i+j ∈ range (2*M+1) := by
        simp only [mem_range] at hi hj ⊢
        omega
      simp only [smul_ite, smul_zero, sum_ite_eq, hmem, ite_true]
    _ = evaluate (2*M) κ (convolution M B u v) := by
      symm
      unfold evaluate convolution
      simp only [smul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]

theorem convolution_above (M n : ℕ) (hn : 2 * M < n)
    (B : V →ₗ[ℝ] W →ₗ[ℝ] Q) (u : ℕ → V) (v : ℕ → W) :
    convolution M B u v n = 0 := by
  unfold convolution
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  have hne : i+j ≠ n := by
    simp only [mem_range] at hi hj
    omega
  exact ite_eq_right hne

theorem convolution_zero (M : ℕ) (B : V →ₗ[ℝ] W →ₗ[ℝ] Q)
    (u : ℕ → V) (v : ℕ → W) (hu : u 0 = 0) : convolution M B u v 0 = 0 := by
  unfold convolution
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j _
  by_cases h : i+j=0
  · have hi : i=0 := by omega
    rw [ite_eq_left h, hi, hu, map_zero, LinearMap.zero_apply]
  · exact ite_eq_right h

/-- A vanishing constant term justifies the fast derivative's inverse power of κ. -/
theorem inverse_evaluate (M : ℕ) (κ : ℝ) (hκ : κ ≠ 0) (u : ℕ → V) (hu : u 0 = 0) :
    κ⁻¹ • evaluate M κ u = ∑ n ∈ range M, κ^n • u (n+1) := by
  rw [evaluate, sum_range_succ']
  simp only [pow_zero, one_smul, hu, add_zero, smul_sum, smul_smul]
  apply sum_congr rfl
  intro n _
  congr 1
  rw [pow_succ]
  field_simp [hκ]

/-- Exact cancellation of low grades leaves only the literal finite high-grade tail. -/
theorem evaluate_eq_tail (M K : ℕ) (hK : K ≤ M + 1) (κ : ℝ) (u : ℕ → V)
    (hzero : ∀ n < K, u n = 0) :
    evaluate M κ u = ∑ n ∈ Ico K (M+1), κ^n • u n := by
  have hz : ∑ n ∈ range K, κ^n • u n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [hzero n (mem_range.mp hn), smul_zero]
  have h := sum_range_add_sum_Ico (fun n => κ^n • u n) hK
  rw [hz, zero_add] at h
  exact h.symm

end EulerFiniteGrades

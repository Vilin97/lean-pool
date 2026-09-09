/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAlgebra
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

@[expose] public section

/-! The finite residual convolution is exactly the source's sum over i+j=n. -/

noncomputable section

namespace EulerFiniteGrades

open Finset Finset.HasAntidiagonal

variable {V W Q : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Q] [Module ℝ Q]

theorem bounded_pairs_eq_antidiagonal (M n : ℕ) (hn : n ≤ M) :
    ((range (M+1)) ×ˢ (range (M+1))).filter (fun ij => ij.1+ij.2=n) = antidiagonal n := by
  ext ij
  simp only [mem_filter, mem_product, mem_range, mem_antidiagonal]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem convolution_eq_antidiagonal (M n : ℕ) (hn : n ≤ M)
    (B : V →ₗ[ℝ] W →ₗ[ℝ] Q) (u : ℕ → V) (v : ℕ → W) :
    convolution M B u v n = ∑ ij ∈ antidiagonal n, B (u ij.1) (v ij.2) := by
  rw [← bounded_pairs_eq_antidiagonal M n hn]
  simp only [sum_filter, sum_product, convolution]

theorem convolution_eq_range (M n : ℕ) (hn : n ≤ M)
    (B : V →ₗ[ℝ] W →ₗ[ℝ] Q) (u : ℕ → V) (v : ℕ → W) :
    convolution M B u v n = ∑ i ∈ range (n+1), B (u i) (v (n-i)) := by
  rw [convolution_eq_antidiagonal M n hn]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => B (u i) (v j)) n

/-- No coefficient above the target grade enters its slow convolution. -/
theorem convolution_congr_below (M n : ℕ) (hn : n ≤ M)
    (B : V →ₗ[ℝ] W →ₗ[ℝ] Q) (u u' : ℕ → V) (v v' : ℕ → W)
    (hu : ∀ i ≤ n, u i = u' i) (hv : ∀ i ≤ n, v i = v' i) :
    convolution M B u v n = convolution M B u' v' n := by
  rw [convolution_eq_range M n hn, convolution_eq_range M n hn]
  apply sum_congr rfl
  intro i hi
  rw [hu i (by have h := mem_range.mp hi; omega), hv (n-i) (Nat.sub_le n i)]

end EulerFiniteGrades

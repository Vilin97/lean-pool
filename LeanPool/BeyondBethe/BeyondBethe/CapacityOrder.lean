/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Stable
import Mathlib.Tactic

/-! # Capacity Order -/

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

theorem realMonomial_pos
    {σ : Type*} [Fintype σ] {z : σ → ℝ}
    (hz : ∀ i, 0 < z i) (α : σ → ℝ) :
    0 < realMonomial z α := by
  rw [realMonomial]
  exact Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hz i) _

theorem eval_nonneg_of_nonnegativeCoefficients
    {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} (hp : HasNonnegativeCoefficients p)
    {z : σ → ℝ} (hz : ∀ i, 0 ≤ z i) :
    0 ≤ p.eval z := by
  rw [eval_eq]
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg (hp d) (Finset.prod_nonneg fun i _ ↦
    pow_nonneg (hz i) _)

theorem polynomialCapacity_nonneg
    {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} (hp : HasNonnegativeCoefficients p)
    (α : σ → ℝ) :
    0 ≤ polynomialCapacity α p := by
  apply le_csInf
  · let one : σ → ℝ := fun _ ↦ 1
    exact ⟨p.eval one / realMonomial one α,
      ⟨one, fun _ ↦ by norm_num, rfl⟩⟩
  · intro b hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact div_nonneg
      (eval_nonneg_of_nonnegativeCoefficients hp (fun i ↦ le_of_lt (hz i)))
      (le_of_lt (realMonomial_pos hz α))

theorem polynomialCapacity_le_ratio
    {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} (hp : HasNonnegativeCoefficients p)
    (α z : σ → ℝ) (hz : ∀ i, 0 < z i) :
    polynomialCapacity α p ≤ p.eval z / realMonomial z α := by
  apply csInf_le
  · exact ⟨0, fun b hb ↦ by
      obtain ⟨w, hw, rfl⟩ := hb
      exact div_nonneg
        (eval_nonneg_of_nonnegativeCoefficients hp
          (fun i ↦ le_of_lt (hw i)))
        (le_of_lt (realMonomial_pos hw α))⟩
  · exact ⟨z, hz, rfl⟩

theorem le_polynomialCapacity_of_le_ratio
    {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} {α : σ → ℝ} {L : ℝ}
    (hL : ∀ z : σ → ℝ, (∀ i, 0 < z i) →
      L ≤ p.eval z / realMonomial z α) :
    L ≤ polynomialCapacity α p := by
  apply le_csInf
  · let one : σ → ℝ := fun _ ↦ 1
    exact ⟨p.eval one / realMonomial one α,
      ⟨one, fun _ ↦ by norm_num, rfl⟩⟩
  · intro b hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact hL z hz

end BeyondBethe

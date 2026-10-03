/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

/-!
# Growth of finite weighted power sums

This file formalizes the elementary power-sum lemma used in the
Corvaja--Zannier passage from even-extension point-count estimates to bounds
on Frobenius parameters.

For a finite set `s` of distinct complex numbers and nonzero weights, an
`O(ρ ^ n)` bound on the weighted power sum forces every member of `s` to
have norm at most `ρ`.  The proof uses an isolation polynomial: applying a
polynomial that vanishes at all the other members of `s` expresses the chosen
geometric progression as a fixed linear combination of shifted power sums.
-/

@[expose] public section

namespace BGS.HasseWeil

open Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- The finite power sum with base set `s` and coefficient function `weight`. -/
def weightedPowerSum (s : Finset ℂ) (weight : ℂ → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ s, weight z * z ^ n

/-- The polynomial that vanishes at every member of `s` other than `z`. -/
private def isolatePolynomial (s : Finset ℂ) (z : ℂ) : Polynomial ℂ :=
  ∏ w ∈ s.erase z, (Polynomial.X - Polynomial.C w)

private lemma isolatePolynomial_eval_self_ne_zero {s : Finset ℂ} {z : ℂ} :
    (isolatePolynomial s z).eval z ≠ 0 := by
  classical
  rw [isolatePolynomial, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_ne_zero_iff.mpr fun w hw ↦
    sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hw))

private lemma isolatePolynomial_eval_eq_zero_of_mem_of_ne
    {s : Finset ℂ} {z w : ℂ} (hw : w ∈ s) (hwz : w ≠ z) :
    (isolatePolynomial s z).eval w = 0 := by
  classical
  rw [isolatePolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hwz, hw⟩) (by simp)

private lemma isolatePolynomial_sum_weightedPowerSum
    {s : Finset ℂ} {weight : ℂ → ℂ} {z : ℂ} (hz : z ∈ s) (n : ℕ) :
    (isolatePolynomial s z).sum
        (fun k a ↦ a * weightedPowerSum s weight (n + k)) =
      weight z * z ^ n * (isolatePolynomial s z).eval z := by
  classical
  rw [Polynomial.sum_def]
  simp_rw [weightedPowerSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x ∈ s, weight x * x ^ n *
        ∑ k ∈ (isolatePolynomial s z).support,
          (isolatePolynomial s z).coeff k * x ^ k := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add]
      ring
    _ = ∑ x ∈ s, weight x * x ^ n * (isolatePolynomial s z).eval x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ = weight z * z ^ n * (isolatePolynomial s z).eval z := by
      rw [Finset.sum_eq_single z]
      · intro x hx hne
        rw [isolatePolynomial_eval_eq_zero_of_mem_of_ne hx hne, mul_zero]
      · exact fun hnot ↦ (hnot hz).elim

/-- A single complex geometric progression can be `O(ρ ^ n)` only when its
base has norm at most the nonnegative real number `ρ`. -/
theorem norm_le_of_pow_isBigO {z : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : (fun n : ℕ ↦ z ^ n) =O[atTop] fun n : ℕ ↦ ρ ^ n) :
    ‖z‖ ≤ ρ := by
  by_contra hz
  have hlt : ρ < ‖z‖ := lt_of_not_ge hz
  have hsmall : (fun n : ℕ ↦ ρ ^ n) =o[atTop] fun n : ℕ ↦ ‖z‖ ^ n :=
    isLittleO_pow_pow_of_lt_left hρ hlt
  have hself : (fun n : ℕ ↦ z ^ n) =o[atTop] fun n : ℕ ↦ ‖z‖ ^ n :=
    h.trans_isLittleO hsmall
  have hhalf := hself.def' (by norm_num : (0 : ℝ) < 1 / 2)
  rcases hhalf.bound.exists with ⟨n, hn⟩
  have hzpos : 0 < ‖z‖ := by linarith
  have hpos : 0 < ‖z‖ ^ n := pow_pos hzpos n
  have hle : ‖z‖ ^ n ≤ (1 / 2 : ℝ) * ‖z‖ ^ n := by
    simpa [norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg z) n)] using hn
  nlinarith

/-- If a finite weighted power sum is `O(ρ ^ n)` and every coefficient is
nonzero, then each base occurring in the sum has norm at most `ρ`.

Distinctness is encoded by `s` being a `Finset`.  No nonzero assumption on the
bases is needed: zero bases satisfy the conclusion automatically. -/
theorem norm_le_of_mem_of_weightedPowerSum_isBigO
    {s : Finset ℂ} {weight : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hweight : ∀ z ∈ s, weight z ≠ 0)
    (hO : weightedPowerSum s weight =O[atTop] fun n : ℕ ↦ ρ ^ n)
    {z : ℂ} (hz : z ∈ s) :
    ‖z‖ ≤ ρ := by
  classical
  have hshift (k : ℕ) :
      (fun n : ℕ ↦ weightedPowerSum s weight (n + k)) =O[atTop]
        fun n : ℕ ↦ ρ ^ n := by
    have hcomp := hO.comp_tendsto (tendsto_add_atTop_nat k)
    change (fun n : ℕ ↦ weightedPowerSum s weight (n + k)) =O[atTop]
      (fun n : ℕ ↦ ρ ^ (n + k)) at hcomp
    refine hcomp.trans ?_
    simpa only [pow_add, mul_comm] using
      (isBigO_refl (fun n : ℕ ↦ ρ ^ n) atTop).const_mul_left (ρ ^ k)
  have hfiltered :
      (fun n : ℕ ↦ (isolatePolynomial s z).sum
        (fun k a ↦ a * weightedPowerSum s weight (n + k))) =O[atTop]
          fun n : ℕ ↦ ρ ^ n := by
    convert! (IsBigO.sum (s := (isolatePolynomial s z).support) fun k hk ↦
      (hshift k).const_mul_left ((isolatePolynomial s z).coeff k)) using 1
    funext n
    simp only [Polynomial.sum_def, Finset.sum_apply]
  have hisolated :
      (fun n : ℕ ↦ weight z * z ^ n * (isolatePolynomial s z).eval z) =O[atTop]
        fun n : ℕ ↦ ρ ^ n := by
    simpa only [isolatePolynomial_sum_weightedPowerSum hz] using hfiltered
  have hcoefficient : weight z * (isolatePolynomial s z).eval z ≠ 0 :=
    mul_ne_zero (hweight z hz) isolatePolynomial_eval_self_ne_zero
  have hpower : (fun n : ℕ ↦ z ^ n) =O[atTop] fun n : ℕ ↦ ρ ^ n := by
    apply (isBigO_const_mul_left_iff hcoefficient).mp
    exact hisolated.congr_left fun n ↦ by ring
  exact norm_le_of_pow_isBigO hρ hpower

/-- Simultaneous form of `norm_le_of_mem_of_weightedPowerSum_isBigO`. -/
theorem weightedPowerSum_base_norm_le
    {s : Finset ℂ} {weight : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hweight : ∀ z ∈ s, weight z ≠ 0)
    (hO : weightedPowerSum s weight =O[atTop] fun n : ℕ ↦ ρ ^ n) :
    ∀ z ∈ s, ‖z‖ ≤ ρ :=
  fun _z hz ↦ norm_le_of_mem_of_weightedPowerSum_isBigO hρ hweight hO hz

end

end BGS.HasseWeil

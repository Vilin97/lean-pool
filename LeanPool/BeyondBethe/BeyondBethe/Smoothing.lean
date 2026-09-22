/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Permanent
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-! # Smoothing -/

open scoped BigOperators

namespace BeyondBethe

/-- The smoothing level from paper (48), written for an abstract matrix order
`n`. -/
noncomputable def smoothingDelta (n : ℕ) (m χ : ℝ) : ℝ :=
  min (1 / (2 * n)) (χ * m ^ n / (4 * Nat.factorial n))

theorem smoothingDelta_pos {n : ℕ} {m χ : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hχ : 0 < χ) :
    0 < smoothingDelta n m χ := by
  rw [smoothingDelta, lt_min_iff]
  constructor <;> positivity

theorem smoothingDelta_scale {n : ℕ} {m χ : ℝ} :
    smoothingDelta n m χ ≤ χ * m ^ n / (4 * Nat.factorial n) := by
  exact min_le_right _ _

theorem smoothingDelta_half {n : ℕ} {m χ : ℝ}
    (hn : 0 < n) :
    (n : ℝ) * smoothingDelta n m χ ≤ 1 / 2 := by
  have hle : smoothingDelta n m χ ≤ 1 / (2 * (n : ℝ)) := by
    rw [smoothingDelta]
    exact min_le_left _ _
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    (n : ℝ) * smoothingDelta n m χ
        ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / 2 := by field_simp

/-- The elementary geometric-series estimate used after choosing
`n * δ ≤ 1/2` in the smoothing argument. -/
theorem one_add_pow_sub_one_le_two_mul
    {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hhalf : (n : ℝ) * δ ≤ 1 / 2) :
    (1 + δ) ^ n - 1 ≤ 2 * n * δ := by
  let x : ℝ := n * δ
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by simpa [x] using hhalf
  have hxlt : x < 1 := hxhalf.trans_lt (by norm_num)
  have hpowexp : (1 + δ) ^ n ≤ Real.exp x := by
    have h := Real.prod_one_add_le_exp_sum
      (Finset.univ : Finset (Fin n)) (f := fun _ ↦ δ) (fun _ ↦ hδ)
    simpa [Finset.prod_const, Finset.sum_const, nsmul_eq_mul, x,
      mul_comm] using h
  have hexp : Real.exp x ≤ 1 / (1 - x) :=
    Real.exp_bound_div_one_sub_of_interval hx0 hxlt
  have hden : 0 < 1 - x := by linarith
  have hfrac : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    (1 + δ) ^ n - 1 ≤ Real.exp x - 1 := sub_le_sub_right hpowexp 1
    _ ≤ 1 / (1 - x) - 1 := sub_le_sub_right hexp 1
    _ ≤ 2 * x := by linarith
    _ = 2 * n * δ := by dsimp [x]; ring

/-- Increasing every factor in a product by `δ` changes the product by at
most the change at the all-ones vector.  This is the termwise estimate used in
the smoothing lemma. -/
theorem prod_add_const_sub_prod_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i)
    (ha1 : ∀ i ∈ s, a i ≤ 1) :
    (∏ i ∈ s, (a i + δ)) - (∏ i ∈ s, a i)
      ≤ (1 + δ) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hx0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self x s)
      have hx1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x s)
      have hs0 : ∀ i ∈ s, 0 ≤ a i := fun i hi ↦ ha0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, a i ≤ 1 := fun i hi ↦ ha1 i (Finset.mem_insert_of_mem hi)
      have hprod : (∏ i ∈ s, (a i + δ)) ≤ (1 + δ) ^ s.card := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod₀
          (fun i hi ↦ add_nonneg (hs0 i hi) hδ)
          (fun i hi ↦ by simpa [add_comm] using add_le_add_right (hs1 i hi) δ)
      have hpow : 0 ≤ (1 + δ) ^ s.card - 1 := by
        apply sub_nonneg.mpr
        exact one_le_pow₀ (by linarith)
      calc
        (∏ i ∈ insert x s, (a i + δ)) - (∏ i ∈ insert x s, a i)
            = δ * (∏ i ∈ s, (a i + δ)) +
                a x * ((∏ i ∈ s, (a i + δ)) - (∏ i ∈ s, a i)) := by
                rw [Finset.prod_insert hx, Finset.prod_insert hx]
                ring
        _ ≤ δ * (1 + δ) ^ s.card +
              a x * ((1 + δ) ^ s.card - 1) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hprod hδ)
                  (mul_le_mul_of_nonneg_left (ih hs0 hs1) hx0)
        _ ≤ δ * (1 + δ) ^ s.card +
              ((1 + δ) ^ s.card - 1) := by
                have hmul := mul_le_mul_of_nonneg_right hx1 hpow
                nlinarith
        _ = (1 + δ) ^ (insert x s).card - 1 := by
              rw [Finset.card_insert_of_notMem hx, pow_succ]
              ring

/-- Matrix-level smoothing bound before choosing the smoothing scale. -/
theorem permanent_add_uniform_sub_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hA0 : Matrix.Nonnegative A)
    (hA1 : ∀ i j, A i j ≤ 1) :
    Matrix.permanent (fun i j ↦ A i j + δ) - Matrix.permanent A
      ≤ Nat.factorial (Fintype.card n) * ((1 + δ) ^ Fintype.card n - 1) := by
  classical
  unfold Matrix.permanent
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ σ : Equiv.Perm n,
        ((∏ i, (A (σ i) i + δ)) - ∏ i, A (σ i) i)
        ≤ ∑ _σ : Equiv.Perm n, ((1 + δ) ^ Fintype.card n - 1) := by
          apply Finset.sum_le_sum
          intro σ _
          simpa using prod_add_const_sub_prod_le Finset.univ
            (fun i ↦ A (σ i) i) hδ
            (fun i _ ↦ hA0 (σ i) i)
            (fun i _ ↦ hA1 (σ i) i)
    _ = Nat.factorial (Fintype.card n) * ((1 + δ) ^ Fintype.card n - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- The quantitative form used in paper Lemma 21 once `δ ≤ 1/(2n)` has
been imposed. -/
theorem permanent_add_uniform_sub_le_two_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hhalf : (Fintype.card n : ℝ) * δ ≤ 1 / 2)
    (hA0 : Matrix.Nonnegative A) (hA1 : ∀ i j, A i j ≤ 1) :
    Matrix.permanent (fun i j ↦ A i j + δ) - Matrix.permanent A
      ≤ Nat.factorial (Fintype.card n) *
        (2 * Fintype.card n * δ) := by
  refine (permanent_add_uniform_sub_le A hδ hA0 hA1).trans ?_
  exact mul_le_mul_of_nonneg_left
    (one_add_pow_sub_one_le_two_mul hδ hhalf)
    (Nat.cast_nonneg _)

/-- The mathematical comparison in paper Lemma 21.  The statement isolates
the two inequalities imposed on the chosen smoothing scale `δ`; the paper's
explicit minimum satisfies both. -/
theorem smoothing_comparison
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {m χ δ : ℝ}
    (hn : 0 < Fintype.card n) (hm : 0 < m) (hχ : 0 ≤ χ)
    (hδ : 0 ≤ δ)
    (hhalf : (Fintype.card n : ℝ) * δ ≤ 1 / 2)
    (hscale : δ ≤
      χ * m ^ Fintype.card n /
        (4 * Nat.factorial (Fintype.card n)))
    (hA0 : Matrix.Nonnegative A) (hA1 : ∀ i j, A i j ≤ 1)
    (hmin : ∀ i j, A i j ≠ 0 → m ≤ A i j)
    (hmatch : Matrix.HasPerfectMatching A) :
    Matrix.permanent A ≤ Matrix.permanent (fun i j ↦ A i j + δ) ∧
      Matrix.permanent (fun i j ↦ A i j + δ) ≤
        (1 + χ * Fintype.card n / 2) * Matrix.permanent A := by
  let N : ℝ := Fintype.card n
  let F : ℝ := Nat.factorial (Fintype.card n)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hper0 : 0 ≤ Matrix.permanent A := Matrix.permanent_nonneg_real A hA0
  have hmatched : m ^ Fintype.card n ≤ Matrix.permanent A :=
    Matrix.pow_card_le_permanent_of_hasPerfectMatching A hm.le hA0 hmin hmatch
  have hlower : Matrix.permanent A ≤ Matrix.permanent (fun i j ↦ A i j + δ) := by
    exact Matrix.permanent_mono_real hA0 fun i j ↦ by linarith
  have hdiff := permanent_add_uniform_sub_le_two_mul A hδ hhalf hA0 hA1
  have hscale' :
      F * (2 * N * δ) ≤ χ * N / 2 * m ^ Fintype.card n := by
    have hmultiplier : 0 ≤ F * (2 * N) :=
      mul_nonneg hF.le (mul_nonneg (by norm_num) hN)
    have hmul : (F * (2 * N)) * δ ≤
        (F * (2 * N)) *
          (χ * m ^ Fintype.card n /
            (4 * Nat.factorial (Fintype.card n))) :=
      mul_le_mul_of_nonneg_left hscale hmultiplier
    dsimp [F, N] at hmul ⊢
    calc
      (Nat.factorial (Fintype.card n) : ℝ) *
          (2 * (Fintype.card n : ℝ) * δ)
          = ((Nat.factorial (Fintype.card n) : ℝ) *
              (2 * (Fintype.card n : ℝ))) * δ := by ring
      _ ≤ ((Nat.factorial (Fintype.card n) : ℝ) *
              (2 * (Fintype.card n : ℝ))) *
            (χ * m ^ Fintype.card n /
              (4 * Nat.factorial (Fintype.card n))) := hmul
      _ = χ * (Fintype.card n : ℝ) / 2 *
            m ^ Fintype.card n := by
          field_simp
          ring
  refine ⟨hlower, ?_⟩
  have hdiff' :
      Matrix.permanent (fun i j ↦ A i j + δ) - Matrix.permanent A
        ≤ χ * N / 2 * m ^ Fintype.card n := by
    exact hdiff.trans (by simpa [F, N] using hscale')
  have hcoef : 0 ≤ χ * N / 2 := by positivity
  have hmatched' := mul_le_mul_of_nonneg_left hmatched hcoef
  dsimp [N] at hdiff' hmatched' ⊢
  linarith

/-- Paper Lemma 21 with its explicit smoothing level.  This is the exact
real-inequality content; rational bit length and construction time belong to
the algorithmic layer. -/
theorem smoothing_comparison_explicit
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {m χ : ℝ}
    (hn : 0 < Fintype.card n) (hm : 0 < m) (hχ : 0 < χ)
    (hA0 : Matrix.Nonnegative A) (hA1 : ∀ i j, A i j ≤ 1)
    (hmin : ∀ i j, A i j ≠ 0 → m ≤ A i j)
    (hmatch : Matrix.HasPerfectMatching A) :
    let δ := smoothingDelta (Fintype.card n) m χ
    Matrix.permanent A ≤ Matrix.permanent (fun i j ↦ A i j + δ) ∧
      Matrix.permanent (fun i j ↦ A i j + δ) ≤
        (1 + χ * Fintype.card n / 2) * Matrix.permanent A := by
  dsimp only
  exact smoothing_comparison A hn hm hχ.le
    (smoothingDelta_pos hn hm hχ).le
    (smoothingDelta_half hn)
    smoothingDelta_scale hA0 hA1 hmin hmatch

end BeyondBethe

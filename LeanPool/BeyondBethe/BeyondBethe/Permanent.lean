/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators

/-! # Permanent -/

namespace Matrix

/-- Entrywise nonnegativity. -/
def Nonnegative {m n : Type*} {R : Type*} [Zero R] [LE R]
    (A : Matrix m n R) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- The positive support of `A` has a perfect matching, in the orientation
used by Mathlib's definition of the permanent. -/
def HasPerfectMatching {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Zero R] (A : Matrix n n R) : Prop :=
  ∃ σ : Equiv.Perm n, ∀ i, A (σ i) i ≠ 0

theorem permanent_fin_one {R : Type*} [CommSemiring R]
    (A : Matrix (Fin 1) (Fin 1) R) :
    permanent A = A 0 0 := by
  simp

theorem permanent_nonneg_real {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Nonnegative A) :
    0 ≤ permanent A := by
  classical
  rw [permanent]
  exact Finset.sum_nonneg fun σ _ ↦
    Finset.prod_nonneg fun i _ ↦ hA (σ i) i

theorem permanent_mono_real {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : Nonnegative A)
    (hAB : ∀ i j, A i j ≤ B i j) :
    permanent A ≤ permanent B := by
  classical
  rw [permanent, permanent]
  apply Finset.sum_le_sum
  intro σ _
  exact Finset.prod_le_prod₀ (fun i _ ↦ hA (σ i) i) fun i _ ↦ hAB (σ i) i

/-- Degree-`n` homogeneity under global scaling, as used when the algorithm
normalizes the largest matrix entry. -/
theorem permanent_scale_real {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (c : ℝ) :
    permanent (c • A) = c ^ Fintype.card n * permanent A :=
  permanent_smul A c

/-- Casting a rational permanent to the reals is the same as first casting
the entries and then taking the real permanent. -/
theorem cast_permanent_rat {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) :
    ((permanent A : ℚ) : ℝ) = permanent (fun i j ↦ (A i j : ℝ)) := by
  classical
  simp [permanent]

theorem permanent_eq_zero_of_noPerfectMatching
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommSemiring R] (A : Matrix n n R)
    (hA : ¬HasPerfectMatching A) :
    permanent A = 0 := by
  classical
  rw [permanent]
  apply Finset.sum_eq_zero
  intro σ _
  have hzero : ∃ i, A (σ i) i = 0 := by
    by_contra hnone
    apply hA
    refine ⟨σ, ?_⟩
    intro i hi
    exact hnone ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hzero
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem permanent_pos_of_hasPerfectMatching
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Nonnegative A)
    (hmatch : HasPerfectMatching A) :
    0 < permanent A := by
  classical
  obtain ⟨σ, hσ⟩ := hmatch
  rw [permanent]
  apply Finset.sum_pos'
  · exact fun τ _ ↦ Finset.prod_nonneg fun i _ ↦ hA (τ i) i
  · refine ⟨σ, Finset.mem_univ σ, ?_⟩
    exact Finset.prod_pos fun i _ ↦ lt_of_le_of_ne (hA (σ i) i) (Ne.symm (hσ i))

/-- A perfect matching whose nonzero entries are at least `m` contributes at
least `m ^ |n|` to the permanent. -/
theorem pow_card_le_permanent_of_hasPerfectMatching
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hA : Nonnegative A)
    (hmin : ∀ i j, A i j ≠ 0 → m ≤ A i j)
    (hmatch : HasPerfectMatching A) :
    m ^ Fintype.card n ≤ permanent A := by
  classical
  obtain ⟨σ, hσ⟩ := hmatch
  rw [permanent]
  calc
    m ^ Fintype.card n = ∏ _i : n, m := by simp
    _ ≤ ∏ i : n, A (σ i) i := by
      exact Finset.prod_le_prod₀ (fun _ _ ↦ hm) fun i _ ↦ hmin (σ i) i (hσ i)
    _ ≤ ∑ τ : Equiv.Perm n, ∏ i : n, A (τ i) i := by
      exact Finset.single_le_sum
        (fun τ _ ↦ Finset.prod_nonneg fun i _ ↦ hA (τ i) i)
        (Finset.mem_univ σ)

end Matrix

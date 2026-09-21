/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Birkhoff
import LeanPool.BeyondBethe.BeyondBethe.Entropy
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-! # Bethe -/

open scoped BigOperators

namespace BeyondBethe

def Matrix.Positive
    {m n : Type*} (A : Matrix m n ℝ) : Prop :=
  ∀ i j, 0 < A i j

/-- Feasibility for the Bethe program on a matrix with possible zero entries.
The support condition realizes the paper's `-∞` convention without using
extended reals in the objective. -/
def BetheAdmissible
    {n : Type*} [Fintype n] (A X : Matrix n n ℝ) : Prop :=
  IsDoublyStochastic X ∧ ∀ i j, A i j = 0 → X i j = 0

/-- Bethe objective (paper (2)), using `negMulLog` for the continuous
`-x log x` term. -/
noncomputable def betheRowObjective
    {n : Type*} [Fintype n] (A X : Matrix n n ℝ) (i : n) : ℝ := by
  classical
  exact ∑ j : n,
    (X i j * Real.log (A i j) + Real.negMulLog (X i j) +
      (1 - X i j) * Real.log (1 - X i j))

noncomputable def betheObjective
    {n : Type*} [Fintype n] (A X : Matrix n n ℝ) : ℝ := by
  classical
  exact ∑ i : n, betheRowObjective A X i

/-- Singleton factor in logarithmic coordinates. -/
noncomputable def singletonFactor
    {n : Type*} [Fintype n] (A X : Matrix n n ℝ) (i : n) : ℝ :=
  Real.exp (betheRowObjective A X i)

theorem prod_singletonFactor_eq_exp_betheObjective
    {n : Type*} [Fintype n]
    (A X : Matrix n n ℝ) :
    ∏ i, singletonFactor A X i = Real.exp (betheObjective A X) := by
  classical
  simp only [singletonFactor, betheObjective]
  exact (Real.exp_sum Finset.univ (betheRowObjective A X)).symm

/-- Variational logarithm of the Bethe permanent. -/
noncomputable def betheLogValue
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) : ℝ :=
  sSup {v : ℝ | ∃ X, BetheAdmissible A X ∧ betheObjective A X = v}

/-- Bethe permanent.  If the positive support has no perfect matching, both
the permanent and the variational lower bound are zero. -/
noncomputable def bethePermanent
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ℝ := by
  classical
  exact if Matrix.HasPerfectMatching A then Real.exp (betheLogValue A) else 0

theorem bethePermanent_eq_zero_of_noPerfectMatching
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ¬Matrix.HasPerfectMatching A) :
    bethePermanent A = 0 := by
  simp [bethePermanent, hA]

theorem bethePermanent_pos_of_hasPerfectMatching
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Matrix.HasPerfectMatching A) :
    0 < bethePermanent A := by
  simp [bethePermanent, hA, Real.exp_pos]

/-- Exact interface for the Gurvits and Anari--Rezaei Bethe sandwich. -/
def BetheSandwich : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ), Matrix.Nonnegative A →
      bethePermanent A ≤ Matrix.permanent A ∧
      Matrix.permanent A ≤
        (Real.sqrt 2) ^ Fintype.card n * bethePermanent A

/-- Exact interface for Vontobel's concavity theorem, restricted to positive
matrices as used in the structural proof. -/
def VontobelBetheConcavity : Prop :=
  ∀ {n : Type*} [Fintype n]
    (A : Matrix n n ℝ), Matrix.Positive A →
      ConcaveOn ℝ {X : Matrix n n ℝ | IsDoublyStochastic X}
        (betheObjective A)

/-- Row-entropy regularization from paper (34). -/
noncomputable def regularizedBetheObjective
    {n : Type*} [Fintype n]
    (τ : ℝ) (A X : Matrix n n ℝ) : ℝ :=
  betheObjective A X + τ * totalRowEntropy X

/-- Comparing a regularized maximizer with any unregularized competitor loses
at most `τ n log n` in the Bethe objective.  This is the quantitative part of
paper Lemma 14 that does not use KKT or boundary analysis. -/
theorem regularized_near_bethe
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {τ : ℝ} (hτ : 0 ≤ τ) (A X Y : Matrix n n ℝ)
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    (hmax : regularizedBetheObjective τ A Y ≤
      regularizedBetheObjective τ A X) :
    betheObjective A Y -
        τ * (Fintype.card n * Real.log (Fintype.card n))
      ≤ betheObjective A X := by
  have hEY0 := totalRowEntropy_nonneg hY
  have hEX := totalRowEntropy_le hX
  rw [regularizedBetheObjective, regularizedBetheObjective] at hmax
  have hτEX := mul_le_mul_of_nonneg_left hEX hτ
  nlinarith

end BeyondBethe

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.ErdosMoser.DiscreteVariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Variance of distinct subset sums

This file proves the first and second moment identities for subset sums and
combines them with the discrete variance bound to obtain Leo Moser's exact
finite sum-of-squares inequality.
-/

namespace LeanPool.ErdosMoser

open Finset

/-- Twice the sum of all subset sums is `2 ^ |B|` times the sum of the
elements of `B`. -/
theorem sumSubsetSums (B : Finset ℕ) (f : ℕ → ℝ) :
    2 * ∑ T ∈ B.powerset, (∑ i ∈ T, f i) =
      (2 : ℝ) ^ B.card * ∑ i ∈ B, f i := by
  refine Finset.induction_on B ?_ ?_
  · simp
  · intro x B hx ih
    rw [Finset.sum_powerset_insert hx, Finset.sum_insert hx]
    have hInsert : ∀ T ∈ B.powerset,
        (∑ i ∈ insert x T, f i) = f x + ∑ i ∈ T, f i := by
      intro T hT
      have hxT : x ∉ T := fun hxT ↦ hx (Finset.mem_powerset.mp hT hxT)
      exact Finset.sum_insert hxT
    rw [Finset.sum_congr rfl hInsert]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powerset,
      nsmul_eq_mul]
    have hCard :
        (2 : ℝ) ^ (insert x B).card = 2 * (2 : ℝ) ^ B.card := by
      rw [Finset.card_insert_of_notMem hx, pow_succ]
      ring
    rw [hCard]
    push_cast
    linarith [ih]

/-- Exact second-moment identity for the subset sums of a finite set. -/
theorem secondMomentSubsetSums (B : Finset ℕ) (f : ℕ → ℝ) :
    4 * ∑ S ∈ B.powerset, (∑ i ∈ S, f i) ^ 2 =
      (2 : ℝ) ^ B.card *
        ((∑ i ∈ B, f i ^ 2) + (∑ i ∈ B, f i) ^ 2) := by
  refine Finset.induction_on B ?_ ?_
  · simp
  · intro x B hx ih
    rw [Finset.sum_powerset_insert hx]
    have hInsertSquare : ∀ T ∈ B.powerset,
        (∑ i ∈ insert x T, f i) ^ 2 =
          f x ^ 2 + 2 * f x * (∑ i ∈ T, f i) +
            (∑ i ∈ T, f i) ^ 2 := by
      intro T hT
      have hxT : x ∉ T := fun hxT ↦ hx (Finset.mem_powerset.mp hT hxT)
      rw [Finset.sum_insert hxT]
      ring
    rw [Finset.sum_congr rfl hInsertSquare]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_powerset, nsmul_eq_mul, ← Finset.mul_sum]
    have hFirstMoment := sumSubsetSums B f
    have hCard :
        (2 : ℝ) ^ (insert x B).card = 2 * (2 : ℝ) ^ B.card := by
      rw [Finset.card_insert_of_notMem hx, pow_succ]
      ring
    have hSumSquares :
        (∑ i ∈ insert x B, f i ^ 2) = f x ^ 2 + ∑ i ∈ B, f i ^ 2 :=
      Finset.sum_insert hx
    have hSum :
        (∑ i ∈ insert x B, f i) = f x + ∑ i ∈ B, f i :=
      Finset.sum_insert hx
    rw [hCard, hSumSquares, hSum]
    push_cast
    have hExpand :
        (f x + ∑ i ∈ B, f i) ^ 2 =
          f x ^ 2 + 2 * f x * (∑ i ∈ B, f i) +
            (∑ i ∈ B, f i) ^ 2 := by
      ring
    rw [hExpand]
    have hFirstMomentMul :
        4 * f x * (2 * ∑ T ∈ B.powerset, ∑ i ∈ T, f i) =
          4 * f x * ((2 : ℝ) ^ B.card * ∑ i ∈ B, f i) := by
      rw [hFirstMoment]
    linarith [ih, hFirstMomentMul]

/-- Algebraic variance identity for subset sums. -/
theorem varianceIdentitySubsetSums (B : Finset ℕ) (f : ℕ → ℝ) :
    4 * (∑ S ∈ B.powerset, (∑ i ∈ S, f i) ^ 2) -
        (2 : ℝ) ^ B.card * (∑ i ∈ B, f i) ^ 2 =
      (2 : ℝ) ^ B.card * ∑ i ∈ B, f i ^ 2 := by
  have h := secondMomentSubsetSums B f
  linarith [h]

/-- The image of the subset-sum map has cardinality `2 ^ A.card` when the
subset sums of `A` are distinct. -/
lemma imageSubsetSumsCard {A : Finset ℕ} (h : HasDistinctSubsetSums A) :
    (A.powerset.image (fun S ↦ S.sum id)).card = 2 ^ A.card := by
  have hInjective :
      Set.InjOn (fun S ↦ S.sum id) (A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT hEqual
    exact h S hS T hT hEqual
  rw [Finset.card_image_of_injOn hInjective]
  exact powersetCardEqTwoPow A

/-- **Leo Moser's finite variance inequality.** If a finite set of natural
numbers has distinct subset sums, then
`4 ^ |A| - 1 ≤ 3 * ∑ a ∈ A, a ^ 2`.

This is Theorem 2 of Richard K. Guy's 1982 account, where it is attributed to
Leo Moser. -/
theorem leoMoserVarianceBound {A : Finset ℕ}
    (h : HasDistinctSubsetSums A) :
    (4 : ℝ) ^ A.card - 1 ≤ 3 * ∑ a ∈ A, (a : ℝ) ^ 2 := by
  set T : Finset ℕ :=
    A.powerset.image (fun S ↦ S.sum (id : ℕ → ℕ)) with hDefinition
  have hCard : T.card = 2 ^ A.card := imageSubsetSumsCard h
  have hInjective :
      Set.InjOn (fun S ↦ S.sum (id : ℕ → ℕ))
        (A.powerset : Set (Finset ℕ)) := by
    intro S hS U hU hEqual
    exact h S hS U hU hEqual
  have hSumT :
      ∑ t ∈ T, (t : ℝ) =
        ∑ S ∈ A.powerset, ((S.sum (id : ℕ → ℕ) : ℕ) : ℝ) := by
    rw [hDefinition, Finset.sum_image (fun S hS U hU ↦ hInjective hS hU)]
  have hSquareSumT :
      ∑ t ∈ T, (t : ℝ) ^ 2 =
        ∑ S ∈ A.powerset, ((S.sum (id : ℕ → ℕ) : ℕ) : ℝ) ^ 2 := by
    rw [hDefinition, Finset.sum_image (fun S hS U hU ↦ hInjective hS hU)]
  have hSubsetSumCast : ∀ S : Finset ℕ,
      ((S.sum (id : ℕ → ℕ) : ℕ) : ℝ) = ∑ i ∈ S, (i : ℝ) := by
    intro S
    change ((∑ i ∈ S, id i : ℕ) : ℝ) = ∑ i ∈ S, (i : ℝ)
    push_cast
    rfl
  have hVarianceLower :
      (T.card : ℝ) ^ 2 * ((T.card : ℝ) ^ 2 - 1) / 12 ≤
        (T.card : ℝ) * (∑ t ∈ T, (t : ℝ) ^ 2) -
          (∑ t ∈ T, (t : ℝ)) ^ 2 :=
    varianceLowerBoundFinsetNat T
  rw [hCard] at hVarianceLower
  have hTwoPowCast :
      (((2 : ℕ) ^ A.card : ℕ) : ℝ) = (2 : ℝ) ^ A.card := by
    push_cast
    rfl
  rw [hTwoPowCast, hSumT, hSquareSumT] at hVarianceLower
  have hSquareSubset :
      ∑ S ∈ A.powerset, ((S.sum (id : ℕ → ℕ) : ℕ) : ℝ) ^ 2 =
        ∑ S ∈ A.powerset, (∑ i ∈ S, (i : ℝ)) ^ 2 := by
    refine Finset.sum_congr rfl (fun S _ ↦ ?_)
    rw [hSubsetSumCast]
  have hSumSubset :
      ∑ S ∈ A.powerset, ((S.sum (id : ℕ → ℕ) : ℕ) : ℝ) =
        ∑ S ∈ A.powerset, (∑ i ∈ S, (i : ℝ)) := by
    refine Finset.sum_congr rfl (fun S _ ↦ ?_)
    rw [hSubsetSumCast]
  rw [hSquareSubset, hSumSubset] at hVarianceLower
  have hVarianceIdentity :=
    varianceIdentitySubsetSums A (fun i : ℕ ↦ (i : ℝ))
  have hFirstMoment := sumSubsetSums A (fun i : ℕ ↦ (i : ℝ))
  have hTwoPowPositive : 0 < (2 : ℝ) ^ A.card := by
    positivity
  have hTwoPowSquarePositive : 0 < ((2 : ℝ) ^ A.card) ^ 2 := by
    positivity
  have hFourPow :
      (4 : ℝ) ^ A.card = ((2 : ℝ) ^ A.card) ^ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
  rw [hFourPow]
  have hScaledIdentity :
      12 * ((2 : ℝ) ^ A.card *
            (∑ U ∈ A.powerset, (∑ i ∈ U, (i : ℝ)) ^ 2) -
            (∑ U ∈ A.powerset, (∑ i ∈ U, (i : ℝ))) ^ 2) =
        3 * ((2 : ℝ) ^ A.card) ^ 2 * ∑ a ∈ A, (a : ℝ) ^ 2 := by
    have hFirstMomentSquare :
        (∑ U ∈ A.powerset, (∑ i ∈ U, (i : ℝ))) ^ 2 * 4 =
          ((2 : ℝ) ^ A.card) ^ 2 * (∑ a ∈ A, (a : ℝ)) ^ 2 := by
      have hSquare :
          (2 * ∑ U ∈ A.powerset, (∑ i ∈ U, (i : ℝ))) ^ 2 =
            ((2 : ℝ) ^ A.card * ∑ a ∈ A, (a : ℝ)) ^ 2 := by
        rw [hFirstMoment]
      nlinarith [hSquare]
    nlinarith [hVarianceIdentity, hFirstMomentSquare]
  have hScaledBound :
      ((2 : ℝ) ^ A.card) ^ 2 * (((2 : ℝ) ^ A.card) ^ 2 - 1) ≤
        3 * ((2 : ℝ) ^ A.card) ^ 2 * ∑ a ∈ A, (a : ℝ) ^ 2 := by
    have hIntermediate :
        ((2 : ℝ) ^ A.card) ^ 2 * (((2 : ℝ) ^ A.card) ^ 2 - 1) ≤
          12 * ((2 : ℝ) ^ A.card *
            (∑ U ∈ A.powerset, (∑ i ∈ U, (i : ℝ)) ^ 2) -
            (∑ U ∈ A.powerset, (∑ i ∈ U, (i : ℝ))) ^ 2) := by
      linarith [hVarianceLower]
    linarith [hIntermediate, hScaledIdentity]
  nlinarith [hScaledBound, hTwoPowSquarePositive, hTwoPowPositive]

end LeanPool.ErdosMoser

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Distinct subset sums

This file defines finite sets of natural numbers with distinct subset sums and
establishes the elementary upper bound on their sum of squares in terms of
their largest element.
-/

namespace LeanPool.ErdosMoser

open Finset

/-- A finite set has distinct subset sums if the subset-sum map on its powerset
is injective. -/
def HasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T

/-- The powerset of a finite set has cardinality `2 ^ A.card`. -/
theorem powersetCardEqTwoPow (A : Finset ℕ) :
    A.powerset.card = 2 ^ A.card := by
  rw [Finset.card_powerset]

/-- The sum of the squared elements of a nonempty finite set is at most its
cardinality times the square of its largest element. -/
lemma sumSquaresLeCardMulMaxSquare {A : Finset ℕ} (hA : A.Nonempty) :
    ∑ a ∈ A, (a : ℝ) ^ 2 ≤ A.card * ((A.max' hA : ℕ) : ℝ) ^ 2 := by
  have hPointwise : ∀ a ∈ A, (a : ℝ) ^ 2 ≤ ((A.max' hA : ℕ) : ℝ) ^ 2 := by
    intro a ha
    have hLe : a ≤ A.max' hA := A.le_max' a ha
    have hLeReal : (a : ℝ) ≤ ((A.max' hA : ℕ) : ℝ) := by
      exact_mod_cast hLe
    have hNonnegative : (0 : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast Nat.zero_le a
    exact pow_le_pow_left₀ hNonnegative hLeReal 2
  have hSum := Finset.sum_le_card_nsmul A (fun a ↦ (a : ℝ) ^ 2)
    (((A.max' hA : ℕ) : ℝ) ^ 2) hPointwise
  simpa [nsmul_eq_mul, mul_comm] using hSum

end LeanPool.ErdosMoser

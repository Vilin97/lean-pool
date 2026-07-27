/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.ErdosMoser.SubsetSums
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite lower bounds for the largest element

This file derives direct and square-root forms of the largest-element bound
from Leo Moser's exact sum-of-squares inequality.
-/

namespace LeanPool.ErdosMoser

open Finset

/-- If a nonempty finite set of natural numbers has distinct subset sums, then
`4 ^ |A| - 1 ≤ 3 * |A| * max(A) ^ 2`. -/
theorem erdosMoserMaxBound {A : Finset ℕ} (hA : A.Nonempty)
    (h : HasDistinctSubsetSums A) :
    (4 : ℝ) ^ A.card - 1 ≤
      3 * A.card * ((A.max' hA : ℕ) : ℝ) ^ 2 := by
  have hVariance :
      (4 : ℝ) ^ A.card - 1 ≤ 3 * ∑ a ∈ A, (a : ℝ) ^ 2 :=
    leoMoserVarianceBound h
  have hUpper :
      ∑ a ∈ A, (a : ℝ) ^ 2 ≤
        A.card * ((A.max' hA : ℕ) : ℝ) ^ 2 :=
    sumSquaresLeCardMulMaxSquare hA
  have hScaled :
      3 * ∑ a ∈ A, (a : ℝ) ^ 2 ≤
        3 * (A.card * ((A.max' hA : ℕ) : ℝ) ^ 2) := by
    linarith
  linarith

/-- Square-root form of the finite largest-element bound:
`sqrt ((4 ^ |A| - 1) / (3 * |A|)) ≤ max(A)`. -/
theorem erdosMoserMaxSqrt {A : Finset ℕ} (hA : A.Nonempty)
    (h : HasDistinctSubsetSums A) :
    Real.sqrt (((4 : ℝ) ^ A.card - 1) / (3 * A.card)) ≤
      ((A.max' hA : ℕ) : ℝ) := by
  have hCardPositive : (0 : ℝ) < A.card := by
    have : 0 < A.card := Finset.card_pos.mpr hA
    exact_mod_cast this
  have hDenominatorPositive : (0 : ℝ) < 3 * A.card := by
    linarith
  have hMain :
      (4 : ℝ) ^ A.card - 1 ≤
        3 * A.card * ((A.max' hA : ℕ) : ℝ) ^ 2 :=
    erdosMoserMaxBound hA h
  have hMaxNonnegative : (0 : ℝ) ≤ ((A.max' hA : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hSquare :
      ((4 : ℝ) ^ A.card - 1) / (3 * A.card) ≤
        ((A.max' hA : ℕ) : ℝ) ^ 2 := by
    rw [div_le_iff₀ hDenominatorPositive]
    linarith
  exact (Real.sqrt_le_left hMaxNonnegative).mpr hSquare

end LeanPool.ErdosMoser

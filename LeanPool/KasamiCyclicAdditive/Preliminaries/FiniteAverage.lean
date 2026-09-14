/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

/-!
# Finite-average forcing lemmas

Generic consequences of an average identity and pointwise nonnegativity.
-/

@[expose] public section

open Finset

namespace KasamiCyclicAdditive

/-- If `N i = c + Z i / Q` on a nonempty finite index set, the mean of `N` is
`c`, and `Z ≥ 0` pointwise, then `N` is constantly `c` and `Z` vanishes. -/
theorem forcing_of_average_and_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (N Z : ι → ℝ) (c Q : ℝ) (hQ : 0 < Q)
    (hN : ∀ i ∈ s, N i = c + Z i / Q)
    (hAV : (∑ i ∈ s, N i) / (s.card : ℝ) = c)
    (hZ : ∀ i ∈ s, 0 ≤ Z i) :
    ∀ i ∈ s, N i = c ∧ Z i = 0 := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.2 hs
    positivity
  have hsum : ∑ i ∈ s, N i = (s.card : ℝ) * c := by
    field_simp at hAV
    linarith
  have hsum' : ∑ i ∈ s, N i = (s.card : ℝ) * c + (∑ i ∈ s, Z i) / Q := by
    rw [Finset.sum_congr rfl hN]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
  have hZsum : ∑ i ∈ s, Z i = 0 := by
    have h0 : (∑ i ∈ s, Z i) / Q = 0 := by linarith
    rcases div_eq_zero_iff.1 h0 with h | h
    · exact h
    · exact absurd h (ne_of_gt hQ)
  have hZ0 : ∀ i ∈ s, Z i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hZ).1 hZsum
  intro i hi
  exact ⟨by rw [hN i hi, hZ0 i hi, zero_div, add_zero], hZ0 i hi⟩

end KasamiCyclicAdditive

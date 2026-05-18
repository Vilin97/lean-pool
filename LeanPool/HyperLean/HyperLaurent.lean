/-
Copyright (c) 2026 Pannous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pannous
-/

import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring

/-!
# Laurent-Series Hyperreals

This module vendors the constructive Laurent-series core of `pannous/hyper-lean`.
It models a hyperreal-like ordered field as lexicographically ordered Laurent
series over `ℝ`, with `epsilon` at exponent `1` and `omega` at exponent `-1`.
-/

open HahnSeries

namespace LeanPool.HyperLean

/-- Laurent series over `ℝ` with `ℤ`-indexed coefficients. -/
abbrev LaurentHyperrealRing := LaurentSeries ℝ

/-- Hyperreal-like ordered field: Laurent series with lexicographic order. -/
abbrev LaurentHyperreal := Lex LaurentHyperrealRing

noncomputable instance : Field LaurentHyperreal := inferInstance

noncomputable instance instLaurentHyperrealLinearOrder : LinearOrder LaurentHyperreal :=
  inferInstanceAs (LinearOrder (Lex (HahnSeries ℤ ℝ)))

/-- The canonical infinitesimal, with coefficient `1` at exponent `1`. -/
noncomputable def epsilon : LaurentHyperreal :=
  toLex (single (1 : ℤ) (1 : ℝ))

/-- The canonical infinite element, with coefficient `1` at exponent `-1`. -/
noncomputable def omega : LaurentHyperreal :=
  toLex (single (-1 : ℤ) (1 : ℝ))

/-- Embed `ℝ` as Laurent series supported at exponent `0`. -/
noncomputable def embedReal (r : ℝ) : LaurentHyperreal :=
  toLex (single (0 : ℤ) r)

/-- The standard part: the coefficient at exponent `0`. -/
noncomputable def standardPart (x : LaurentHyperreal) : ℝ :=
  (ofLex x : LaurentHyperrealRing).coeff 0

/-- The fundamental gauging relation `omega * epsilon = 1`. -/
theorem omega_mul_epsilon : omega * epsilon = 1 := by
  change toLex (single (-1 : ℤ) (1 : ℝ) * single 1 1) = 1
  rw [single_mul_single, show (-1 : ℤ) + 1 = 0 by norm_num, one_mul, single_zero_one]
  rfl

/-- The commuted fundamental gauging relation `epsilon * omega = 1`. -/
theorem epsilon_mul_omega : epsilon * omega = 1 := by
  rw [mul_comm]
  exact omega_mul_epsilon

/-- The inverse of `1 + epsilon` exists in the Laurent-series field. -/
theorem one_add_epsilon_ne_zero : (1 : LaurentHyperreal) + epsilon ≠ 0 := by
  intro h
  have : (ofLex (1 + epsilon : LaurentHyperreal) : LaurentHyperrealRing).coeff 0 = 0 := by
    simp [h]
  simp [epsilon, coeff_one] at this

/-- `(1 + epsilon)⁻¹` is an exact field inverse in Laurent series. -/
theorem one_add_epsilon_mul_inv : (1 + epsilon) * (1 + epsilon)⁻¹ = (1 : LaurentHyperreal) :=
  mul_inv_cancel₀ one_add_epsilon_ne_zero

/-- Standard part respects the real embedding. -/
theorem standardPart_embedReal (r : ℝ) : standardPart (embedReal r) = r := by
  simp [standardPart, embedReal, coeff_single_same]

/-- The standard part of `epsilon` is zero. -/
@[simp]
theorem standardPart_epsilon : standardPart epsilon = 0 := by
  simp [standardPart, epsilon]

/-- `epsilon` is positive in the lexicographic order. -/
theorem epsilon_pos : (0 : LaurentHyperreal) < epsilon := by
  change (0 : Lex (HahnSeries ℤ ℝ)) < toLex (single (1 : ℤ) (1 : ℝ))
  rw [HahnSeries.lt_iff]
  exact ⟨1,
    fun j hj => by simp [coeff_single_of_ne (ne_of_lt hj)],
    by simp [coeff_single_same]⟩

/-- `epsilon` is smaller than every positive embedded real. -/
theorem epsilon_lt_embedReal (r : ℝ) (hr : 0 < r) : epsilon < embedReal r := by
  change toLex (single (1 : ℤ) (1 : ℝ)) < toLex (single (0 : ℤ) r)
  rw [HahnSeries.lt_iff]
  refine ⟨0, fun j hj => ?_, ?_⟩
  · simp [coeff_single_of_ne (by omega : j ≠ 1), coeff_single_of_ne (by omega : j ≠ 0)]
  · simp only [ofLex_toLex, ne_eq, zero_ne_one, not_false_eq_true, coeff_single_of_ne,
      coeff_single_same]
    exact hr

end LeanPool.HyperLean

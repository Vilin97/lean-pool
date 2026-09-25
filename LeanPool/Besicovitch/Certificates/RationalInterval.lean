/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Exact rational interval arithmetic

The intervals in this file have rational endpoints, while their semantics is over the real
numbers. The operations provide the enclosure primitives used by the radical-expression evaluator,
with soundness checked by the kernel.
-/

@[expose] public section

open Set

namespace LeanPool.Besicovitch

/-- A nonempty closed interval with rational endpoints. -/
structure RationalInterval where
  /-- The lower rational endpoint. -/
  lower : ℚ
  /-- The upper rational endpoint. -/
  upper : ℚ
  lower_le_upper : lower ≤ upper

namespace RationalInterval

/-- A real number belongs to a rational interval. -/
def Contains (I : RationalInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

/-- The degenerate interval containing one rational number. -/
def singleton (q : ℚ) : RationalInterval :=
  ⟨q, q, le_rfl⟩

/-- The interval sum. -/
def add (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper, add_le_add I.lower_le_upper J.lower_le_upper⟩

/-- The additive inverse of an interval. -/
def neg (I : RationalInterval) : RationalInterval :=
  ⟨-I.upper, -I.lower, neg_le_neg I.lower_le_upper⟩

/-- The smallest interval whose endpoints include all four endpoint products. -/
def mul (I J : RationalInterval) : RationalInterval where
  lower := min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  upper := max (max (I.lower * J.lower) (I.lower * J.upper))
    (max (I.upper * J.lower) (I.upper * J.upper))
  lower_le_upper :=
    (min_le_left _ _).trans <| (min_le_left _ _).trans <|
      (le_max_left _ _).trans (le_max_left _ _)

/-- Natural powers of a rational interval. -/
def pow (I : RationalInterval) : ℕ → RationalInterval
  | 0 => singleton 1
  | n + 1 => (pow I n).mul I

/-- An interval which avoids zero has a well-defined reciprocal interval. -/
def inv (I : RationalInterval) (h : 0 < I.lower ∨ I.upper < 0) : RationalInterval where
  lower := 1 / I.upper
  upper := 1 / I.lower
  lower_le_upper := by
    rcases h with h | h
    · exact one_div_le_one_div_of_le h I.lower_le_upper
    · exact one_div_le_one_div_of_neg_of_le h I.lower_le_upper

theorem singleton_contains (q : ℚ) : (singleton q).Contains q := by
  simp [Contains, singleton]

theorem add_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  constructor <;> norm_num [Contains, add] at hx hy ⊢ <;> linarith

theorem neg_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  constructor <;> norm_num [Contains, neg] at hx ⊢ <;> linarith

private theorem mul_mem_Icc {a b c d x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hLac : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * c :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hLad : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * d :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hLbc : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * c :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hLbd : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * d :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hUac : a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hUad : a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hUbc : b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hUbd : b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · by_cases hy0 : 0 ≤ y
    · have haxy : a * y ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      by_cases ha0 : 0 ≤ a
      · exact hLac.trans <| (mul_le_mul_of_nonneg_left hy.1 ha0).trans haxy
      · exact hLad.trans <| (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha0)).trans haxy
    · have hbxy : b * y ≤ x * y := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
      by_cases hb0 : 0 ≤ b
      · exact hLbc.trans <| (mul_le_mul_of_nonneg_left hy.1 hb0).trans hbxy
      · exact hLbd.trans <| (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hb0)).trans hbxy
  · by_cases hy0 : 0 ≤ y
    · have hxyb : x * y ≤ b * y := mul_le_mul_of_nonneg_right hx.2 hy0
      by_cases hb0 : 0 ≤ b
      · exact hxyb.trans <| (mul_le_mul_of_nonneg_left hy.2 hb0).trans hUbd
      · exact hxyb.trans <| (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)).trans hUbc
    · have hxya : x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)
      by_cases ha0 : 0 ≤ a
      · exact hxya.trans <| (mul_le_mul_of_nonneg_left hy.2 ha0).trans hUad
      · exact hxya.trans <| (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)).trans hUac

theorem mul_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x * y) := by
  simpa only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    mul_mem_Icc hx hy

/-- Interval powers contain the corresponding real powers. -/
theorem pow_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    ∀ n, (I.pow n).Contains (x ^ n)
  | 0 => by simpa [pow] using singleton_contains 1
  | n + 1 => by
      simpa [pow, pow_succ] using mul_contains (pow_contains hx n) hx

theorem inv_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x)
    (h : 0 < I.lower ∨ I.upper < 0) : (I.inv h).Contains x⁻¹ := by
  change (↑(1 / I.upper) : ℝ) ≤ x⁻¹ ∧ x⁻¹ ≤ ↑(1 / I.lower)
  norm_num only [Rat.cast_div, Rat.cast_one]
  norm_num [Contains] at hx
  rcases h with h | h
  · have hl : 0 < x := lt_of_lt_of_le (by exact_mod_cast h) hx.1
    constructor
    · simpa [one_div] using one_div_le_one_div_of_le hl hx.2
    · simpa [one_div] using one_div_le_one_div_of_le (by exact_mod_cast h) hx.1
  · have hu : x < 0 := lt_of_le_of_lt hx.2 (by exact_mod_cast h)
    constructor
    · simpa [one_div] using
        one_div_le_one_div_of_neg_of_le (by exact_mod_cast h) hx.2
    · simpa [one_div] using one_div_le_one_div_of_neg_of_le hu hx.1

end RationalInterval

end LeanPool.Besicovitch

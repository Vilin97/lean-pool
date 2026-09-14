/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Exact rational interval arithmetic

The intervals in this file have rational endpoints, while their semantics is over the real
numbers. The expression evaluator therefore produces small, auditable certificates whose
soundness is checked by the kernel.
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

/-- Rational expressions supported by the exact interval evaluator. -/
inductive RationalExpression (n : ℕ) where
  | var : Fin n → RationalExpression n
  | constant : ℚ → RationalExpression n
  | add : RationalExpression n → RationalExpression n → RationalExpression n
  | neg : RationalExpression n → RationalExpression n
  | mul : RationalExpression n → RationalExpression n → RationalExpression n
  | inv : RationalExpression n → RationalExpression n

namespace RationalExpression

/-- Evaluate a rational expression at a real environment. -/
noncomputable def eval {n : ℕ} : RationalExpression n → (Fin n → ℝ) → ℝ
  | var i, x => x i
  | constant q, _ => q
  | add f g, x => f.eval x + g.eval x
  | neg f, x => -f.eval x
  | mul f g, x => f.eval x * g.eval x
  | inv f, x => (f.eval x)⁻¹

/-- Evaluate an expression by exact interval arithmetic, failing only at an unsafe inverse. -/
def enclosure {n : ℕ} : RationalExpression n → (Fin n → RationalInterval) →
    Option RationalInterval
  | var i, X => some (X i)
  | constant q, _ => some (.singleton q)
  | add f g, X => do
      let I ← f.enclosure X
      let J ← g.enclosure X
      return I.add J
  | neg f, X => do
      let I ← f.enclosure X
      return I.neg
  | mul f g, X => do
      let I ← f.enclosure X
      let J ← g.enclosure X
      return I.mul J
  | inv f, X => do
      let I ← f.enclosure X
      if h : 0 < I.lower ∨ I.upper < 0 then return I.inv h else none

/-- Every successful result of `enclosure` contains the real value of the expression. -/
theorem enclosure_sound {n : ℕ} {f : RationalExpression n}
    {X : Fin n → RationalInterval} {x : Fin n → ℝ}
    (hx : ∀ i, (X i).Contains (x i)) {I : RationalInterval} (hI : f.enclosure X = some I) :
    I.Contains (f.eval x) := by
  induction f generalizing I with
  | var i =>
      simp only [enclosure, Option.some.injEq] at hI
      subst I
      exact hx i
  | constant q =>
      simp only [enclosure, Option.some.injEq] at hI
      subst I
      exact RationalInterval.singleton_contains q
  | add f g hf hg =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          cases hgI : g.enclosure X with
          | none => simp [hfI, hgI] at hI
          | some Ig =>
              simp [hfI, hgI] at hI
              subst I
              exact RationalInterval.add_contains (hf hfI) (hg hgI)
  | neg f hf =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          simp [hfI] at hI
          subst I
          exact RationalInterval.neg_contains (hf hfI)
  | mul f g hf hg =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          cases hgI : g.enclosure X with
          | none => simp [hfI, hgI] at hI
          | some Ig =>
              simp [hfI, hgI] at hI
              subst I
              exact RationalInterval.mul_contains (hf hfI) (hg hgI)
  | inv f hf =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          rw [hfI] at hI
          dsimp at hI
          split at hI
          · rename_i h
            simp only [Option.some.injEq] at hI
            subst I
            exact RationalInterval.inv_contains (hf hfI) h
          · contradiction

end RationalExpression

end LeanPool.Besicovitch

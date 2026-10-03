/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Growth.TablePrime
public import LeanPool.Zeta5Irrational.Growth.OuterPrime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Helpers for the piece tables

On a piece where `⌊x⌋`, `⌊αx⌋`, `⌊2λx⌋` are constant, `Ê_in(x, k)` and `Ê_out(x)` are explicit
combinations of the interval counts `c_{ij}({x}, {αx})`; the counts have closed forms.
-/

public section

open Finset

namespace Zeta5Irrational

lemma nat_floor_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : ⌊x⌋₊ = q := by
  rw [Nat.floor_eq_iff (by linarith)]; exact ⟨h1, h2⟩

lemma fract_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : Int.fract x = x - q :=
  by
  rw [Int.fract, show ⌊x⌋ = (q : ℤ) by rw [Int.floor_eq_iff]; push_cast; exact ⟨h1, h2⟩]
  push_cast; ring

lemma two_Jc_lin {u : ℝ} (μ : ℕ) (h1 : (μ : ℝ) ≤ 2 * u) (h2 : 2 * u < μ + 1) (hu : u ≤ 500) :
    2 * Jc u = 2 * μ * u - (μ : ℝ) * (μ + 1) / 2 := by
  have hu0 : 0 ≤ u := by
    have : (0 : ℝ) ≤ μ := by positivity
    linarith
  have e := two_Jc_eq hu0 hu
  have hfr : Int.fract (2 * u) = 2 * u - μ := fract_of_bounds h1 h2
  rw [e, hfr]; ring

/-- `ψ` in closed form. -/
lemma psiR_eq (k β : ℤ) : psiR k β = (lrow k β : ℚ) * (((k - β : ℤ) : ℚ) - lrow k β + 1) / 2 := by
  unfold psiR
  rw [← sum_range_tri]
  refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring

/-! ### Closed forms of the interval counts -/

section

variable {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)

lemma cc00 : ccount f g 0 0 = 1 / 2 := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hg0 hg1 in
lemma cc01 : ccount f g 0 1 = min g (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hg1 in
lemma cc02 : ccount f g 0 2 = max 0 (g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 in
lemma cc10 : ccount f g 1 0 = min f (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf1 in
lemma cc20 : ccount f g 2 0 = max 0 (f - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 in
lemma cc11 : ccount f g 1 1 = min (min f g) (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hg1 in
lemma cc12 : ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf1 in
lemma cc21 : ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hg1 in
lemma cc22 : ccount f g 2 2 = max 0 (min f g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

end

/-- `Ê_in` on a piece. -/
lemma Ein_expand {x : ℝ} (k : ℤ) {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1) (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x))
    (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Ein x k =
      -2 * (37 / 40 * x) * q + 12 * (37 / 40 * x) * q' +
            (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) -
          37 / 40 * x * k +
        2 * ∑ i, ∑ j, bIn q q' k i j * ccount (x - q) (3 / 40 * x - q') i j := by
  unfold Ein
  rw [nat_floor_of_bounds hq1 hq2, nat_floor_of_bounds hr1 hr2, fract_of_bounds hq1 hq2,
    fract_of_bounds hr1 hr2, two_Jc_lin μ hm1 hm2 (by linarith)]

/-- `Ê_out` on a piece. -/
lemma Eout_expand {x : ℝ} {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1) (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x))
    (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Eout x =
      -2 * (37 / 40 * x) * q + (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) -
          2 * ∑ i, ∑ j, bGO q i j * ccount (x - q) (3 / 40 * x - q') i j +
        max 0 (13 / 10 * x - 2) := by
  unfold Eout
  rw [nat_floor_of_bounds hq1 hq2, fract_of_bounds hq1 hq2, fract_of_bounds hr1 hr2,
    two_Jc_lin μ hm1 hm2 (by linarith)]

theorem toNat_cast_q (a : ℤ) : ((a.toNat : ℕ) : ℚ) = max (a : ℚ) 0 := by
  have := Int.toNat_eq_max a
  have h2 : (((a.toNat : ℕ) : ℤ) : ℚ) = ((max a 0 : ℤ) : ℚ) := by rw [this]
  push_cast at h2; exact h2

end Zeta5Irrational

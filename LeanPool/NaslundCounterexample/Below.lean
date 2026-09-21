/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.NaslundCounterexample.Polynomials

/-!
# Degree below `m`, internally

The public statements bound degrees with `natDegree f < n`, a comparison of natural numbers. That
formulation cannot express `P_{3,0} = {0}`, because the zero polynomial has natural degree `0`;
and the recursion of the construction starts exactly there. So internally a polynomial has
*degree below `m`* when `degree f < m` in `WithBot ℕ`, where `m = 0` says `f = 0` and no separate
base case is needed. The two agree for `m ≥ 1`, which is where the public statements live.

This file is the toolkit: the coefficient characterisation, the passage to `natDegree`, closure
under the operations the lift performs, and the two multiplication bounds for `P` and `Q`.
-/

@[expose] public section

namespace NaslundCounterexample

open Polynomial

/-- `f` has degree below `m`: membership in `P_{3,m}`, the polynomials of degree less than `m`.
For `m = 0` this says `f = 0`, since `degree 0 = ⊥`. -/
def Below (m : ℕ) (f : (ZMod 3)[X]) : Prop := f.degree < m

/-- Every element of `B` has degree below `m`, that is, `B ⊆ P_{3,m}`. -/
def AllBelow (m : ℕ) (B : Finset (ZMod 3)[X]) : Prop := ∀ f ∈ B, Below m f

/-- Degree below `m` read off the coefficients: all coefficients from `T^m` on vanish. -/
theorem below_iff_coeff (m : ℕ) (f : (ZMod 3)[X]) : Below m f ↔ ∀ i, m ≤ i → f.coeff i = 0 :=
  degree_lt_iff_coeff_zero f m

/-- The coefficients of a polynomial of degree below `m` vanish from `T^m` on. -/
theorem Below.coeff_eq_zero {m : ℕ} {f : (ZMod 3)[X]} (h : Below m f) {i : ℕ} (hi : m ≤ i) :
    f.coeff i = 0 := (below_iff_coeff m f).mp h i hi

/-- `P_{3,0} = {0}`: degree below `0` is exactly being the zero polynomial. -/
theorem below_zero_iff (f : (ZMod 3)[X]) : Below 0 f ↔ f = 0 := by
  simp only [Below, Nat.cast_zero, ← degree_eq_bot, Nat.WithBot.lt_zero_iff]

/-- For `m ≥ 1`, degree below `m` is the public bound `natDegree f < m`. -/
theorem below_iff_natDegree_lt (m : ℕ) (f : (ZMod 3)[X]) (hm : 1 ≤ m) :
    Below m f ↔ f.natDegree < m := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [Below, degree_zero, natDegree_zero]
    exact iff_of_true (WithBot.bot_lt_coe m) hm
  · exact (natDegree_lt_iff_degree_lt hf).symm

/-- For `m ≥ 1`, the internal and the public degree bounds on a finite set agree. -/
theorem allBelow_iff_degreeBelow (m : ℕ) (B : Finset (ZMod 3)[X]) (hm : 1 ≤ m) :
    AllBelow m B ↔ DegreeBelow m B :=
  ⟨fun h f hf => (below_iff_natDegree_lt m f hm).mp (h f hf),
    fun h f hf => (below_iff_natDegree_lt m f hm).mpr (h f hf)⟩

/-- A degree bound may be weakened. -/
theorem Below.mono {m m' : ℕ} (h : m ≤ m') {f : (ZMod 3)[X]} (hf : Below m f) : Below m' f :=
  lt_of_lt_of_le hf (by exact_mod_cast h)

/-- Degree below `m + 1` is natural degree at most `m`. -/
theorem Below.natDegree_le {m : ℕ} {f : (ZMod 3)[X]} (h : Below (m + 1) f) : f.natDegree ≤ m :=
  Nat.lt_succ_iff.mp ((below_iff_natDegree_lt (m + 1) f (Nat.succ_le_succ (Nat.zero_le m))).mp h)

/-- The zero polynomial has degree below every `m`, including `m = 0`. -/
theorem below_zero (m : ℕ) : Below m (0 : (ZMod 3)[X]) := by
  simp only [Below, degree_zero]
  exact WithBot.bot_lt_coe m

/-- Degree at most `m` is degree below `m + 1`. -/
theorem below_of_degree_le {m : ℕ} {f : (ZMod 3)[X]} (h : f.degree ≤ m) : Below (m + 1) f :=
  lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self m)

/-- A sum of polynomials of degree below `m` has degree below `m`. -/
theorem Below.add {m : ℕ} {f g : (ZMod 3)[X]} (hf : Below m f) (hg : Below m g) :
    Below m (f + g) := lt_of_le_of_lt (degree_add_le f g) (max_lt hf hg)

/-- Negation preserves the degree bound. -/
theorem Below.neg {m : ℕ} {f : (ZMod 3)[X]} (hf : Below m f) : Below m (-f) := by
  simpa only [Below, degree_neg] using hf

/-- A difference of polynomials of degree below `m` has degree below `m`. -/
theorem Below.sub {m : ℕ} {f g : (ZMod 3)[X]} (hf : Below m f) (hg : Below m g) :
    Below m (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- A single term `a T^i` with `i < m` has degree below `m`. -/
theorem below_C_mul_X_pow (a : ZMod 3) (i m : ℕ) (h : i < m) : Below m (C a * X ^ i) :=
  lt_of_le_of_lt (degree_C_mul_X_pow_le i a) (by exact_mod_cast h)

/-- Multiplying by `P` raises the degree bound by `3`. -/
theorem Below.P_mul {m : ℕ} {f : (ZMod 3)[X]} (h : Below m f) : Below (m + 3) (P * f) := by
  simp only [Below, degree_mul, degree_P]
  rw [show ((m + 3 : ℕ) : WithBot ℕ) = 3 + (m : WithBot ℕ) by push_cast; ring]
  exact WithBot.add_lt_add_left (by decide) h

/-- Multiplying by `Q` raises the degree bound by `6`. -/
theorem Below.Q_mul {m : ℕ} {f : (ZMod 3)[X]} (h : Below m f) : Below (m + 6) (Q * f) := by
  simp only [Below, degree_mul, degree_Q]
  rw [show ((m + 6 : ℕ) : WithBot ℕ) = 6 + (m : WithBot ℕ) by push_cast; ring]
  exact WithBot.add_lt_add_left (by decide) h

end NaslundCounterexample

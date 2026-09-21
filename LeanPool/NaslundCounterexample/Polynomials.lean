/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.NaslundCounterexample.Definitions

/-!
# The four polynomials of the lift

`P = T^3 - T` vanishes at every element of `F_3`, and `Q = P^2` is the multiplier that carries a
set of small polynomials into the top of a larger degree range. `V_s` is the quadratic
interpolant that realises a prescribed triple of values at `0, 1, 2`, and `R_r` is a general
polynomial of degree below `3`.

This file records their degrees, their values on `F_3`, the two coefficients of `Q` the
construction reads (`[T^5] Q = 0` and `[T^6] Q = 1`), and the two divisibility facts the
square-freeness argument needs: a polynomial of degree at most `2` vanishing on `F_3` is zero,
and `P` divides any polynomial vanishing on `F_3`.
-/

@[expose] public section

namespace NaslundCounterexample

open Polynomial

/-- `P = T^3 - T`, which vanishes at every element of `F_3`. -/
noncomputable def P : (ZMod 3)[X] := X ^ 3 - X

/-- `Q = P^2 = T^6 + T^4 + T^2`, the multiplier of the lift. -/
noncomputable def Q : (ZMod 3)[X] := P ^ 2

/-- The interpolant `V_s = s_0 + (s_2 - s_1) T - (s_0 + s_1 + s_2) T^2`, whose value at `c` is
`s_c` for `c = 0, 1, 2`. -/
noncomputable def V (s : Fin 4 → ZMod 3) : (ZMod 3)[X] :=
  C (s 0) + C (s 2 - s 1) * X - C (s 0 + s 1 + s 2) * X ^ 2

/-- The polynomial `r_0 + r_1 T + r_2 T^2` of degree below `3` with coefficient vector `r`. -/
noncomputable def R (r : Fin 3 → ZMod 3) : (ZMod 3)[X] :=
  C (r 0) + C (r 1) * X + C (r 2) * X ^ 2

/-! ## `P` -/

/-- `P` is monic, being `T^3` minus a polynomial of smaller degree. -/
theorem P_monic : P.Monic := by
  have h : ((X : (ZMod 3)[X])).degree < (3 : ℕ) := by
    rw [degree_X]; exact_mod_cast (by norm_num : (1 : ℕ) < 3)
  simpa [P] using monic_X_pow_sub h

/-- `P` is not the zero polynomial. -/
theorem P_ne_zero : P ≠ 0 := P_monic.ne_zero

/-- `P` has degree `3`. -/
theorem degree_P : P.degree = 3 := by
  unfold P; compute_degree!

/-- `P` has natural degree `3`. -/
theorem natDegree_P : P.natDegree = 3 := natDegree_eq_of_degree_eq_some degree_P

/-- `P` vanishes at every element of `F_3`: `c ^ 3 = c` there. -/
theorem eval_P (c : ZMod 3) : P.eval c = 0 := by
  simp only [P, eval_sub, eval_pow, eval_X]
  revert c; decide

/-! ## `Q` -/

/-- `Q = T^6 + T^4 + T^2`: squaring `P` in characteristic `3` turns `-2` into `1`. -/
theorem Q_eq : Q = X ^ 6 + X ^ 4 + X ^ 2 := by
  have h3 : (3 : (ZMod 3)[X]) = 0 := by
    exact_mod_cast CharP.cast_eq_zero ((ZMod 3)[X]) 3
  simp only [Q, P]
  linear_combination (-(X : (ZMod 3)[X]) ^ 4) * h3

/-- `Q` is monic. -/
theorem Q_monic : Q.Monic := P_monic.pow 2

/-- `Q` is not the zero polynomial. -/
theorem Q_ne_zero : Q ≠ 0 := Q_monic.ne_zero

/-- `Q` has degree `6`. -/
theorem degree_Q : Q.degree = 6 := by
  rw [Q_eq]; compute_degree!

/-- `Q` has natural degree `6`. -/
theorem natDegree_Q : Q.natDegree = 6 := natDegree_eq_of_degree_eq_some degree_Q

/-- `Q` vanishes at every element of `F_3`. -/
theorem eval_Q (c : ZMod 3) : Q.eval c = 0 := by
  simp [Q, eval_P c]

/-- `Q` has no `T^5` term; this is why the parameter `u` does not disturb the top coordinate of
a lifted polynomial. -/
theorem coeff_Q_five : Q.coeff 5 = 0 := by
  rw [Q_eq]; simp [coeff_add, coeff_X_pow]

/-- The leading coefficient of `Q`, read at `T^6`. -/
theorem coeff_Q_six : Q.coeff 6 = 1 := by
  rw [Q_eq]; simp [coeff_add, coeff_X_pow]

/-! ## The interpolant `V_s` -/

/-- `V_s(0) = s_0`. -/
theorem eval_V_zero (s : Fin 4 → ZMod 3) : (V s).eval 0 = s 0 := by
  simp [V]

/-- `V_s(1) = s_1`: the three coefficients sum to `s_1` in `F_3`. -/
theorem eval_V_one (s : Fin 4 → ZMod 3) : (V s).eval 1 = s 1 := by
  simp only [V, eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow, one_pow, mul_one]
  generalize s 0 = a; generalize s 1 = b; generalize s 2 = c
  revert a b c; decide

/-- `V_s(2) = s_2`. -/
theorem eval_V_two (s : Fin 4 → ZMod 3) : (V s).eval 2 = s 2 := by
  simp only [V, eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  generalize s 0 = a; generalize s 1 = b; generalize s 2 = c
  revert a b c; decide

/-- `V_s` has degree at most `2`. -/
theorem degree_V_le (s : Fin 4 → ZMod 3) : (V s).degree ≤ 2 := by
  unfold V; compute_degree

/-- `V_s` depends only on the first three coordinates of `s`. -/
theorem V_congr (s s' : Fin 4 → ZMod 3) (h0 : s 0 = s' 0) (h1 : s 1 = s' 1) (h2 : s 2 = s' 2) :
    V s = V s' := by
  simp only [V, h0, h1, h2]

/-! ## The general polynomial `R_r` of degree below `3` -/

/-- `R_r` has degree at most `2`. -/
theorem degree_R_le (r : Fin 3 → ZMod 3) : (R r).degree ≤ 2 := by
  unfold R; compute_degree

/-- The coefficients of `R_r` below `T^3` are the entries of `r`. -/
theorem coeff_R (r : Fin 3 → ZMod 3) (i : Fin 3) : (R r).coeff (i : ℕ) = r i := by
  fin_cases i <;> simp [R, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]

/-- Distinct coefficient vectors give distinct polynomials. -/
theorem R_injective : Function.Injective R := by
  intro r r' h
  funext i
  rw [← coeff_R r i, ← coeff_R r' i, h]

/-- `P · R_r` has degree at most `5`. -/
theorem degree_P_mul_R_le (r : Fin 3 → ZMod 3) : (P * R r).degree ≤ 5 := by
  rw [degree_mul, degree_P]
  calc (3 : WithBot ℕ) + (R r).degree = (R r).degree + 3 := add_comm _ _
    _ ≤ 2 + 3 := add_le_add_left (degree_R_le r) 3
    _ = 5 := by decide

/-- The part of a lifted polynomial below the multiplier `Q` has degree at most `5`. -/
theorem degree_V_add_P_mul_R_le (s : Fin 4 → ZMod 3) (r : Fin 3 → ZMod 3) :
    (V s + P * R r).degree ≤ 5 :=
  le_trans (degree_add_le _ _)
    (max_le (le_trans (degree_V_le s) (by decide)) (degree_P_mul_R_le r))

/-! ## Vanishing on `F_3` -/

/-- A polynomial of degree at most `2` vanishing at `0`, `1` and `2` is zero: it has three roots
in a field and degree below `3`. -/
theorem eq_zero_of_degree_le_two_of_eval (f : (ZMod 3)[X]) (hf : f.degree ≤ 2)
    (h0 : f.eval 0 = 0) (h1 : f.eval 1 = 0) (h2 : f.eval 2 = 0) : f = 0 := by
  have hnat : f.natDegree ≤ 2 := natDegree_le_iff_degree_le.mpr (by exact_mod_cast hf)
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' f (Finset.univ : Finset (ZMod 3)) ?_ ?_
  · have hcases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
    intro c _
    rcases hcases c with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  · rw [Finset.card_univ, ZMod.card]
    omega

/-- `P` divides every polynomial vanishing at `0`, `1` and `2`: the remainder of the division by
the monic `P` has degree below `3` and vanishes there too, hence is zero. -/
theorem P_dvd_of_eval (z : (ZMod 3)[X]) (h0 : z.eval 0 = 0) (h1 : z.eval 1 = 0)
    (h2 : z.eval 2 = 0) : P ∣ z := by
  have hsplit : z %ₘ P + P * (z /ₘ P) = z := modByMonic_add_div z P
  have hrem : ∀ c : ZMod 3, z.eval c = 0 → (z %ₘ P).eval c = 0 := by
    intro c hc
    have h := congrArg (Polynomial.eval c) hsplit
    simp only [eval_add, eval_mul, eval_P c, zero_mul, add_zero, hc] at h
    exact h
  have hP_ne_one : P ≠ 1 := fun h => by
    have h3 : (3 : ℕ) = 0 := by rw [← natDegree_P, h, natDegree_one]
    exact absurd h3 (by norm_num)
  have hdeg : (z %ₘ P).degree ≤ 2 := by
    have h := natDegree_modByMonic_lt z P_monic hP_ne_one
    rw [natDegree_P] at h
    refine le_trans degree_le_natDegree ?_
    have h' : (z %ₘ P).natDegree ≤ 2 := by omega
    exact_mod_cast h'
  have hzero : z %ₘ P = 0 :=
    eq_zero_of_degree_le_two_of_eval _ hdeg (hrem 0 h0) (hrem 1 h1) (hrem 2 h2)
  exact (modByMonic_eq_zero_iff_dvd P_monic).mp hzero

/-- A multiple of `Q` of degree below `6` is zero. -/
theorem eq_zero_of_Q_dvd_of_degree_lt (f : (ZMod 3)[X]) (hf : f.degree < 6) (h : Q ∣ f) :
    f = 0 :=
  eq_zero_of_dvd_of_degree_lt h (by rw [degree_Q]; exact hf)

end NaslundCounterexample

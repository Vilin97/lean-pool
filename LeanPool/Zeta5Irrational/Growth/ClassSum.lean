/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

/-! # Class sums and their continuous limits

For `p = 2m + 1` and `0 ≤ v, v' < p` put, for `1 ≤ c ≤ m`,
`a_c = [c ≤ v] + [p - v ≤ c]` and `a'_c = [c ≤ v'] + [p - v' ≤ c]`.
Every function `h` of `(a_c, a'_c)` is a combination of the products of the interval indicators
`1 = [1 ≤ c ≤ m]`, `A = [c ≤ v]`, `E = [p - v ≤ c]`, so `∑_c h(a_c, a'_c)` is a combination of
nine interval counts. Each count is within `5/2` of `p` times its continuous analogue, where
`v/p = f`, `v'/p = g`.

We also prove `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)`.
-/

public section

open Finset

namespace Zeta5Irrational

/-- The interval `[lo i, hi i]` of the indicator `i ∈ {1, A, E}`. -/
def ivLo (p v : ℕ) : Fin 3 → ℕ :=
  ![1, 1, p - v]

/-- Upper endpoints of the three discrete intervals used in the class-count expansion. -/
def ivHi (m v : ℕ) : Fin 3 → ℕ :=
  ![m, v, m]

/-- The continuous intervals. -/
@[expose] noncomputable def cvLo (f : ℝ) : Fin 3 → ℝ :=
  ![0, 0, 1 - f]

/-- Upper endpoints of the continuous intervals corresponding to `ivHi`. -/
@[expose] noncomputable def cvHi (f : ℝ) : Fin 3 → ℝ :=
  ![1 / 2, f, 1 / 2]

/-- The coefficients of `h` in the basis `1, A, E`. -/
@[expose] def bcoef (h : ℕ → ℝ) : Fin 3 → ℝ :=
  ![h 0, h 1 - h 0, h 2 - h 1]

/-- `a(c) = [c ≤ v] + [p - v ≤ c]`. -/
@[expose] def aCnt (p v c : ℕ) : ℕ :=
  (if c ≤ v then 1 else 0) + (if p - v ≤ c then 1 else 0)

/-- The interval indicator. -/
def ivInd (p m v : ℕ) (i : Fin 3) (c : ℕ) : ℝ :=
  if ivLo p v i ≤ c ∧ c ≤ ivHi m v i then 1 else 0

lemma expand_one {p m v c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hc1 : 1 ≤ c) (hcm : c ≤ m)
    (h : ℕ → ℝ) : h (aCnt p v c) = ∑ i, bcoef h i * ivInd p m v i c := by
  simp only [Fin.sum_univ_three, bcoef, ivInd, ivLo, ivHi, aCnt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  by_cases h1 : c ≤ v <;> by_cases h2 : p - v ≤ c
  · simp [h1, h2, hc1, hcm]
  · simp [h1, h2, hc1, hcm]
  · exfalso; omega
  · simp [h1, h2, hc1, hcm]

lemma expand_two {p m v v' c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (hc1 : 1 ≤ c)
    (hcm : c ≤ m) (h : ℕ → ℕ → ℝ) :
    h (aCnt p v c) (aCnt p v' c) =
      ∑ i,
        ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * (ivInd p m v i c * ivInd p m v' j c) :=
  by
  rw [expand_one hm hv hc1 hcm (fun a => h a (aCnt p v' c))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ a, h a (aCnt p v' c) = ∑ j, bcoef (fun b => h a b) j * ivInd p m v' j c := fun a =>
    expand_one hm hv' hc1 hcm (fun b => h a b)
  simp only [e]
  simp only [bcoef, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fin_cases i <;> simp <;> ring

/-- The discrete count of an intersection of two intervals within `[1, m]`. -/
lemma card_two_intervals (m lo hi lo' hi' : ℕ) :
    ((Icc 1 m).filter fun c => (lo ≤ c ∧ c ≤ hi) ∧ (lo' ≤ c ∧ c ≤ hi')).card =
      min (min hi hi') m + 1 - max (max lo lo') 1 := by
  have :
    (Icc 1 m).filter (fun c => (lo ≤ c ∧ c ≤ hi) ∧ (lo' ≤ c ∧ c ≤ hi')) =
      Icc (max (max lo lo') 1) (min (min hi hi') m) :=
    by ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]

/-- **Class sums as interval counts.** -/
theorem class_sum {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    ∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) =
      ∑ i,
        ∑ j,
          bcoef (fun a => bcoef (fun b => h a b) j) i *
            ((min (min (ivHi m v i) (ivHi m v' j)) m + 1 -
                  max (max (ivLo p v i) (ivLo p v' j)) 1 :
                ℕ) :
              ℝ) := by
  rw [Finset.sum_congr rfl fun c hc =>
      expand_two hm hv hv' (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2 h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, ← card_two_intervals]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ivInd]
  split_ifs <;> simp_all

/-- The continuous analogue of an interval count. -/
@[expose] noncomputable def ccount (f g : ℝ) (i j : Fin 3) : ℝ :=
  max 0 (min (min (cvHi f i) (cvHi g j)) (1 / 2) - max (max (cvLo f i) (cvLo g j)) 0)

lemma cast_trunc_sub (a b : ℕ) : ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
  rcases le_or_gt b a with h | h
  · have h' : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_right (by linarith)]
  · have h' : (a : ℝ) < b := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h.le, max_eq_left (by linarith)]
    simp

lemma abs_max0_sub (u w : ℝ) : |max 0 u - max 0 w| ≤ |u - w| := by
  have := abs_max_sub_max_le_max (0 : ℝ) u 0 w
  simpa using this

lemma hi_approx {p m v : ℕ} (hm : 2 * m + 1 = p) (_hv : v < p) (i : Fin 3) :
    |(ivHi m v i : ℝ) - p * cvHi ((v : ℝ) / p) i| ≤ 1 / 2 := by
  have hp : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hmR : (m : ℝ) = (p - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hm
    push_cast at this; linarith
  fin_cases i <;> simp only [ivHi, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, hmR, cvHi,
      one_div, ge_iff_le, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · rw [abs_le]; constructor <;> linarith
  · rw [mul_div_cancel₀ _ hp.ne']; simp
  · rw [abs_le]; constructor <;> linarith

lemma lo_approx {p v : ℕ} (hv : v < p) (i : Fin 3) :
    |(ivLo p v i : ℝ) - p * cvLo ((v : ℝ) / p) i| ≤ 1 := by
  have hp : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  fin_cases i <;> simp only [ivLo, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Nat.cast_one,
      cvLo, mul_zero, sub_zero, abs_one, Std.le_refl, Fin.mk_one, Matrix.cons_val_one,
      Fin.reduceFinMk, Matrix.cons_val, ge_iff_le]
  rw [Nat.cast_sub hv.le, mul_sub, mul_one, mul_div_cancel₀ _ hp.ne']
  simp

/-- **Each interval count is within `5/2` of `p` times its continuous analogue.** -/
lemma count_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (i j : Fin 3) :
    |((min (min (ivHi m v i) (ivHi m v' j)) m + 1 - max (max (ivLo p v i) (ivLo p v' j)) 1 : ℕ) :
            ℝ) -
          (p : ℝ) * ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤
      5 / 2 := by
  have hp : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hmR : (m : ℝ) = (p - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hm
    push_cast at this; linarith
  rw [cast_trunc_sub]
  unfold ccount
  rw [mul_max_of_nonneg _ _ hp.le, mul_zero, mul_sub, mul_min_of_nonneg _ _ hp.le,
    mul_min_of_nonneg _ _ hp.le, mul_max_of_nonneg _ _ hp.le, mul_max_of_nonneg _ _ hp.le,
    mul_zero]
  refine (abs_max0_sub _ _).trans ?_
  push_cast
  have h1 :
    |min (min (ivHi m v i : ℝ) (ivHi m v' j)) m -
          min (min (p * cvHi ((v : ℝ) / p) i) (p * cvHi ((v' : ℝ) / p) j)) (p * (1 / 2))| ≤
      1 / 2 := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · exact
        (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hi_approx hm hv i) (hi_approx hm hv' j))
    · rw [hmR, abs_le]; constructor <;> linarith
  have h2 :
    |max (max (ivLo p v i : ℝ) (ivLo p v' j)) 1 -
          max (max (p * cvLo ((v : ℝ) / p) i) (p * cvLo ((v' : ℝ) / p) j)) 0| ≤
      1 := by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (by norm_num))
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (lo_approx hv i) (lo_approx hv' j))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Class sums versus their continuous limit.** -/
theorem class_sum_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    |∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) -
          (p : ℝ) *
            ∑ i,
              ∑ j,
                bcoef (fun a => bcoef (fun b => h a b) j) i *
                  ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤
      5 / 2 * ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i| := by
  rw [class_sum hm hv hv', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm, ← mul_sub, abs_mul, mul_comm (5 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (count_approx hm hv hv' i j) (abs_nonneg _)

end Zeta5Irrational

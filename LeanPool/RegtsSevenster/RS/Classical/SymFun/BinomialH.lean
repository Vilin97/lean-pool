/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums

/-!
# Complete homogeneous values at constant sequences

At the constant power-sum sequence `m` the complete homogeneous
values are the binomial coefficients `C(m+d−1, d)` (the generating
function `(1−z)^{−m}`); at `−m` they are the signed binomials
`(−1)^d C(m, d)` (the generating function `(1−z)^m`).  These feed
the tensor-space traces of the dimension-bound argument.
-/

namespace RS

open Finset

/-- Partial sums of the positive binomial column (hockey stick). -/
private theorem sum_choose_partial (m d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), (Nat.choose (m + j - 1) j : ℂ) =
      (Nat.choose (m + d) d : ℂ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show m + (d + 1) - 1 = m + d from by omega]
    rw [show m + (d + 1) = (m + d) + 1 from by omega]
    rw [Nat.choose_succ_succ (m + d) d]
    push_cast
    ring

/-- Alternating partial sums of a binomial row. -/
private theorem sum_alt_choose_partial (m d : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range (d + 1),
        ((-1 : ℂ)) ^ j * (Nat.choose m j : ℂ) =
      ((-1 : ℂ)) ^ d * (Nat.choose (m - 1) d : ℂ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    have hnat : Nat.choose (m - 1) d + Nat.choose (m - 1) (d + 1) =
        Nat.choose m (d + 1) := by
      conv_rhs => rw [show m = (m - 1) + 1 from by omega]
      rw [Nat.choose_succ_succ (m - 1) d]
    have hcast : (Nat.choose (m - 1) d : ℂ) +
        (Nat.choose (m - 1) (d + 1) : ℂ) =
        (Nat.choose m (d + 1) : ℂ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℂ)) hnat
    rw [pow_succ]
    linear_combination (-((-1 : ℂ) ^ (d + 1))) * hcast

/-- **Complete homogeneous values at the constant sequence** are
binomial coefficients. -/
theorem newtonH_const (m : ℕ) (d : ℕ) :
    newtonH (fun _ => (m : ℂ)) d =
      (Nat.choose (m + d - 1) d : ℂ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp [newtonH_zero]
    | d + 1 =>
      rw [newtonH]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [ih (d - i) (by
          rw [Finset.mem_range] at hi
          omega)])]
      rw [show (∑ i ∈ Finset.range (d + 1),
          (m : ℂ) * (Nat.choose (m + (d - i) - 1) (d - i) : ℂ)) =
        (m : ℂ) * ∑ j ∈ Finset.range (d + 1),
          (Nat.choose (m + j - 1) j : ℂ) from by
        rw [Finset.mul_sum]
        exact Finset.sum_nbij' (fun i => d - i) (fun j => d - j)
          (fun i hi => Finset.mem_range.mpr (by
            rw [Finset.mem_range] at hi; omega))
          (fun j hj => Finset.mem_range.mpr (by
            rw [Finset.mem_range] at hj; omega))
          (fun i hi => by rw [Finset.mem_range] at hi; omega)
          (fun j hj => by rw [Finset.mem_range] at hj; omega)
          (fun i _ => rfl)]
      rw [sum_choose_partial m d]
      have h2 : Nat.choose (m + d) (d + 1) * (d + 1) =
          Nat.choose (m + d) d * m := by
        have h3 := Nat.choose_succ_right_eq (m + d) d
        rw [show m + d - d = m from by omega] at h3
        exact h3
      have hne : ((d : ℂ) + 1) ≠ 0 := by
        exact Nat.cast_add_one_ne_zero d
      rw [show m + (d + 1) - 1 = m + d from by omega]
      rw [inv_mul_eq_iff_eq_mul₀ hne]
      have hcast : (Nat.choose (m + d) (d + 1) : ℂ) *
          ((d : ℂ) + 1) = (Nat.choose (m + d) d : ℂ) * (m : ℂ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℂ)) h2
      linear_combination -hcast

/-- **Complete homogeneous values at the negated constant
sequence** are signed binomials. -/
theorem newtonH_neg_const (m : ℕ) (hm : 1 ≤ m) (d : ℕ) :
    newtonH (fun _ => -(m : ℂ)) d =
      ((-1 : ℂ)) ^ d * (Nat.choose m d : ℂ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp [newtonH_zero]
    | d + 1 =>
      rw [newtonH]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [ih (d - i) (by
          rw [Finset.mem_range] at hi
          omega)])]
      rw [show (∑ i ∈ Finset.range (d + 1),
          (-(m : ℂ)) * (((-1 : ℂ)) ^ (d - i) *
            (Nat.choose m (d - i) : ℂ))) =
        (-(m : ℂ)) * ∑ j ∈ Finset.range (d + 1),
          ((-1 : ℂ)) ^ j * (Nat.choose m j : ℂ) from by
        rw [Finset.mul_sum]
        exact Finset.sum_nbij' (fun i => d - i) (fun j => d - j)
          (fun i hi => Finset.mem_range.mpr (by
            rw [Finset.mem_range] at hi; omega))
          (fun j hj => Finset.mem_range.mpr (by
            rw [Finset.mem_range] at hj; omega))
          (fun i hi => by rw [Finset.mem_range] at hi; omega)
          (fun j hj => by rw [Finset.mem_range] at hj; omega)
          (fun i _ => rfl)]
      rw [sum_alt_choose_partial m d hm]
      have h2 : m * Nat.choose (m - 1) d =
          Nat.choose m (d + 1) * (d + 1) := by
        have h3 := Nat.add_one_mul_choose_eq (m - 1) d
        rw [show (m - 1) + 1 = m from by omega] at h3
        exact h3
      have hne : ((d : ℂ) + 1) ≠ 0 := by
        exact Nat.cast_add_one_ne_zero d
      rw [inv_mul_eq_iff_eq_mul₀ hne]
      have hcast : (m : ℂ) * (Nat.choose (m - 1) d : ℂ) =
          (Nat.choose m (d + 1) : ℂ) * ((d : ℂ) + 1) := by
        have := congrArg (Nat.cast (R := ℂ)) h2
        push_cast at this
        linear_combination this
      rw [pow_succ]
      linear_combination (-((-1 : ℂ) ^ d)) * hcast

end RS

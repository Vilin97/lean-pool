/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.EHConv

/-!
# Integer-indexed complete homogeneous polynomials

The `ℤ`-indexed extension of `hSub`, vanishing in negative
degrees, and the guarded range-`k` form of the resolvent — the
entry form of the bialternant matrices.
-/

namespace RS

open Finset MvPolynomial

variable {k : ℕ}

/-- The `ℤ`-indexed extension of `hSub`, vanishing in negative
degrees. -/
noncomputable def hSubZ (A : Finset (Fin k)) (d : ℤ) :
    MvPolynomial (Fin k) ℂ :=
  if 0 ≤ d then hSub A d.toNat else 0

/-- The integer extension agrees in non-negative degrees. -/
@[simp]
theorem hSubZ_natCast (A : Finset (Fin k)) (m : ℕ) :
    hSubZ A (m : ℤ) = hSub A m := by
  rw [hSubZ, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast]

/-- And vanishes in negative ones. -/
@[simp]
theorem hSubZ_neg (A : Finset (Fin k)) (d : ℤ) (hd : d < 0) :
    hSubZ A d = 0 := by
  rw [hSubZ, ite_eq_right (not_le.mpr hd)]

/-- The resolvent in guarded range-`k` form: for `j ∉ A` with
`insert j A` filling all `k` variables, the `r`-sum over `Fin k`
computes `X j ^ m` for every `m`. -/
theorem sum_fin_resolvent (hrec : HSubRec k)
    {A : Finset (Fin k)} {j : Fin k} (hj : j ∉ A)
    (hcard : A.card + 1 = k) (m : ℕ) :
    ∑ r : Fin k,
      (-1 : MvPolynomial (Fin k) ℂ) ^ (r : ℕ) *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - (r : ℕ))) =
      X j ^ m := by
  classical
  have h1 : (∑ r : Fin k,
      (-1 : MvPolynomial (Fin k) ℂ) ^ (r : ℕ) *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - (r : ℕ)))) =
      ∑ r ∈ Finset.range k,
        (-1 : MvPolynomial (Fin k) ℂ) ^ r *
          (eSub A r * hSubZ (insert j A) ((m : ℤ) - r)) :=
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ => (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - r))) k
  have h2 : (∑ r ∈ Finset.range k,
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - r))) =
      ∑ r ∈ Finset.range (k + (m + 1)),
        (-1 : MvPolynomial (Fin k) ℂ) ^ r *
          (eSub A r * hSubZ (insert j A) ((m : ℤ) - r)) := by
    refine Finset.sum_subset
      (fun x hx => ?_) fun r _ hnr => ?_
    · rw [Finset.mem_range] at hx ⊢
      omega
    have hr : k ≤ r := by
      rw [Finset.mem_range] at hnr
      omega
    rw [eSub_eq_zero_of_lt A r (by omega)]
    ring
  have h3 : (∑ r ∈ Finset.range (m + 1),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - r))) =
      ∑ r ∈ Finset.range (k + (m + 1)),
        (-1 : MvPolynomial (Fin k) ℂ) ^ r *
          (eSub A r * hSubZ (insert j A) ((m : ℤ) - r)) := by
    refine Finset.sum_subset
      (fun x hx => ?_) fun r _ hnr => ?_
    · rw [Finset.mem_range] at hx ⊢
      omega
    have hr : m + 1 ≤ r := by
      rw [Finset.mem_range] at hnr
      omega
    rw [hSubZ_neg _ _ (by omega)]
    ring
  have h4 : (∑ r ∈ Finset.range (m + 1),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - r))) =
      fmix A j m := by
    rw [fmix]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrm : r ≤ m := by
      rw [Finset.mem_range] at hr
      omega
    have hc : ((m - r : ℕ) : ℤ) = (m : ℤ) - r := by omega
    rw [← hc, hSubZ_natCast]
  rw [h1, h2, ← h3, h4]
  exact fmix_eq_pow hrec hj m

end RS

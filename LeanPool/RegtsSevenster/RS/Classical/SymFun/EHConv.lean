/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.SubsetEH

/-!
# The e–h convolution and the single-variable resolvent

Over any variable subset `A`, the alternating e–h convolution
vanishes in positive degree, and the mixed convolution with one
extra variable `j` telescopes to `X j ^ m` — the entrywise content
of the bialternant matrix factorization.  The `hSub`
add-one-variable recurrence enters as the hypothesis `HSubRec`,
discharged in `HInsert.lean`.
-/

namespace RS

open Finset MvPolynomial

variable {k : ℕ}

/-- The `hSub` add-one-variable recurrence, as a hypothesis. -/
abbrev HSubRec (k : ℕ) : Prop :=
  ∀ {A : Finset (Fin k)} {j : Fin k}, j ∉ A → ∀ m : ℕ,
    hSub (insert j A) (m + 1) =
      hSub A (m + 1) + X j * hSub (insert j A) m

/-- Positive-degree `hSub` of the empty subset vanishes. -/
theorem hSub_empty (m : ℕ) :
    hSub (∅ : Finset (Fin k)) (m + 1) = 0 := by
  classical
  rw [hSub, Finset.filter_false_of_mem, Finset.sum_empty]
  intro w _ hall
  obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp
    (by rw [w.2]; omega)
  exact absurd (hall i hi) (Finset.notMem_empty i)

/-- The mixed e–h convolution with one extra variable. -/
noncomputable def fmix (A : Finset (Fin k)) (j : Fin k) (M : ℕ) :
    MvPolynomial (Fin k) ℂ :=
  ∑ r ∈ Finset.range (M + 1),
    (-1 : MvPolynomial (Fin k) ℂ) ^ r *
      (eSub A r * hSub (insert j A) (M - r))

private theorem conv_insert_eq {A : Finset (Fin k)} {j : Fin k}
    (hj : j ∉ A) (m : ℕ) :
    (∑ r ∈ Finset.range (m + 2),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub (insert j A) r * hSub (insert j A) (m + 1 - r))) =
    fmix A j (m + 1) - X j * fmix A j m := by
  have e1 : (∑ r ∈ Finset.range (m + 2),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub (insert j A) r * hSub (insert j A) (m + 1 - r))) =
      (∑ r ∈ Finset.range (m + 1),
        ((-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
          (eSub A (r + 1) * hSub (insert j A) (m - r)) +
        (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
          (X j * (eSub A r * hSub (insert j A) (m - r))))) +
      hSub (insert j A) (m + 1) := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl
      (fun r (_ : r ∈ Finset.range (m + 1)) =>
        show (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
            (eSub (insert j A) (r + 1) *
              hSub (insert j A) (m + 1 - (r + 1))) =
          (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
            (eSub A (r + 1) * hSub (insert j A) (m - r)) +
          (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
            (X j * (eSub A r * hSub (insert j A) (m - r)))
          from by
        rw [eSub_insert hj r, Nat.succ_sub_succ]
        ring)]
    rw [pow_zero, eSub_zero, Nat.sub_zero, one_mul, one_mul]
  have e2 : fmix A j (m + 1) =
      (∑ r ∈ Finset.range (m + 1),
        (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
          (eSub A (r + 1) * hSub (insert j A) (m - r))) +
      hSub (insert j A) (m + 1) := by
    rw [fmix, Finset.sum_range_succ']
    rw [Finset.sum_congr rfl
      (fun r (_ : r ∈ Finset.range (m + 1)) =>
        show (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
            (eSub A (r + 1) * hSub (insert j A) (m + 1 - (r + 1))) =
          (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
            (eSub A (r + 1) * hSub (insert j A) (m - r))
          from by rw [Nat.succ_sub_succ])]
    rw [pow_zero, eSub_zero, Nat.sub_zero, one_mul, one_mul]
  have e3 : (∑ r ∈ Finset.range (m + 1),
      (-1 : MvPolynomial (Fin k) ℂ) ^ (r + 1) *
        (X j * (eSub A r * hSub (insert j A) (m - r)))) =
      -(X j * fmix A j m) := by
    rw [fmix, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [e1, Finset.sum_add_distrib, e3, e2]
  ring

private theorem fmix_sub (hrec : HSubRec k) {A : Finset (Fin k)}
    {j : Fin k} (hj : j ∉ A) (m : ℕ) :
    fmix A j (m + 1) - X j * fmix A j m =
      ∑ r ∈ Finset.range (m + 2),
        (-1 : MvPolynomial (Fin k) ℂ) ^ r *
          (eSub A r * hSub A (m + 1 - r)) := by
  have e1 : fmix A j (m + 1) =
      (∑ r ∈ Finset.range (m + 1),
        (-1 : MvPolynomial (Fin k) ℂ) ^ r *
          (eSub A r * hSub (insert j A) (m + 1 - r))) +
      (-1 : MvPolynomial (Fin k) ℂ) ^ (m + 1) *
        (eSub A (m + 1) * 1) := by
    rw [fmix, Finset.sum_range_succ, Nat.sub_self, hSub_zero]
  have e2 : (∑ r ∈ Finset.range (m + 2),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSub A (m + 1 - r))) =
      (∑ r ∈ Finset.range (m + 1),
        (-1 : MvPolynomial (Fin k) ℂ) ^ r *
          (eSub A r * hSub A (m + 1 - r))) +
      (-1 : MvPolynomial (Fin k) ℂ) ^ (m + 1) *
        (eSub A (m + 1) * 1) := by
    rw [Finset.sum_range_succ, Nat.sub_self, hSub_zero]
  have e4 : ∀ r ∈ Finset.range (m + 1),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSub (insert j A) (m + 1 - r)) -
      X j * ((-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSub (insert j A) (m - r))) =
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSub A (m + 1 - r)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hd : m + 1 - r = (m - r) + 1 := by omega
    rw [hd, hrec hj (m - r)]
    ring
  rw [e1, e2, fmix, Finset.mul_sum, add_sub_right_comm,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl e4]

/-- **The e–h convolution vanishes in positive degree.** -/
theorem conv_eq_zero (hrec : HSubRec k) (A : Finset (Fin k))
    (m : ℕ) :
    ∑ r ∈ Finset.range (m + 2),
      (-1 : MvPolynomial (Fin k) ℂ) ^ r *
        (eSub A r * hSub A (m + 1 - r)) = 0 := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine Finset.sum_eq_zero fun r _ => ?_
    match r with
    | 0 =>
      rw [pow_zero, one_mul, eSub_zero, one_mul, Nat.sub_zero,
        hSub_empty]
    | r + 1 =>
      rw [eSub_eq_zero_of_lt _ _ (by
        rw [Finset.card_empty]; omega)]
      ring
  | insert j A hj ih =>
    rw [conv_insert_eq hj m, fmix_sub hrec hj m, ih]

/-- **The single-variable resolvent**: the mixed convolution
telescopes to a power of the extra variable. -/
theorem fmix_eq_pow (hrec : HSubRec k) {A : Finset (Fin k)}
    {j : Fin k} (hj : j ∉ A) (m : ℕ) :
    fmix A j m = X j ^ m := by
  induction m with
  | zero =>
    rw [fmix, Finset.sum_range_one, pow_zero,
      eSub_zero, hSub_zero]
    ring
  | succ m ih =>
    have h1 := fmix_sub hrec hj m
    rw [conv_eq_zero hrec A m] at h1
    have h2 : fmix A j (m + 1) = X j * fmix A j m :=
      sub_eq_zero.mp h1
    rw [h2, ih, pow_succ]
    ring

end RS

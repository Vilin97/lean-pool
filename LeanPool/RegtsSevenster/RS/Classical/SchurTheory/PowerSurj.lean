/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.HVal

/-!
# Surjectivity of the power-sum specialization

Every finite sequence of prospective power sums is realized by an
actual finite family of complex numbers: Newton-invert the
prescribed values to elementary symmetric values, build the monic
polynomial with those (sign-alternating) coefficients, split it
over ℂ, and read the roots.  The roots' elementary values match by
Vieta, and their power sums then agree with the prescription by
the triangular Newton recursion.

This is the globalization device: symmetric-function
identities are proved for genuine variable families and transferred
to arbitrary prospective power sums.
-/

namespace RS

open Finset Polynomial

/-- The elementary values prescribed by a sequence of power sums,
via the Newton recursion. -/
noncomputable def eSeq (t : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 =>
    ((k : ℂ) + 1)⁻¹ * (-1) ^ (k + 2) *
      ∑ a ∈ ((antidiagonal (k + 1)).filter
          (fun a => a.1 < k + 1)).attach,
        (-1) ^ a.1.1 * eSeq t a.1.1 * t a.1.2
  decreasing_by
    exact (Finset.mem_filter.mp a.2).2

/-- The defining relation of `eSeq`, unattached and cleared of the
inverse. -/
theorem eSeq_mul (t : ℕ → ℂ) (k : ℕ) :
    ((k : ℂ) + 1) * eSeq t (k + 1) =
      (-1) ^ (k + 2) *
        ∑ a ∈ (antidiagonal (k + 1)).filter
            (fun a => a.1 < k + 1),
          (-1) ^ a.1 * eSeq t a.1 * t a.2 := by
  rw [eSeq]
  rw [← Finset.sum_attach ((antidiagonal (k + 1)).filter
      (fun a => a.1 < k + 1))
    (fun a => (-1 : ℂ) ^ a.1 * eSeq t a.1 * t a.2)]
  rw [← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_add_one_ne_zero k : ((k : ℂ) + 1) ≠ 0),
    one_mul]

/-- The prescription satisfies the solved form of the Newton
recursion. -/
theorem t_eq_of_eSeq (t : ℕ → ℂ) (c : ℕ) (hc : 0 < c) :
    t c = (-1) ^ (c + 1) * c * eSeq t c -
      ∑ a ∈ (antidiagonal c).filter (fun a => a.1 ∈ Set.Ioo 0 c),
        (-1) ^ a.1 * eSeq t a.1 * t a.2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hc
  rw [zero_add] at *
  have h := eSeq_mul t k
  -- Split the `a.1 = 0` term off the filtered sum.
  have hsplit : ((antidiagonal (k + 1)).filter
      (fun a => a.1 < k + 1)) =
      insert ((0 : ℕ), k + 1)
        ((antidiagonal (k + 1)).filter
          (fun a => a.1 ∈ Set.Ioo 0 (k + 1))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_antidiagonal, Set.mem_Ioo]
    constructor
    · rintro ⟨hsum, hlt⟩
      by_cases h0 : a.1 = 0
      · left
        obtain ⟨a1, a2⟩ := a
        simp only at h0 hsum ⊢
        subst h0
        rw [zero_add] at hsum
        rw [hsum]
      · right
        exact ⟨hsum, Nat.pos_of_ne_zero h0, hlt⟩
    · rintro (rfl | ⟨hsum, h0, hlt⟩)
      · exact ⟨by rw [zero_add], by omega⟩
      · exact ⟨hsum, hlt⟩
  rw [hsplit, Finset.sum_insert (by
    simp only [Finset.mem_filter, Set.mem_Ioo]
    rintro ⟨-, h0, -⟩
    exact absurd rfl (Nat.ne_of_gt h0))] at h
  rw [show ((-1 : ℂ)) ^ (0 : ℕ) * eSeq t 0 * t (k + 1) = t (k + 1) from by
    rw [pow_zero, eSeq, one_mul, one_mul]] at h
  have h2 : (-1 : ℂ) ^ (k + 2) * (((k : ℂ) + 1) * eSeq t (k + 1)) =
      t (k + 1) + ∑ a ∈ (antidiagonal (k + 1)).filter
          (fun a => a.1 ∈ Set.Ioo 0 (k + 1)),
        (-1) ^ a.1 * eSeq t a.1 * t a.2 := by
    rw [h, ← mul_assoc, ← pow_add,
      show k + 2 + (k + 2) = 2 * (k + 2) from by ring,
      pow_mul, neg_one_sq, one_pow, one_mul]
  push_cast
  linear_combination -h2

/-! ### The realizing polynomial and its roots -/

/-- The monic polynomial with the prescribed alternating
elementary coefficients. -/
noncomputable def ePoly (t : ℕ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1),
    Polynomial.monomial (n - k) ((-1) ^ k * eSeq t k)

/-- The polynomial's coefficients are the prescribed elementary
values, alternating in sign. -/
theorem ePoly_coeff {t : ℕ → ℂ} {n k : ℕ} (hk : k ≤ n) :
    (ePoly t n).coeff (n - k) = (-1) ^ k * eSeq t k := by
  rw [ePoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl (fun j hj => Polynomial.coeff_monomial)]
  rw [Finset.sum_congr rfl (fun j hj => show
      (if n - j = n - k then ((-1 : ℂ)) ^ j * eSeq t j else 0) =
      (if j = k then ((-1 : ℂ)) ^ j * eSeq t j else 0) from
    if_congr (by
      have := Finset.mem_range.mp hj
      omega) rfl rfl)]
  rw [Finset.sum_ite_eq' (range (n + 1)) k
    (fun j => ((-1 : ℂ)) ^ j * eSeq t j)]
  rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- Its leading coefficient is `1`. -/
theorem ePoly_coeff_self (t : ℕ → ℂ) (n : ℕ) :
    (ePoly t n).coeff n = 1 := by
  have h := ePoly_coeff (t := t) (n := n) (k := 0) (Nat.zero_le n)
  rw [Nat.sub_zero] at h
  rw [h, pow_zero, one_mul, eSeq]

/-- Its degree is the number of prescribed values. -/
theorem ePoly_natDegree (t : ℕ → ℂ) (n : ℕ) :
    (ePoly t n).natDegree = n := by
  refine le_antisymm ?_ ?_
  · refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le n, fun j _ => ?_⟩
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le n j)
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [ePoly_coeff_self]
    exact one_ne_zero

/-- It is monic. -/
theorem ePoly_monic (t : ℕ → ℂ) (n : ℕ) : (ePoly t n).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, ePoly_natDegree,
    ePoly_coeff_self]

/-- Hence it has exactly that many roots over ℂ — the family the
prescription is realized by. -/
theorem ePoly_card_roots (t : ℕ → ℂ) (n : ℕ) :
    Multiset.card (ePoly t n).roots = n := by
  have h := Polynomial.splits_iff_card_roots.mp
    (IsAlgClosed.splits (k := ℂ) (ePoly t n))
  rw [ePoly_natDegree] at h
  exact h

/-- Vieta: the roots of the realizing polynomial have the
prescribed elementary values. -/
theorem ePoly_roots_esymm (t : ℕ → ℂ) {n k : ℕ} (hk : k ≤ n) :
    (ePoly t n).roots.esymm k = eSeq t k := by
  have h := Polynomial.coeff_eq_esymm_roots_of_card
    (p := ePoly t n)
    (by rw [ePoly_card_roots, ePoly_natDegree])
    (k := n - k) (by rw [ePoly_natDegree]; omega)
  rw [ePoly_natDegree, show n - (n - k) = k from by omega,
    (ePoly_monic t n).leadingCoeff, one_mul, ePoly_coeff hk] at h
  exact (mul_left_cancel₀
    (pow_ne_zero k (neg_ne_zero.mpr (one_ne_zero (α := ℂ)))) h).symm

/-! ### The surjectivity of the power-sum specialization -/

/-- Evaluation of the power-sum polynomial is `pVal`. -/
theorem aeval_psum {N : ℕ} (x : Fin N → ℂ) (k : ℕ) :
    MvPolynomial.aeval x (MvPolynomial.psum (Fin N) ℂ k) =
      pVal x k := by
  rw [MvPolynomial.psum, map_sum, pVal]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_pow, MvPolynomial.aeval_X]

/-- **Every prospective power-sum sequence is realized** by a
finite family of complex numbers, up to any given degree. -/
theorem exists_pVal_eq (n : ℕ) (t : ℕ → ℂ) :
    ∃ (N : ℕ) (x : Fin N → ℂ),
      ∀ c, 1 ≤ c → c ≤ n → pVal x c = t c := by
  classical
  refine ⟨(ePoly t n).roots.toList.length,
    fun i => (ePoly t n).roots.toList.get i, ?_⟩
  set x : Fin (ePoly t n).roots.toList.length → ℂ :=
    fun i => (ePoly t n).roots.toList.get i with hx
  have hmul : (Finset.univ.val.map x) = (ePoly t n).roots := by
    rw [hx]
    rw [show (Finset.univ.val : Multiset
        (Fin (ePoly t n).roots.toList.length)) =
      ((List.finRange (ePoly t n).roots.toList.length : List _) :
        Multiset _) from rfl]
    rw [Multiset.map_coe, List.map_get_finRange,
      Multiset.coe_toList]
  have hesymm : ∀ k ≤ n,
      Multiset.esymm (Finset.univ.val.map x) k = eSeq t k := by
    intro k hk
    rw [hmul]
    exact ePoly_roots_esymm t hk
  suffices H : ∀ c, (∀ d, d < c → 1 ≤ d → d ≤ n → pVal x d = t d) →
      1 ≤ c → c ≤ n → pVal x c = t c by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih => exact H c (fun d hd => ih d hd)
  intro c ih h1 hn
  have hps := congrArg (MvPolynomial.aeval x)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum
      (Fin (ePoly t n).roots.toList.length) ℂ c (by omega))
  simp only [map_sub, map_mul, map_pow, map_neg, map_one,
    map_natCast, map_sum, aeval_psum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at hps
  rw [hps]
  rw [t_eq_of_eSeq t c (by omega)]
  congr 1
  · rw [hesymm c hn]
  · refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨hmem, hIoo⟩ := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp hmem
    obtain ⟨h0, hlt⟩ := hIoo
    rw [hesymm a.1 (by omega), ih a.2 (by omega) (by omega) (by omega)]

end RS

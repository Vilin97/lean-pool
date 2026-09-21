/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.AlternantPieri

/-!
# Coefficients of strict alternants

An alternant with a repeated exponent vanishes; the coefficient of
a strictly decreasing monomial in a strictly decreasing alternant
is the equality indicator — the two facts driving nonnegativity in
the Pieri chain.
-/

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- An alternant with a repeated exponent vanishes. -/
theorem altDet_eq_zero_of_repeat (e : Fin k → ℕ) {i j : Fin k}
    (hij : i ≠ j) (he : e i = e j) : altDet e = 0 := by
  rw [altDet]
  apply Matrix.det_zero_of_row_eq hij
  funext l
  show (X l : MvPolynomial (Fin k) ℂ) ^ (e i) = X l ^ (e j)
  rw [he]

/-- Strictly decreasing sequences agreeing after a permutation
agree with the identity permutation. -/
private theorem perm_eq_one_of_strict (e w : Fin k → ℕ)
    (he : ∀ i j : Fin k, i < j → w j < w i)
    (hw : ∀ i j : Fin k, i < j → e j < e i)
    (τ : Equiv.Perm (Fin k)) (h : ∀ i, e (τ i) = w i) :
    e = w := by
  have hop : ∀ a b : Fin k, a < b → ¬ (τ b < τ a) := by
    intro a b hab hba
    have h2 : e (τ a) < e (τ b) := hw (τ b) (τ a) hba
    rw [h a, h b] at h2
    exact absurd h2 (not_lt.mpr (le_of_lt (he a b hab)))
  have hmono2 : StrictMono (τ : Fin k → Fin k) := by
    intro a b hab
    rcases lt_trichotomy (τ a) (τ b) with h1 | h1 | h1
    · exact h1
    · exact absurd (τ.injective h1) (ne_of_lt hab)
    · exact absurd h1 (hop a b hab)
  have happ : ∀ i : Fin k, τ i = i := by
    intro i
    have h2 := congrFun (StrictMono.coe_orderIsoOfSurjective
      (τ : Fin k → Fin k) hmono2 τ.surjective) i
    rw [Subsingleton.elim (StrictMono.orderIsoOfSurjective
      (τ : Fin k → Fin k) hmono2 τ.surjective)
      (OrderIso.refl (Fin k))] at h2
    exact h2.symm
  funext i
  have := h i
  rw [happ i] at this
  exact this

/-- **The strict alternant coefficient dichotomy**: the coefficient
of a strictly decreasing monomial in a strictly decreasing
alternant is the equality indicator. -/
theorem alternant_coeff_strict (e w : Fin k → ℕ)
    (he : ∀ i j : Fin k, i < j → e j < e i)
    (hw : ∀ i j : Fin k, i < j → w j < w i) :
    MvPolynomial.coeff (∑ i, Finsupp.single i (w i)) (altDet e) =
      if e = w then 1 else 0 := by
  classical
  by_cases heq : e = w
  · subst heq
    rw [if_pos rfl, altDet]
    exact alternant_coeff e (fun i j hij => by
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (ne_of_gt (he i j h))
      · exact h
      · exact absurd hij.symm (ne_of_gt (he j i h)))
  · rw [if_neg heq, altDet, Matrix.det_apply']
    rw [Finset.sum_congr rfl
      (fun (τ : Equiv.Perm (Fin k)) (_ : τ ∈ Finset.univ) =>
        show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
            ∏ i, (Matrix.of fun i j : Fin k =>
              (X j : MvPolynomial (Fin k) ℂ) ^ (e i)) (τ i) i =
          ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
            monomial (∑ i, Finsupp.single i (e (τ i))) (1 : ℂ)
          from by
        rw [show (∏ i, (Matrix.of fun i j : Fin k =>
            (X j : MvPolynomial (Fin k) ℂ) ^ (e i)) (τ i) i) =
          ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i))
          from rfl]
        rw [prod_pow_eq_monomial])]
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) =
        MvPolynomial.C ((Equiv.Perm.sign τ : ℤ) : ℂ) from by simp,
      MvPolynomial.coeff_C_mul, coeff_monomial]
    rw [if_neg (fun hc => ?_), mul_zero]
    have hpt : ∀ i : Fin k, e (τ i) = w i := by
      intro i
      have h1 := congrArg (fun f : Fin k →₀ ℕ => f i) hc
      rw [sum_single_apply, sum_single_apply] at h1
      exact h1
    exact heq (perm_eq_one_of_strict e w hw he τ hpt)

end RS

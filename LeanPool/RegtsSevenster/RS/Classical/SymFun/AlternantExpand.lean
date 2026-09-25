/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.CoeffExtract

/-!
# Coefficients against the staircase alternant

Multiplying by the zero-shape alternant `det (powMat 0) = a_δ`
shifts coefficient extraction by the permuted staircase: the
coefficient of `w₀` in `P · a_δ` is the signed sum over
permutations of the guarded shifted coefficients of `P`.
-/

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- The permuted staircase exponent. -/
noncomputable def stairShift (τ : Equiv.Perm (Fin k)) :
    Fin k →₀ ℕ :=
  ∑ i, Finsupp.single i ((k - 1) - ((τ i : Fin k) : ℕ))

/-- The staircase shift at a row, under a permutation. -/
theorem stairShift_apply (τ : Equiv.Perm (Fin k)) (j : Fin k) :
    stairShift τ j = (k - 1) - ((τ j : Fin k) : ℕ) :=
  sum_single_apply (fun i => (k - 1) - ((τ i : Fin k) : ℕ)) j

/-- **Coefficient extraction against the staircase alternant.** -/
theorem coeff_mul_alternant (P : MvPolynomial (Fin k) ℂ)
    (w₀ : Fin k →₀ ℕ) :
    (P * (powMat (fun _ : Fin k => 0)).det).coeff w₀ =
      ∑ τ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          (if stairShift τ ≤ w₀
            then P.coeff (w₀ - stairShift τ)
            else 0) := by
  classical
  rw [Matrix.det_apply']
  rw [Finset.sum_congr rfl
    (fun (τ : Equiv.Perm (Fin k)) (_ : τ ∈ Finset.univ) =>
      show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, powMat (fun _ : Fin k => 0) (τ i) i =
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          monomial (stairShift τ) (1 : ℂ) from by
      rw [show (∏ i, powMat (fun _ : Fin k => 0) (τ i) i) =
        ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^
          ((k - 1) - ((τ i : Fin k) : ℕ)) from
        Finset.prod_congr rfl fun i _ => by
          change (X i : MvPolynomial (Fin k) ℂ) ^
              (0 + ((k - 1) - ((τ i : Fin k) : ℕ))) = _
          rw [Nat.zero_add]]
      rw [prod_pow_eq_monomial, stairShift])]
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl
    (fun (τ : Equiv.Perm (Fin k)) (_ : τ ∈ Finset.univ) =>
      show P * (((Equiv.Perm.sign τ : ℤ) :
          MvPolynomial (Fin k) ℂ) *
          monomial (stairShift τ) (1 : ℂ)) =
        MvPolynomial.C ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          (P * monomial (stairShift τ) (1 : ℂ)) from by
      rw [show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) =
          MvPolynomial.C ((Equiv.Perm.sign τ : ℤ) : ℂ) from by simp]
      ring)]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_mul_monomial']
  by_cases hle : stairShift τ ≤ w₀
  · rw [ite_eq_left hle, ite_eq_left hle, mul_one]
  · rw [ite_eq_right hle, ite_eq_right hle]

end RS

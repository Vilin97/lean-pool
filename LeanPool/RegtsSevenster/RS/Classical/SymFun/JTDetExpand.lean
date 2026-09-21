/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.AlternantExpand

/-!
# Leibniz expansion of the Jacobi–Trudi determinant

The determinant of `jtMat v` in row-normal form: a signed sum over
permutations of complete homogeneous products, with terms
containing a negative degree vanishing.
-/

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- The Leibniz expansion of the Jacobi–Trudi determinant in
row-normal form. -/
theorem det_jtMat_expand (v : Fin k → ℕ) :
    (jtMat v).det =
      ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, hSubZ (Finset.univ : Finset (Fin k))
            ((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1

/-- Guarded form: a Leibniz term with all degrees nonnegative is a
complete homogeneous product; otherwise it vanishes. -/
theorem jt_term_guard (v : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    (∏ i, hSubZ (Finset.univ : Finset (Fin k))
        ((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ))) =
      if ∀ i : Fin k, 0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
        then ∏ i, hSub (Finset.univ : Finset (Fin k))
          (((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)).toNat)
        else 0 := by
  classical
  by_cases hp : ∀ i : Fin k,
      0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
  · rw [if_pos hp]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show ((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)) =
      ((((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)).toNat : ℕ) :
        ℤ) from (Int.toNat_of_nonneg (hp i)).symm]
    rw [hSubZ_natCast, Int.toNat_natCast]
  · rw [if_neg hp]
    rw [not_forall] at hp
    obtain ⟨i0, hi0⟩ := hp
    exact Finset.prod_eq_zero (Finset.mem_univ i0)
      (hSubZ_neg _ _ (not_le.mp hi0))

/-- **Coefficient of the Jacobi–Trudi determinant**: signed
guarded sum of coefficients of complete homogeneous products. -/
theorem coeff_det_jtMat (v : Fin k → ℕ) (w : Fin k →₀ ℕ) :
    ((jtMat v).det).coeff w =
      ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if ∀ i : Fin k,
              0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
            then (∏ i, hSub (Finset.univ : Finset (Fin k))
              (((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)).toNat)).coeff w
            else 0) := by
  classical
  rw [det_jtMat_expand]
  rw [Finset.sum_congr rfl
    (fun (σ : Equiv.Perm (Fin k)) (_ : σ ∈ Finset.univ) => by
      rw [jt_term_guard v σ])]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin k) ℂ) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) from by simp,
    MvPolynomial.coeff_C_mul]
  by_cases hp : ∀ i : Fin k,
      0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, AddMonoidAlgebra.coeff_zero]
    rfl

end RS

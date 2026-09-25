/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.JTDetExpand

/-!
# The signed double-sum identity

Combining the bialternant, the diagonal coefficient, the staircase
expansion, and the Jacobi–Trudi Leibniz expansion: the signed
double sum of guarded coefficients of complete homogeneous
products equals `1`.  This is the polynomial form of the
orthonormality `⟨χ_μ, χ_μ⟩ = 1`.
-/

@[expose] public section

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- The diagonal staircase exponent of a shape. -/
noncomputable def diagExp (v : Fin k → ℕ) : Fin k →₀ ℕ :=
  ∑ i, Finsupp.single i (v i + ((k - 1) - (i : ℕ)))

/-- **The signed double-sum identity.** -/
theorem t_identity (v : Fin k → ℕ)
    (hinj : Function.Injective
      (fun i : Fin k => v i + ((k - 1) - (i : ℕ)))) :
    (∑ τ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if stairShift τ ≤ diagExp v
          then ∑ σ : Equiv.Perm (Fin k),
            ((Equiv.Perm.sign σ : ℤ) : ℂ) *
              (if ∀ i : Fin k,
                  0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
                then (∏ i, hSub (Finset.univ : Finset (Fin k))
                    (((v i : ℤ) + ((σ i : Fin k) : ℕ) -
                      (i : ℕ)).toNat)).coeff (diagExp v - stairShift τ)
                else 0)
          else 0)) = 1 := by
  classical
  have h1 : ((powMat v).det).coeff (diagExp v) = 1 :=
    alternant_coeff (fun i : Fin k => v i + ((k - 1) - (i : ℕ)))
      hinj
  have h2 : ((jtMat v).det * (powMat (fun _ : Fin k => 0)).det).coeff (diagExp v) = 1 := by
    rw [← bialternant]
    exact h1
  rw [coeff_mul_alternant] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hle : stairShift τ ≤ diagExp v
  · rw [ite_eq_left hle, ite_eq_left hle, coeff_det_jtMat]
  · rw [ite_eq_right hle, ite_eq_right hle]

end RS

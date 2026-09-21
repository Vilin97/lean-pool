/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.CoeffExtract

/-!
# Pieri rule for plain alternants

The power-sum `p₁ = ∑ l, X l` times the plain alternant `a_e`
equals the sum of alternants with one exponent bumped:

    `p₁ · a_e = ∑ i, a_{e + δ_i}`.

The proof is a signed-monomial reindexing: expand both sides
via `det_apply'`, use the per-term product identity for
`Function.update`, swap/reindex sums via `Equiv.sum_comp`, and
match termwise.
-/

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- The plain power alternant of an exponent vector. -/
noncomputable def altDet {k : ℕ} (e : Fin k → ℕ) :
    MvPolynomial (Fin k) ℂ :=
  (Matrix.of fun i j : Fin k =>
    (X j : MvPolynomial (Fin k) ℂ) ^ (e i)).det

/-- Per-term product identity: bumping exponent `m` in the product
over a permutation pulls out `X (τ.symm m)`. -/
private theorem prod_update_eq (τ : Equiv.Perm (Fin k))
    (e : Fin k → ℕ) (m : Fin k) :
    ∏ i : Fin k, (X i : MvPolynomial (Fin k) ℂ) ^
        (Function.update e m (e m + 1) (τ i)) =
      X (τ.symm m) *
        ∏ i : Fin k, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i)) := by
  -- Each factor: X i ^ (update e m (e m+1) (τ i))
  --   = (if i = τ.symm m then X i else 1) * X i ^ (e (τ i))
  have hfact : ∀ i : Fin k,
      (X i : MvPolynomial (Fin k) ℂ) ^
        (Function.update e m (e m + 1) (τ i)) =
      (if i = τ.symm m then (X i : MvPolynomial (Fin k) ℂ) else 1) *
        (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i)) := by
    intro i
    by_cases h : i = τ.symm m
    · subst h
      rw [show (τ : Fin k → Fin k) (τ.symm m) = m
        from Equiv.apply_symm_apply τ m]
      rw [Function.update_self, if_pos rfl, pow_succ,
          mul_comm ((X (τ.symm m) : MvPolynomial (Fin k) ℂ) ^ _)]
    · have hne : (τ : Fin k → Fin k) i ≠ m := fun h' =>
        h (show i = τ.symm m from by
          rw [← h', Equiv.symm_apply_apply])
      rw [Function.update_of_ne hne _ _, if_neg h, one_mul]
  rw [Finset.prod_congr rfl (fun i _ => hfact i)]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' Finset.univ (τ.symm m)
    (fun i => (X i : MvPolynomial (Fin k) ℂ))]
  rw [if_pos (Finset.mem_univ _)]

open scoped Classical in
/-- **The Pieri rule for alternants**: multiplying by the first
power sum bumps one exponent, summed over which. -/
theorem p1_mul_altDet {k : ℕ} (e : Fin k → ℕ) :
    (∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) * altDet e =
      ∑ i : Fin k, altDet (Function.update e i (e i + 1)) := by
  -- Abbreviations for readability:
  --   P τ  := ∏ i, X i ^ (e (τ i))
  --   ε τ  := ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ)
  -- We show both sides equal ∑ τ, ∑ l, ε τ * (X l * P τ).
  -- === LHS transformation ===
  -- Step L1: Expand altDet e via det_apply', reduce Matrix.of
  rw [show altDet e =
      ∑ τ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i))
    from by
      rw [show altDet e = (Matrix.of fun i j : Fin k =>
          (X j : MvPolynomial (Fin k) ℂ) ^ (e i)).det from rfl]
      rw [Matrix.det_apply']
      exact Finset.sum_congr rfl fun τ _ => rfl]
  -- Step L2: Distribute (∑ l, X l) * ∑ τ via mul_sum
  rw [Finset.mul_sum]
  -- Step L3: For each τ, distribute to get ∑ l
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) =>
    show (∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) *
        (((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i))) =
      ∑ l : Fin k,
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ((X l : MvPolynomial (Fin k) ℂ) *
            ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i)))
    from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _]
  -- === RHS transformation ===
  -- Step R1: Expand each altDet (update ...) via det_apply'
  rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) =>
    show altDet (Function.update e m (e m + 1)) =
      ∑ τ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^
            (Function.update e m (e m + 1) (τ i))
    from by
      rw [show altDet (Function.update e m (e m + 1)) =
          (Matrix.of fun i j : Fin k =>
            (X j : MvPolynomial (Fin k) ℂ) ^
              (Function.update e m (e m + 1) i)).det from rfl]
      rw [Matrix.det_apply']
      exact Finset.sum_congr rfl fun τ _ => rfl]
  -- Step R2: Apply prod_update_eq
  rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) =>
    show (∑ τ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^
            (Function.update e m (e m + 1) (τ i))) =
      ∑ τ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          (X (τ.symm m) *
            ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i)))
    from Finset.sum_congr rfl fun τ _ => by
      rw [prod_update_eq]]
  -- Step R3: Swap sums on RHS only: ∑ m, ∑ τ → ∑ τ, ∑ m
  conv_rhs => rw [Finset.sum_comm]
  -- Step R4: Reindex inner sum via τ.symm (reverse direction)
  exact Finset.sum_congr rfl fun (τ : Equiv.Perm (Fin k)) _ =>
    (Equiv.sum_comp τ.symm _).symm

end RS

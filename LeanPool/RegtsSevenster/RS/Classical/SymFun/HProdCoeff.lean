/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.CoeffExtract

/-!
# Coefficient of a product of complete homogeneous polynomials

The coefficient of a monomial `w` in the product
`∏ i, hSub univ (c i)` counts the number of tuples of
symmetric-function indices whose combined weight equals `w`.
-/

@[expose] public section

namespace RS

open Finset MvPolynomial

variable {k : ℕ}

/-- The product of a multiset mapped through `X` equals the monomial
whose exponent is the multiset's `toFinsupp`. -/
private theorem map_X_prod_eq_monomial (s : Multiset (Fin k)) :
    (s.map X).prod = monomial (Multiset.toFinsupp s) (1 : ℂ) := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero,
        Multiset.toFinsupp_zero, monomial_zero', MvPolynomial.C_1]
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih]
    rw [show (X a : MvPolynomial (Fin k) ℂ) =
      monomial (Finsupp.single a 1) 1 from rfl]
    rw [MvPolynomial.monomial_mul_monomial, one_mul]
    congr 1
    rw [← Multiset.singleton_add]
    rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

open scoped Classical in
/-- A coefficient of a product of complete homogeneous polynomials
counts the tuples of multisets with the prescribed column sums. -/
theorem coeff_hSub_prod {k : ℕ} (c : Fin k → ℕ) (w : Fin k →₀ ℕ) :
    (∏ i, hSub (Finset.univ : Finset (Fin k)) (c i)).coeff w =
      (Fintype.card {W : ∀ i : Fin k, Sym (Fin k) (c i) //
        ∀ j : Fin k, (∑ i, (W i).1.count j) = w j} : ℂ) := by
  -- Step 1: Remove the trivially-true filter in hSub univ
  -- and rewrite each summand as a monomial
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    show hSub Finset.univ (c i) =
      ∑ s : Sym (Fin k) (c i),
        monomial (Multiset.toFinsupp s.1) (1 : ℂ) from by
    rw [hSub, Finset.filter_true_of_mem
      (fun _ _ => fun j _ => Finset.mem_univ j)]
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) =>
      map_X_prod_eq_monomial s.1)])]
  -- Step 2: Expand the product of sums via Fintype.prod_sum
  rw [Fintype.prod_sum]
  -- Step 3: Each term is a product of monomials = a single monomial
  rw [Finset.sum_congr rfl
    (fun (W : ∀ i : Fin k, Sym (Fin k) (c i)) (_ : W ∈ Finset.univ) =>
      show (∏ i, monomial (Multiset.toFinsupp (W i).1) (1 : ℂ)) =
        monomial (∑ i, Multiset.toFinsupp (W i).1) (1 : ℂ) from by
      rw [← monomial_sum_prod, Finset.prod_const_one])]
  -- Step 4: Extract coefficient, rewrite each term
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  -- Step 5: Rewrite the condition from Finsupp equality to pointwise
  have cond_iff : ∀ W : (∀ i : Fin k, Sym (Fin k) (c i)),
      ((∑ i, Multiset.toFinsupp (W i).1) = w) ↔
      (∀ j : Fin k, (∑ i, (W i).1.count j) = w j) := by
    intro W
    rw [DFunLike.ext_iff]
    constructor
    · intro h j
      specialize h j
      rw [Finsupp.finsetSum_apply] at h
      simpa [Multiset.toFinsupp_apply] using h
    · intro h j
      rw [Finsupp.finsetSum_apply]
      simp only [Multiset.toFinsupp_apply]
      exact h j
  rw [Finset.sum_congr rfl
    (fun (W : ∀ i : Fin k, Sym (Fin k) (c i)) (_ : W ∈ Finset.univ) =>
      show (if (∑ i, Multiset.toFinsupp (W i).1) = w then (1 : ℂ) else 0) =
        (if (∀ j : Fin k, (∑ i, (W i).1.count j) = w j) then (1 : ℂ)
          else 0) from
      if_congr (cond_iff W) rfl rfl)]
  -- Step 6: Sum of indicators = cardinality
  rw [Finset.sum_boole]
  congr 1
  rw [Fintype.card_subtype]

end RS

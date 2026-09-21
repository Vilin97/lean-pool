/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.HProdCoeff

/-!
# Coefficient of a power of p₁

The coefficient of a monomial `w` in `(∑ l, X l) ^ |T|` counts the
number of functions `T → Fin k` whose fibre sizes match `w`.
-/

namespace RS

open Finset MvPolynomial

open scoped Classical in
/-- A coefficient of a power of the first power sum counts the
functions with the prescribed fibre sizes. -/
theorem coeff_p1_pow {k : ℕ} (T : Type) [Fintype T] (w : Fin k →₀ ℕ) :
    ((∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ Fintype.card T).coeff w =
    ((Finset.univ.filter (fun t : T → Fin k =>
      ∀ a : Fin k,
        (Finset.univ.filter (fun i : T => t i = a)).card = w a)).card : ℂ) := by
  -- Step 1: Rewrite the power as a product over T, then expand
  -- (∑ l, X l) ^ card T = ∏ _ : T, (∑ l, X l) = ∑ t : T → Fin k, ∏ i, X (t i)
  rw [show Fintype.card T = Finset.card (Finset.univ : Finset T) from
    Finset.card_univ.symm]
  rw [← Finset.prod_const]
  rw [Fintype.prod_sum
    (fun (_ : T) (j : Fin k) => (X j : MvPolynomial (Fin k) ℂ))]
  -- Step 2: Each ∏ i, X (t i) is a monomial
  rw [Finset.sum_congr rfl
    (fun (t : T → Fin k) (_ : t ∈ Finset.univ) =>
      show (∏ i : T, (X (t i) : MvPolynomial (Fin k) ℂ)) =
        monomial (∑ i : T, Finsupp.single (t i) 1) (1 : ℂ) from by
      rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        show (X (t i) : MvPolynomial (Fin k) ℂ) =
          monomial (Finsupp.single (t i) 1) (1 : ℂ) from rfl)]
      rw [← monomial_sum_prod]
      rw [Finset.prod_const_one])]
  -- Step 3: Extract coefficients
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  -- Step 4: Rewrite condition from Finsupp equality to pointwise filter-card
  have cond_iff : ∀ t : T → Fin k,
      ((∑ i : T, Finsupp.single (t i) 1) = w) ↔
      (∀ a : Fin k,
        (Finset.univ.filter (fun i : T => t i = a)).card = w a) := by
    intro t
    rw [DFunLike.ext_iff]
    refine forall_congr' fun a => ?_
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    constructor
    · intro h
      rw [← h]
      simp [Finset.sum_boole]
    · intro h
      rw [← h]
      simp [Finset.sum_boole]
  rw [Finset.sum_congr rfl
    (fun (t : T → Fin k) (_ : t ∈ Finset.univ) =>
      show (if (∑ i : T, Finsupp.single (t i) 1) = w then (1 : ℂ) else 0) =
        (if (∀ a : Fin k,
            (Finset.univ.filter (fun i : T => t i = a)).card = w a)
          then (1 : ℂ) else 0) from
      if_congr (cond_iff t) rfl rfl)]
  -- Step 5: Sum of indicators = cardinality of filter
  rw [Finset.sum_boole]

end RS

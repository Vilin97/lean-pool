/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Subset-indexed elementary and complete homogeneous polynomials

For a subset `A` of the variables of `MvPolynomial (Fin k) ℂ`, the
elementary symmetric polynomial `eSub A r` in the variables of `A`
and the complete homogeneous polynomial `hSub A m` supported in
`A`, with the add-one-variable recurrence for `eSub` — the engine
of the e–h convolution and the bialternant Jacobi–Trudi identity.
The `hSub` recurrence is proven in `HInsert.lean`.
-/

namespace RS

open Finset MvPolynomial

variable {k : ℕ}

/-- The elementary symmetric polynomial in a subset of the
variables. -/
noncomputable def eSub (A : Finset (Fin k)) (r : ℕ) :
    MvPolynomial (Fin k) ℂ :=
  (A.val.map X).esymm r

open scoped Classical in
/-- The complete homogeneous polynomial supported in a subset of
the variables. -/
noncomputable def hSub (A : Finset (Fin k)) (m : ℕ) :
    MvPolynomial (Fin k) ℂ :=
  ∑ w ∈ Finset.univ.filter
    (fun w : Sym (Fin k) m => ∀ i ∈ w.1, i ∈ A),
    (w.1.map X).prod

/-- The empty elementary symmetric polynomial is `1`. -/
theorem eSub_zero (A : Finset (Fin k)) : eSub A 0 = 1 := by
  rw [eSub, Multiset.esymm, Multiset.powersetCard_zero_left,
    Multiset.map_singleton, Multiset.prod_zero,
    Multiset.sum_singleton]

/-- And so is the degree-zero complete homogeneous one. -/
theorem hSub_zero (A : Finset (Fin k)) : hSub A 0 = 1 := by
  classical
  rw [hSub, Finset.filter_true_of_mem (fun w _ => fun i hi =>
    absurd ((Multiset.card_eq_zero.mp w.2) ▸ hi)
      (Multiset.notMem_zero i))]
  let : Unique (Sym (Fin k) 0) :=
    ⟨⟨Sym.nil⟩, fun s => Sym.eq_nil_of_card_zero s⟩
  rw [Fintype.sum_unique]
  rw [show ((default : Sym (Fin k) 0)).1 = 0 from rfl]
  rw [Multiset.map_zero, Multiset.prod_zero]

/-- Vanishing of `eSub` beyond the subset size. -/
theorem eSub_eq_zero_of_lt (A : Finset (Fin k)) (r : ℕ)
    (hr : A.card < r) : eSub A r = 0 := by
  rw [eSub, Multiset.esymm]
  rw [show Multiset.powersetCard r (A.val.map X) = 0 from
    Multiset.powersetCard_eq_empty _ (by
      rw [Multiset.card_map]
      exact hr)]
  rw [Multiset.map_zero, Multiset.sum_zero]

/-- **The add-one-variable recurrence for `eSub`.** -/
theorem eSub_insert {A : Finset (Fin k)} {j : Fin k} (hj : j ∉ A)
    (r : ℕ) :
    eSub (insert j A) (r + 1) =
      eSub A (r + 1) + X j * eSub A r := by
  rw [eSub, eSub, eSub]
  rw [show (insert j A).val = j ::ₘ A.val from
    Finset.insert_val_of_notMem hj]
  rw [Multiset.map_cons]
  rw [Multiset.esymm, Multiset.esymm, Multiset.esymm]
  rw [Multiset.powersetCard_cons,
    Multiset.map_add, Multiset.sum_add]
  congr 1
  rw [Multiset.map_map]
  rw [show ((Multiset.powersetCard r (A.val.map X)).map
      (Multiset.prod ∘ Multiset.cons (X j))) =
    (Multiset.powersetCard r (A.val.map X)).map
      (fun t => X j * t.prod) from
    Multiset.map_congr rfl (fun t _ => by
      change (X j ::ₘ t).prod = X j * t.prod
      rw [Multiset.prod_cons])]
  exact Multiset.sum_map_mul_left

end RS

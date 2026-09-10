/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
import Mathlib.Tactic.Ring
import LeanPool.Koethe.Pencil
import LeanPool.Koethe.Mortality.Minors

/-!
# The one-row parameter-degree bound

Multilinearity in the rows expands a minor of a product into row products
of the first factor and minors of the remaining factors.  Repeated rows
make the latter minors zero.  Thus a single parameter row contributes at
most one to the degree per factor, not the size of the minor.
-/

noncomputable section

open scoped BigOperators
open Matrix Polynomial

namespace KoetheCounterexample.Mortality

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R] {d r : ℕ}

theorem lift_entry_natDegree_le (P : Pencil k d) (a : Fin 3 → R)
    (i j : Fin (d + 1)) : (P.lift a i j).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp only [Polynomial.natDegree_C, Nat.zero_le]
  · exact (Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le

theorem lift_entry_natDegree_off_root (P : Pencil k d) (a : Fin 3 → R)
    (i j : Fin (d + 1)) (hi : i ≠ 0) : (P.lift a i j).natDegree = 0 := by
  simp only [Pencil.lift, P.linear_off_root _ _ _ hi, map_zero, zero_mul,
    Finset.sum_const_zero, mul_zero, add_zero, Polynomial.natDegree_C]

/-- A product using distinct rows of one factor has parameter degree at most one. -/
theorem lift_row_prod_natDegree_le (P : Pencil k d) (a : Fin 3 → R)
    (I : Fin r → Fin (d + 1)) (f : Fin r → Fin (d + 1))
    (hI : Function.Injective I) :
    (∏ i : Fin r, P.lift a (I i) (f i)).natDegree ≤ 1 := by
  classical
  apply (Polynomial.natDegree_prod_le _ _).trans
  by_cases hroot : ∃ i, I i = 0
  · obtain ⟨i, hi⟩ := hroot
    rw [Finset.sum_eq_single i]
    · exact lift_entry_natDegree_le P a _ _
    · intro j _ hji
      exact lift_entry_natDegree_off_root P a _ _
        (fun hj => hji (hI (hj.trans hi.symm)))
    · simp
  · have hsum : (∑ i : Fin r, (P.lift a (I i) (f i)).natDegree) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact lift_entry_natDegree_off_root P a _ _ (fun hi => hroot ⟨i, hi⟩)
    omega

/-- Every minor of a forward word of lifted letters has degree at most the
word length.  The coefficient ring is an arbitrary commutative `k`-algebra. -/
theorem det_liftWord_natDegree_le (P : Pencil k d) (w : List (Fin 3 → R))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I) :
    ((((w.map P.lift).prod).submatrix I J).det).natDegree ≤ w.length := by
  classical
  induction w generalizing I J with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    have hone : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) R[X]) =
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) R).map Polynomial.C := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hone, Matrix.submatrix_map, det_map]
    simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [submatrix_mul_outer, det_mul_expand_rows]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro f _
    simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix,
      Function.id_comp, Function.comp_id, id_eq]
    by_cases hf : Function.Injective f
    · have h := Polynomial.natDegree_mul_le_of_le
        (lift_row_prod_natDegree_le P a I f hI) (ih f J hf)
      simpa only [Nat.add_comm] using h
    · rw [det_submatrix_zero_of_not_injective _ f J hf]
      simp

end KoetheCounterexample.Mortality

end

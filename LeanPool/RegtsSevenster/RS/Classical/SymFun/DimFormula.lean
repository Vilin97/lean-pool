/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.DeltaSeq
import LeanPool.RegtsSevenster.RS.Classical.SymFun.DescVandermonde

/-!
# The exact dimension determinant

Row-normalizing the Jacobi–Trudi determinant at the delta sequence
by the staircase factorials turns its entries into descending
Pochhammer evaluations; reversing both indices removes all signs
and evaluates the determinant as a manifestly positive Vandermonde
product of staircase differences.
-/

namespace RS

open Finset

/-- The staircase exponents of a diagram over its own row count. -/
noncomputable def eStair (μ : YoungDiagram)
    (i : Fin μ.rowLens.length) : ℕ :=
  μ.rowLens.get i + ((μ.rowLens.length - 1) - (i : ℕ))

/-- **The row-normalized dimension determinant**: the Jacobi–Trudi
determinant at the delta sequence times the staircase factorials
is the Vandermonde product of the staircase differences. -/
theorem diagramSchur_delta_mul (μ : YoungDiagram) :
    diagramSchur μ deltaSeq *
      ∏ i : Fin μ.rowLens.length, ((eStair μ i).factorial : ℂ) =
    ∏ i : Fin μ.rowLens.length, ∏ j ∈ Finset.Ioi i,
      (((eStair μ (Fin.revPerm j)) : ℂ) -
        ((eStair μ (Fin.revPerm i)) : ℂ)) := by
  classical
  set k := μ.rowLens.length with hk
  -- entrywise normalization
  have hentry : ∀ i j : Fin k,
      ((eStair μ i).factorial : ℂ) *
        newtonHZ deltaSeq
          ((μ.rowLens.get i : ℤ) + (j : ℕ) - (i : ℕ)) =
      (descPochhammer ℂ ((k - 1) - (j : ℕ))).eval
        ((eStair μ i : ℕ) : ℂ) := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hE : eStair μ i =
        μ.rowLens.get i + ((k - 1) - (i : ℕ)) := rfl
    rw [descPochhammer_eval_eq_descFactorial]
    by_cases hpos :
        0 ≤ (μ.rowLens.get i : ℤ) + (j : ℕ) - (i : ℕ)
    · have harg : ((μ.rowLens.get i : ℤ) + (j : ℕ) -
          (i : ℕ)).toNat =
          eStair μ i - ((k - 1) - (j : ℕ)) := by
        rw [hE]
        omega
      have hle : (k - 1) - (j : ℕ) ≤ eStair μ i := by
        rw [hE]
        omega
      rw [newtonHZ, if_pos hpos, harg, newtonH_deltaSeq]
      have hfac := Nat.factorial_mul_descFactorial hle
      have hcast : ((eStair μ i - ((k - 1) - (j : ℕ))).factorial :
          ℂ) * ((eStair μ i).descFactorial
            ((k - 1) - (j : ℕ)) : ℂ) =
          ((eStair μ i).factorial : ℂ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℂ)) hfac
      have hne : (((eStair μ i - ((k - 1) - (j : ℕ))).factorial :
          ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      rw [← div_eq_mul_inv, div_eq_iff hne]
      linear_combination -hcast
    · rw [newtonHZ, if_neg hpos, mul_zero]
      have hlt : eStair μ i < (k - 1) - (j : ℕ) := by
        rw [hE]
        omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
      rw [Nat.cast_zero]
  -- normalize the determinant
  have h1 : (∏ i : Fin k, ((eStair μ i).factorial : ℂ)) *
      diagramSchur μ deltaSeq =
      (Matrix.of fun i j : Fin k =>
        (descPochhammer ℂ ((k - 1) - (j : ℕ))).eval
          ((eStair μ i : ℕ) : ℂ)).det := by
    rw [diagramSchur, schurDet]
    rw [← Matrix.det_mul_column
      (fun i => ((eStair μ i).factorial : ℂ))]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply]
    exact hentry i j
  -- reverse both indices
  have h2 : (Matrix.of fun i j : Fin k =>
      (descPochhammer ℂ ((k - 1) - (j : ℕ))).eval
        ((eStair μ i : ℕ) : ℂ)).det =
      (Matrix.of fun i j : Fin k =>
        (descPochhammer ℂ (j : ℕ)).eval
          ((eStair μ (Fin.revPerm i) : ℕ) : ℂ)).det := by
    rw [← Matrix.det_submatrix_equiv_self
      (Fin.revPerm : Equiv.Perm (Fin k))]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply]
    congr 2
    have hj := j.isLt
    have hrev : ((Fin.revPerm j : Fin k) : ℕ) =
        k - ((j : ℕ) + 1) := Fin.val_rev j
    omega
  rw [mul_comm] at h1
  rw [h1, h2, det_descPochhammer_eval]

end RS

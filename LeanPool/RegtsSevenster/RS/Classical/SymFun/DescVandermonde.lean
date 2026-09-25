/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Determinant of the descending-Pochhammer evaluation matrix

The determinant of the matrix whose `(i, j)` entry is
`(descPochhammer ℂ j).eval (y i)` is the Vandermonde product
`∏ i, ∏ j ∈ Ioi i, (y j - y i)`.

This follows from the Mathlib theorem
`det_eval_matrixOfPolynomials_eq_det_vandermonde` applied to
the descending Pochhammer polynomials (which are monic of the
correct degree) combined with `det_vandermonde`.
-/

@[expose] public section

open Polynomial Matrix Finset

namespace RS

/-- The descending-Pochhammer evaluation matrix has the Vandermonde
determinant, the Pochhammers being monic of the right degrees. -/
theorem det_descPochhammer_eval {k : ℕ} (y : Fin k → ℂ) :
    (Matrix.of fun i j : Fin k =>
      (descPochhammer ℂ (j : ℕ)).eval (y i)).det =
    ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (y j - y i) := by
  rw [← det_vandermonde y]
  exact (det_eval_matrixOfPolynomials_eq_det_vandermonde y
    (fun j => descPochhammer ℂ (j : ℕ))
    (fun i => descPochhammer_natDegree (R := ℂ) (i : ℕ))
    (fun i => monic_descPochhammer (R := ℂ) (i : ℕ))).symm

end RS

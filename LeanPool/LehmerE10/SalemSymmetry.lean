/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Defs
import LeanPool.LehmerE10.Main

/-!
# unimodularity and the reciprocal (Salem-pair) symmetry.
Two small facts, downstream of `main_theorem`, recording the structure of the Coxeter
element as an integer lattice automorphism:
* `coxeterE10_det_one` : the Coxeter element lies in `SL(10, ℤ)` — `det = 1`.  A product
  of the ten simple reflections (each `det = -1`) is unimodular, and its determinant is
  pinned by the charpoly identity to the constant coefficient of Lehmer's polynomial.
* `lehmerPolynomial_selfReciprocal` : Lehmer's polynomial is palindromic, `coeff i =
  coeff (10 - i)`.  This is the reciprocal / Salem-pair symmetry: the off-circle roots
  come in a pair `{μ, 1/μ}`, so the spectral radius `μ` (Lehmer's number) has its inverse
  as a conjugate.  Equivalently, the Coxeter element and its inverse share a charpoly.
-/

open Polynomial Matrix

namespace LehmerE10

/-- The E₁₀ Coxeter element is **unimodular**: `det = 1`, i.e. it lies in `SL(10, ℤ)`.
Proof: `det = (-1)^(card) · charpoly.coeff 0`; the charpoly is Lehmer's polynomial, whose
constant coefficient is `1`, and `card (Fin 10) = 10` is even. -/
theorem coxeterE10_det_one : coxeterE10.det = 1 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, coxeter_charpoly_lehmer]
  have hcard : Fintype.card (Fin 10) = 10 := Fintype.card_fin 10
  have hc0 : lehmerPolynomial.coeff 0 = 1 := by
    simp [lehmerPolynomial, coeff_X_pow]
  rw [hcard, hc0]
  norm_num

/-- Lehmer's polynomial is **self-reciprocal** (palindromic): `coeff i = coeff (10 - i)`
for `i ≤ 10`.  This is the Salem-pair symmetry `{μ, 1/μ}` off the unit circle. -/
theorem lehmerPolynomial_selfReciprocal (i : ℕ) (hi : i ≤ 10) :
    lehmerPolynomial.coeff i = lehmerPolynomial.coeff (10 - i) := by
  interval_cases i <;> simp [lehmerPolynomial, coeff_X_pow, coeff_X, coeff_one]

end LehmerE10

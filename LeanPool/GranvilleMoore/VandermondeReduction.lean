/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.LinearAlgebra.Vandermonde

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The Vandermonde reduction

A square matrix whose entries factor as a column scalar times a power of a column value,
`M i j = c j * v j ^ (i : ℕ)`, is a column-rescaled transposed Vandermonde matrix. Its
determinant is therefore `(∏ j, c j)` times the Vandermonde product `∏_{i < j} (v j - v i)`,
and — over a domain, with every `c j` a unit — it is nonzero exactly when the `v j` are
pairwise distinct.

This is the linear-algebra half of the four ladder lemmas: each of them reduces the last rung
`det L_{d-1}` modulo `p` to a Vandermonde determinant in the Fermat quotients, and the step
that turns "the entries look like `c j * v j ^ i`" into "the determinant is the Vandermonde
product" needs nothing about Fermat quotients whatsoever. It is stated here once, for a
general commutative ring.

The `d = p` case of the paper is the reason the file is more general than the main theorem
needs: there the bottom row's exponent is not `d - 1` but comes from the *exceptional* Fermat
congruence, which contributes `v ^ (p-1) - v` rather than `v ^ (p-1)`. So the bottom row is a
`v ^ (iLast)`-row minus a multiple of an *earlier* row of the same matrix, and the relevant
fact is that this row operation does not change the determinant.

## Main results

* `GranvilleMoore.det_of_eq_mul_pow_exponents`: for an arbitrary exponent function `f`, the
  column scalars come out whole: `det M = (∏ j, c j) * det (fun i j => v j ^ f i)`.
* `GranvilleMoore.det_of_eq_mul_pow`: the scaled Vandermonde determinant, `f = id`. The main
  result of the file:
  `det M = (∏ j, c j) * ∏ i, ∏ j ∈ Ioi i, (v j - v i)`.
* `GranvilleMoore.det_of_eq_mul_pow_ne_zero_iff` and
  `GranvilleMoore.det_of_eq_mul_pow_eq_zero_iff`: over a domain, with all `c j ≠ 0`, the
  determinant is nonzero iff `v` is injective.
* `GranvilleMoore.det_updateRow_sub_smul_self`: subtracting a multiple of another row of the
  same matrix preserves the determinant (the `d = p` row operation).
* `GranvilleMoore.det_of_eq_mul_pow_updateRow`, `..._updateRow_last`, `..._updateRow_sub`: the
  one-row-modified variants, the last of which is the shape the `d = p` case produces.

## Implementation notes

This file is deliberately free of project imports: nothing in it mentions `p`, a Fermat
quotient, the Moore matrix or the ladder. The reduction is a statement about matrices over a
commutative ring, so keeping it separate makes it reusable at every rung, keeps it immune to
churn in the congruence files, and means the ladder lemmas can be wired to it independently of
how the congruences are eventually proved.

Two Mathlib names behave contrary to their reading and are worth flagging: `Matrix.det_mul_row`
is the one that scales **columns** (`(fun i j => v j * A i j).det = (∏ i, v i) * A.det`), and
`Matrix.det_mul_column` is the one that scales **rows**. This file needs the column version, so
it uses `Matrix.det_mul_row`.

Also note the index convention: `Matrix.vandermonde v i j = v i ^ (j : ℕ)` puts the power on
the *column* index, whereas the entry shape arising from the ladder puts it on the *row* index.
So the matrix here is the **transpose** of a Vandermonde matrix; `Matrix.det_transpose` bridges
the two. In fact `(Matrix.vandermonde v)ᵀ` is definitionally `Matrix.of fun i j => v j ^ (i : ℕ)`.
-/

@[expose] public section

open Finset Matrix

namespace GranvilleMoore

variable {R : Type*} [CommRing R] {n : ℕ}

/-- If the entries of a square matrix factor as a column scalar times a power of a column
value, the exponent depending only on the row — `M i j = c j * v j ^ f i` — then the column
scalars factor out of the determinant all at once.

This is the general form: no relation between `f` and the row index is assumed, so the residual
determinant is a generalized Vandermonde determinant rather than a product. Every other result
in this file is a specialization. -/
theorem det_of_eq_mul_pow_exponents (c v : Fin n → R) (f : Fin n → ℕ)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, M i j = c j * v j ^ f i) :
    M.det = (∏ j, c j) * (Matrix.of fun i j => v j ^ f i).det := by
  have hM : M = Matrix.of fun i j => c j * (Matrix.of fun i j => v j ^ f i) i j := by
    ext i j
    simpa using h i j
  rw [hM, Matrix.det_mul_row]

/-- `Matrix.of fun i j => v j ^ (i : ℕ)` is the transpose of Mathlib's Vandermonde matrix.

Mathlib's `Matrix.vandermonde` puts the power on the column index, so this is the bookkeeping
lemma that turns the row-indexed shape used throughout this file into a Vandermonde matrix. -/
private theorem of_pow_row_eq_vandermonde_transpose (v : Fin n → R) :
    (Matrix.of fun (i j : Fin n) => v j ^ (i : ℕ)) = (Matrix.vandermonde v)ᵀ := by
  ext i j
  simp [Matrix.vandermonde_apply]

/-- The determinant of a matrix with entries `c j * v j ^ (i : ℕ)`, before the Vandermonde
product is expanded. Kept separate because the vanishing criterion is cleanest read off
Mathlib's `Matrix.det_vandermonde_ne_zero_iff` rather than off the product. -/
private theorem det_of_eq_mul_pow_eq_mul_det_vandermonde (c v : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    M.det = (∏ j, c j) * (Matrix.vandermonde v).det := by
  rw [det_of_eq_mul_pow_exponents c v (fun i => (i : ℕ)) M h,
    of_pow_row_eq_vandermonde_transpose v, Matrix.det_transpose]

/-- **The scaled Vandermonde determinant.** If the entries of a square matrix over a
commutative ring factor as `M i j = c j * v j ^ (i : ℕ)` — a scalar depending only on the
column, times the column's value raised to the row index — then

`det M = (∏ j, c j) * ∏ i, ∏ j ∈ Ioi i, (v j - v i)`.

The shape is what it is because such an `M` is `(Matrix.vandermonde v)ᵀ` with column `j`
rescaled by `c j`: rescaling a column multiplies the determinant by that scalar, and
transposing does not change it. -/
theorem det_of_eq_mul_pow (c v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    M.det = (∏ j, c j) * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  rw [det_of_eq_mul_pow_eq_mul_det_vandermonde c v M h, Matrix.det_vandermonde]

/-- **The vanishing criterion.** Over an integral domain, a matrix with entries
`c j * v j ^ (i : ℕ)` and no vanishing column scalar has nonzero determinant exactly when the
`v j` are pairwise distinct.

This is the form the main theorem needs: the `p`-adic valuation of the Moore determinant hits
its lower bound iff the reduced last rung is invertible mod `p`, and that is a statement about
the Fermat quotients being distinct. -/
theorem det_of_eq_mul_pow_ne_zero_iff [IsDomain R] (c v : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (hc : ∀ j, c j ≠ 0)
    (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    M.det ≠ 0 ↔ Function.Injective v := by
  rw [det_of_eq_mul_pow_eq_mul_det_vandermonde c v M h, mul_ne_zero_iff,
    Matrix.det_vandermonde_ne_zero_iff,
    and_iff_right (Finset.prod_ne_zero_iff.mpr fun j _ => hc j)]

/-- The contrapositive of `GranvilleMoore.det_of_eq_mul_pow_ne_zero_iff`, in the explicit
"two coincident values" form. -/
theorem det_of_eq_mul_pow_eq_zero_iff [IsDomain R] (c v : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (hc : ∀ j, c j ≠ 0)
    (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    M.det = 0 ↔ ∃ i j, v i = v j ∧ i ≠ j := by
  rw [det_of_eq_mul_pow_eq_mul_det_vandermonde c v M h, mul_eq_zero,
    Matrix.det_vandermonde_eq_zero_iff,
    or_iff_right (Finset.prod_ne_zero_iff.mpr fun j _ => hc j)]

/-- Subtracting a multiple of another row of the *same* matrix from row `i` does not change the
determinant. This is `Matrix.det_updateRow_add_smul_self` phrased with a subtraction and a ring
multiplication, which is how the row operation of the `d = p` case actually presents itself. -/
theorem det_updateRow_sub_smul_self (M : Matrix (Fin n) (Fin n) R) {i i₁ : Fin n}
    (hne : i ≠ i₁) (k : R) :
    (M.updateRow i fun j => M i j - k * M i₁ j).det = M.det := by
  rw [show (fun j => M i j - k * M i₁ j) = M i + (-k) • M i₁ by
    ext j; simp [sub_eq_add_neg]]
  exact Matrix.det_updateRow_add_smul_self M hne (-k)

/-- **The one-row-modified variant.** Replacing row `iLast` of a `c j * v j ^ (i : ℕ)` matrix
by `fun j => c j * v j ^ e` still lets the column scalars out whole; what is left is the
generalized Vandermonde determinant for the exponent list `0, 1, …` with the entry at `iLast`
replaced by `e`.

No further simplification is available in general: for `e` outside the original exponent list
the residual determinant is a Schur polynomial times the Vandermonde product, not the
Vandermonde product itself. The two cases that *do* collapse are
`GranvilleMoore.det_of_eq_mul_pow_updateRow_last` and
`GranvilleMoore.det_of_eq_mul_pow_updateRow_sub`. -/
theorem det_of_eq_mul_pow_updateRow (c v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (iLast : Fin n) (e : ℕ) (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    (M.updateRow iLast fun j => c j * v j ^ e).det
      = (∏ j, c j) * (Matrix.of fun i j => v j ^ (if i = iLast then e else (i : ℕ))).det := by
  refine det_of_eq_mul_pow_exponents c v (fun i => if i = iLast then e else (i : ℕ)) _ ?_
  intro i j
  rw [Matrix.updateRow_apply]
  split <;> simp_all

/-- The special case of `GranvilleMoore.det_of_eq_mul_pow_updateRow` in which the modified
exponent is the one the row already had, `e = n - 1` in the last row: the determinant is the
plain scaled Vandermonde determinant, so the caller can reduce to
`GranvilleMoore.det_of_eq_mul_pow`. -/
theorem det_of_eq_mul_pow_updateRow_last (c v : Fin (n + 1) → R)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    (M.updateRow (Fin.last n) fun j => c j * v j ^ n).det
      = (∏ j, c j) * ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  refine det_of_eq_mul_pow c v _ ?_
  intro i j
  rw [Matrix.updateRow_apply]
  split <;> simp_all

/-- **The `d = p` shape.** If the bottom row of a `c j * v j ^ (i : ℕ)` matrix is replaced by
`fun j => c j * (v j ^ (iLast : ℕ) - k * v j ^ (i₁ : ℕ))` for some *other* row index `i₁`, the
determinant is unchanged, hence still the scaled Vandermonde determinant.

This is exactly what the exceptional Fermat congruence produces: it contributes
`x * q_p(x) ^ (p-1) - x * q_p(x)` in the last row instead of `x * q_p(x) ^ (p-1)`, i.e. the
`v ^ (iLast)` row minus one copy of the `v ^ 1` row, and a row operation of that form is
determinant-preserving. -/
theorem det_of_eq_mul_pow_updateRow_sub (c v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    {iLast i₁ : Fin n} (hne : iLast ≠ i₁) (k : R)
    (h : ∀ i j, M i j = c j * v j ^ (i : ℕ)) :
    (M.updateRow iLast fun j => c j * (v j ^ (iLast : ℕ) - k * v j ^ (i₁ : ℕ))).det
      = (∏ j, c j) * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  have hrow : (fun j => c j * (v j ^ (iLast : ℕ) - k * v j ^ (i₁ : ℕ)))
      = fun j => M iLast j - k * M i₁ j := by
    ext j
    rw [h iLast j, h i₁ j]
    ring
  rw [hrow, det_updateRow_sub_smul_self M hne k, det_of_eq_mul_pow c v M h]

end GranvilleMoore

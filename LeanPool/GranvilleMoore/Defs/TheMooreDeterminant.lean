/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.Defs.TheIteratedFermatQuotients
public import Mathlib.Data.Matrix.Basic

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The Moore matrix and the reduction ladder

The two matrices whose determinants the main theorems compare: the Moore matrix, whose determinant
is the object of study, and the ladder of matrices interpolating between it and a matrix of
iterated Fermat quotients.

## Main definitions

* `GranvilleMoore.mooreMatrix p x`: the Moore matrix of `x = (x 1, …, x d)`, whose
  `(i, j)` entry is `x j ^ p ^ i`. Rows are indexed by the Frobenius level `i` and
  columns by the point `j`, so this is the paper's `(i, j)` entry
  `x_j ^ (p ^ (i - 1))` under the shift from `1`-based to `0`-based indices.
* `GranvilleMoore.ladderMatrix p x i`: the `i`-th matrix `L i` of the reduction ladder,
  the matrix over `ℚ` whose rows are the vectors of iterated Fermat quotients
  `F⁽⁰⁾_0, F⁽¹⁾_0, …, F⁽ⁱ⁾_0, F⁽ⁱ⁾_1, …, F⁽ⁱ⁾_(d - 1 - i)` evaluated at `x`.

## Implementation notes

The row of `ladderMatrix p x i` at index `r` is `F⁽ᵃ⁾_b` with `(a, b) = (min r i, r - i)`:
the superscript grows along the first `i + 1` rows and the subscript grows along the
remaining ones, with truncated subtraction on `ℕ` performing the case split. The two
regimes are `ladderMatrix_row_of_le` and `ladderMatrix_row_of_ge`, which are the lemmas
to use in place of unfolding.

The Moore matrix is defined over any monoid, since its entries are powers and nothing else is
needed; the paper's integer matrix is the case `R = ℤ`, and `mooreMatrix_map` is the passage to its
image over `ℚ`, where the ladder lives. Neither definition needs `p` prime, `d ≥ 1`, or
`i ≤ d - 1`: the standing hypotheses of the paper belong to the results about these matrices, not
to the constructions. For `d ≤ i + 1` the ladder has stabilised, every row then falling in the
first regime.

## References

* A. Granville, *The p-divisibility of the integer Moore determinant and iterated
  Fermat quotients*.
-/

@[expose] public section

namespace GranvilleMoore

variable {R S : Type*} {d : ℕ}

/-! ### The Moore matrix -/

section MooreMatrix

variable [Monoid R]

/-- The **Moore matrix** of `x = (x 1, …, x d)` at `p`: the `d × d` matrix whose
`(i, j)` entry is `x j ^ p ^ i`, so that its `i`-th row is the image of `x` under the
`i`-th iterate of the `p`-power map. -/
def mooreMatrix (p : ℕ) (x : Fin d → R) : Matrix (Fin d) (Fin d) R :=
  Matrix.of fun i j => x j ^ p ^ (i : ℕ)

/-- The `(i, j)` entry of the Moore matrix is `x j ^ p ^ i`. -/
@[simp]
theorem mooreMatrix_apply (p : ℕ) (x : Fin d → R) (i j : Fin d) :
    mooreMatrix p x i j = x j ^ p ^ (i : ℕ) :=
  rfl

/-- The first row of the Moore matrix is `x` itself. -/
theorem mooreMatrix_apply_zero (p : ℕ) (x : Fin (d + 1) → R) (j : Fin (d + 1)) :
    mooreMatrix p x 0 j = x j := by
  simp

/-- Each row of the Moore matrix is the `p`-th power of the preceding one. -/
theorem mooreMatrix_succ_apply (p : ℕ) (x : Fin (d + 1) → R) (i : Fin d) (j : Fin (d + 1)) :
    mooreMatrix p x i.succ j = mooreMatrix p x i.castSucc j ^ p := by
  simp [Fin.val_succ, pow_succ, pow_mul]

/-- Forming the Moore matrix commutes with applying a monoid homomorphism entrywise; this
is the passage from the integer Moore matrix to its image over `ℚ`. -/
theorem mooreMatrix_map [Monoid S] (p : ℕ) (x : Fin d → R) (f : R →* S) :
    (mooreMatrix p x).map f = mooreMatrix p fun j => f (x j) := by
  ext i j
  simp

end MooreMatrix

/-! ### The reduction ladder -/

/-- The `i`-th matrix `L i` of the **reduction ladder** of `x = (x 1, …, x d)` at `p`: the
`d × d` matrix over `ℚ` whose rows are, in order, the vectors of iterated Fermat
quotients
`F⁽⁰⁾_0, F⁽¹⁾_0, …, F⁽ⁱ⁾_0, F⁽ⁱ⁾_1, …, F⁽ⁱ⁾_(d - 1 - i)`
evaluated at `x`; that is, the row at index `r` is `fun j => iteratedFermatQuot p a b (x j)`
with `(a, b) = (min r i, r - i)`. -/
def ladderMatrix (p : ℕ) (x : Fin d → ℤ) (i : ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  Matrix.of fun r j => iteratedFermatQuot p (min (r : ℕ) i) ((r : ℕ) - i) (x j)

/-- The `(r, j)` entry of `L i` is `F⁽ᵃ⁾_b (x j)` with `(a, b) = (min r i, r - i)`. -/
@[simp]
theorem ladderMatrix_apply (p : ℕ) (x : Fin d → ℤ) (i : ℕ) (r j : Fin d) :
    ladderMatrix p x i r j = iteratedFermatQuot p (min (r : ℕ) i) ((r : ℕ) - i) (x j) :=
  rfl

/-- The row at index `r` of `L i` is the vector `F⁽ᵃ⁾_b` at `x` with
`(a, b) = (min r i, r - i)`. -/
theorem ladderMatrix_row (p : ℕ) (x : Fin d → ℤ) (i : ℕ) (r : Fin d) :
    ladderMatrix p x i r = fun j => iteratedFermatQuot p (min (r : ℕ) i) ((r : ℕ) - i) (x j) :=
  rfl

/-- The first `i + 1` rows of `L i` carry the growing superscript: the row at index
`r ≤ i` is `F⁽ʳ⁾_0`. -/
theorem ladderMatrix_row_of_le {p : ℕ} {x : Fin d → ℤ} {i : ℕ} {r : Fin d} (h : (r : ℕ) ≤ i) :
    ladderMatrix p x i r = fun j => iteratedFermatQuot p (r : ℕ) 0 (x j) := by
  rw [ladderMatrix_row, min_eq_left h, Nat.sub_eq_zero_of_le h]

/-- The last `d - 1 - i` rows of `L i` carry the growing subscript: the row at index
`r ≥ i` is `F⁽ⁱ⁾_(r - i)`. -/
theorem ladderMatrix_row_of_ge {p : ℕ} {x : Fin d → ℤ} {i : ℕ} {r : Fin d} (h : i ≤ (r : ℕ)) :
    ladderMatrix p x i r = fun j => iteratedFermatQuot p i ((r : ℕ) - i) (x j) := by
  rw [ladderMatrix_row, min_eq_right h]

end GranvilleMoore

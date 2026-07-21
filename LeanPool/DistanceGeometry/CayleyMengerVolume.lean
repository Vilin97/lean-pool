/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.DistanceGeometry.Defs
public import LeanPool.DistanceGeometry.Schoenberg
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Cayley–Menger determinant and simplex volume

The Cayley–Menger matrix of an `(n+1)`-point configuration is the `(n+2)×(n+2)`
matrix obtained by bordering the squared-distance matrix `D` with a `0` in the
top-left corner and `1`'s along the rest of the first row and column. Cayley–Menger's
theorem says its determinant is a fixed constant times the squared `n`-volume of the
simplex on the points:

`det CM = (-1)^(n+1) · 2^n · det G`,

where `G` is the Gram matrix of the `n` edge vectors `x i - x 0`, namely the
nonzero block of the basepoint-centered matrix `centeredGram D` from `Defs.lean`.

This file proves the identity in low dimension:

* `n = 1` (a segment): `det CM = 2 · ℓ²` (`cayleyMenger_det_segment`).
* `n = 2` (a triangle): `det CM = -4 · det G` (`cayleyMenger_det_triangle`).
* `n = 2`, geometric: `det CM = -16 · area²`, the triangle-area identity underlying
  Heron's formula (`cayleyMenger_det_heron`).

The `n = 2` core identity is a pure algebraic identity in the entries of any
symmetric hollow `3×3` matrix. The geometric triangle-area specialization identifies
the edge-Gram `2×2` block with the basepoint-centered matrix `centeredGram D` and
reads the triangle area from the edge coordinates.

## Main results

* `DistanceGeometry.cayleyMenger` : the Cayley–Menger matrix.
* `DistanceGeometry.cayleyMenger_det_segment`, `..._det_triangle`, `..._det_heron`.

## Implementation notes

The `n = 2` proofs expand a `4×4` determinant via `det_fin_four`, a Laplace
cofactor expansion that fills the gap left by Mathlib (which ships `det_fin_one`
through `det_fin_three`). For upstreaming, `det_fin_four` belongs as a public
`Matrix.det_fin_four` next to `det_fin_three`; only `n ≤ 2` of the Cayley–Menger
identity is proved here.

## References

* A. Cayley, *On a theorem in the geometry of position*, 1841.
* K. Menger, *Untersuchungen über allgemeine Metrik*, 1928.
-/

@[expose] public section

namespace DistanceGeometry

open Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

/-! ### The Cayley–Menger matrix -/

/-- The Cayley–Menger matrix of a squared-distance matrix `D` on `n+1` points: the
`(n+2)×(n+2)` matrix with a `0` in the top-left corner, `1`'s on the rest of the
first row and column, and `D` in the lower-right `(n+1)×(n+1)` block.

Built with `Fin.cons`: row `0` is `[0, 1, …, 1]`; row `i+1` is `[1, D i 0, …]`. -/
def cayleyMenger (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons 0 (fun _ => 1)) (fun i => Fin.cons 1 (D i)))

/-- The top-left entry of the Cayley–Menger matrix is `0`. -/
@[simp] theorem cayleyMenger_zero_zero (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    cayleyMenger D 0 0 = 0 := rfl

/-- Off the corner, the first row of the Cayley–Menger matrix is all `1`s. -/
@[simp] theorem cayleyMenger_zero_succ (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (j : Fin (n + 1)) : cayleyMenger D 0 j.succ = 1 := rfl

/-- Off the corner, the first column of the Cayley–Menger matrix is all `1`s. -/
@[simp] theorem cayleyMenger_succ_zero (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) : cayleyMenger D i.succ 0 = 1 := rfl

/-- The lower-right block of the Cayley–Menger matrix is `D`. -/
@[simp] theorem cayleyMenger_succ_succ (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) : cayleyMenger D i.succ j.succ = D i j := rfl

/-! ### A reusable `4×4` cofactor expansion -/

/-- Laplace cofactor expansion of a `4×4` determinant along the first row, fully
reduced to entry products. Mathlib ships `det_fin_one`/`det_fin_two`/`det_fin_three`
but not `_four`; this fills the gap, used for the `n = 2` Cayley–Menger determinant.
For upstreaming this belongs as a public `Matrix.det_fin_four`. -/
private theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
                - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
                + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
                - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
                + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
                - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
                + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
                - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
                + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, submatrix_apply, Fin.succAbove]
  ring

/-! ### `n = 1` : the segment -/

/-- The segment case (`n = 1`) of Cayley–Menger. For two points with squared distance
`ℓ² = D 0 1`, the `3×3` Cayley–Menger determinant is `2·ℓ²` (the general sign is
`(-1)^(n+1)·2^n·det G`, here `(-1)²·2¹ = +2` and the `1×1` edge-Gram is `[ℓ²]`). With
`D` hollow this reads `det CM = 2 · D 0 1`. -/
theorem cayleyMenger_det_segment (D : Matrix (Fin 2) (Fin 2) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (s01 : D 1 0 = D 0 1) :
    (cayleyMenger D).det = 2 * D 0 1 := by
  rw [det_fin_three]
  rw [show cayleyMenger D 0 0 = 0 from rfl, show cayleyMenger D 0 1 = 1 from rfl,
      show cayleyMenger D 0 2 = 1 from rfl, show cayleyMenger D 1 0 = 1 from rfl,
      show cayleyMenger D 1 1 = D 0 0 from rfl, show cayleyMenger D 1 2 = D 0 1 from rfl,
      show cayleyMenger D 2 0 = 1 from rfl, show cayleyMenger D 2 1 = D 1 0 from rfl,
      show cayleyMenger D 2 2 = D 1 1 from rfl, h00, h11, s01]
  ring

/-! ### `n = 2` : the triangle (pure algebra) -/

/-- The triangle case (`n = 2`) of Cayley–Menger, algebraic form. For three points
with a symmetric hollow squared-distance matrix `D`, the `4×4` Cayley–Menger
determinant equals `-4` times the determinant of the `2×2` edge-Gram block

`G = [[D 0 1, (D 0 1 + D 0 2 - D 1 2)/2],`
`     [(D 0 1 + D 0 2 - D 1 2)/2, D 0 2]]`

i.e. `det CM = -4 · (D 0 1 · D 0 2 - ((D 0 1 + D 0 2 - D 1 2)/2)²)`. This is a pure
algebraic identity in the entries of `D`; no geometry is used. -/
theorem cayleyMenger_det_triangle (D : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (h22 : D 2 2 = 0)
    (s01 : D 1 0 = D 0 1) (s02 : D 2 0 = D 0 2) (s12 : D 2 1 = D 1 2) :
    (cayleyMenger D).det
      = -4 * (D 0 1 * D 0 2 - ((D 0 1 + D 0 2 - D 1 2) / 2) ^ 2) := by
  rw [det_fin_four]
  rw [show cayleyMenger D 0 0 = 0 from rfl, show cayleyMenger D 0 1 = 1 from rfl,
      show cayleyMenger D 0 2 = 1 from rfl, show cayleyMenger D 0 3 = 1 from rfl,
      show cayleyMenger D 1 0 = 1 from rfl, show cayleyMenger D 1 1 = D 0 0 from rfl,
      show cayleyMenger D 1 2 = D 0 1 from rfl, show cayleyMenger D 1 3 = D 0 2 from rfl,
      show cayleyMenger D 2 0 = 1 from rfl, show cayleyMenger D 2 1 = D 1 0 from rfl,
      show cayleyMenger D 2 2 = D 1 1 from rfl, show cayleyMenger D 2 3 = D 1 2 from rfl,
      show cayleyMenger D 3 0 = 1 from rfl, show cayleyMenger D 3 1 = D 2 0 from rfl,
      show cayleyMenger D 3 2 = D 2 1 from rfl, show cayleyMenger D 3 3 = D 2 2 from rfl,
      h00, h11, h22, s01, s02, s12]
  ring

/-- The triangle Cayley–Menger determinant in terms of the basepoint-centered
matrix `centeredGram`. The `2×2` edge-Gram block above is exactly `centeredGram D`
restricted to the nonzero
indices `{1, 2}` (cf. `Defs.centeredGram`): its diagonal entries are
`centeredGram D 1 1 = D 0 1`, `centeredGram D 2 2 = D 0 2` (by hollowness) and its
off-diagonal is `centeredGram D 1 2`. Hence

`det CM = -4 · (centeredGram D 1 1 · centeredGram D 2 2 - (centeredGram D 1 2)²)`.

This is the bridge from the Cayley–Menger determinant to the Schoenberg core. -/
theorem cayleyMenger_det_triangle_centeredGram (D : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (h22 : D 2 2 = 0)
    (s01 : D 1 0 = D 0 1) (s02 : D 2 0 = D 0 2) (s12 : D 2 1 = D 1 2) :
    (cayleyMenger D).det
      = -4 * (centeredGram D 1 1 * centeredGram D 2 2 - (centeredGram D 1 2) ^ 2) := by
  rw [cayleyMenger_det_triangle D h00 h11 h22 s01 s02 s12]
  -- evaluate the three centeredGram entries on `Fin 3`
  have e11 : centeredGram D 1 1 = D 0 1 := by simp [centeredGram_apply, h11]
  have e22 : centeredGram D 2 2 = D 0 2 := by simp [centeredGram_apply, h22]
  have e12 : centeredGram D 1 2 = (D 0 1 + D 0 2 - D 1 2) / 2 := by simp [centeredGram_apply]
  rw [e11, e22, e12]

/-! ### `n = 2` : the geometric triangle-area identity -/

/-- The inner product on `ℝ` (the real scalar field) is multiplication. -/
private theorem real_scalar_inner (a b : ℝ) : ⟪a, b⟫ = a * b := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [Real.norm_eq_abs, abs_mul_abs_self]
  ring

/-- The inner product of two vectors of `EuclideanSpace ℝ (Fin 2)` is the dot product
of their two coordinates. -/
private theorem inner_fin_two (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, real_scalar_inner, real_scalar_inner]

/-- The unsigned area of the triangle on three points of the Euclidean plane, as half
the absolute value of the `2×2` determinant of the edge-coordinate matrix
`[x 1 - x 0; x 2 - x 0]`. (The signed area is `det E / 2`; this is `|det E| / 2`.) -/
noncomputable def triangleArea (x : Fin 3 → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((x 1 - x 0) 0 * (x 2 - x 0) 1 - (x 1 - x 0) 1 * (x 2 - x 0) 0)| / 2

/-- The Gram–volume identity for `n = 2`. The determinant of the `2×2` edge-Gram block
of the basepoint-centered matrix `centeredGram D` (indices `{1, 2}`) equals the square of the
edge-coordinate determinant `det E`, where `E = [x 1 - x 0; x 2 - x 0]`. This is the
`n = 2` case of `det G = (n!·Vol)²` (here `det G = (2·area)²`). -/
theorem det_centeredGram_block_eq_sq
    {D : Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hD : IsSqDistMatrix D x) :
    centeredGram D 1 1 * centeredGram D 2 2 - (centeredGram D 1 2) ^ 2
      = ((x 1 - x 0) 0 * (x 2 - x 0) 1 - (x 1 - x 0) 1 * (x 2 - x 0) 0) ^ 2 := by
  rw [centeredGram_apply_eq_inner hD 1 1, centeredGram_apply_eq_inner hD 2 2,
      centeredGram_apply_eq_inner hD 1 2, inner_fin_two, inner_fin_two, inner_fin_two]
  ring

/-- The Cayley–Menger triangle-area identity (`n = 2`). For a triangle on three points
`x` of the Euclidean plane with squared-distance matrix `D`, the `4×4`
Cayley–Menger determinant equals `-16` times the squared area:

`det CM = -16 · area²`.

After expansion and factorization in the three side lengths, this identity is equivalent
to Heron's formula `16·area² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`. This file does not
state that factorized formula as a separate theorem. -/
theorem cayleyMenger_det_heron
    {D : Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hD : IsSqDistMatrix D x) :
    (cayleyMenger D).det = -16 * (triangleArea x) ^ 2 := by
  rw [cayleyMenger_det_triangle_centeredGram D (hD.hollow 0) (hD.hollow 1) (hD.hollow 2)
        (hD.symm 1 0) (hD.symm 2 0) (hD.symm 2 1),
      det_centeredGram_block_eq_sq hD, triangleArea]
  rw [div_pow, sq_abs]
  ring

end DistanceGeometry

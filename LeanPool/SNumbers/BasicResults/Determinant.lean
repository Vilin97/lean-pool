/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant facts: adjoint, singular values, diagonal and bordered matrices

* `LinearMap.det_adjoint` — `det T* = conj (det T)`, for an endomorphism of a
  finite-dimensional inner product space. In an orthonormal basis the matrix of
  the adjoint is the conjugate transpose, and `det Aᴴ = conj (det A)`.
* `LinearMap.det_eq_prod_of_apply_eq_smul` — the determinant of an endomorphism
  that is diagonal in some basis (`T (b i) = μ i • b i`) is the product `∏ μᵢ`.
* `Matrix.det_eq_corner_mul_det_submatrix` — the **bordered determinant**: if,
  above the corner, the last column of a `(k+1)×(k+1)` matrix is a combination
  of the first `k` columns, then `det M` is the corner entry left after that
  column operation times the determinant of the top-left `k×k` block. The
  elementary column-operation form of the Schur determinant formula, over any
  commutative ring and with no invertibility hypothesis.
-/

open LinearMap
open scoped ComplexConjugate

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **`det T* = conj (det T)`.** In an orthonormal basis the matrix of the
adjoint is the conjugate transpose, and `det Aᴴ = conj (det A)`. -/
theorem LinearMap.det_adjoint (T : E →ₗ[𝕜] E) :
    LinearMap.det (adjoint T) = conj (LinearMap.det T) := by
  set v := stdOrthonormalBasis 𝕜 E with hv
  rw [← LinearMap.det_toMatrix v.toBasis (adjoint T), LinearMap.toMatrix_adjoint v v T,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix v.toBasis T, starRingEnd_apply]

/-! ## Determinant of an endomorphism diagonal in a basis -/

/-- If a basis `b` consists of eigenvectors of `T`, with `T (b i) = μ i • b i`, then
`det T = ∏ᵢ μᵢ`. (The matrix of `T` in the basis `b` is `diagonal μ`.) -/
theorem LinearMap.det_eq_prod_of_apply_eq_smul {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] (b : Module.Basis ι R M) (T : M →ₗ[R] M)
    (μ : ι → R) (h : ∀ i, T (b i) = μ i • b i) :
    LinearMap.det T = ∏ i, μ i := by
  classical
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b T = Matrix.diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply, h j, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]
  rw [hmat, Matrix.det_diagonal]

/-! ## Bordered determinants

If the last column of a `(k+1)×(k+1)` matrix `M` is, *above the corner*, the
combination of the first `k` columns with coefficients `w`, then subtracting
that combination clears the column and Laplace expansion gives `det M` as the
resulting corner entry times the determinant of the top-left `k×k` block. -/

/-- **Bordered determinant.** Let `M` be a `(k+1)×(k+1)` matrix and `w` a
vector of `k` scalars such that the entries of the last column of `M` above the
corner are given by the combination of the first `k` columns with coefficients
`w`, i.e. `M i last = ∑ⱼ M i j · wⱼ` for `i < k`. Then

  `det M = (M last last - ∑ⱼ M last j · wⱼ) · det (M restricted to the first k
  rows and columns)`.

No invertibility of the top-left block is required; this is the elementary
column-operation form of the Schur determinant formula. -/
theorem Matrix.det_eq_corner_mul_det_submatrix {R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (w : Fin k → R)
    (hw : ∀ i : Fin k, M i.castSucc (Fin.last k)
      = ∑ j, M i.castSucc j.castSucc * w j) :
    M.det = (M (Fin.last k) (Fin.last k) - ∑ j, M (Fin.last k) j.castSucc * w j)
      * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  classical
  -- The coefficients of the column operation: keep the last column, subtract
  -- `wⱼ` times the `j`-th one.
  set c : Fin (k + 1) → R := Fin.lastCases 1 (fun j => -w j) with hc
  have hclast : c (Fin.last k) = 1 := by rw [hc]; simp
  have hccast : ∀ j : Fin k, c j.castSucc = -w j := fun j => by rw [hc]; simp
  -- The column obtained from the operation.
  have hcol : ∀ r : Fin (k + 1), (∑ i, c i • M r i)
      = M r (Fin.last k) - ∑ j, M r j.castSucc * w j := by
    intro r
    rw [Fin.sum_univ_castSucc, hclast, one_smul]
    have hterm : ∀ j : Fin k,
        c j.castSucc • M r j.castSucc = -(M r j.castSucc * w j) := by
      intro j
      rw [hccast j, neg_smul, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib]
    ring
  -- The matrix after the column operation; its determinant is unchanged.
  set M' := M.updateCol (Fin.last k) (fun r => ∑ i, c i • M r i) with hM'
  have hMM' : M'.det = M.det := by
    rw [hM', Matrix.det_updateCol_sum, hclast, one_smul]
  have hlastcol : ∀ r, M' r (Fin.last k)
      = M r (Fin.last k) - ∑ j, M r j.castSucc * w j := fun r => by
    rw [hM', Matrix.updateCol_self, hcol r]
  -- The last column of `M'` vanishes above the corner.
  have hzero : ∀ i : Fin k, M' i.castSucc (Fin.last k) = 0 := fun i => by
    rw [hlastcol, hw i, sub_self]
  -- The top-left block is unchanged.
  have hsub : M'.submatrix Fin.castSucc Fin.castSucc
      = M.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hM',
      Matrix.updateCol_ne (Fin.castSucc_lt_last j).ne]
  -- Laplace expansion along the last column of `M'`.
  have hsign : ((-1 : R)) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
    rw [Fin.val_last]
    exact Even.neg_one_pow ⟨k, rfl⟩
  rw [← hMM', Matrix.det_succ_column M' (Fin.last k),
    Finset.sum_eq_single (Fin.last k)
      (fun i _ hi => by
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [hzero i', mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
    hsign, one_mul, Fin.succAbove_last, hsub, hlastcol]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

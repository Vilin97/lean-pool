/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order

/-!
# Frobenius Positivity

If `G` is positive semidefinite and nonzero, and `B` is positive definite, then the Frobenius
inner product `⟪G, B⟫ = ∑ j l, G j l * B j l` is strictly positive. The proof diagonalizes
`B = U D Uᵀ` via the spectral theorem, conjugates `G` to `H = Uᵀ G U` (which remains PSD and
nonzero), and reduces to `⟪G, B⟫ = tr(H D) = ∑ i, λᵢ Hᵢᵢ > 0`.
-/

open Matrix

open scoped BigOperators MatrixOrder


universe u

variable {ι : Type u}

/-- Helper: Frobenius inner product equals `trace (Gᵀ * B)` (real case). -/
lemma frobenius_eq_trace_transpose_mul
  [Fintype ι] (G B : Matrix ι ι ℝ) :
  (∑ j, ∑ l, G j l * B j l) = Matrix.trace (G.transpose * B) := by
  classical
  -- Expand the trace of Gᵀ * B
  have htrace : Matrix.trace (G.transpose * B) = ∑ i, ∑ k, G k i * B k i := by
    simp [Matrix.trace, Matrix.mul_apply]
  -- Reorder the Frobenius double sum and rename indices to match htrace
  calc
    (∑ j, ∑ l, G j l * B j l) = ∑ i, ∑ k, G k i * B k i := by
          simpa using
            (Finset.sum_comm :
              (∑ j, ∑ l, G j l * B j l) = (∑ i, ∑ k, G k i * B k i))
    _ = Matrix.trace (G.transpose * B) := htrace.symm

/-- Congruence by an orthogonal/invertible matrix preserves nonzeroness (real case).
If `U * Uᵀ = 1`, then `Uᵀ G U ≠ 0` whenever `G ≠ 0`.
-/
lemma congr_transpose_mul_mul_ne_zero
  [Fintype ι] [DecidableEq ι]
  (U G : Matrix ι ι ℝ) (hU_right : U * U.transpose = 1)
  (hG_ne_zero : G ≠ 0) :
  U.transpose * G * U ≠ 0 := by
  intro hH
  -- Conjugate back with U on the left and Uᵀ on the right to recover G
  have hcalc : U * (U.transpose * G * U) * U.transpose
      = (U * U.transpose) * G * (U * U.transpose) := by
    simp [Matrix.mul_assoc]
  have hG_eq : G = U * (U.transpose * G * U) * U.transpose := by
    simpa [hU_right, Matrix.one_mul, Matrix.mul_one] using hcalc.symm
  have : G = 0 := by simpa [hH, Matrix.mul_zero, Matrix.zero_mul] using hG_eq
  exact hG_ne_zero this

/-- Cauchy–Schwarz for the semi-inner product induced by a PSD real matrix.
For all vectors x,y: (xᵀ H y)^2 ≤ (xᵀ H x) (yᵀ H y).
-/
lemma psd_cauchy_schwarz
  [Fintype ι] (H : Matrix ι ι ℝ) (hH_psd : H.PosSemidef) (x y : ι → ℝ) :
  ((x ⬝ᵥ H.mulVec y)^2) ≤ (x ⬝ᵥ H.mulVec x) * (y ⬝ᵥ H.mulVec y) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH_psd.nonneg
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hB
  subst hB
  have hform (a b : ι → ℝ) :
      a ⬝ᵥ (B.transpose * B).mulVec b = (B.mulVec a) ⬝ᵥ (B.mulVec b) := by
    have h1 : (B.transpose * B).mulVec b = B.transpose.mulVec (B.mulVec b) := by
      exact (Matrix.mulVec_mulVec b B.transpose B).symm
    calc
      a ⬝ᵥ (B.transpose * B).mulVec b
          = a ⬝ᵥ B.transpose.mulVec (B.mulVec b) := by rw [h1]
      _ = (Matrix.vecMul a B.transpose) ⬝ᵥ (B.mulVec b) := dotProduct_mulVec a Bᵀ (B.mulVec b)
      _ = (B.mulVec a) ⬝ᵥ (B.mulVec b) := by
        have := (Matrix.vecMul_transpose (A := B) (x := a))
        simpa using congrArg (fun w => w ⬝ᵥ (B.mulVec b)) this
  let u : ι → ℝ := B.mulVec x
  let v : ι → ℝ := B.mulVec y
  -- xᵀ (Bᵀ B) y = (Bx)⋅(By), and similarly for x/x and y/y
  have hxy : x ⬝ᵥ (B.transpose * B).mulVec y = u ⬝ᵥ v := by
    simpa [u, v] using hform x y
  have hxx : x ⬝ᵥ (B.transpose * B).mulVec x = u ⬝ᵥ u := by
    simpa [u] using hform x x
  have hyy : y ⬝ᵥ (B.transpose * B).mulVec y = v ⬝ᵥ v := by
    simpa [v] using hform y y
  -- Cauchy–Schwarz in ℝ^ι: |u⋅v|^2 ≤ (u⋅u)(v⋅v)
  have hCS : (u ⬝ᵥ v)^2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
    classical
    -- Finset version of Cauchy–Schwarz with s = univ
    simpa [dotProduct, sq] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι))
        (f := fun i => u i) (g := fun i => v i))
  simpa [hxy, hxx, hyy] using hCS

/-- If H is PSD over ℝ and H ii = H jj = 0 then H ij = 0. -/
lemma psd_offdiag_zero_of_diag_zero
  [Finite ι]
  (H : Matrix ι ι ℝ) (hH_psd : H.PosSemidef) {i j : ι}
  (hii : H i i = 0) (hjj : H j j = 0) : H i j = 0 := by
  letI := Fintype.ofFinite ι
  classical
  -- Apply Cauchy–Schwarz with x = e_i, y = e_j
  have hcs := psd_cauchy_schwarz H hH_psd (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))
  -- Rewrite each quadratic form
  have hx : (Pi.single i (1 : ℝ)) ⬝ᵥ H.mulVec (Pi.single i 1) = H i i := by simp
  have hy : (Pi.single j (1 : ℝ)) ⬝ᵥ H.mulVec (Pi.single j 1) = H j j := by simp
  have hxy : (Pi.single i (1 : ℝ)) ⬝ᵥ H.mulVec (Pi.single j 1) = H i j := by simp
  -- Substitute and use hii, hjj
  have : (H i j)^2 ≤ (H i i) * (H j j) := by simpa [hx, hy, hxy]
    using hcs
  -- Right side is 0, left is square ≥ 0, hence equality and H i j = 0 over ℝ
  have : (H i j)^2 ≤ 0 := by simpa [hii, hjj]
  have hsq_nonneg : 0 ≤ (H i j)^2 := by have := sq_nonneg (H i j); simpa using this
  have : (H i j)^2 = 0 := le_antisymm this hsq_nonneg
  exact sq_eq_zero_iff.mp this

/-- For a real PSD matrix, if it is nonzero then some diagonal entry is strictly positive. -/
lemma posSemidef_diag_pos_exists_of_ne_zero
  [Finite ι]
  (H : Matrix ι ι ℝ) (hH_psd : H.PosSemidef) (hH_ne_zero : H ≠ 0) :
  ∃ i, 0 < H i i := by
  letI := Fintype.ofFinite ι
  classical
  -- Suppose all diagonal entries are ≤ 0; PSD gives ≥ 0, hence all zeros
  by_contra h
  push Not at h
  have hdiag_nonneg : ∀ i, 0 ≤ H i i := fun i => hH_psd.diag_nonneg
  have hdiag_zero : ∀ i, H i i = 0 := fun i => le_antisymm (h i) (hdiag_nonneg i)
  -- Show all off-diagonals are zero
  have hoff : ∀ i j, H i j = 0 := by
    intro i j
    exact psd_offdiag_zero_of_diag_zero H hH_psd (hdiag_zero i) (hdiag_zero j)
  -- Hence H = 0, contradiction
  have : H = 0 := by
    ext i j
    simp [hoff i j]
  exact hH_ne_zero this

/-- Frobenius positivity for a nonzero PSD matrix against a PD matrix (real case).
If `G` is positive semidefinite and nonzero, and `B` is positive definite,
then the Frobenius inner product `∑ j, ∑ l, G j l * B j l` is strictly positive.

High-level proof sketch (to be formalized):
- Use spectral theorem for real symmetric PD matrices: B = U D Uᵀ with D diagonal,
  diag(λ), λ > 0.
- Let H := Uᵀ G U. Then H is PSD and H ≠ 0 (congruence by invertible U).
- Frobenius inner product equals trace: ⟪G,B⟫ = tr(G B) = tr(H D) = ∑ i λ i * H i i.
- For PSD H, diagonal entries are ≥ 0, and H ≠ 0 ⇒ ∃ i, H i i > 0.
- Since all λ i > 0, the sum is strictly positive.
- This avoids Cholesky and uses spectral decomposition/unitary congruence invariance.
-/
lemma frobenius_pos_of_psd_posdef
  [Fintype ι]
  (G B : Matrix ι ι ℝ) (hG_psd : G.PosSemidef) (hG_ne_zero : G ≠ 0) (hB : B.PosDef) :
  0 < ∑ j, ∑ l, G j l * B j l := by
  classical
  -- Step 1: rewrite as a trace
  have hfrob_trace : (∑ j, ∑ l, G j l * B j l) = Matrix.trace (G.transpose * B) :=
    frobenius_eq_trace_transpose_mul G B
  -- Step 2: spectral decomposition of B using positive definite eigenvalues
  have hB_herm : B.IsHermitian := hB.1
  have hd_pos : ∀ i, 0 < hB_herm.eigenvalues i := hB.eigenvalues_pos
  -- Get the spectral decomposition B = U * D * U*
  have hB_spectral := hB_herm.spectral_theorem
  -- Define the eigenvector unitary and its underlying matrix, and eigenvalue function
  let Uu := hB_herm.eigenvectorUnitary
  let U : Matrix ι ι ℝ := (Uu : Matrix ι ι ℝ)
  let d : ι → ℝ := hB_herm.eigenvalues
  -- Since we're over ℝ, star = transpose and RCLike.ofReal = identity
  have hB_decomp : B = U * Matrix.diagonal d * U.transpose := by
    rw [hB_spectral]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
               Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
                 RCLike.ofReal_real_eq_id, id]
    rfl
  -- Define H := Uᵀ * G * U and show PSD
  let H : Matrix ι ι ℝ := U.transpose * G * U
  have hH_psd : H.PosSemidef := by
    rw [show H = U.conjTranspose * G * U from by
        simp [H, Matrix.conjTranspose_eq_transpose_of_trivial]]
    exact hG_psd.conjTranspose_mul_mul_same U
  -- Use a local lemma to avoid inline unitary algebra: H ≠ 0
  have hH_ne_zero : H ≠ 0 := by
    -- From the unitary eigenvector matrix, we have U * Uᵀ = 1 (over ℝ)
    have hU_mem : U ∈ Matrix.unitaryGroup ι ℝ := by
      -- Uu is a unitary group element, coerce to show membership
      rw [show U = Uu.val from rfl]
      exact Uu.property
    have hU_unitary : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hU_mem
    have hU_right : U * U.transpose = 1 := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hU_unitary
    exact congr_transpose_mul_mul_ne_zero U G hU_right hG_ne_zero
  -- Trace cyclicity: reduce to trace(H * diagonal d)
  have hG_herm : G.IsHermitian := hG_psd.1
  have htrace_cycle : Matrix.trace (G.transpose * B) = Matrix.trace (H * (Matrix.diagonal d)) := by
    have hG_symm : G.transpose = G := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hG_herm
    rw [hG_symm, hB_decomp]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    simp [H, Matrix.mul_assoc]
  -- Expand trace(H * diagonal d) as ∑ i d i * H i i
  have htrace_sum : Matrix.trace (H * Matrix.diagonal d) = ∑ i, d i * H i i := by
    classical
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, mul_comm]
  -- Diagonal entries of H are ≥ 0 from PSD
  have hdiag_nonneg : ∀ i, 0 ≤ H i i := fun i => hH_psd.diag_nonneg
  -- From nonzero PSD, some diagonal is positive (local lemma)
  have hdiag_pos_exists : ∃ i, 0 < H i i :=
    posSemidef_diag_pos_exists_of_ne_zero H hH_psd hH_ne_zero
  -- Conclude positivity: all d i > 0, some H i i > 0, and others ≥ 0
  rcases hdiag_pos_exists with ⟨i0, hi0pos⟩
  have hsum_pos : 0 < ∑ i, d i * H i i := by
    have h_pos : 0 < d i0 * H i0 i0 := mul_pos (hd_pos i0) hi0pos
    rw [← Finset.add_sum_erase Finset.univ (fun i => d i * H i i) (Finset.mem_univ i0)]
    have h_nonneg : 0 ≤ ∑ x ∈ Finset.univ.erase i0, d x * H x x := by
      apply Finset.sum_nonneg; intro i _
      exact mul_nonneg (le_of_lt (hd_pos i)) (hdiag_nonneg i)
    exact add_pos_of_pos_of_nonneg h_pos h_nonneg
  -- Transport back to the original Frobenius sum
  have htrace_pos : 0 < Matrix.trace (H * Matrix.diagonal d) := by
    simpa [htrace_sum] using hsum_pos
  have htrace_pos' : 0 < Matrix.trace (G.transpose * B) := by
    simpa [htrace_cycle] using htrace_pos
  simpa [hfrob_trace] using htrace_pos'

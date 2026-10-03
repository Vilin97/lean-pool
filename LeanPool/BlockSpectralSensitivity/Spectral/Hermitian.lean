/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Eigenvalues and the L2 operator norm of a real symmetric matrix

`Matrix.IsHermitian.spectral_theorem` diagonalises a Hermitian matrix by a unitary change of
basis; since unitaries are isometries for the L2 operator norm and the norm of a diagonal
matrix is the sup norm of its diagonal, this bounds `‖A‖` by the largest absolute eigenvalue
(`Matrix.IsHermitian.l2_opNorm_le_of_abs_eigenvalues_le`).

In the other direction, an eigenvector for `μ` exhibits `μ` in the spectrum, which for a
Hermitian matrix is the range of the eigenvalue function; hence `μ ≤ ⨆ i, eigenvalues i`
(`Matrix.IsHermitian.le_ciSup_eigenvalues`).  Applying this to the top eigenvector, whose norm
the operator norm bounds, gives the reverse inequality `⨆ i, eigenvalues i ≤ ‖A‖`
(`Matrix.IsHermitian.ciSup_eigenvalues_le_l2_opNorm`).

Together these are the two directions of the variational characterisation of the largest
eigenvalue that Section 14 of `bs_lambda.txt` needs.  Nothing here is specific to the
sensitivity graph; it is all material that belongs upstream in Mathlib, and it is stated in
the `Matrix.IsHermitian` namespace accordingly.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace Matrix.IsHermitian

open scoped Matrix Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The L2 operator norm of a symmetric matrix is bounded by any bound on the absolute values
of its eigenvalues. -/
theorem l2_opNorm_le_of_abs_eigenvalues_le [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ i, |hA.eigenvalues i| ≤ c) : ‖A‖ ≤ c := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (Classical.arbitrary n))
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg hc0]
  intro i
  simpa using hc i

/-- Every eigenvalue of a symmetric matrix is at most the largest eigenvalue. -/
theorem le_ciSup_eigenvalues (hA : A.IsHermitian) {μ : ℝ} {v : n → ℝ} (hv : v ≠ 0)
    (hev : A *ᵥ v = μ • v) : μ ≤ ⨆ i, hA.eigenvalues i := by
  have hmem : μ ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hev), hv⟩
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, rfl⟩ := hmem
  exact le_ciSup (Finite.bddAbove_range _) i

/-- The largest eigenvalue of a symmetric matrix is at most its L2 operator norm. -/
theorem ciSup_eigenvalues_le_l2_opNorm [Nonempty n] (hA : A.IsHermitian) :
    ⨆ i, hA.eigenvalues i ≤ ‖A‖ := by
  refine ciSup_le fun i ↦ ?_
  have hb : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h := l2_opNorm_mulVec A (hA.eigenvectorBasis i)
  rw [hA.mulVec_eigenvectorBasis i, hb, mul_one] at h
  exact (le_abs_self _).trans (by simpa [norm_smul, hb] using h)

/-- The largest eigenvalue of a symmetric matrix is attained by an eigenvector. -/
theorem exists_eigenvector_ciSup_eigenvalues [Nonempty n] (hA : A.IsHermitian) :
    ∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = (⨆ i, hA.eigenvalues i) • v := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := hA.eigenvalues)
  refine ⟨⇑(hA.eigenvectorBasis i),
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i, ?_⟩
  rw [← hi]
  exact hA.mulVec_eigenvectorBasis i

end Matrix.IsHermitian

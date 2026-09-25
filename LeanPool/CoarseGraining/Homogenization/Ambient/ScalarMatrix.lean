/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField

/-! # Scalar Matrix -/

@[expose] public section

namespace Homogenization

/-!
# Positive scalar matrices

Small helpers for scalar multiples of the identity, used when a deterministic
black-box statement is meant only for scalar constant backgrounds.
-/

/-- The scalar matrix `sigma • I`. -/
abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)

/-- A matrix is a positive scalar matrix if it is `sigma • I` with `sigma > 0`. -/
def IsPositiveScalarMatrix {d : ℕ} (A : Mat d) : Prop :=
  ∃ sigma : ℝ, 0 < sigma ∧ A = scalarMatrix (d := d) sigma

theorem matVecMul_scalarMatrix {d : ℕ} (sigma : ℝ) (x : Vec d) :
    matVecMul (scalarMatrix (d := d) sigma) x = sigma • x := by
  funext i
  rw [scalarMatrix, matVecMul, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    simp [hij]
  · simp

theorem scalarMatrix_isSymm {d : ℕ} (sigma : ℝ) :
    (scalarMatrix (d := d) sigma).IsSymm := by
  exact (Matrix.isSymm_one (n := Fin d) (α := ℝ)).smul sigma

theorem isEllipticMatrix_scalarMatrix {d : ℕ} {sigma : ℝ}
    (hsigma : 0 < sigma) :
    IsEllipticMatrix sigma sigma (scalarMatrix (d := d) sigma) := by
  refine ⟨hsigma, le_rfl, ?_, ?_⟩
  · intro ξ
    rw [matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]
  · intro ξ
    have hInv :
        ((scalarMatrix (d := d) sigma)⁻¹ : Mat d) = sigma⁻¹ • (1 : Mat d) := by
      rw [scalarMatrix, nonsing_inv_smul sigma (ne_of_gt hsigma) (by simp)]
      simp
    rw [hInv, matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]

theorem IsPositiveScalarMatrix.isSymm {d : ℕ} {A : Mat d}
    (hA : IsPositiveScalarMatrix A) :
    A.IsSymm := by
  rcases hA with ⟨sigma, _hsigma, rfl⟩
  exact scalarMatrix_isSymm sigma

theorem IsPositiveScalarMatrix.isEllipticMatrix {d : ℕ} {A : Mat d}
    (hA : IsPositiveScalarMatrix A) :
    ∃ sigma : ℝ, 0 < sigma ∧ IsEllipticMatrix sigma sigma A := by
  rcases hA with ⟨sigma, hsigma, rfl⟩
  exact ⟨sigma, hsigma, isEllipticMatrix_scalarMatrix hsigma⟩

end Homogenization

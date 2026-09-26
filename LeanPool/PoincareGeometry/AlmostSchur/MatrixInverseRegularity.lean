/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DensityDerivative

/-! # Smoothness of matrix inversion on nonsingular matrices

The adjugate is polynomial in the matrix entries, and division by the nonzero
determinant gives inversion. The result uses the entrywise finite-dimensional
matrix topology and does not require an operator-norm instance.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The adjugate is smooth to every order as a matrix-valued polynomial. -/
theorem contDiff_matrix_adjugate (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun A : Matrix ι ι ℝ => A.adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply (determinantMultilinear (ι := ι)).contDiff.comp
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hk]
    fun_prop

/-- Inversion is smooth at every matrix with nonzero determinant. -/
theorem contDiffAt_matrix_inverse (n : WithTop ℕ∞) (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) : ContDiffAt ℝ n (fun B : Matrix ι ι ℝ => B⁻¹) A := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((determinantMultilinear (ι := ι)).contDiff.contDiffAt.inv hA).smul
    (contDiff_matrix_adjugate n).contDiffAt

/-- A smooth matrix field with nonvanishing determinant has a smooth inverse on its domain. -/
theorem contDiffOn_matrix_inverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set V} (A : V → Matrix ι ι ℝ)
    (hA : ContDiffOn ℝ n A U) (hd : ∀ x ∈ U, (A x).det ≠ 0) :
    ContDiffOn ℝ n (fun x => (A x)⁻¹) U := by
  intro x hx
  exact (contDiffAt_matrix_inverse n (A x) (hd x hx)).comp_contDiffWithinAt x (hA x hx)

end AlmostSchur

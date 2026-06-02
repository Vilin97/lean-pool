/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import LeanPool.Monlib4.LinearAlgebra.InnerAut
import LeanPool.Monlib4.LinearAlgebra.Matrix.StarOrderedRing

/-!
# Real powers of positive definite matrices

This file restores the upstream monlib4 API for real powers of positive
semidefinite and positive definite matrices.  The definitions are stated in
terms of the current Mathlib Hermitian spectral theorem.
-/

namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators ComplexOrder MatrixOrder

theorem _root_.Matrix.IsHermitian.eigenvectorMatrix_conjTranspose_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    hA.eigenvectorMatrixᴴ * hA.eigenvectorMatrix = 1 := by
  rw [IsHermitian.eigenvectorMatrix, ← star_eq_conjTranspose]
  exact UnitaryGroup.star_mul_self _

/-- Real powers of a Hermitian matrix, defined by spectral calculus. -/
noncomputable def _root_.Matrix.IsHermitian.rpow {Q : Matrix n n 𝕜}
    (hQ : IsHermitian Q) (r : ℝ) :
    Matrix n n 𝕜 :=
  Matrix.innerAut hQ.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ (hQ.eigenvalues ^ (r : ℝ) : n → ℝ) : n → 𝕜))

/-- Real powers of a positive semidefinite matrix. -/
noncomputable abbrev _root_.Matrix.PosSemidef.rpow {Q : Matrix n n 𝕜}
    (hQ : PosSemidef Q) (r : ℝ) :
    Matrix n n 𝕜 :=
  hQ.1.rpow r

/-- Real powers of a positive definite matrix. -/
noncomputable abbrev _root_.Matrix.PosDef.rpow {Q : Matrix n n 𝕜}
    (hQ : PosDef Q) (r : ℝ) :
    Matrix n n 𝕜 :=
  hQ.1.rpow r

lemma _root_.Matrix.PosDef.rpow_eq {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    hQ.rpow r =
      Matrix.innerAut hQ.1.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ r : n → ℝ) : n → 𝕜)) :=
  rfl

theorem _root_.Matrix.PosSemidef.rpow_mul_rpow (r₁ r₂ : NNRealˣ) {Q : Matrix n n 𝕜}
    (hQ : PosSemidef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) := by
  simp_rw [PosSemidef.rpow, IsHermitian.rpow, ← innerAut.map_mul, Pi.pow_def,
    diagonal_mul_diagonal, Function.comp_apply, ← RCLike.ofReal_mul]
  congr
  ext i
  simp only [Function.comp_apply]
  by_cases h : hQ.1.eigenvalues i = 0
  · simp_rw [h]
    have hr₁ : (r₁ : ℝ) ≠ 0 := by
      exact_mod_cast Units.ne_zero r₁
    have hr₂ : (r₂ : ℝ) ≠ 0 := by
      exact_mod_cast Units.ne_zero r₂
    have hsum : ((r₁ : ℝ) + (r₂ : ℝ)) ≠ 0 := by
      intro hsum
      have hnn : ((r₁ : NNReal) + (r₂ : NNReal)) = 0 := by
        exact_mod_cast hsum
      exact Units.ne_zero r₁ (add_eq_zero.mp hnn).1
    simp [Real.zero_rpow, hr₁, hr₂, hsum]
  · rw [← Real.rpow_add]
    apply lt_of_le_of_ne (hQ.eigenvalues_nonneg _)
    rw [ne_eq, eq_comm]
    exact h

theorem _root_.Matrix.PosDef.rpow_mul_rpow (r₁ r₂ : ℝ) {Q : Matrix n n 𝕜}
    (hQ : PosDef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) := by
  simp_rw [Matrix.PosDef.rpow, IsHermitian.rpow, ← innerAut.map_mul, Pi.pow_def,
    diagonal_mul_diagonal, Function.comp_apply, ← RCLike.ofReal_mul,
    ← Real.rpow_add (hQ.pos_eigenvalues _)]
  rfl

theorem _root_.Matrix.IsHermitian.rpow_one_eq_self {Q : Matrix n n 𝕜}
    (hQ : Q.IsHermitian) :
    hQ.rpow 1 = Q := by
  simp_rw [IsHermitian.rpow, Pi.pow_def, Real.rpow_one]
  rw [← IsHermitian.spectral_theorem'' hQ]

theorem _root_.Matrix.PosSemidef.rpow_one_eq_self {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) :
    hQ.rpow 1 = Q :=
  hQ.1.rpow_one_eq_self

theorem _root_.Matrix.PosDef.rpow_one_eq_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow 1 = Q :=
  hQ.1.rpow_one_eq_self

@[reducible, instance]
noncomputable def _root_.Matrix.PosDef.eigenvaluesInvertible {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) :
    Invertible (IsHermitian.eigenvalues hQ.1) := by
  use (IsHermitian.eigenvalues hQ.1)⁻¹
  · ext i
    simp_rw [Pi.mul_apply, Pi.inv_apply]
    simp_rw [inv_mul_cancel₀ (NeZero.of_pos (hQ.pos_eigenvalues i)).out]
    rfl
  · ext i
    simp_rw [Pi.mul_apply, Pi.inv_apply]
    simp_rw [mul_inv_cancel₀ (NeZero.of_pos (hQ.pos_eigenvalues i)).out]
    rfl

@[reducible, instance]
noncomputable def _root_.Matrix.PosDef.eigenvaluesInvertible' {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) :
    Invertible (RCLike.ofReal ∘ (IsHermitian.eigenvalues hQ.1) : n → 𝕜) := by
  letI := hQ.eigenvaluesInvertible
  use (RCLike.ofReal ∘ (IsHermitian.eigenvalues hQ.1)⁻¹ : n → 𝕜)
  · ext i
    simp only [Pi.mul_def, Function.comp_apply, ← RCLike.ofReal_mul, Pi.inv_def,
      inv_mul_cancel_of_invertible, RCLike.ofReal_one, Pi.one_def]
  · ext i
    simp only [Pi.mul_def, Function.comp_apply, ← RCLike.ofReal_mul, Pi.inv_def,
      mul_inv_cancel_of_invertible, RCLike.ofReal_one, Pi.one_def]

theorem _root_.Matrix.PosDef.rpow_neg_one_eq_inv_self {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) :
    hQ.rpow (-1) = Q⁻¹ := by
  simp_rw [Matrix.PosDef.rpow]
  symm
  nth_rw 1 [IsHermitian.spectral_theorem'' hQ.1]
  simp_rw [innerAut.map_inv, IsHermitian.rpow, Pi.pow_def, Real.rpow_neg_one,
    Matrix.inv_diagonal]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Function.comp_apply]
  intro i
  letI := hQ.eigenvaluesInvertible'
  simp_rw [Ring.inverse_invertible]
  rfl

theorem _root_.Matrix.IsHermitian.rpow_zero {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    hQ.rpow 0 = 1 := by
  rw [IsHermitian.rpow, innerAut_eq_iff, innerAut_apply_one]
  ext i j
  by_cases h : i = j <;> simp [diagonal, h, Matrix.one_apply]

theorem _root_.Matrix.PosSemidef.rpow_zero {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    hQ.rpow 0 = 1 :=
  hQ.1.rpow_zero

theorem _root_.Matrix.PosDef.rpow_zero {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow 0 = 1 :=
  hQ.1.rpow_zero

theorem _root_.Matrix.IsHermitian.rpow.isHermitian {Q : Matrix n n 𝕜}
    (hQ : Q.IsHermitian) (r : ℝ) :
    (hQ.rpow r).IsHermitian := by
  rw [IsHermitian.rpow, ← innerAut_isHermitian_iff, isHermitian_diagonal_iff]
  simp only [Function.comp_apply, Pi.pow_apply, _root_.IsSelfAdjoint, RCLike.star_def,
    RCLike.conj_ofReal, implies_true]

theorem _root_.Matrix.PosSemidef.rpow.isPosSemidef {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (r : ℝ) :
    (hQ.rpow r).PosSemidef := by
  rw [Matrix.PosSemidef.rpow, IsHermitian.rpow, innerAut_posSemidef_iff,
    Matrix.PosSemidef.diagonal_iff]
  simp only [Function.comp_apply, RCLike.zero_le_real, Pi.pow_apply]
  exact fun i => Real.rpow_nonneg (PosSemidef.eigenvalues_nonneg hQ i) r

theorem _root_.Matrix.PosDef.rpow.isPosDef {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) (r : ℝ) :
    (hQ.rpow r).PosDef := by
  rw [Matrix.PosDef.rpow_eq, innerAut_posDef_iff, Matrix.PosDef.diagonal_iff]
  simp only [Function.comp_apply, RCLike.zero_lt_real, Pi.pow_apply]
  exact fun i => Real.rpow_pos_of_pos (PosDef.pos_eigenvalues hQ i) r

theorem _root_.Matrix.PosSemidef.sqrt_eq_rpow {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) :
    CFC.sqrt Q = hQ.rpow (1 / 2) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ Q, hQ.1.cfc_eq]
  simp only [Real.coe_sqrt, Real.coe_toNNReal', one_div]
  have hdiag :
      (diagonal (RCLike.ofReal ∘ (fun x => Real.sqrt (max x 0)) ∘ hQ.1.eigenvalues) :
        Matrix n n 𝕜) =
        diagonal (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ ((2 : ℝ)⁻¹))) := by
    ext i j
    by_cases hij : i = j <;> simp [diagonal, hij, Real.sqrt_eq_rpow,
      max_eq_left (hQ.eigenvalues_nonneg j)]
  simp [PosSemidef.rpow, IsHermitian.rpow, IsHermitian.cfc, hdiag]

theorem _root_.Matrix.PosDef.sqrt_eq_rpow {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    CFC.sqrt Q = hQ.rpow (1 / 2) :=
  hQ.posSemidef.sqrt_eq_rpow

theorem _root_.Matrix.PosDef.rpow_ne_zero [Nonempty n] {Q : Matrix n n ℂ}
    (hQ : Q.PosDef) {r : ℝ} :
    hQ.rpow r ≠ 0 := by
  simp_rw [Matrix.PosDef.rpow_eq, ne_eq, innerAut_eq_iff, innerAut_apply_zero,
    ← Matrix.ext_iff, Matrix.diagonal, Matrix.zero_apply, of_apply,
    ite_eq_right_iff, Function.comp_apply, RCLike.ofReal_eq_zero, Pi.pow_apply,
    Real.rpow_eq_zero_iff_of_nonneg (le_of_lt (hQ.pos_eigenvalues _)),
    (NeZero.of_pos (hQ.pos_eigenvalues _)).out, false_and, imp_false,
    Classical.not_forall, Classical.not_not, exists_eq', exists_const]

lemma _root_.Matrix.IsHermitian.rpow_cast {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (r : ℝ)
    {S : Matrix n n 𝕜} (hQS : Q = S) :
    hQ.rpow r = (by rw [← hQS]; exact hQ : IsHermitian S).rpow r := by
  aesop

lemma _root_.Matrix.PosDef.rpow_cast {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ)
    {S : Matrix n n 𝕜} (hQS : Q = S) :
    hQ.rpow r = (by rw [← hQS]; exact hQ : PosDef S).rpow r :=
  Matrix.IsHermitian.rpow_cast _ _ hQS

lemma _root_.Matrix.PosSemidef.rpow_cast {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (r : ℝ)
    {S : Matrix n n 𝕜} (hQS : Q = S) :
    hQ.rpow r = (by rw [← hQS]; exact hQ : PosSemidef S).rpow r :=
  Matrix.IsHermitian.rpow_cast _ _ hQS

theorem _root_.Matrix.posDefOne_rpow (n : Type _) [Fintype n] [DecidableEq n] (r : ℝ) :
    (posDefOne : PosDef (1 : Matrix n n 𝕜)).rpow r = 1 := by
  let hQ : PosDef (1 : Matrix n n 𝕜) := posDefOne
  have heig : hQ.1.eigenvalues = fun _ => 1 := by
    ext i
    rw [hQ.1.eigenvalues_eq i, one_mulVec]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    rw [inner_self_eq_norm_sq_to_K, hQ.1.eigenvectorBasis.orthonormal.norm_eq_one]
    simp
  rw [PosDef.rpow_eq]
  rw [heig]
  simp_rw [Pi.pow_def, Real.one_rpow]
  have hdiag : (diagonal (RCLike.ofReal ∘ fun _ : n => (1 : ℝ)) : Matrix n n 𝕜) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [diagonal, hij, Matrix.one_apply]
  rw [hdiag, innerAut_apply_one]

end Matrix

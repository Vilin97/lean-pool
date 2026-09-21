/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.Basic

/-!
# Local block energy: pointwise algebra

Pointwise (single-matrix) inequalities feeding the local-energy estimate of
`p.local.block.energy` (the high-moment paper (Armstrong–Kuusi–Loher, in
preparation), §3.4).  Everything here is elementary linear algebra on
`Vec d = Fin d → ℝ`;
no `EuclideanSpace`.

The central tool is the *Young inequality in the `s`-metric*
(`symmForm_young`): for the symmetric part `s = symmPart A` of an elliptic
matrix and `t > 0`,

`ξ · V ≤ (2t)⁻¹ (ξ · s⁻¹ ξ) + (t/2) (V · s V)`,

with no square roots.  Combined with the coefficient bounds
`q · s⁻¹ q ≤ |q|²`, `(a p) · s⁻¹ (a p) ≤ Θ |p|²`, and the flux corollary
`‖a e‖² ≤ 2Θ (e · s e)` this drives the bulk and cutoff estimates.
-/

namespace Homogenization

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## The symmetric form is nonnegative and equals the full quadratic form -/

/-- `V · a V = V · s V`: the skew part drops out of the diagonal quadratic form. -/
theorem vecDot_matVecMul_eq_symmPart (A : Mat d) (V : Vec d) :
    vecDot V (matVecMul A V) = vecDot V (matVecMul (symmPart A) V) :=
  (vecDot_matVecMul_symmPart A V).symm

/-- Nonnegativity of the `s`-form for an elliptic matrix. -/
theorem vecDot_matVecMul_symmPart_nonneg {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (V : Vec d) :
    0 ≤ vecDot V (matVecMul (symmPart A) V) :=
  le_trans (by simpa using vecNormSq_nonneg V)
    (lowerBound_symmPart_of_isEllipticMatrix hA V)

/-! ## The Young inequality in the `s`-metric -/

/-- **`s`-metric Young.**  For the symmetric part `s = symmPart A` of a
`(1, Θ)`-elliptic matrix and any `t > 0`,
`ξ · V ≤ (2t)⁻¹ (ξ · s⁻¹ ξ) + (t/2) (V · s V)`. -/
theorem symmForm_young {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A)
    {t : ℝ} (ht : 0 < t) (ξ V : Vec d) :
    vecDot ξ V ≤ (2 * t)⁻¹ * vecDot ξ (matVecMul ((symmPart A)⁻¹) ξ)
      + (t / 2) * vecDot V (matVecMul (symmPart A) V) := by
  set s := symmPart A with hs
  have hsdet : IsUnit s.det :=
    (Matrix.isUnit_iff_isUnit_det (A := s)).mp (isUnit_symmPart_of_isEllipticMatrix hA)
  set a := matVecMul s⁻¹ ξ with ha
  have hsa : matVecMul s a = ξ := by
    rw [ha, matVecMul_mul, Matrix.mul_nonsing_inv _ hsdet, matVecMul_one]
  -- ξ · V = a · s V
  have hxV : vecDot a (matVecMul s V) = vecDot ξ V := by
    have := vecDot_matVecMul_transpose a V s
    rw [matTranspose_symmPart] at this
    rw [this, hsa]
  -- a · ξ = ξ · s⁻¹ ξ
  have hxinv : vecDot a ξ = vecDot ξ (matVecMul s⁻¹ ξ) := by
    rw [ha, vecDot_comm]
  have eVξ : vecDot V ξ = vecDot ξ V := vecDot_comm V ξ
  -- PSD of the perturbation
  set W : Vec d := t • V - a with hW
  have hWpsd : 0 ≤ vecDot W (matVecMul s W) :=
    vecDot_matVecMul_symmPart_nonneg hA W
  have hsW : matVecMul s W = t • matVecMul s V - ξ := by
    rw [hW, sub_eq_add_neg, matVecMul_add, matVecMul_neg, matVecMul_smul, hsa,
      ← sub_eq_add_neg]
  have hexpand :
      vecDot W (matVecMul s W) =
        t ^ 2 * vecDot V (matVecMul s V) - 2 * t * vecDot ξ V
          + vecDot ξ (matVecMul s⁻¹ ξ) := by
    rw [hsW, hW]
    simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right, vecDot_smul_left,
      vecDot_smul_right, vecDot_neg_left, vecDot_neg_right]
    rw [hxV, eVξ, hxinv]
    ring
  rw [hexpand] at hWpsd
  -- clear the denominator
  set B := vecDot ξ (matVecMul s⁻¹ ξ) with hB
  set C := vecDot V (matVecMul s V) with hC
  set X := vecDot ξ V with hX
  have hkey : 2 * t * X ≤ B + t ^ 2 * C := by nlinarith [hWpsd]
  have he : (2 * t)⁻¹ * B + t / 2 * C = (2 * t)⁻¹ * (B + t ^ 2 * C) := by
    field_simp
  rw [he]
  calc X = (2 * t)⁻¹ * (2 * t * X) := by field_simp
    _ ≤ (2 * t)⁻¹ * (B + t ^ 2 * C) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-! ## Coefficient bounds in the `s⁻¹`-metric -/

/-- `q · s⁻¹ q ≤ |q|²`. -/
theorem symmPartInv_quadratic_le_normSq {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (q : Vec d) :
    vecDot q (matVecMul ((symmPart A)⁻¹) q) ≤ vecNormSq q := by
  simpa using symmPart_inv_upperBound_of_isEllipticMatrix hA q

/-- `(a p) · s⁻¹ (a p) ≤ Θ |p|²`. -/
theorem symmPartInv_image_le {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (p : Vec d) :
    vecDot (matVecMul A p) (matVecMul ((symmPart A)⁻¹) (matVecMul A p)) ≤
      Θ * vecNormSq p :=
  image_symmPartInv_le hA p

/-- `(aᵀ p) · s⁻¹ (aᵀ p) ≤ Θ |p|²`, using `symmPart Aᵀ = symmPart A`. -/
theorem symmPartInv_imageTranspose_le {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (p : Vec d) :
    vecDot (matVecMul (matTranspose A) p)
        (matVecMul ((symmPart A)⁻¹) (matVecMul (matTranspose A) p)) ≤
      Θ * vecNormSq p := by
  have hAT : IsThetaElliptic Θ (matTranspose A) := isEllipticMatrix_transpose hA
  have h := image_symmPartInv_le hAT p
  rwa [symmPart_matTranspose] at h

/-! ## The bulk coefficient vectors -/

/-- `(q − ½ a p) · s⁻¹ (q − ½ a p) ≤ 2 (Θ|p|² + |q|²)`. -/
theorem symmPartInv_bulkV_le {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (p q : Vec d) :
    vecDot (q - (1 / 2 : ℝ) • matVecMul A p)
        (matVecMul ((symmPart A)⁻¹) (q - (1 / 2 : ℝ) • matVecMul A p)) ≤
      2 * (Θ * vecNormSq p + vecNormSq q) := by
  have hN : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul ((symmPart A)⁻¹) x) :=
    fun x => symmPart_inv_nonneg_of_isEllipticMatrix hA x
  have hpar := vecDot_matVecMul_sub_le_two hN q ((1 / 2 : ℝ) • matVecMul A p)
  have hq := symmPartInv_quadratic_le_normSq hA q
  have hap := symmPartInv_image_le hA p
  -- b · s⁻¹ b with b = ½ (a p)
  have hb : vecDot ((1 / 2 : ℝ) • matVecMul A p)
      (matVecMul ((symmPart A)⁻¹) ((1 / 2 : ℝ) • matVecMul A p)) =
        (1 / 4 : ℝ) * vecDot (matVecMul A p)
          (matVecMul ((symmPart A)⁻¹) (matVecMul A p)) := by
    rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    ring
  rw [hb] at hpar
  have hΘ : (0 : ℝ) ≤ Θ := le_trans zero_le_one hA.2.1
  nlinarith [hpar, hq, hap, vecNormSq_nonneg p, mul_nonneg hΘ (vecNormSq_nonneg p)]

/-- `(½ aᵀ p) · s⁻¹ (½ aᵀ p) ≤ Θ|p|² + |q|²`. -/
theorem symmPartInv_bulkVstar_le {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (p q : Vec d) :
    vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose A) p)
        (matVecMul ((symmPart A)⁻¹) ((1 / 2 : ℝ) • matVecMul (matTranspose A) p)) ≤
      Θ * vecNormSq p + vecNormSq q := by
  have haTp := symmPartInv_imageTranspose_le hA p
  have hval : vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose A) p)
      (matVecMul ((symmPart A)⁻¹) ((1 / 2 : ℝ) • matVecMul (matTranspose A) p)) =
        (1 / 4 : ℝ) * vecDot (matVecMul (matTranspose A) p)
          (matVecMul ((symmPart A)⁻¹) (matVecMul (matTranspose A) p)) := by
    rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    ring
  rw [hval]
  have hΘ : (0 : ℝ) ≤ Θ := le_trans zero_le_one hA.2.1
  nlinarith [haTp, vecNormSq_nonneg p, vecNormSq_nonneg q, mul_nonneg hΘ (vecNormSq_nonneg p)]

/-! ## The flux corollary `‖a e‖² ≤ 2Θ (e · s e)` -/

/-- `‖a e‖² ≤ 2Θ (e · s e)`. -/
theorem vecNormSq_image_le {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (e : Vec d) :
    vecNormSq (matVecMul A e) ≤ 2 * Θ * vecDot e (matVecMul (symmPart A) e) := by
  have h := vecNormSq_image_add_transpose_le_of_isThetaElliptic hA e
  nlinarith [h, vecNormSq_nonneg (matVecMul (matTranspose A) e)]

/-- `‖aᵀ e‖² ≤ 2Θ (e · s e)`. -/
theorem vecNormSq_imageTranspose_le {Θ : ℝ} {A : Mat d}
    (hA : IsThetaElliptic Θ A) (e : Vec d) :
    vecNormSq (matVecMul (matTranspose A) e) ≤
      2 * Θ * vecDot e (matVecMul (symmPart A) e) := by
  have h := vecNormSq_image_add_transpose_le_of_isThetaElliptic hA e
  nlinarith [h, vecNormSq_nonneg (matVecMul A e)]

/-! ## An AM-GM helper with square roots -/

/-- `2 √A √B ≤ t A + t⁻¹ B` for `A, B ≥ 0` and `t > 0`. -/
theorem two_mul_sqrt_mul_sqrt_le {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 < t) :
    2 * Real.sqrt A * Real.sqrt B ≤ t * A + t⁻¹ * B := by
  have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsqB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hnn : 0 ≤ (Real.sqrt t * Real.sqrt A - Real.sqrt t⁻¹ * Real.sqrt B) ^ 2 :=
    sq_nonneg _
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hsti : Real.sqrt t⁻¹ ^ 2 = t⁻¹ := Real.sq_sqrt (by positivity)
  have hcross : Real.sqrt t * Real.sqrt t⁻¹ = 1 := by
    rw [← Real.sqrt_mul ht.le, mul_inv_cancel₀ ht.ne', Real.sqrt_one]
  have hexp : (Real.sqrt t * Real.sqrt A - Real.sqrt t⁻¹ * Real.sqrt B) ^ 2 =
      t * A - 2 * (Real.sqrt A * Real.sqrt B) + t⁻¹ * B := by
    have hrw : (Real.sqrt t * Real.sqrt A - Real.sqrt t⁻¹ * Real.sqrt B) ^ 2 =
        Real.sqrt t ^ 2 * Real.sqrt A ^ 2
          - 2 * (Real.sqrt t * Real.sqrt t⁻¹) * (Real.sqrt A * Real.sqrt B)
          + Real.sqrt t⁻¹ ^ 2 * Real.sqrt B ^ 2 := by ring
    rw [hrw, hst, hsqA, hsti, hsqB, hcross]; ring
  rw [hexp] at hnn
  nlinarith [hnn]

end

end Homogenization

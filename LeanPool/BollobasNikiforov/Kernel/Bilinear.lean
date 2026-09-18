/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.Kernel.Data
import LeanPool.BollobasNikiforov.Kernel.SM
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Bilinear expansion of `𝒦`

Completing squares in coordinates `2,1,0` yields `eq:bilinear`, and
substituting `U` yields the factorization `eq:factor` of `docs/sol.tex` §3.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix
open scoped Matrix

noncomputable section

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-! ### Fin 3 expansions -/

lemma mulVec_fin3 (M : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) (i : Fin 3) :
    (M *ᵥ z) i = M i 0 * z 0 + M i 1 * z 1 + M i 2 * z 2 := by
  simp [mulVec, dotProduct, Fin.sum_univ_three]

lemma dotProduct_mulVec_fin3 (M : Matrix (Fin 3) (Fin 3) ℝ) (z w : Fin 3 → ℝ) :
    z ⬝ᵥ M *ᵥ w =
      z 0 * (M 0 0 * w 0 + M 0 1 * w 1 + M 0 2 * w 2) +
      z 1 * (M 1 0 * w 0 + M 1 1 * w 1 + M 1 2 * w 2) +
      z 2 * (M 2 0 * w 0 + M 2 1 * w 1 + M 2 2 * w 2) := by
  simp [dotProduct, mulVec_fin3, Fin.sum_univ_three]

/-- Completing the square in coordinate `2` for a real symmetric `3×3` form. -/
lemma bilinear_complete_last (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsHermitian)
    (z w : Fin 3 → ℝ) (h22 : M 2 2 ≠ 0) :
    z ⬝ᵥ M *ᵥ w =
      (M *ᵥ z) 2 * (M *ᵥ w) 2 / M 2 2 +
      z 0 * w 0 * (M 0 0 - M 0 2 * M 2 0 / M 2 2) +
      z 0 * w 1 * (M 0 1 - M 0 2 * M 2 1 / M 2 2) +
      z 1 * w 0 * (M 1 0 - M 1 2 * M 2 0 / M 2 2) +
      z 1 * w 1 * (M 1 1 - M 1 2 * M 2 1 / M 2 2) := by
  have hsym (i j : Fin 3) : M i j = M j i := by
    simpa using (hM.apply i j).symm
  field_simp [h22]
  simp only [mulVec_fin3, dotProduct_mulVec_fin3]
  rw [hsym 0 2, hsym 1 2, hsym 0 1]
  ring

/-! ### KR08: pivot `𝒦 2 2` -/

lemma inv_𝒜_two_two (hq : ∀ i, 0 < q i) :
    (𝒜 t q)⁻¹ 2 2 = D2 t q / Δ t q := by
  have hΔ : Δ t q ≠ 0 := (Δ_pos t q hq).ne'
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul, Δ]
  have hadj : (𝒜 t q).adjugate 2 2 = D2 t q := by
    rw [adjugate_fin_three]
    simp [𝒜_00, 𝒜_11, 𝒜_01, 𝒜_10, D2]
    ring_nf
    rw [hsq]
    ring
  rw [hadj]
  field_simp [hΔ]

lemma 𝒦_two_two (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    𝒦 t q γ 2 2 = D2 t q / Δ t q := by
  have he : Pi.single 0 (1 : ℝ) ⬝ᵥ Pi.single (2 : Fin 3) 1 = 0 := by simp
  have hvec :
      𝒦 t q γ *ᵥ Pi.single (2 : Fin 3) 1 =
        (𝒜 t q)⁻¹ *ᵥ Pi.single (2 : Fin 3) 1 := by
    rw [𝒦_shermanMorrison t q γ hq hγ, sub_mulVec, smul_mulVec, mulVec_vecMulVec_self]
    simp [he]
  calc
    𝒦 t q γ 2 2
        = (𝒦 t q γ *ᵥ Pi.single (2 : Fin 3) 1) 2 := by
          rw [mulVec_single_one, col_apply]
    _ = ((𝒜 t q)⁻¹ *ᵥ Pi.single (2 : Fin 3) 1) 2 :=
          congrArg (fun v : Fin 3 → ℝ ↦ v 2) hvec
    _ = (𝒜 t q)⁻¹ 2 2 := by
          rw [mulVec_single_one, col_apply]
    _ = D2 t q / Δ t q := inv_𝒜_two_two t q hq

/-! ### Leading `2×2` block of `𝒜` -/

lemma leading2_𝒜_inv_one_one (hq : ∀ i, 0 < q i) :
    ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 1 = a0 t q / D2 t q := by
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [← D2_eq_det_leading, adjugate_fin_two]
  simp [submatrix_apply, 𝒜_00]
  field_simp [hD]

lemma leading2_𝒜_inv_one_zero (hq : ∀ i, 0 < q i) :
    ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 0 =
      Real.sqrt 2 * m t q 1 / D2 t q := by
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [← D2_eq_det_leading, adjugate_fin_two]
  simp [submatrix_apply, 𝒜_10]
  field_simp [hD]

/-- The `{0,1}` Schur complement of `𝒜⁻¹` is `(𝒜[{0,1}])⁻¹`. -/
lemma leading2_mul_schur_inv_𝒜 (hq : ∀ i, 0 < q i) :
    (𝒜 t q).submatrix Fin.castSucc Fin.castSucc *
        Matrix.of (fun i j : Fin 2 ↦
          (𝒜 t q)⁻¹ i.castSucc j.castSucc -
            (𝒜 t q)⁻¹ i.castSucc 2 * (𝒜 t q)⁻¹ 2 j.castSucc /
              (𝒜 t q)⁻¹ 2 2) =
      1 := by
  have h22 : (𝒜 t q)⁻¹ 2 2 ≠ 0 := by
    rw [inv_𝒜_two_two t q hq]
    exact div_ne_zero (D2_pos t q hq).ne' (Δ_pos t q hq).ne'
  have hAA : 𝒜 t q * (𝒜 t q)⁻¹ = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (𝒜_isUnit t q hq))
  ext i j
  have hi : (i.castSucc : Fin 3) ≠ 2 := by
    fin_cases i <;> decide
  have hrow (k : Fin 3) :
      𝒜 t q i.castSucc 0 * (𝒜 t q)⁻¹ 0 k + 𝒜 t q i.castSucc 1 * (𝒜 t q)⁻¹ 1 k =
        (if i.castSucc = k then (1 : ℝ) else 0) - 𝒜 t q i.castSucc 2 * (𝒜 t q)⁻¹ 2 k := by
    have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M i.castSucc k) hAA
    simp only [mul_apply, one_apply, Fin.sum_univ_three] at hentry
    linarith
  have hR := hrow j.castSucc
  have h2 := hrow 2
  simp only [hi, ↓reduceIte] at h2
  have hgoal :
      𝒜 t q i.castSucc 0 *
          ((𝒜 t q)⁻¹ 0 j.castSucc -
            (𝒜 t q)⁻¹ 0 2 * (𝒜 t q)⁻¹ 2 j.castSucc / (𝒜 t q)⁻¹ 2 2) +
        𝒜 t q i.castSucc 1 *
          ((𝒜 t q)⁻¹ 1 j.castSucc -
            (𝒜 t q)⁻¹ 1 2 * (𝒜 t q)⁻¹ 2 j.castSucc / (𝒜 t q)⁻¹ 2 2) =
        if i.castSucc = j.castSucc then (1 : ℝ) else 0 := by
    have hexpand :
        𝒜 t q i.castSucc 0 *
            ((𝒜 t q)⁻¹ 0 j.castSucc -
              (𝒜 t q)⁻¹ 0 2 * (𝒜 t q)⁻¹ 2 j.castSucc / (𝒜 t q)⁻¹ 2 2) +
          𝒜 t q i.castSucc 1 *
            ((𝒜 t q)⁻¹ 1 j.castSucc -
              (𝒜 t q)⁻¹ 1 2 * (𝒜 t q)⁻¹ 2 j.castSucc / (𝒜 t q)⁻¹ 2 2) =
        (𝒜 t q i.castSucc 0 * (𝒜 t q)⁻¹ 0 j.castSucc +
          𝒜 t q i.castSucc 1 * (𝒜 t q)⁻¹ 1 j.castSucc) -
        (𝒜 t q i.castSucc 0 * (𝒜 t q)⁻¹ 0 2 +
          𝒜 t q i.castSucc 1 * (𝒜 t q)⁻¹ 1 2) *
          (𝒜 t q)⁻¹ 2 j.castSucc / (𝒜 t q)⁻¹ 2 2 := by
      ring
    rw [hexpand, hR, h2]
    field_simp [h22]
    ring
  simp only [mul_apply, one_apply, Fin.sum_univ_two, submatrix_apply, of_apply,
    Fin.castSucc_zero]
  have c1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := rfl
  simp only [c1]
  simpa [Fin.castSucc_inj] using hgoal

lemma schur_inv_𝒜 (hq : ∀ i, 0 < q i) (i j : Fin 2) :
    (𝒜 t q)⁻¹ i.castSucc j.castSucc -
        (𝒜 t q)⁻¹ i.castSucc 2 * (𝒜 t q)⁻¹ 2 j.castSucc / (𝒜 t q)⁻¹ 2 2 =
      ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ i j := by
  have hPS := leading2_mul_schur_inv_𝒜 t q hq
  rw [inv_eq_right_inv hPS, of_apply]

/-! ### KR09: `{0,1}` block of `𝒦⁻¹ = 𝒦Mat` -/

lemma Vvec_one : Vvec t q 1 = -Real.sqrt 2 * m t q 1 := by
  rw [Vvec, mulVec_single_one, col_apply, 𝒜_10]

lemma 𝒦Mat_zero_zero (γ : ℝ) (hγ : 0 < γ) :
    𝒦Mat t q γ 0 0 = a0 t q * (γ + a0 t q) / γ := by
  unfold 𝒦Mat
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, 𝒜_00, Vvec_zero, smul_eq_mul]
  field_simp [hγ.ne']

lemma 𝒦Mat_one_zero (γ : ℝ) (hγ : 0 < γ) :
    𝒦Mat t q γ 1 0 = -Real.sqrt 2 * m t q 1 * (γ + a0 t q) / γ := by
  unfold 𝒦Mat
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, 𝒜_10, Vvec_one, Vvec_zero,
    smul_eq_mul]
  field_simp [hγ.ne']
  ring

lemma 𝒦Mat_zero_one (γ : ℝ) (hγ : 0 < γ) :
    𝒦Mat t q γ 0 1 = -Real.sqrt 2 * m t q 1 * (γ + a0 t q) / γ := by
  unfold 𝒦Mat
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, 𝒜_01, Vvec_one, Vvec_zero,
    smul_eq_mul]
  field_simp [hγ.ne']
  ring

lemma 𝒦Mat_one_one (γ : ℝ) (hγ : 0 < γ) :
    𝒦Mat t q γ 1 1 = 1 + 2 * m t q 2 + 2 * m t q 1 ^ 2 / γ := by
  unfold 𝒦Mat
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, 𝒜_11, Vvec_one, smul_eq_mul]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hγ.ne']
  rw [hsq]

lemma 𝒦Mat01_det (γ : ℝ) (_hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    ((𝒦Mat t q γ).submatrix Fin.castSucc Fin.castSucc).det =
      D2 t q * (γ + a0 t q) / γ := by
  rw [det_fin_two]
  simp only [submatrix_apply, Fin.castSucc_zero]
  have c1 : Fin.castSucc (1 : Fin 2) = 1 := rfl
  simp only [c1, 𝒦Mat_zero_zero t q γ hγ, 𝒦Mat_one_one t q γ hγ, 𝒦Mat_zero_one t q γ hγ,
    𝒦Mat_one_zero t q γ hγ]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hγ.ne']
  rw [hsq]
  simp [D2, a0]
  ring

lemma 𝒦Mat01_inv_one_one (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    ((𝒦Mat t q γ).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 1 = a0 t q / D2 t q := by
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [𝒦Mat01_det t q γ hq hγ, adjugate_fin_two]
  simp [submatrix_apply, 𝒦Mat_zero_zero t q γ hγ]
  field_simp [hD, hγ.ne', hγa]

lemma 𝒦Mat01_inv_one_zero (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    ((𝒦Mat t q γ).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 0 =
      Real.sqrt 2 * m t q 1 / D2 t q := by
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [𝒦Mat01_det t q γ hq hγ, adjugate_fin_two]
  simp [submatrix_apply, 𝒦Mat_one_zero t q γ hγ]
  field_simp [hD, hγ.ne', hγa]

lemma 𝒦Mat01_inv_ratio (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    ((𝒦Mat t q γ).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 0 /
        ((𝒦Mat t q γ).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 1 =
      Real.sqrt 2 * m t q 1 / a0 t q := by
  rw [𝒦Mat01_inv_one_zero t q γ hq hγ, 𝒦Mat01_inv_one_one t q γ hq hγ]
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  have ha : a0 t q ≠ 0 := (a0_pos t q hq).ne'
  field_simp [hD, ha]

/-! ### KR10: last pivot -/

lemma inv_𝒦Mat_zero_zero (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    1 / 𝒦Mat t q γ 0 0 = γ / (a0 t q * (γ + a0 t q)) := by
  rw [𝒦Mat_zero_zero t q γ hγ]
  have ha : a0 t q ≠ 0 := (a0_pos t q hq).ne'
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  field_simp [hγ.ne', ha, hγa]

/-! ### Inverse bilinear form of `𝒜` -/

lemma inv_𝒜_isHermitian (hq : ∀ i, 0 < q i) : ((𝒜 t q)⁻¹).IsHermitian :=
  (𝒜_posDef t q hq).isHermitian.inv

lemma leading2_inv_bilinear (hq : ∀ i, 0 < q i) (z0 z1 w0 w1 : ℝ) :
    z0 * w0 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 0 +
      z0 * w1 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 1 +
      z1 * w0 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 0 +
      z1 * w1 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 1 =
      (a0 t q * z1 + Real.sqrt 2 * m t q 1 * z0) *
          (a0 t q * w1 + Real.sqrt 2 * m t q 1 * w0) / (a0 t q * D2 t q) +
        z0 * w0 / a0 t q := by
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  have ha : a0 t q ≠ 0 := (a0_pos t q hq).ne'
  have h11 := leading2_𝒜_inv_one_one t q hq
  have h10 := leading2_𝒜_inv_one_zero t q hq
  have h01 : ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 1 =
      Real.sqrt 2 * m t q 1 / D2 t q := by
    have hH : (((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹).IsHermitian :=
      ((𝒜_posDef t q hq).submatrix (Fin.castSucc_injective 2)).isHermitian.inv
    have hsym := hH.apply 0 1
    simp only [star_trivial] at hsym
    rw [← hsym, h10]
  have h00 : ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 0 =
      (1 + 2 * m t q 2) / D2 t q := by
    rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
    rw [← D2_eq_det_leading, adjugate_fin_two]
    simp [submatrix_apply, 𝒜_11]
    field_simp [hD]
  rw [h00, h01, h10, h11]
  field_simp [hD, ha]
  ring_nf
  simp [D2]
  ring

lemma dotProduct_inv_𝒜 (hq : ∀ i, 0 < q i) (z w : Fin 3 → ℝ) :
    z ⬝ᵥ (𝒜 t q)⁻¹ *ᵥ w =
      Δ t q * ((𝒜 t q)⁻¹ *ᵥ z) 2 * (Δ t q * ((𝒜 t q)⁻¹ *ᵥ w) 2) / (Δ t q * D2 t q) +
        (a0 t q * z 1 + Real.sqrt 2 * m t q 1 * z 0) *
            (a0 t q * w 1 + Real.sqrt 2 * m t q 1 * w 0) / (a0 t q * D2 t q) +
          z 0 * w 0 / a0 t q := by
  have h22 : (𝒜 t q)⁻¹ 2 2 ≠ 0 := by
    rw [inv_𝒜_two_two t q hq]
    exact div_ne_zero (D2_pos t q hq).ne' (Δ_pos t q hq).ne'
  have hΔ : Δ t q ≠ 0 := (Δ_pos t q hq).ne'
  have hD : D2 t q ≠ 0 := (D2_pos t q hq).ne'
  rw [bilinear_complete_last _ (inv_𝒜_isHermitian t q hq) z w h22]
  have h00 := schur_inv_𝒜 t q hq 0 0
  have h01 := schur_inv_𝒜 t q hq 0 1
  have h10 := schur_inv_𝒜 t q hq 1 0
  have h11 := schur_inv_𝒜 t q hq 1 1
  simp only [Fin.castSucc_zero] at h00 h01 h10 h11
  have c1 : Fin.castSucc (1 : Fin 2) = 1 := rfl
  simp only [c1] at h00 h01 h10 h11
  rw [h00, h01, h10, h11]
  have hreassoc :
      ((𝒜 t q)⁻¹ *ᵥ z) 2 * ((𝒜 t q)⁻¹ *ᵥ w) 2 / (𝒜 t q)⁻¹ 2 2 +
          z 0 * w 0 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 0 +
          z 0 * w 1 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 1 +
          z 1 * w 0 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 0 +
          z 1 * w 1 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 1 =
      ((𝒜 t q)⁻¹ *ᵥ z) 2 * ((𝒜 t q)⁻¹ *ᵥ w) 2 / (𝒜 t q)⁻¹ 2 2 +
        (z 0 * w 0 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 0 +
          z 0 * w 1 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 0 1 +
          z 1 * w 0 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 0 +
          z 1 * w 1 * ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc)⁻¹ 1 1) := by
    ring
  rw [hreassoc, leading2_inv_bilinear t q hq (z 0) (z 1) (w 0) (w 1)]
  have hfirst (u v : ℝ) :
      u * v / (𝒜 t q)⁻¹ 2 2 =
        Δ t q * u * (Δ t q * v) / (Δ t q * D2 t q) := by
    have hp := inv_𝒜_two_two t q hq
    rw [hp]
    field_simp [hΔ, hD]
  rw [hfirst (((𝒜 t q)⁻¹ *ᵥ z) 2) (((𝒜 t q)⁻¹ *ᵥ w) 2)]
  ring

/-! ### KR11: `eq:bilinear` -/

lemma dotProduct_𝒦_eq_inv_𝒜 (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ)
    (z w : Fin 3 → ℝ) :
    z ⬝ᵥ 𝒦 t q γ *ᵥ w =
      z ⬝ᵥ (𝒜 t q)⁻¹ *ᵥ w - z 0 * w 0 / (γ + a0 t q) := by
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  rw [𝒦_shermanMorrison t q γ hq hγ]
  rw [sub_mulVec, smul_mulVec, mulVec_vecMulVec_self, dotProduct_sub, dotProduct_smul]
  simp [single_dotProduct, smul_eq_mul]
  field_simp [hγa]

lemma 𝒦_bilinear (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) (z w : Fin 3 → ℝ) :
    z ⬝ᵥ 𝒦 t q γ *ᵥ w =
      Δ t q * ((𝒜 t q)⁻¹ *ᵥ z) 2 * (Δ t q * ((𝒜 t q)⁻¹ *ᵥ w) 2) / (Δ t q * D2 t q) +
        (a0 t q * z 1 + Real.sqrt 2 * m t q 1 * z 0) *
            (a0 t q * w 1 + Real.sqrt 2 * m t q 1 * w 0) / (a0 t q * D2 t q) +
          γ * z 0 * w 0 / (a0 t q * (γ + a0 t q)) := by
  have ha : a0 t q ≠ 0 := (a0_pos t q hq).ne'
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  rw [dotProduct_𝒦_eq_inv_𝒜 t q γ hq hγ z w, dotProduct_inv_𝒜 t q hq z w]
  field_simp [ha, hγa]
  ring

/-! ### KR12: substituting `U` -/

lemma bhat_zero (x : ℝ) : bhat t q x 0 = x ^ 2 + h t q x := by
  simp [bhat, b, h, Finset.sum_apply, v_zero, smul_eq_mul]

lemma bhat_one (x : ℝ) :
    bhat t q x 1 = Real.sqrt 2 * x - Real.sqrt 2 * h1 t q x := by
  simp only [bhat, b, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, v_one, smul_eq_mul]
  simp only [h1]
  calc
    Real.sqrt 2 * x + ∑ i, q i * truncSq (t i) x * (-Real.sqrt 2 * t i)
        = Real.sqrt 2 * x + ∑ i, -Real.sqrt 2 * (q i * t i * truncSq (t i) x) := by
          refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
          ring
    _ = Real.sqrt 2 * x - Real.sqrt 2 * ∑ i, q i * t i * truncSq (t i) x := by
          rw [← Finset.mul_sum]
          ring

lemma N_eq_Δ_inv_U (γ : ℝ) (hq : ∀ i, 0 < q i) (x : ℝ) :
    N t q x = Δ t q * ((𝒜 t q)⁻¹ *ᵥ U t q γ x) 2 := by
  simp only [N, U, mulVec_add, mulVec_smul]
  rw [𝒜_inv_mulVec_Vvec t q hq]
  simp

lemma U_zero (γ x : ℝ) (hγ : 0 < γ) :
    U t q γ x 0 = Z t q γ x / γ := by
  simp only [U, Z, Pi.add_apply, Pi.smul_apply, bhat_zero, Vvec_zero, smul_eq_mul]
  field_simp [hγ.ne']
  ring

lemma U_weighted (γ x : ℝ) (hγ : 0 < γ) :
    a0 t q * U t q γ x 1 + Real.sqrt 2 * m t q 1 * U t q γ x 0 =
      Real.sqrt 2 * P t q x := by
  simp only [U, P, Pi.add_apply, Pi.smul_apply, bhat_zero, bhat_one, Vvec_zero, Vvec_one,
    smul_eq_mul]
  field_simp [hγ.ne']
  ring

/-! ### KR13: `eq:factor` -/

lemma 𝒦_factor (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) (x y : ℝ) :
    U t q γ x ⬝ᵥ 𝒦 t q γ *ᵥ U t q γ y =
      N t q x * N t q y / (Δ t q * D2 t q) +
        2 * P t q x * P t q y / (a0 t q * D2 t q) +
          Z t q γ x * Z t q γ y / (γ * a0 t q * (γ + a0 t q)) := by
  have ha : a0 t q ≠ 0 := (a0_pos t q hq).ne'
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [𝒦_bilinear t q γ hq hγ (U t q γ x) (U t q γ y)]
  rw [← N_eq_Δ_inv_U t q γ hq x, ← N_eq_Δ_inv_U t q γ hq y]
  rw [U_weighted t q γ x hγ, U_weighted t q γ y hγ]
  rw [U_zero t q γ x hγ, U_zero t q γ y hγ]
  field_simp [ha, hγ0, hγa]
  rw [hsq]
  ring

end

end BollobasNikiforov

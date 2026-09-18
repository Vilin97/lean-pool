/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.Kernel.Data
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Sherman–Morrison formula for `𝒦`

The rank-one update `𝒦 = (𝒜 + VVᵀ/γ)⁻¹` expands as
`𝒜⁻¹ - e₀ e₀ᵀ / (γ + a₀)`, using `𝒜⁻¹ V = e₀` and `V 0 = a₀`.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix
open scoped Matrix

noncomputable section

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-- `a₀ = 1 + ∑ qᵢ` is positive when each `qᵢ` is. -/
lemma a0_pos (hq : ∀ i, 0 < q i) : 0 < a0 t q := by
  rw [a0, m_zero]
  have hsum : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ ↦ (hq i).le
  exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hsum)

lemma γ_add_a0_pos (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) : 0 < γ + a0 t q :=
  add_pos hγ (a0_pos t q hq)

lemma γ_add_a0_ne_zero (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) : γ + a0 t q ≠ 0 :=
  (γ_add_a0_pos t q γ hq hγ).ne'

/-- `V = 𝒜 e₀`, so the `0`-coordinate is `𝒜 0 0 = a₀`. -/
lemma Vvec_zero : Vvec t q 0 = a0 t q := by
  rw [Vvec, mulVec_single_one, col_apply, 𝒜_00]

lemma Vvec_dotProduct_single : Vvec t q ⬝ᵥ Pi.single 0 1 = a0 t q := by
  simp [dotProduct_single, Vvec_zero]

/-- `𝒜` is real symmetric. -/
lemma 𝒜_transpose (hq : ∀ i, 0 < q i) : (𝒜 t q)ᵀ = 𝒜 t q := by
  have h := (𝒜_posDef t q hq).isHermitian.eq
  ext i j
  simpa [conjTranspose_apply, transpose_apply] using congr_fun₂ h i j

/-- `Vᵀ 𝒜⁻¹ = e₀ᵀ`, equivalently `V ᵥ* 𝒜⁻¹ = e₀`. -/
lemma vecMul_inv_Vvec (hq : ∀ i, 0 < q i) :
    Vvec t q ᵥ* (𝒜 t q)⁻¹ = Pi.single 0 1 := by
  have hAT := 𝒜_transpose t q hq
  rw [show (𝒜 t q)⁻¹ = ((𝒜 t q)ᵀ)⁻¹ from congrArg (fun M ↦ M⁻¹) hAT.symm]
  rw [← transpose_nonsing_inv, vecMul_transpose, 𝒜_inv_mulVec_Vvec t q hq]

/-- Sherman–Morrison: `𝒦 = 𝒜⁻¹ - e₀ e₀ᵀ / (γ + a₀)`. -/
lemma 𝒦_shermanMorrison (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    𝒦 t q γ =
      (𝒜 t q)⁻¹ - (1 / (γ + a0 t q)) • vecMulVec (Pi.single 0 1) (Pi.single 0 1) := by
  set A := 𝒜 t q
  set V := Vvec t q
  set e : Fin 3 → ℝ := Pi.single 0 1
  set c := (1 : ℝ) / (γ + a0 t q)
  have hAdet : IsUnit A.det := (isUnit_iff_isUnit_det _).mp (𝒜_isUnit t q hq)
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hγa : γ + a0 t q ≠ 0 := γ_add_a0_ne_zero t q γ hq hγ
  have hAe : A *ᵥ e = V := rfl
  have hVA : V ᵥ* A⁻¹ = e := vecMul_inv_Vvec t q hq
  have hVe : V ⬝ᵥ e = a0 t q := Vvec_dotProduct_single t q
  have hKR :
      𝒦Mat t q γ * (A⁻¹ - c • vecMulVec e e) = 1 := by
    unfold 𝒦Mat
    change (A + (1 / γ) • vecMulVec V V) * (A⁻¹ - c • vecMulVec e e) = 1
    rw [mul_sub, add_mul, add_mul, sub_add_eq_sub_sub]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [mul_nonsing_inv _ hAdet, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul_vecMulVec]
    rw [hAe, hVA, hVe, vecMulVec_smul]
    simp only [smul_smul]
    have hcoeff : (1 / γ : ℝ) - c - (1 / γ) * (c * a0 t q) = 0 := by
      simp only [c]
      field_simp [hγ0, hγa]
      ring
    set W := vecMulVec V e
    calc
      (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 / γ) • W - c • W
          - ((1 / γ) * (c * a0 t q)) • W
          = 1 + ((1 / γ) - c) • W - ((1 / γ) * (c * a0 t q)) • W := by
            rw [add_sub_assoc, ← sub_smul]
      _ = 1 + ((1 / γ) - c - (1 / γ) * (c * a0 t q)) • W := by
            rw [add_sub_assoc, ← sub_smul]
      _ = 1 + (0 : ℝ) • W := by rw [hcoeff]
      _ = 1 := by simp
  rw [𝒦]
  exact inv_eq_right_inv hKR

end

end BollobasNikiforov

/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.CP.Basic
import LeanPool.BollobasNikiforov.Kernel.Data
import LeanPool.BollobasNikiforov.Kernel.Main
import LeanPool.BollobasNikiforov.M.Config
import LeanPool.BollobasNikiforov.M.Elim
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Feature factorisation `M = FFᵀ + L` and the Schur complement of `E`

`SC01`–`SC07` record the weights `q i`, `γ`, the feature matrix `F`, the
weighted Laplacian `L`, the `E`-block `L_EE` and its inverse, and the
reduced data `L_red`, `𝒰` of `docs/sol.tex` §4.

After block elimination replaces `L` by `diag(L_EE, L_red)` and the feature
rows by `(F_E, 𝒰)`, the Schur complement of the first block is
`L_red + 𝒰 (I - F_Eᵀ (L_EE + F_E F_Eᵀ)⁻¹ F_E) 𝒰ᵀ`. The bracket equals
`(I + F_Eᵀ L_EE⁻¹ F_E)⁻¹` by the Woodbury companion identity
(paper (eq:Schur)).
-/

open Matrix
open scoped Matrix

namespace BollobasNikiforov

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R : Type*} [CommRing R]


noncomputable section

/-- Woodbury formula for a rank-`κ` update `L + F Fᵀ`. -/
lemma woodbury_add_mul_transpose (L : Matrix ι ι R) (F : Matrix ι κ R)
    (hL : IsUnit L) (hW : IsUnit (1 + Fᵀ * L⁻¹ * F)) :
    (L + F * Fᵀ)⁻¹ = L⁻¹ - L⁻¹ * F * (1 + Fᵀ * L⁻¹ * F)⁻¹ * Fᵀ * L⁻¹ := by
  have hC : IsUnit (1 : Matrix κ κ R) := isUnit_one
  have hAC : IsUnit ((1 : Matrix κ κ R)⁻¹ + Fᵀ * L⁻¹ * F) := by
    simpa using hW
  have h := add_mul_mul_inv_eq_sub L F (1 : Matrix κ κ R) Fᵀ hL hC hAC
  simp only [Matrix.mul_one, inv_one] at h
  exact h

/-- **SC08.** Woodbury companion identity:
`I - Fᵀ (L + F Fᵀ)⁻¹ F = (I + Fᵀ L⁻¹ F)⁻¹`. -/
lemma one_sub_transpose_mul_inv_mul (L : Matrix ι ι R) (F : Matrix ι κ R)
    (hL : IsUnit L) (hW : IsUnit (1 + Fᵀ * L⁻¹ * F)) :
    (1 : Matrix κ κ R) - Fᵀ * (L + F * Fᵀ)⁻¹ * F = (1 + Fᵀ * L⁻¹ * F)⁻¹ := by
  rw [woodbury_add_mul_transpose L F hL hW]
  set S := Fᵀ * L⁻¹ * F
  set W := (1 : Matrix κ κ R) + S
  have hsub :
      Fᵀ * (L⁻¹ - L⁻¹ * F * W⁻¹ * Fᵀ * L⁻¹) * F = S - S * W⁻¹ * S := by
    simp only [S, W, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [hsub]
  have hrearr : (1 : Matrix κ κ R) - (S - S * W⁻¹ * S) = 1 - S + S * W⁻¹ * S := by
    abel
  rw [hrearr]
  have hWr : W⁻¹ * W = 1 := by
    simpa [W, S] using nonsing_inv_mul W ((isUnit_iff_isUnit_det _).1 hW)
  have hWS : S * (1 + S) = W * S := by
    simp [W, Matrix.mul_add, Matrix.add_mul]
  have h1S : (1 - S) * (1 + S) = 1 - S * S := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  have hright : (1 - S + S * W⁻¹ * S) * W = 1 := by
    calc
      (1 - S + S * W⁻¹ * S) * W
          = (1 - S) * W + S * W⁻¹ * S * W := by rw [add_mul]
      _ = (1 - S) * (1 + S) + S * W⁻¹ * (S * (1 + S)) := by
            simp [W, Matrix.mul_assoc]
      _ = 1 - S * S + S * W⁻¹ * (W * S) := by rw [h1S, hWS]
      _ = 1 - S * S + S * (W⁻¹ * W) * S := by simp [Matrix.mul_assoc]
      _ = 1 - S * S + S * S := by rw [hWr, Matrix.mul_one]
      _ = 1 := by abel
  exact (inv_eq_left_inv hright).symm

/-- Expanding `𝒰 (I - F_Eᵀ (L_EE + F_E F_Eᵀ)⁻¹ F_E) 𝒰ᵀ` as a Schur remainder. -/
lemma mul_one_sub_conj {ε τ : Type*} [Fintype ε] [DecidableEq ε]
    (U : Matrix τ κ R) (FE : Matrix ε κ R) (A : Matrix ε ε R) :
    U * ((1 : Matrix κ κ R) - FEᵀ * A⁻¹ * FE) * Uᵀ =
      U * Uᵀ - U * FEᵀ * A⁻¹ * FE * Uᵀ := by
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

/-- After replacing `L` by `diag(L_EE, L_red)`, the Schur complement of `E` in
`FFᵀ + L` is `L_red + 𝒰 (I - F_Eᵀ (L_EE + F_E F_Eᵀ)⁻¹ F_E) 𝒰ᵀ`. -/
lemma schurComplement_diag_add_mul {ε τ : Type*} [Fintype ε] [DecidableEq ε]
    (Lred : Matrix τ τ R) (U : Matrix τ κ R) (FE : Matrix ε κ R)
    (A : Matrix ε ε R) :
    (Lred + U * Uᵀ) - U * FEᵀ * A⁻¹ * FE * Uᵀ =
      Lred + U * ((1 : Matrix κ κ R) - FEᵀ * A⁻¹ * FE) * Uᵀ := by
  rw [mul_one_sub_conj]
  abel

/-- **SC08**, reduced coordinates. The Schur complement of `E` in `FFᵀ + L`
after block diagonalization of `L` equals
`L_red + 𝒰 (I + F_Eᵀ L_EE⁻¹ F_E)⁻¹ 𝒰ᵀ`. -/
lemma schurComplement_woodbury {ε τ : Type*}
    [Fintype ε] [DecidableEq ε]
    (LEE : Matrix ε ε R) (Lred : Matrix τ τ R)
    (FE : Matrix ε κ R) (U : Matrix τ κ R)
    (hLEE : IsUnit LEE) (hW : IsUnit (1 + FEᵀ * LEE⁻¹ * FE)) :
    (Lred + U * Uᵀ) - U * FEᵀ * (LEE + FE * FEᵀ)⁻¹ * FE * Uᵀ =
      Lred + U * (1 + FEᵀ * LEE⁻¹ * FE)⁻¹ * Uᵀ := by
  rw [schurComplement_diag_add_mul, one_sub_transpose_mul_inv_mul LEE FE hLEE hW]

omit [DecidableEq κ] in
/-- Assembling `FFᵀ + diag(L_EE, L_red)` as a 2×2 block matrix. -/
lemma fromBlocks_add_mul_transpose {ε τ : Type*}
    (LEE : Matrix ε ε R) (Lred : Matrix τ τ R)
    (FE : Matrix ε κ R) (U : Matrix τ κ R) :
    fromRows FE U * (fromRows FE U)ᵀ + fromBlocks LEE 0 0 Lred =
      fromBlocks (LEE + FE * FEᵀ) (FE * Uᵀ) (U * FEᵀ) (Lred + U * Uᵀ) := by
  rw [transpose_fromRows, fromRows_mul_fromCols]
  simp [fromBlocks_add, add_comm]


/-! ### Configuration-dependent Schur data (SC01–SC07) -/


open Finset

variable {k p : ℕ}

/-! ### SC01 — weights `q i` and `γ` -/

/-- `qᵢ = sᵢ / dᵢ`. -/
def configQ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) : ℝ :=
  s i / configD t ρ x i

lemma configQ_pos (s t : Fin k → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j)
    (x : Fin p → ℝ) {i : Fin k} (hsi : 0 < s i) :
    0 < configQ s t ρ x i :=
  div_pos hsi (configD_pos t hρ x i)

/-- `γ = σ - ∑ qᵢ`. -/
def configγ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) : ℝ :=
  configσ s - ∑ i, configQ s t ρ x i

lemma configγ_eq_sum (s t : Fin k → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j)
    (x : Fin p → ℝ) :
    configγ s t ρ x = ∑ i, s i * configH t ρ x i / configD t ρ x i := by
  simp only [configγ, configσ, configQ]
  rw [← sum_sub_distrib]
  refine Fintype.sum_congr _ _ fun i => ?_
  have hd : configD t ρ x i ≠ 0 := (configD_pos t hρ x i).ne'
  calc
    s i - s i / configD t ρ x i
        = (s i * configD t ρ x i - s i) / configD t ρ x i := by
          field_simp [hd]
    _ = s i * (configD t ρ x i - 1) / configD t ρ x i := by ring
    _ = s i * configH t ρ x i / configD t ρ x i := by
          simp [configD]

lemma configγ_nonneg (s t : Fin k → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j)
    (x : Fin p → ℝ) (hs : ∀ i, 0 < s i) :
    0 ≤ configγ s t ρ x := by
  rw [configγ_eq_sum s t hρ x]
  exact sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (hs i).le (configH_nonneg t hρ x i))
      (configD_pos t hρ x i).le

/-! ### SC02 — feature matrix `F` -/

/-- Rows: `e₀ᵀ` at `z₀`, `sᵢ v(tᵢ)ᵀ` at `zᵢ`, `ρⱼ b(xⱼ)ᵀ` at `yⱼ`. -/
def configF (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (Fin 3) ℝ :=
  fun α =>
    match configIdxEquiv k p α with
    | Sum.inl none => e (0 : Fin 3)
    | Sum.inl (some i) => s i • v (t i)
    | Sum.inr j => ρ j • b (x j)

lemma configF_z0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    configF s t ρ x idxZ0 = e (0 : Fin 3) := by
  simp [configF, idxZ0]

lemma configF_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    configF s t ρ x (idxZ i) = s i • v (t i) := by
  simp [configF, idxZ]

lemma configF_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin p) :
    configF s t ρ x (idxY j) = ρ j • b (x j) := by
  simp [configF, idxY]

lemma configF_mul_transpose_apply (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (α β : ConfigIdx k p) :
    (configF s t ρ x * (configF s t ρ x)ᵀ) α β =
      configF s t ρ x α ⬝ᵥ configF s t ρ x β := by
  simp [mul_apply, transpose_apply, dotProduct]

/-! Feature inner products -/

lemma v_dot_v (t₁ t₂ : ℝ) : v t₁ ⬝ᵥ v t₂ = (1 + t₁ * t₂) ^ 2 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [v, dotProduct, Fin.sum_univ_three]
  ring_nf
  simp
  ring

lemma v_dot_b (ti xj : ℝ) : v ti ⬝ᵥ b xj = (xj - ti) ^ 2 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [v, b, dotProduct, Fin.sum_univ_three]
  ring_nf
  simp
  ring

lemma b_dot_b (x₁ x₂ : ℝ) : b x₁ ⬝ᵥ b x₂ = (1 + x₁ * x₂) ^ 2 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [b, dotProduct, Fin.sum_univ_three]
  ring_nf
  simp

lemma e0_dot_v (ti : ℝ) : e (0 : Fin 3) ⬝ᵥ v ti = 1 := by
  simp [e, v, dotProduct, Pi.single_apply]

lemma e0_dot_b (xj : ℝ) : e (0 : Fin 3) ⬝ᵥ b xj = xj ^ 2 := by
  simp [e, b, dotProduct, Pi.single_apply]

lemma e0_dot_e0 : e (0 : Fin 3) ⬝ᵥ e (0 : Fin 3) = 1 := by
  simp [e, dotProduct, Pi.single_apply]

lemma yVec_dot_yVec (ρ x : Fin p → ℝ) (j ℓ : Fin p) :
    yVec ρ x j ⬝ᵥ yVec ρ x ℓ =
      Real.sqrt (ρ j) * Real.sqrt (ρ ℓ) * (x j * x ℓ + 1) := by
  simp [yVec, dotProduct, Fin.sum_univ_two]
  ring

lemma Xconfig_y_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j ℓ : Fin p) :
    Xconfig s t ρ x (idxY j) (idxY ℓ) =
      Real.sqrt (ρ j) * Real.sqrt (ρ ℓ) * (x j * x ℓ + 1) := by
  rw [Xconfig_apply, configVec_y, configVec_y, yVec_dot_yVec]

/-! ### SC03 — Laplacian `L` and `M = FFᵀ + L` -/

/-- Weighted Laplacian: weight `sᵢ` on `z₀–zᵢ` and `sᵢ ρⱼ aᵢ(xⱼ)` on `zᵢ–yⱼ`. -/
def configL (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  ∑ i, s i • vecMulVec
      (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
      (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
    + ∑ i, ∑ j, (s i * ρ j * truncSq (t i) (x j)) •
        vecMulVec (e (idxZ (p := p) i) - e (idxY (k := k) j))
          (e (idxZ (p := p) i) - e (idxY (k := k) j))

lemma configL_apply (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (α β : ConfigIdx k p) :
    configL s t ρ x α β =
      ∑ i, s i *
          vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
            (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i)) α β
        + ∑ i, ∑ j, (s i * ρ j * truncSq (t i) (x j)) *
            vecMulVec (e (idxZ (p := p) i) - e (idxY (k := k) j))
              (e (idxZ (p := p) i) - e (idxY (k := k) j)) α β := by
  simp [configL, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]

lemma configH_eq_sum_truncSq (t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    configH t ρ x i = ∑ j, ρ j * truncSq (t i) (x j) :=
  rfl

lemma configIdx_cases {P : ConfigIdx k p → Prop} (α : ConfigIdx k p)
    (h0 : P idxZ0) (hz : ∀ i, P (idxZ i)) (hy : ∀ j, P (idxY j)) : P α := by
  rw [← (configIdxEquiv k p).symm_apply_apply α]
  rcases configIdxEquiv k p α with o | j
  · rcases o with _ | i
    · simpa [idxZ0] using h0
    · simpa [idxZ] using hz i
  · simpa [idxY] using hy j

lemma idxY_injective {j ℓ : Fin p} (h : (idxY (k := k) j : ConfigIdx k p) = idxY ℓ) :
    j = ℓ := by
  have := congrArg Fin.val h
  simp only [idxY_val, Nat.add_left_cancel_iff] at this
  exact Fin.ext this

lemma idxZ_injective {i h : Fin k} (heq : (idxZ (p := p) i : ConfigIdx k p) = idxZ h) :
    i = h := by
  have := congrArg Fin.val heq
  simp only [idxZ_val, Nat.add_right_cancel_iff] at this
  exact Fin.ext this

@[simp] lemma idxZ_eq_iff {i h : Fin k} :
    (idxZ (p := p) i : ConfigIdx k p) = idxZ h ↔ i = h :=
  ⟨idxZ_injective, fun h => h ▸ rfl⟩

@[simp] lemma idxY_eq_iff {j ℓ : Fin p} :
    (idxY (k := k) j : ConfigIdx k p) = idxY ℓ ↔ j = ℓ :=
  ⟨idxY_injective, fun h => h ▸ rfl⟩

@[simp] lemma idxZ_ne_idxZ0 (i : Fin k) :
    (idxZ (p := p) i : ConfigIdx k p) ≠ idxZ0 :=
  (idxZ0_ne_idxZ (p := p) i).symm

@[simp] lemma idxY_ne_idxZ0 (j : Fin p) :
    (idxY (k := k) j : ConfigIdx k p) ≠ idxZ0 :=
  (idxZ0_ne_idxY (k := k) j).symm

@[simp] lemma idxY_ne_idxZ (i : Fin k) (j : Fin p) :
    (idxY (k := k) j : ConfigIdx k p) ≠ idxZ i :=
  (idxZ_ne_idxY (p := p) i j).symm

variable (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)

lemma sub_edge_z0 (i : Fin k) (α : ConfigIdx k p) :
    (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i)) α =
      if α = idxZ0 then (1 : ℝ) else if α = idxZ i then -1 else 0 :=
  sub_single_apply (idxZ0_ne_idxZ (p := p) i) α

lemma sub_edge_zy (i : Fin k) (j : Fin p) (α : ConfigIdx k p) :
    (e (idxZ (p := p) i) - e (idxY (k := k) j)) α =
      if α = idxZ i then (1 : ℝ) else if α = idxY j then -1 else 0 :=
  sub_single_apply (idxZ_ne_idxY (p := p) i j) α

lemma edge_z0 (i : Fin k) (α β : ConfigIdx k p) :
    vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
      (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i)) α β =
      (if α = idxZ0 then (1 : ℝ) else if α = idxZ i then -1 else 0) *
      (if β = idxZ0 then (1 : ℝ) else if β = idxZ i then -1 else 0) := by
  rw [vecMulVec_apply, sub_edge_z0, sub_edge_z0]

lemma edge_zy (i : Fin k) (j : Fin p) (α β : ConfigIdx k p) :
    vecMulVec (e (idxZ (p := p) i) - e (idxY (k := k) j))
      (e (idxZ (p := p) i) - e (idxY (k := k) j)) α β =
      (if α = idxZ i then (1 : ℝ) else if α = idxY j then -1 else 0) *
      (if β = idxZ i then (1 : ℝ) else if β = idxY j then -1 else 0) := by
  rw [vecMulVec_apply, sub_edge_zy, sub_edge_zy]

lemma configL_z0_z0 : configL s t ρ x idxZ0 idxZ0 = configσ s := by
  rw [configL_apply]
  have h1 : ∑ i, s i *
      vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i)) idxZ0 idxZ0 = configσ s := by
    refine Fintype.sum_congr _ _ fun i => ?_
    rw [edge_z0]; simp
  have h2 : ∑ i, ∑ j, (s i * ρ j * truncSq (t i) (x j)) *
      vecMulVec (e (idxZ (p := p) i) - e (idxY (k := k) j))
        (e (idxZ (p := p) i) - e (idxY (k := k) j)) idxZ0 idxZ0 = 0 := by
    refine Fintype.sum_eq_zero _ fun i => Fintype.sum_eq_zero _ fun j => ?_
    rw [edge_zy]
    simp [idxZ0_ne_idxZ (p := p) i, idxZ0_ne_idxY (k := k) j]
  rw [h1, h2, add_zero]

lemma configL_z0_z (i : Fin k) : configL s t ρ x idxZ0 (idxZ i) = -s i := by
  rw [configL_apply]
  have h1 : ∑ i', s i' *
      vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i'))
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i')) idxZ0 (idxZ i) = -s i := by
    rw [Fintype.sum_eq_single i]
    · rw [edge_z0]; simp
    · intro i' hi'
      have hne : idxZ (p := p) i ≠ idxZ i' := fun h => hi' (idxZ_injective h.symm)
      rw [edge_z0]; simp [hne]
  have h2 : ∑ i', ∑ j, (s i' * ρ j * truncSq (t i') (x j)) *
      vecMulVec (e (idxZ (p := p) i') - e (idxY (k := k) j))
        (e (idxZ (p := p) i') - e (idxY (k := k) j)) idxZ0 (idxZ i) = 0 := by
    refine Fintype.sum_eq_zero _ fun i' => Fintype.sum_eq_zero _ fun j => ?_
    rw [edge_zy]
    simp [idxZ0_ne_idxZ (p := p) i', idxZ0_ne_idxY (k := k) j,
      idxZ_ne_idxY (p := p) i j]
  rw [h1, h2, add_zero]

lemma configL_z0_y (j : Fin p) : configL s t ρ x idxZ0 (idxY j) = 0 := by
  rw [configL_apply]
  have h1 : ∑ i, s i *
      vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i)) idxZ0 (idxY j) = 0 := by
    refine Fintype.sum_eq_zero _ fun i => ?_
    rw [edge_z0]
    simp
  have h2 : ∑ i, ∑ j', (s i * ρ j' * truncSq (t i) (x j')) *
      vecMulVec (e (idxZ (p := p) i) - e (idxY (k := k) j'))
        (e (idxZ (p := p) i) - e (idxY (k := k) j')) idxZ0 (idxY j) = 0 := by
    refine Fintype.sum_eq_zero _ fun i => Fintype.sum_eq_zero _ fun j' => ?_
    rw [edge_zy]
    simp [idxZ0_ne_idxZ (p := p) i, idxZ0_ne_idxY (k := k) j']
  rw [h1, h2, add_zero]

lemma configL_z_z (i h : Fin k) :
    configL s t ρ x (idxZ i) (idxZ h) =
      if i = h then s i * configD t ρ x i else 0 := by
  rw [configL_apply]
  have h1 : ∑ i', s i' *
      vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i'))
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i')) (idxZ i) (idxZ h) =
      if i = h then s i else 0 := by
    by_cases hih : i = h
    · subst hih
      rw [ite_eq_left rfl, Fintype.sum_eq_single i]
      · rw [edge_z0]; simp
      · intro i' hi'
        have hne : idxZ (p := p) i ≠ idxZ i' := fun eq => hi' (idxZ_injective eq.symm)
        rw [edge_z0]; simp [hne]
    · rw [ite_eq_right hih]
      refine Fintype.sum_eq_zero _ fun i' => ?_
      have hne : idxZ (p := p) i ≠ idxZ h := fun eq => hih (idxZ_injective eq)
      rw [edge_z0]
      simp only [idxZ_ne_idxZ0, ↓reduceIte, idxZ_eq_iff, mul_ite, mul_neg, mul_one, mul_zero,
        ite_eq_right_iff, neg_eq_zero]
      exact fun h1 h2 => (hih (h2.trans h1.symm)).elim
  have h2 : ∑ i', ∑ j, (s i' * ρ j * truncSq (t i') (x j)) *
      vecMulVec (e (idxZ (p := p) i') - e (idxY (k := k) j))
        (e (idxZ (p := p) i') - e (idxY (k := k) j)) (idxZ i) (idxZ h) =
      if i = h then s i * configH t ρ x i else 0 := by
    by_cases hih : i = h
    · subst hih
      rw [ite_eq_left rfl, Fintype.sum_eq_single i]
      · have : ∑ j, s i * ρ j * truncSq (t i) (x j) = s i * configH t ρ x i := by
          simp only [configH, truncSq, Finset.mul_sum, mul_assoc]
        convert this using 1
        refine Fintype.sum_congr _ _ fun j => ?_
        rw [edge_zy]; simp
      · intro i' hi'
        refine Fintype.sum_eq_zero _ fun j => ?_
        have hne : idxZ (p := p) i ≠ idxZ i' := fun eq => hi' (idxZ_injective eq.symm)
        rw [edge_zy]
        simp [hne, idxZ_ne_idxY (p := p) i j]
    · rw [ite_eq_right hih]
      refine Fintype.sum_eq_zero _ fun i' => Fintype.sum_eq_zero _ fun j => ?_
      have hne : idxZ (p := p) i ≠ idxZ h := fun eq => hih (idxZ_injective eq)
      rw [edge_zy]
      simp only [idxZ_eq_iff, idxZ_ne_idxY (p := p) i j, ↓reduceIte, idxZ_ne_idxY (p := p) h j,
        mul_ite, mul_one, mul_zero, ite_eq_right_iff, mul_eq_zero]
      exact fun h1 h2 => (hih (h2.trans h1.symm)).elim
  rw [h1, h2]
  split_ifs with hih
  · subst hih; simp [configD]; ring
  · ring

lemma configL_z_y (i : Fin k) (j : Fin p) :
    configL s t ρ x (idxZ i) (idxY j) = -(s i * ρ j * truncSq (t i) (x j)) := by
  rw [configL_apply]
  have h1 : ∑ i', s i' *
      vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i'))
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i')) (idxZ i) (idxY j) = 0 := by
    refine Fintype.sum_eq_zero _ fun i' => ?_
    rw [edge_z0]
    simp
  have h2 : ∑ i', ∑ j', (s i' * ρ j' * truncSq (t i') (x j')) *
      vecMulVec (e (idxZ (p := p) i') - e (idxY (k := k) j'))
        (e (idxZ (p := p) i') - e (idxY (k := k) j')) (idxZ i) (idxY j) =
      -(s i * ρ j * truncSq (t i) (x j)) := by
    rw [Fintype.sum_eq_single i]
    · rw [Fintype.sum_eq_single j]
      · rw [edge_zy]; simp
      · intro j' hj'
        have hne : idxY (k := k) j ≠ idxY j' := fun eq => hj' (idxY_injective eq.symm)
        rw [edge_zy]; simp [hne]
    · intro i' hi'
      refine Fintype.sum_eq_zero _ fun j' => ?_
      have hne : idxZ (p := p) i ≠ idxZ i' := fun eq => hi' (idxZ_injective eq.symm)
      rw [edge_zy]
      simp [hne, idxZ_ne_idxY (p := p) i]
  rw [h1, h2, zero_add]

lemma configL_y_y (j ℓ : Fin p) :
    configL s t ρ x (idxY j) (idxY ℓ) =
      if j = ℓ then ∑ i, s i * ρ j * truncSq (t i) (x j) else 0 := by
  rw [configL_apply]
  have h1 : ∑ i, s i *
      vecMulVec (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i)) (idxY j) (idxY ℓ) = 0 := by
    refine Fintype.sum_eq_zero _ fun i => ?_
    rw [edge_z0]
    simp
  have h2 : ∑ i, ∑ j', (s i * ρ j' * truncSq (t i) (x j')) *
      vecMulVec (e (idxZ (p := p) i) - e (idxY (k := k) j'))
        (e (idxZ (p := p) i) - e (idxY (k := k) j')) (idxY j) (idxY ℓ) =
      if j = ℓ then ∑ i, s i * ρ j * truncSq (t i) (x j) else 0 := by
    by_cases hjl : j = ℓ
    · subst hjl
      rw [ite_eq_left rfl]
      refine Fintype.sum_congr _ _ fun i => ?_
      rw [Fintype.sum_eq_single j]
      · rw [edge_zy]; simp
      · intro j' hj'
        have hne : idxY (k := k) j ≠ idxY j' := fun eq => hj' (idxY_injective eq.symm)
        rw [edge_zy]; simp [hne]
    · rw [ite_eq_right hjl]
      refine Fintype.sum_eq_zero _ fun i => Fintype.sum_eq_zero _ fun j' => ?_
      have hne : idxY (k := k) j ≠ idxY ℓ := fun eq => hjl (idxY_injective eq)
      rw [edge_zy]
      simp only [idxY_ne_idxZ, ↓reduceIte, idxY_eq_iff, mul_ite, mul_neg, mul_one, mul_zero,
        ite_eq_right_iff, neg_eq_zero, mul_eq_zero]
      exact fun h1 h2 => (hjl (h2.trans h1.symm)).elim
  rw [h1, h2, zero_add]

lemma configL_symm (α β : ConfigIdx k p) :
    configL s t ρ x α β = configL s t ρ x β α := by
  simp [configL_apply, vecMulVec_apply, mul_comm]

lemma M_Xconfig_symm (α β : ConfigIdx k p) :
    M (Xconfig s t ρ x) α β = M (Xconfig s t ρ x) β α := by
  rcases eq_or_ne α β with rfl | hne
  · rfl
  · rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) hne,
      M_apply_of_ne _ (Xconfig_isSymm s t ρ x) hne.symm,
      posPart_apply, posPart_apply, (Xconfig_isSymm s t ρ x).apply]

lemma FF_z0_z0 : (configF s t ρ x * (configF s t ρ x)ᵀ) idxZ0 idxZ0 = 1 := by
  rw [configF_mul_transpose_apply, configF_z0, e0_dot_e0]

lemma FF_z0_z (i : Fin k) :
    (configF s t ρ x * (configF s t ρ x)ᵀ) idxZ0 (idxZ i) = s i := by
  rw [configF_mul_transpose_apply, configF_z0, configF_z, dotProduct_smul, e0_dot_v]
  simp [smul_eq_mul]

lemma FF_z0_y (j : Fin p) :
    (configF s t ρ x * (configF s t ρ x)ᵀ) idxZ0 (idxY j) = ρ j * x j ^ 2 := by
  rw [configF_mul_transpose_apply, configF_z0, configF_y, dotProduct_smul, e0_dot_b]
  simp [smul_eq_mul]

lemma FF_z_z (i h : Fin k) :
    (configF s t ρ x * (configF s t ρ x)ᵀ) (idxZ i) (idxZ h) =
      s i * s h * (1 + t i * t h) ^ 2 := by
  rw [configF_mul_transpose_apply, configF_z, configF_z, dotProduct_smul,
    smul_dotProduct, v_dot_v]
  simp [smul_eq_mul]; ring

lemma FF_z_y (i : Fin k) (j : Fin p) :
    (configF s t ρ x * (configF s t ρ x)ᵀ) (idxZ i) (idxY j) =
      s i * ρ j * (x j - t i) ^ 2 := by
  rw [configF_mul_transpose_apply, configF_z, configF_y, dotProduct_smul,
    smul_dotProduct, v_dot_b]
  simp [smul_eq_mul]; ring

lemma FF_y_y (j ℓ : Fin p) :
    (configF s t ρ x * (configF s t ρ x)ᵀ) (idxY j) (idxY ℓ) =
      ρ j * ρ ℓ * (1 + x j * x ℓ) ^ 2 := by
  rw [configF_mul_transpose_apply, configF_y, configF_y, dotProduct_smul,
    smul_dotProduct, b_dot_b]
  simp [smul_eq_mul]; ring

lemma truncSq_neg_id (ti xj : ℝ) :
    max (ti - xj) 0 ^ 2 = (xj - ti) ^ 2 - truncSq ti xj := by
  rcases le_total ti xj with h | h
  · simp [truncSq, max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
  · simp [truncSq, max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring

lemma MX_y_y_of_ne (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) {j ℓ : Fin p}
    (hjl : j ≠ ℓ) :
    M (Xconfig s t ρ x) (idxY j) (idxY ℓ) =
      ρ j * ρ ℓ * (1 + x j * x ℓ) ^ 2 := by
  have hidx : (idxY (k := k) j : ConfigIdx k p) ≠ idxY ℓ :=
    fun eq => hjl (idxY_injective eq)
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) hidx, posPart_apply, Xconfig_y_y]
  have hnn : 0 ≤ Real.sqrt (ρ j) * Real.sqrt (ρ ℓ) * (x j * x ℓ + 1) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (add_nonneg (mul_nonneg (hx j) (hx ℓ)) zero_le_one)
  rw [max_eq_left hnn, mul_pow, mul_pow, Real.sq_sqrt (hρ j).le, Real.sq_sqrt (hρ ℓ).le]
  ring

lemma MX_y_y_diag (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (j : Fin p) :
    M (Xconfig s t ρ x) (idxY j) (idxY j) =
      ρ j * ρ j * (1 + x j * x j) ^ 2 +
        ∑ i, s i * ρ j * truncSq (t i) (x j) := by
  rw [M_diag, Xconfig_y_y]
  have hX : (Real.sqrt (ρ j) * Real.sqrt (ρ j) * (x j * x j + 1)) ^ 2 =
      ρ j * ρ j * (1 + x j * x j) ^ 2 := by
    rw [Real.mul_self_sqrt (hρ j).le, mul_pow]; ring
  rw [hX]
  have hup : ∑ q : ConfigIdx k p,
      (if idxY (k := k) j < q ∧ Xconfig s t ρ x (idxY j) q < 0 then
        Xconfig s t ρ x (idxY j) q ^ 2 else 0) = 0 := by
    refine Fintype.sum_eq_zero _ fun q => ?_
    refine configIdx_cases (p := p)
      (P := fun q =>
        (if idxY (k := k) j < q ∧ Xconfig s t ρ x (idxY j) q < 0 then
          Xconfig s t ρ x (idxY j) q ^ 2 else 0) = 0) q ?_ ?_ ?_
    · simp [not_lt.mpr (idxZ0_lt_idxY (k := k) j).le]
    · intro i
      simp [not_lt.mpr (idxZ_lt_idxY (p := p) i j).le]
    · intro ℓ
      have hnn : 0 ≤ Xconfig s t ρ x (idxY (k := k) j) (idxY ℓ) := by
        rw [Xconfig_y_y]
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (add_nonneg (mul_nonneg (hx j) (hx ℓ)) zero_le_one)
      simp [not_lt.mpr hnn]
  have hlow : ∑ u : ConfigIdx k p,
      (if u < idxY (k := k) j ∧ Xconfig s t ρ x u (idxY j) < 0 then
        Xconfig s t ρ x u (idxY j) ^ 2 else 0) =
      ∑ i, s i * ρ j * truncSq (t i) (x j) := by
    rw [sum_configIdx]
    have hz0 : (if idxZ0 < idxY (k := k) j ∧
        Xconfig s t ρ x idxZ0 (idxY j) < 0 then
          Xconfig s t ρ x idxZ0 (idxY j) ^ 2 else 0) = 0 := by
      simp [not_lt.mpr (Xconfig_z0_y_nonneg s t ρ x hx j)]
    have hz : ∑ i : Fin k,
        (if idxZ (p := p) i < idxY (k := k) j ∧
            Xconfig s t ρ x (idxZ i) (idxY j) < 0 then
          Xconfig s t ρ x (idxZ i) (idxY j) ^ 2 else 0) =
        ∑ i, s i * ρ j * truncSq (t i) (x j) := by
      refine Fintype.sum_congr _ _ fun i => ?_
      simp only [idxZ_lt_idxY (p := p), true_and, Xconfig_z_y, truncSq]
      have hc : 0 < Real.sqrt (s i) * Real.sqrt (ρ j) :=
        mul_pos (Real.sqrt_pos.mpr (hs i)) (Real.sqrt_pos.mpr (hρ j))
      by_cases htx : t i < x j
      · have hneg : Real.sqrt (s i) * Real.sqrt (ρ j) * (t i - x j) < 0 :=
          mul_neg_of_pos_of_neg hc (sub_neg.mpr htx)
        have hmax : max (x j - t i) 0 = x j - t i :=
          max_eq_left (sub_nonneg.mpr htx.le)
        rw [ite_eq_left hneg]
        simp only [hmax, mul_pow, Real.sq_sqrt (hs i).le, Real.sq_sqrt (hρ j).le]
        ring
      · have hnn : ¬ Real.sqrt (s i) * Real.sqrt (ρ j) * (t i - x j) < 0 :=
          not_lt.mpr (mul_nonneg hc.le (sub_nonneg.mpr (le_of_not_gt htx)))
        have hmax : max (x j - t i) 0 = 0 :=
          max_eq_right (sub_nonpos.mpr (le_of_not_gt htx))
        simp [hnn, hmax]
    have hy : ∑ ℓ : Fin p,
        (if idxY (k := k) ℓ < idxY j ∧
            Xconfig s t ρ x (idxY ℓ) (idxY j) < 0 then
          Xconfig s t ρ x (idxY ℓ) (idxY j) ^ 2 else 0) = 0 := by
      refine Fintype.sum_eq_zero _ fun ℓ => ?_
      have hnn : 0 ≤ Xconfig s t ρ x (idxY (k := k) ℓ) (idxY j) := by
        rw [Xconfig_y_y]
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (add_nonneg (mul_nonneg (hx ℓ) (hx j)) zero_le_one)
      simp [not_lt.mpr hnn]
    simp [hz0, hz, hy]
  rw [hup, hlow, add_zero]

lemma M_eq_configF_mul_transpose_add_configL (hs : ∀ i, 0 < s i)
    (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    M (Xconfig s t ρ x) =
      configF s t ρ x * (configF s t ρ x)ᵀ + configL s t ρ x := by
  ext α β
  refine configIdx_cases (p := p)
    (P := fun α =>
      M (Xconfig s t ρ x) α β =
        (configF s t ρ x * (configF s t ρ x)ᵀ) α β + configL s t ρ x α β) α ?_ ?_ ?_
  · refine configIdx_cases (p := p)
      (P := fun β =>
        M (Xconfig s t ρ x) idxZ0 β =
          (configF s t ρ x * (configF s t ρ x)ᵀ) idxZ0 β +
            configL s t ρ x idxZ0 β) β ?_ ?_ ?_
    · rw [MX_z0_z0 s t ρ x hs hx, FF_z0_z0, configL_z0_z0]
    · intro i
      rw [MX_z0_z, FF_z0_z, configL_z0_z]; ring
    · intro j
      rw [MX_z0_y s t ρ x hρ hx, FF_z0_y, configL_z0_y]; ring
  · intro i
    refine configIdx_cases (p := p)
      (P := fun β =>
        M (Xconfig s t ρ x) (idxZ i) β =
          (configF s t ρ x * (configF s t ρ x)ᵀ) (idxZ i) β +
            configL s t ρ x (idxZ i) β) β ?_ ?_ ?_
    · rw [M_Xconfig_symm, configF_mul_transpose_apply, dotProduct_comm,
        ← configF_mul_transpose_apply, configL_symm, MX_z0_z, FF_z0_z,
        configL_z0_z]; ring
    · intro h
      rw [MX_z_z s t ρ x hs ht hρ, FF_z_z, configL_z_z]
    · intro j
      rw [MX_z_y s t ρ x hs hρ, FF_z_y, configL_z_y, truncSq_neg_id]; ring
  · intro j
    refine configIdx_cases (p := p)
      (P := fun β =>
        M (Xconfig s t ρ x) (idxY j) β =
          (configF s t ρ x * (configF s t ρ x)ᵀ) (idxY j) β +
            configL s t ρ x (idxY j) β) β ?_ ?_ ?_
    · rw [M_Xconfig_symm, configF_mul_transpose_apply, dotProduct_comm,
        ← configF_mul_transpose_apply, configL_symm, MX_z0_y s t ρ x hρ hx,
        FF_z0_y, configL_z0_y]
      ring
    · intro i
      rw [M_Xconfig_symm, configF_mul_transpose_apply, dotProduct_comm,
        ← configF_mul_transpose_apply, configL_symm, MX_z_y s t ρ x hs hρ,
        FF_z_y, configL_z_y, truncSq_neg_id]
      ring
    · intro ℓ
      rcases eq_or_ne j ℓ with rfl | hjl
      · rw [MX_y_y_diag s t ρ x hs hρ hx, FF_y_y, configL_y_y]
        simp
      · rw [MX_y_y_of_ne s t ρ x hρ hx hjl, FF_y_y, configL_y_y, ite_eq_right hjl]
        ring

/-! ### SC04 — the `E`-block of `L` -/

/-- Embeds the `E`-indices into `ConfigIdx k p`: the axis vector `none ↦ idxZ0` and the left vectors
`some i ↦ idxZ i`. -/
def configEEmbed : Option (Fin k) → ConfigIdx k p
  | none => idxZ0
  | some i => idxZ i

/-- The `E`-block of the weighted Laplacian `configL s t ρ x`. -/
def configLEE : Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  (configL s t ρ x).submatrix configEEmbed configEEmbed

lemma configLEE_none_none : configLEE s t ρ x none none = configσ s := by
  simp [configLEE, configEEmbed, configL_z0_z0]

lemma configLEE_none_some (i : Fin k) :
    configLEE s t ρ x none (some i) = -s i := by
  simp [configLEE, configEEmbed, configL_z0_z]

lemma configLEE_some_none (i : Fin k) :
    configLEE s t ρ x (some i) none = -s i := by
  simp only [configLEE, configEEmbed, submatrix_apply]
  exact (configL_symm s t ρ x (idxZ i) idxZ0).trans (configL_z0_z s t ρ x i)

lemma configLEE_some_some (i h : Fin k) :
    configLEE s t ρ x (some i) (some h) =
      if i = h then s i * configD t ρ x i else 0 := by
  simp [configLEE, configEEmbed, configL_z_z]

lemma configL_posSemidef (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) :
    (configL s t ρ x).PosSemidef := by
  unfold configL
  refine PosSemidef.add ?_ ?_
  · exact posSemidef_sum _ fun i _ =>
      (posSemidef_vecMulVec_self_star (R := ℝ)
        (e (idxZ0 : ConfigIdx k p) - e (idxZ (p := p) i))).smul (hs i).le
  · exact posSemidef_sum _ fun i _ => posSemidef_sum _ fun j _ =>
      (posSemidef_vecMulVec_self_star (R := ℝ)
        (e (idxZ (p := p) i) - e (idxY (k := k) j))).smul
        (mul_nonneg (mul_nonneg (hs i).le (hρ j).le) (sq_nonneg _))

lemma configLEE_posSemidef (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) :
    (configLEE s t ρ x).PosSemidef :=
  (configL_posSemidef s t ρ x hs hρ).submatrix _

lemma configLEE_mulVec_none (v : Option (Fin k) → ℝ) :
    (configLEE s t ρ x *ᵥ v) none =
      configσ s * v none - ∑ i, s i * v (some i) := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_option]
  simp only [configLEE_none_none, configLEE_none_some]
  rw [sub_eq_add_neg]
  congr 1
  simp [neg_mul, sum_neg_distrib]

lemma configLEE_mulVec_some (v : Option (Fin k) → ℝ) (i : Fin k) :
    (configLEE s t ρ x *ᵥ v) (some i) =
      -s i * v none + s i * configD t ρ x i * v (some i) := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_option]
  simp only [configLEE_some_none]
  have : ∑ h : Fin k, configLEE s t ρ x (some i) (some h) * v (some h) =
      s i * configD t ρ x i * v (some i) := by
    rw [Fintype.sum_eq_single i]
    · simp [configLEE_some_some]
    · intro h hh
      simp [configLEE_some_some, Ne.symm hh]
  rw [this]

lemma configLEE_dot (v : Option (Fin k) → ℝ) :
    v ⬝ᵥ configLEE s t ρ x *ᵥ v =
      configσ s * v none ^ 2 - 2 * v none * ∑ i, s i * v (some i) +
        ∑ i, s i * configD t ρ x i * v (some i) ^ 2 := by
  simp only [dotProduct]
  rw [Fintype.sum_option, configLEE_mulVec_none]
  simp only [configLEE_mulVec_some]
  calc
    v none * (configσ s * v none - ∑ i, s i * v (some i)) +
        ∑ i, v (some i) * (-s i * v none + s i * configD t ρ x i * v (some i))
      = configσ s * v none ^ 2 - v none * ∑ i, s i * v (some i) +
          ∑ i, (-(s i * v none * v (some i)) +
            s i * configD t ρ x i * v (some i) ^ 2) := by
          simp [mul_sub, mul_add, sum_add_distrib, pow_two, mul_assoc,
            mul_left_comm, mul_comm]
    _ = configσ s * v none ^ 2 - v none * ∑ i, s i * v (some i) -
          ∑ i, s i * v none * v (some i) +
            ∑ i, s i * configD t ρ x i * v (some i) ^ 2 := by
          simp [sum_add_distrib, sum_neg_distrib]
          abel
    _ = configσ s * v none ^ 2 - 2 * v none * ∑ i, s i * v (some i) +
          ∑ i, s i * configD t ρ x i * v (some i) ^ 2 := by
          have : ∑ i, s i * v none * v (some i) = v none * ∑ i, s i * v (some i) := by
            simp [Finset.mul_sum, mul_left_comm, mul_assoc]
          rw [this]
          ring

lemma configLEE_quad (v : Option (Fin k) → ℝ) :
    v ⬝ᵥ configLEE s t ρ x *ᵥ v =
      ∑ i, s i * (v none - v (some i)) ^ 2 +
        ∑ i, s i * configH t ρ x i * v (some i) ^ 2 := by
  rw [configLEE_dot]
  have hexp : ∑ i, s i * (v none - v (some i)) ^ 2 =
      configσ s * v none ^ 2 - 2 * v none * ∑ i, s i * v (some i) +
        ∑ i, s i * v (some i) ^ 2 := by
    simp only [configσ, sub_sq, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
    simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm]
  rw [hexp]
  have hD : ∑ i, s i * configD t ρ x i * v (some i) ^ 2 =
      ∑ i, s i * v (some i) ^ 2 +
        ∑ i, s i * configH t ρ x i * v (some i) ^ 2 := by
    simp only [configD, mul_add, add_mul, sum_add_distrib, mul_assoc]
    ring
  rw [hD]
  ring

lemma configLEE_isHermitian : (configLEE s t ρ x).IsHermitian := by
  rw [isHermitian_iff_isSymm]
  ext a b
  simp only [transpose_apply]
  cases a <;> cases b
  · rfl
  · rw [configLEE_none_some, configLEE_some_none]
  · rw [configLEE_some_none, configLEE_none_some]
  · simp [configLEE_some_some]
    split_ifs <;> simp_all

lemma configLEE_posDef (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    (configLEE s t ρ x).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (configLEE_isHermitian s t ρ x) fun v hv => ?_
  have hstar : star v = v := funext fun _ => star_trivial _
  rw [hstar, configLEE_quad]
  have h1nn : 0 ≤ ∑ i, s i * (v none - v (some i)) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hs i).le (sq_nonneg _)
  have h2nn : 0 ≤ ∑ i, s i * configH t ρ x i * v (some i) ^ 2 :=
    sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hs i).le (configH_nonneg t hρ x i)) (sq_nonneg _)
  refine lt_of_le_of_ne (add_nonneg h1nn h2nn) fun hz => ?_
  obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg h1nn h2nn).1 hz.symm
  have hconst : ∀ i, v (some i) = v none := by
    intro i
    have : s i * (v none - v (some i)) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hs i).le (sq_nonneg _)).1 h1 _ (mem_univ _)
    exact (eq_of_sub_eq_zero (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp this).resolve_left (hs i).ne'))).symm
  have hv0sq : ∑ i, s i * configH t ρ x i * v none ^ 2 = 0 := by
    simpa [hconst] using h2
  rcases eq_or_ne (v none) 0 with hv0 | hvn
  · have : v = 0 := by
      ext a
      cases a with
      | none => exact hv0
      | some i => simpa [hv0] using hconst i
    exact hv this
  · have hH0 : ∑ i, s i * configH t ρ x i = 0 := by
      have : (∑ i, s i * configH t ρ x i) * v none ^ 2 = 0 := by
        rw [Finset.sum_mul]
        simpa [mul_assoc] using hv0sq
      exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero 2 hvn)
    have hγ0 : configγ s t ρ x = 0 := by
      rw [configγ_eq_sum s t hρ x]
      refine Fintype.sum_eq_zero _ fun i => ?_
      have hterm : s i * configH t ρ x i = 0 :=
        (sum_eq_zero_iff_of_nonneg fun i _ =>
          mul_nonneg (hs i).le (configH_nonneg t hρ x i)).1 hH0 _ (mem_univ _)
      simp [hterm]
    exact (ne_of_gt hγ) hγ0

/-! ### SC05 — Schur complement of the lower-right of `L_EE` is `γ` -/

lemma configγ_eq_schur (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) :
    configσ s - s ⬝ᵥ (diagonal fun i => s i * configD t ρ x i)⁻¹ *ᵥ s =
      configγ s t ρ x := by
  have hA :
      (diagonal fun i : Fin k => s i * configD t ρ x i) *
        (diagonal fun i => (s i * configD t ρ x i)⁻¹) = 1 := by
    ext i j
    simp only [mul_apply, diagonal_apply, one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Fintype.sum_eq_single i]
      · simp only [↓reduceIte]
        have hd : s i * configD t ρ x i ≠ 0 :=
          mul_ne_zero (hs i).ne' (configD_pos t hρ x i).ne'
        field_simp [hd]
        exact div_self hd
      · intro k hk
        simp [hk]
    · simp only [hij, ↓reduceIte]
      refine Fintype.sum_eq_zero _ fun k => ?_
      by_cases hik : i = k
      · subst hik; simp [hij]
      · simp [hik]
  rw [Matrix.inv_eq_right_inv hA]
  simp only [dotProduct, mulVec_diagonal, configγ, configQ, configσ]
  refine congrArg (fun z => configσ s - z) ?_
  refine Fintype.sum_congr _ _ fun i => ?_
  have hd : s i * configD t ρ x i ≠ 0 :=
    mul_ne_zero (hs i).ne' (configD_pos t hρ x i).ne'
  field_simp [hd]

/-! ### SC06 — inverse of `L_EE` -/

/-- The weight vector on the `E`-indices: `1` at the axis vector and `(configD t ρ x i)⁻¹` at the
`i`-th left vector. -/
def configW : Option (Fin k) → ℝ
  | none => 1
  | some i => (configD t ρ x i)⁻¹

/-- The diagonal matrix on the `E`-indices with `0` at the axis vector and `(s i * configD t ρ x
i)⁻¹` at the `i`-th left vector; it is the diagonal part of `(configLEE s t ρ x)⁻¹`. -/
def configLEEInvDiag : Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  diagonal fun
    | none => 0
    | some i => (s i * configD t ρ x i)⁻¹

lemma configLEE_mulVec_w (_hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) :
    configLEE s t ρ x *ᵥ configW t ρ x =
      fun a => if a = none then configγ s t ρ x else 0 := by
  ext a
  cases a with
  | none =>
    rw [configLEE_mulVec_none]
    simp only [configW, ite_true, configγ, configQ, configσ, div_eq_mul_inv]
    ring
  | some i =>
    rw [configLEE_mulVec_some]
    simp only [configW]
    have hd : configD t ρ x i ≠ 0 := (configD_pos t hρ x i).ne'
    simp only [Option.some_ne_none, ite_false]
    field_simp [hd]
    ring

lemma mul_vecMulVec (A : Matrix (Option (Fin k)) (Option (Fin k)) ℝ)
    (u w : Option (Fin k) → ℝ) :
    A * vecMulVec u w = vecMulVec (A *ᵥ u) w := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

lemma configLEE_mul_invDiag_apply (a b : Option (Fin k)) :
    (configLEE s t ρ x * configLEEInvDiag s t ρ x) a b =
      match b with
      | none => 0
      | some j => configLEE s t ρ x a (some j) * (s j * configD t ρ x j)⁻¹ := by
  cases b with
  | none =>
    simp only [mul_apply, configLEEInvDiag]
    refine Fintype.sum_eq_zero _ fun c => ?_
    cases c <;> simp [diagonal]
  | some j =>
    simp only [mul_apply, configLEEInvDiag]
    rw [Fintype.sum_eq_single (some j)]
    · simp [diagonal]
    · intro c hc
      match c with
      | none => simp [diagonal]
      | some i =>
        have hne : i ≠ j := mt (congrArg some) hc
        simp [diagonal, hne]

lemma configLEE_inv (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    (configLEE s t ρ x)⁻¹ =
      configLEEInvDiag s t ρ x +
        (configγ s t ρ x)⁻¹ • vecMulVec (configW t ρ x) (configW t ρ x) := by
  refine Matrix.inv_eq_right_inv ?_
  have hγne : configγ s t ρ x ≠ 0 := hγ.ne'
  have hw := configLEE_mulVec_w s t ρ x hs hρ
  have hprod :
      configLEE s t ρ x *
          (configLEEInvDiag s t ρ x +
            (configγ s t ρ x)⁻¹ • vecMulVec (configW t ρ x) (configW t ρ x)) =
        configLEE s t ρ x * configLEEInvDiag s t ρ x +
          (configγ s t ρ x)⁻¹ •
            vecMulVec (configLEE s t ρ x *ᵥ configW t ρ x) (configW t ρ x) := by
    simp only [mul_add, Matrix.mul_smul, mul_vecMulVec]
  rw [hprod, hw]
  ext a b
  cases a with
  | none =>
    cases b with
    | none =>
      have hL : (configLEE s t ρ x * configLEEInvDiag s t ρ x) none none = 0 :=
        configLEE_mul_invDiag_apply s t ρ x none none
      have hR :
          ((configγ s t ρ x)⁻¹ •
              vecMulVec
                (fun a : Option (Fin k) =>
                  if a = none then configγ s t ρ x else 0)
                (configW t ρ x)) none none =
            (configγ s t ρ x)⁻¹ * configγ s t ρ x := by
        simp [vecMulVec_apply, configW]
      simp [Matrix.add_apply, hL, hR, one_apply]
      field_simp [hγne]
    | some j =>
      have hL : (configLEE s t ρ x * configLEEInvDiag s t ρ x) none (some j) =
          -s j * (s j * configD t ρ x j)⁻¹ := by
        rw [configLEE_mul_invDiag_apply]
        simp [configLEE_none_some]
      have hR :
          ((configγ s t ρ x)⁻¹ •
              vecMulVec
                (fun a : Option (Fin k) =>
                  if a = none then configγ s t ρ x else 0)
                (configW t ρ x)) none (some j) =
            (configγ s t ρ x)⁻¹ * configγ s t ρ x * (configD t ρ x j)⁻¹ := by
        simp [vecMulVec_apply, configW]
        ring
      have hd : configD t ρ x j ≠ 0 := (configD_pos t hρ x j).ne'
      have hsj : s j ≠ 0 := (hs j).ne'
      simp only [Matrix.add_apply, hL, _root_.mul_inv_rev, neg_mul, hR, one_apply, reduceCtorEq,
        ↓reduceIte]
      rw [← mul_assoc, inv_mul_cancel₀ hγne, one_mul]
      field_simp [hsj, hd]
      ring
  | some i =>
    cases b with
    | none =>
      have hL : (configLEE s t ρ x * configLEEInvDiag s t ρ x) (some i) none = 0 :=
        configLEE_mul_invDiag_apply s t ρ x (some i) none
      have hR :
          ((configγ s t ρ x)⁻¹ •
              vecMulVec
                (fun a : Option (Fin k) =>
                  if a = none then configγ s t ρ x else 0)
                (configW t ρ x)) (some i) none = 0 := by
        simp [vecMulVec_apply]
      simp [Matrix.add_apply, hL, hR, one_apply]
    | some j =>
      have hL : (configLEE s t ρ x * configLEEInvDiag s t ρ x) (some i) (some j) =
          (if i = j then s i * configD t ρ x i else 0) *
            (s j * configD t ρ x j)⁻¹ := by
        rw [configLEE_mul_invDiag_apply]
        simp [configLEE_some_some]
      have hR :
          ((configγ s t ρ x)⁻¹ •
              vecMulVec
                (fun a : Option (Fin k) =>
                  if a = none then configγ s t ρ x else 0)
                (configW t ρ x)) (some i) (some j) = 0 := by
        simp [vecMulVec_apply]
      have hdj : configD t ρ x j ≠ 0 := (configD_pos t hρ x j).ne'
      have hsj : s j ≠ 0 := (hs j).ne'
      simp [Matrix.add_apply, hL, hR, one_apply]
      by_cases hij : i = j
      · subst hij
        simp
        field_simp [hdj, hsj]
      · simp [hij]

/-! ### SC07 — `L_red` and `𝒰` -/

/-- The right-vector block of the weighted Laplacian `configL s t ρ x`. -/
def configLTT : Matrix (Fin p) (Fin p) ℝ :=
  (configL s t ρ x).submatrix idxY idxY

/-- The block of the weighted Laplacian `configL s t ρ x` with right-vector rows and `E`-columns. -/
def configLTE : Matrix (Fin p) (Option (Fin k)) ℝ :=
  (configL s t ρ x).submatrix idxY (configEEmbed (p := p))

/-- The block of the weighted Laplacian `configL s t ρ x` with `E`-rows and right-vector columns. -/
def configLET : Matrix (Option (Fin k)) (Fin p) ℝ :=
  (configL s t ρ x).submatrix (configEEmbed (p := p)) idxY

/-- The `E`-rows of the three-column factor `configF s t ρ x`. -/
def configFE : Matrix (Option (Fin k)) (Fin 3) ℝ :=
  (configF s t ρ x).submatrix (configEEmbed (p := p)) id

/-- The right-vector rows of the three-column factor `configF s t ρ x`. -/
def configFT : Matrix (Fin p) (Fin 3) ℝ :=
  (configF s t ρ x).submatrix idxY id

/-- The Schur complement `L_TT - L_TE L_EE⁻¹ L_ET` of the `E`-block in the weighted Laplacian. The
positivity hypotheses are the conditions under which `L_EE` is invertible. -/
def configLred (_hs : ∀ i, 0 < s i) (_hρ : ∀ j, 0 < ρ j)
    (_hγ : 0 < configγ s t ρ x) : Matrix (Fin p) (Fin p) ℝ :=
  configLTT s t ρ x -
    configLTE s t ρ x * (configLEE s t ρ x)⁻¹ * configLET s t ρ x

/-- The reduced three-column factor `F_T - L_TE L_EE⁻¹ F_E`. The positivity hypotheses are the
conditions under which `L_EE` is invertible. -/
def configU (_hs : ∀ i, 0 < s i) (_hρ : ∀ j, 0 < ρ j)
    (_hγ : 0 < configγ s t ρ x) : Matrix (Fin p) (Fin 3) ℝ :=
  configFT s t ρ x -
    configLTE s t ρ x * (configLEE s t ρ x)⁻¹ * configFE s t ρ x

lemma configLEE_isUnit (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) : IsUnit (configLEE s t ρ x) :=
  (configLEE_posDef s t ρ x hs hρ hγ).isUnit

/-! ### Feature / Laplacian blocks on `E` and `T` -/

lemma configFE_none : configFE s t ρ x none = e (0 : Fin 3) := by
  ext c
  simp [configFE, submatrix_apply, configEEmbed, configF_z0]

lemma configFE_some (i : Fin k) :
    configFE s t ρ x (some i) = s i • v (t i) := by
  ext c
  simp [configFE, submatrix_apply, configEEmbed, configF_z]

lemma configFT_apply (j : Fin p) :
    configFT s t ρ x j = ρ j • b (x j) := by
  ext c
  simp [configFT, submatrix_apply, configF_y]

lemma configLTE_none (j : Fin p) : configLTE s t ρ x j none = 0 := by
  simp only [configLTE, configEEmbed, submatrix_apply]
  exact (configL_symm s t ρ x (idxY j) idxZ0).trans (configL_z0_y s t ρ x j)

lemma configLTE_some (j : Fin p) (i : Fin k) :
    configLTE s t ρ x j (some i) = -(s i * ρ j * truncSq (t i) (x j)) := by
  simp only [configLTE, configEEmbed, submatrix_apply]
  exact (configL_symm s t ρ x (idxY j) (idxZ i)).trans (configL_z_y s t ρ x i j)

lemma configLET_none (j : Fin p) : configLET s t ρ x none j = 0 := by
  simp [configLET, configEEmbed, submatrix_apply, configL_z0_y]

lemma configLET_some (i : Fin k) (j : Fin p) :
    configLET s t ρ x (some i) j = -(s i * ρ j * truncSq (t i) (x j)) := by
  simp [configLET, configEEmbed, submatrix_apply, configL_z_y]

lemma configLTT_apply (j ℓ : Fin p) :
    configLTT s t ρ x j ℓ =
      if j = ℓ then ∑ i, s i * ρ j * truncSq (t i) (x j) else 0 := by
  simp [configLTT, submatrix_apply, configL_y_y]

lemma Vvec_eq_e0_add_sum (q : Fin k → ℝ) :
    Vvec t q = e (0 : Fin 3) + ∑ i, q i • v (t i) := by
  simp only [Vvec, 𝒜, add_mulVec, one_mulVec]
  congr 1
  rw [sum_mulVec]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [smul_mulVec, mulVec_vecMulVec_self]
  have hv : v (t i) ⬝ᵥ e (0 : Fin 3) = 1 := by
    rw [dotProduct_comm, e0_dot_v]
  simp

lemma configFE_transpose_mulVec_w :
    (configFE s t ρ x)ᵀ *ᵥ configW t ρ x =
      Vvec t (configQ s t ρ x) := by
  ext c
  simp only [mulVec, transpose_apply, dotProduct]
  rw [Fintype.sum_option]
  simp only [configW]
  have hsum :
      ∑ i, configFE s t ρ x (some i) c * (configD t ρ x i)⁻¹ =
        ∑ i, configQ s t ρ x i * v (t i) c := by
    refine Fintype.sum_congr _ _ fun i => ?_
    simp [configFE_some, configQ, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [configFE_none, hsum, Vvec_eq_e0_add_sum t (configQ s t ρ x)]
  simp [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-! ### SC10 — center row of `L_EE⁻¹ F_E` -/

/-- The product `L_EE⁻¹ F_E` of the inverse `E`-block with the `E`-rows of the three-column
factor. -/
def configInvFE : Matrix (Option (Fin k)) (Fin 3) ℝ :=
  (configLEE s t ρ x)⁻¹ * configFE s t ρ x

lemma configLEE_invDiag_mul_FE_none :
    (configLEEInvDiag s t ρ x * configFE s t ρ x) none = (0 : Fin 3 → ℝ) := by
  ext c
  simp only [mul_apply, configLEEInvDiag, Pi.zero_apply]
  refine Fintype.sum_eq_zero _ fun a => ?_
  cases a <;> simp [diagonal]

lemma configLEE_invDiag_mul_FE_some (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (i : Fin k) :
    (configLEEInvDiag s t ρ x * configFE s t ρ x) (some i) =
      (configD t ρ x i)⁻¹ • v (t i) := by
  ext c
  simp only [mul_apply, configLEEInvDiag, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single (some i)]
  · have hsi : s i ≠ 0 := (hs i).ne'
    have hd : configD t ρ x i ≠ 0 := (configD_pos t hρ x i).ne'
    simp only [diagonal_apply_eq, configFE_some]
    have : (s i * configD t ρ x i)⁻¹ * (s i * v (t i) c) =
        (configD t ρ x i)⁻¹ * v (t i) c := by
      field_simp [hsi, hd]
    exact this
  · intro a ha
    have : configLEEInvDiag s t ρ x (some i) a = 0 := by
      simp only [configLEEInvDiag]
      exact diagonal_apply_ne _ ha.symm
    simp only [configLEEInvDiag] at this
    rw [this, zero_mul]

lemma vecMulVec_w_mul_FE (a : Option (Fin k)) :
    (vecMulVec (configW t ρ x) (configW t ρ x) * configFE s t ρ x) a =
      configW t ρ x a • Vvec t (configQ s t ρ x) := by
  ext c
  simp only [mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have hdot : ∑ b, configW t ρ x b * configFE s t ρ x b c =
      Vvec t (configQ s t ρ x) c := by
    have := congrArg (fun f => f c) (configFE_transpose_mulVec_w s t ρ x)
    simp only [mulVec, transpose_apply, dotProduct] at this
    convert this using 1
    refine Fintype.sum_congr _ _ fun b => ?_
    ring
  have : ∑ b, configW t ρ x a * configW t ρ x b * configFE s t ρ x b c =
      configW t ρ x a * ∑ b, configW t ρ x b * configFE s t ρ x b c := by
    simp_rw [mul_assoc]
    exact (Finset.mul_sum Finset.univ
      (fun b => configW t ρ x b * configFE s t ρ x b c)
      (configW t ρ x a)).symm
  rw [this, hdot]

lemma configInvFE_none (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    configInvFE s t ρ x none =
      (configγ s t ρ x)⁻¹ • Vvec t (configQ s t ρ x) := by
  ext c
  simp only [configInvFE]
  rw [configLEE_inv s t ρ x hs hρ hγ]
  simp only [mul_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  have hterm (a : Option (Fin k)) :
      (configLEEInvDiag s t ρ x none a +
          (configγ s t ρ x)⁻¹ * (configW t ρ x none * configW t ρ x a)) *
        configFE s t ρ x a c =
        configLEEInvDiag s t ρ x none a * configFE s t ρ x a c +
          (configγ s t ρ x)⁻¹ *
            (configW t ρ x none * (configW t ρ x a * configFE s t ρ x a c)) := by
    ring
  simp_rw [hterm, sum_add_distrib]
  have hD : ∑ a, configLEEInvDiag s t ρ x none a * configFE s t ρ x a c = 0 :=
    congrArg (fun f => f c) (configLEE_invDiag_mul_FE_none s t ρ x)
  have hW : ∑ a, configW t ρ x none * (configW t ρ x a * configFE s t ρ x a c) =
      Vvec t (configQ s t ρ x) c := by
    have := congrArg (fun f => f c) (vecMulVec_w_mul_FE s t ρ x none)
    simp only [mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, configW] at this
    simpa [configW, one_mul, mul_assoc] using this
  rw [hD, zero_add, ← Finset.mul_sum, hW]
  simp [smul_eq_mul]

lemma configInvFE_some (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) (i : Fin k) :
    configInvFE s t ρ x (some i) =
      (configD t ρ x i)⁻¹ •
        (v (t i) + (configγ s t ρ x)⁻¹ • Vvec t (configQ s t ρ x)) := by
  ext c
  simp only [configInvFE]
  rw [configLEE_inv s t ρ x hs hρ hγ]
  simp only [mul_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  have hterm (a : Option (Fin k)) :
      (configLEEInvDiag s t ρ x (some i) a +
          (configγ s t ρ x)⁻¹ * (configW t ρ x (some i) * configW t ρ x a)) *
        configFE s t ρ x a c =
        configLEEInvDiag s t ρ x (some i) a * configFE s t ρ x a c +
          (configγ s t ρ x)⁻¹ *
            (configW t ρ x (some i) * (configW t ρ x a * configFE s t ρ x a c)) := by
    ring
  simp_rw [hterm, sum_add_distrib]
  have hD : ∑ a, configLEEInvDiag s t ρ x (some i) a * configFE s t ρ x a c =
      (configD t ρ x i)⁻¹ * v (t i) c :=
    congrArg (fun f => f c) (configLEE_invDiag_mul_FE_some s t ρ x hs hρ i)
  have hW : ∑ a, configW t ρ x (some i) * (configW t ρ x a * configFE s t ρ x a c) =
      configW t ρ x (some i) * Vvec t (configQ s t ρ x) c := by
    have := congrArg (fun f => f c) (vecMulVec_w_mul_FE s t ρ x (some i))
    simp only [mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul] at this
    convert this using 1
    refine Fintype.sum_congr _ _ fun a => ?_
    ring
  rw [hD, ← Finset.mul_sum, hW]
  simp [configW, smul_eq_mul]
  ring

/-! ### SC11 — `I + F_Eᵀ L_EE⁻¹ F_E = 𝒜 + V Vᵀ / γ` -/

lemma one_add_configFE_conj_inv (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) +
      (configFE s t ρ x)ᵀ * (configLEE s t ρ x)⁻¹ * configFE s t ρ x =
      𝒦Mat t (configQ s t ρ x) (configγ s t ρ x) := by
  have hmul :
      (configFE s t ρ x)ᵀ * (configLEE s t ρ x)⁻¹ * configFE s t ρ x =
        (configFE s t ρ x)ᵀ * configInvFE s t ρ x := by
    simp [configInvFE, Matrix.mul_assoc]
  rw [hmul]
  ext c d
  have hentry :
      ((configFE s t ρ x)ᵀ * configInvFE s t ρ x) c d =
        configFE s t ρ x none c * configInvFE s t ρ x none d +
          ∑ i, configFE s t ρ x (some i) c * configInvFE s t ρ x (some i) d := by
    simp only [mul_apply, transpose_apply]
    rw [Fintype.sum_option]
  rw [Matrix.add_apply, one_apply, hentry]
  simp only [configFE_none, configInvFE_none s t ρ x hs hρ hγ, configFE_some,
    configInvFE_some s t ρ x hs hρ hγ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hV : e (0 : Fin 3) c + ∑ i, configQ s t ρ x i * v (t i) c =
      Vvec t (configQ s t ρ x) c := by
    simpa [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun f => f c) (Vvec_eq_e0_add_sum t (configQ s t ρ x)).symm
  have hsum :
      ∑ i, s i * v (t i) c *
          ((configD t ρ x i)⁻¹ *
            (v (t i) d + (configγ s t ρ x)⁻¹ * Vvec t (configQ s t ρ x) d)) =
        ∑ i, configQ s t ρ x i * v (t i) c * v (t i) d +
          (configγ s t ρ x)⁻¹ * (∑ i, configQ s t ρ x i * v (t i) c) *
            Vvec t (configQ s t ρ x) d := by
    simp only [mul_add, sum_add_distrib, configQ, div_eq_mul_inv]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Fintype.sum_congr _ _ fun i => ?_
      ring
    · simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hsum]
  have he0 :
      e (0 : Fin 3) c * ((configγ s t ρ x)⁻¹ * Vvec t (configQ s t ρ x) d) +
          ((configγ s t ρ x)⁻¹ * ∑ i, configQ s t ρ x i * v (t i) c) *
            Vvec t (configQ s t ρ x) d =
        (configγ s t ρ x)⁻¹ * Vvec t (configQ s t ρ x) c *
          Vvec t (configQ s t ρ x) d := by
    linear_combination
      (configγ s t ρ x)⁻¹ * Vvec t (configQ s t ρ x) d * hV
  simp only [𝒦Mat, 𝒜_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, div_eq_inv_mul]
  linear_combination he0

/-! ### SC12 — rows of `𝒰` -/

lemma configLTE_mul_InvFE (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) (j : Fin p) :
    (configLTE s t ρ x * configInvFE s t ρ x) j =
      -ρ j •
        (∑ i, (configQ s t ρ x i * truncSq (t i) (x j)) • v (t i) +
          (h t (configQ s t ρ x) (x j) / configγ s t ρ x) •
            Vvec t (configQ s t ρ x)) := by
  ext c
  simp only [mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_option]
  simp only [configLTE_none, configLTE_some, configInvFE_some s t ρ x hs hρ hγ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add]
  have hsum :
      ∑ i, -(s i * ρ j * truncSq (t i) (x j)) *
          ((configD t ρ x i)⁻¹ *
            (v (t i) c + (configγ s t ρ x)⁻¹ * Vvec t (configQ s t ρ x) c)) =
        -ρ j *
          (∑ i, configQ s t ρ x i * truncSq (t i) (x j) * v (t i) c +
            (h t (configQ s t ρ x) (x j) / configγ s t ρ x) *
              Vvec t (configQ s t ρ x) c) := by
    simp only [h, configQ, div_eq_mul_inv, mul_add, sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, neg_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Fintype.sum_congr _ _ fun i => ?_
      ring
    · simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hsum]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add]

lemma configU_apply (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) (j : Fin p) :
    configU s t ρ x hs hρ hγ j =
      ρ j • U t (configQ s t ρ x) (configγ s t ρ x) (x j) := by
  ext c
  have hmul :
      (configLTE s t ρ x * (configLEE s t ρ x)⁻¹ * configFE s t ρ x) j c =
        (configLTE s t ρ x * configInvFE s t ρ x) j c := by
    simp [configInvFE, Matrix.mul_assoc]
  simp only [configU, Matrix.sub_apply]
  rw [hmul, configFT_apply, configLTE_mul_InvFE s t ρ x hs hρ hγ]
  simp [U, bhat, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  ring

/-- Expand `(A * wwᵀ * C) j ℓ` without unfolding the index type of `w`. -/
lemma mul_vecMulVec_mul_apply {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (w : n → ℝ) (C : Matrix n m ℝ) (j ℓ : m) :
    (A * vecMulVec w w * C) j ℓ =
      (∑ a, A j a * w a) * (∑ b, w b * C b ℓ) := by
  rw [Matrix.mul_assoc]
  have hentry :
      (A * (vecMulVec w w * C)) j ℓ =
        (A *ᵥ fun k => (vecMulVec w w * C) k ℓ) j := by
    simp only [mulVec, dotProduct]
    rw [Matrix.mul_apply]
  have hcol : (fun k => (vecMulVec w w * C) k ℓ) = (w ⬝ᵥ fun b => C b ℓ) • w := by
    ext k
    have : (vecMulVec w w * C) k ℓ = (vecMulVec w w *ᵥ fun b => C b ℓ) k := by
      simp only [mulVec, dotProduct]
      rw [Matrix.mul_apply]
    rw [this, vecMulVec_mulVec, op_smul_eq_smul]
  rw [hentry, hcol, mulVec_smul, Pi.smul_apply, smul_eq_mul]
  simp only [mulVec, dotProduct]
  ring

/-! ### SC14 — off-diagonal of `L_red` -/

lemma configLred_of_ne (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) {j ℓ : Fin p} (hjl : j ≠ ℓ) :
    -(configLred s t ρ x hs hρ hγ j ℓ) =
      ρ j * ρ ℓ *
        (∑ i, configQ s t ρ x i * truncSq (t i) (x j) * truncSq (t i) (x ℓ) +
          h t (configQ s t ρ x) (x j) * h t (configQ s t ρ x) (x ℓ) /
            configγ s t ρ x) := by
  have hLTT : configLTT s t ρ x j ℓ = 0 := by
    simp [configLTT_apply, hjl]
  have hsplit :
      configLTE s t ρ x *
          (configLEEInvDiag s t ρ x +
            (configγ s t ρ x)⁻¹ • vecMulVec (configW t ρ x) (configW t ρ x)) *
          configLET s t ρ x =
        configLTE s t ρ x * configLEEInvDiag s t ρ x * configLET s t ρ x +
          configLTE s t ρ x *
            ((configγ s t ρ x)⁻¹ • vecMulVec (configW t ρ x) (configW t ρ x)) *
            configLET s t ρ x := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have hD :
      (configLTE s t ρ x * configLEEInvDiag s t ρ x * configLET s t ρ x) j ℓ =
        ρ j * ρ ℓ *
          ∑ i, configQ s t ρ x i * truncSq (t i) (x j) * truncSq (t i) (x ℓ) := by
    have hinner (a : Option (Fin k)) :
        ∑ b, configLTE s t ρ x j b * configLEEInvDiag s t ρ x b a =
          configLTE s t ρ x j a * configLEEInvDiag s t ρ x a a := by
      rw [Fintype.sum_eq_single a]
      · intro b hb
        simp only [configLEEInvDiag]
        rw [diagonal_apply_ne _ hb, mul_zero]
    simp only [mul_apply]
    have : ∑ a, (∑ b, configLTE s t ρ x j b * configLEEInvDiag s t ρ x b a) *
        configLET s t ρ x a ℓ =
        ∑ a, configLTE s t ρ x j a * configLEEInvDiag s t ρ x a a *
          configLET s t ρ x a ℓ := by
      refine Fintype.sum_congr _ _ fun a => ?_
      rw [hinner]
    rw [this, Fintype.sum_option]
    simp only [configLTE_none, configLET_none, configLEEInvDiag, diagonal_apply,
      zero_mul, mul_zero, zero_add]
    simp only [configLTE_some, configLET_some, configQ, div_eq_mul_inv, ↓reduceIte]
    have hterm (i : Fin k) :
        -(s i * ρ j * truncSq (t i) (x j)) * (s i * configD t ρ x i)⁻¹ *
            -(s i * ρ ℓ * truncSq (t i) (x ℓ)) =
          ρ j * ρ ℓ *
            (s i * (configD t ρ x i)⁻¹ * truncSq (t i) (x j) * truncSq (t i) (x ℓ)) := by
      have hd : configD t ρ x i ≠ 0 := (configD_pos t hρ x i).ne'
      have hsi : s i ≠ 0 := (hs i).ne'
      field_simp [hd, hsi]
    simp_rw [hterm]
    simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
  have hW :
      (configLTE s t ρ x *
          ((configγ s t ρ x)⁻¹ •
            vecMulVec (configW t ρ x) (configW t ρ x)) *
          configLET s t ρ x) j ℓ =
        ρ j * ρ ℓ * (h t (configQ s t ρ x) (x j) *
          h t (configQ s t ρ x) (x ℓ) / configγ s t ρ x) := by
    have hdot (jj : Fin p) :
        ∑ a, configLTE s t ρ x jj a * configW t ρ x a =
          -ρ jj * h t (configQ s t ρ x) (x jj) := by
      rw [Fintype.sum_option]
      simp only [configLTE_none, configLTE_some, configW, h, configQ,
        div_eq_mul_inv, zero_mul, zero_add]
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have hLETdot :
        ∑ b, configW t ρ x b * configLET s t ρ x b ℓ =
          -ρ ℓ * h t (configQ s t ρ x) (x ℓ) := by
      rw [Fintype.sum_option]
      simp only [configLET_none, configLET_some, configW, h, configQ,
        div_eq_mul_inv]
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have hfactor :
        (configLTE s t ρ x *
            ((configγ s t ρ x)⁻¹ • vecMulVec (configW t ρ x) (configW t ρ x)) *
            configLET s t ρ x) j ℓ =
          (configγ s t ρ x)⁻¹ *
            (∑ a, configLTE s t ρ x j a * configW t ρ x a) *
              (∑ b, configW t ρ x b * configLET s t ρ x b ℓ) := by
      have hsmul :
          configLTE s t ρ x *
              ((configγ s t ρ x)⁻¹ • vecMulVec (configW t ρ x) (configW t ρ x)) *
              configLET s t ρ x =
            (configγ s t ρ x)⁻¹ •
              (configLTE s t ρ x * vecMulVec (configW t ρ x) (configW t ρ x) *
                configLET s t ρ x) := by
        simp [Matrix.mul_smul, Matrix.smul_mul]
      rw [hsmul, Matrix.smul_apply, smul_eq_mul, mul_vecMulVec_mul_apply]
      ring
    rw [hfactor, hdot, hLETdot]
    ring
  simp only [configLred, Matrix.sub_apply, hLTT, zero_sub, neg_neg]
  rw [configLEE_inv s t ρ x hs hρ hγ, hsplit, Matrix.add_apply, hD, hW]
  ring

lemma configLred_of_ne_nonneg (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) {j ℓ : Fin p} (hjl : j ≠ ℓ) :
    0 ≤ -(configLred s t ρ x hs hρ hγ j ℓ) := by
  rw [configLred_of_ne s t ρ x hs hρ hγ hjl]
  refine mul_nonneg (mul_nonneg (hρ j).le (hρ ℓ).le) (add_nonneg ?_ ?_)
  · exact sum_nonneg fun i _ =>
      mul_nonneg
        (mul_nonneg (configQ_pos s t hρ x (hs i)).le (sq_nonneg _))
        (sq_nonneg _)
  · exact div_nonneg
      (mul_nonneg
        (sum_nonneg fun i _ =>
          mul_nonneg (configQ_pos s t hρ x (hs i)).le (sq_nonneg _))
        (sum_nonneg fun i _ =>
          mul_nonneg (configQ_pos s t hρ x (hs i)).le (sq_nonneg _)))
      hγ.le

/-! ### SC15 — `L 1 = 0` implies `L_red 1 = 0` -/

lemma configL_mulVec_one : configL s t ρ x *ᵥ (1 : ConfigIdx k p → ℝ) = 0 := by
  unfold configL
  simp [add_mulVec, sum_mulVec, smul_mulVec, vecMulVec_sub_single_mulVec_one]

lemma configLEE_mulVec_one_add (a : Option (Fin k)) :
    (configLEE s t ρ x *ᵥ (1 : Option (Fin k) → ℝ)) a +
        (configLET s t ρ x *ᵥ (1 : Fin p → ℝ)) a =
      (configL s t ρ x *ᵥ (1 : ConfigIdx k p → ℝ)) (configEEmbed a) := by
  simp only [mulVec, dotProduct, configLEE, configLET, submatrix_apply]
  rw [sum_configIdx, Fintype.sum_option]
  cases a <;> simp [configEEmbed]

lemma configLTT_mulVec_one_add (j : Fin p) :
    (configLTT s t ρ x *ᵥ (1 : Fin p → ℝ)) j +
        (configLTE s t ρ x *ᵥ (1 : Option (Fin k) → ℝ)) j =
      (configL s t ρ x *ᵥ (1 : ConfigIdx k p → ℝ)) (idxY j) := by
  simp only [mulVec, dotProduct, configLTT, configLTE, submatrix_apply]
  rw [sum_configIdx, Fintype.sum_option]
  simp [configEEmbed, add_comm]

lemma configLred_mulVec_one (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    configLred s t ρ x hs hρ hγ *ᵥ (1 : Fin p → ℝ) = 0 := by
  have := (configLEE_isUnit s t ρ x hs hρ hγ).invertible
  have hz : configL s t ρ x *ᵥ (1 : ConfigIdx k p → ℝ) = 0 :=
    configL_mulVec_one s t ρ x
  have hE : configLEE s t ρ x *ᵥ (1 : Option (Fin k) → ℝ) =
      -(configLET s t ρ x *ᵥ (1 : Fin p → ℝ)) := by
    ext a
    have := configLEE_mulVec_one_add s t ρ x a
    simp only [hz, Pi.zero_apply] at this
    simpa [Pi.neg_apply] using add_eq_zero_iff_eq_neg.mp this
  have hT : configLTT s t ρ x *ᵥ (1 : Fin p → ℝ) =
      -(configLTE s t ρ x *ᵥ (1 : Option (Fin k) → ℝ)) := by
    ext j
    have := configLTT_mulVec_one_add s t ρ x j
    simp only [hz, Pi.zero_apply] at this
    simpa [Pi.neg_apply] using add_eq_zero_iff_eq_neg.mp this
  have hcancel :
      (configLEE s t ρ x)⁻¹ *ᵥ configLET s t ρ x *ᵥ (1 : Fin p → ℝ) =
        -(1 : Option (Fin k) → ℝ) := by
    have hI : (configLEE s t ρ x)⁻¹ *ᵥ configLEE s t ρ x *ᵥ
        (1 : Option (Fin k) → ℝ) = 1 := by
      rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
    have := congrArg ((configLEE s t ρ x)⁻¹ *ᵥ ·) hE
    rw [hI, mulVec_neg] at this
    exact neg_eq_iff_eq_neg.mp this.symm
  simp only [configLred, sub_mulVec]
  rw [hT]
  have hassoc :
      (configLTE s t ρ x * (configLEE s t ρ x)⁻¹ * configLET s t ρ x) *ᵥ
          (1 : Fin p → ℝ) =
        configLTE s t ρ x *ᵥ (configLEE s t ρ x)⁻¹ *ᵥ
          configLET s t ρ x *ᵥ (1 : Fin p → ℝ) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [hassoc, hcancel]
  simp [mulVec_neg]

/-! ### SC16 — `L_red` is a weighted Laplacian -/

lemma weighted_sum_offDiag {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (ℓ : n → n → ℝ) {i j : n} (hij : i ≠ j) :
    ∑ p, ∑ q, (if p < q then ℓ p q else 0) *
        vecMulVec (e p - e q) (e p - e q) i j =
      if i < j then -ℓ i j else if j < i then -ℓ j i else 0 := by
  simp_rw [vecMulVec_sub_single_offDiag hij]
  have hdecomp (p q : n) :
      (if p < q then ℓ p q else 0) *
          (if p = i ∧ q = j then (-1 : ℝ) else if p = j ∧ q = i then -1 else 0) =
        (if p = i ∧ q = j then -(if i < j then ℓ i j else 0) else 0) +
          (if p = j ∧ q = i then -(if j < i then ℓ j i else 0) else 0) := by
    by_cases h1 : p = i ∧ q = j
    · simp only [h1, and_self, ↓reduceIte, mul_neg, mul_one, left_eq_add, ite_eq_right_iff,
      neg_eq_zero, and_imp]
      exact fun h_eq _ => (hij h_eq).elim
    · by_cases h2 : p = j ∧ q = i
      · simp only [h2, and_self, ↓reduceIte, ite_self, mul_neg, mul_one, right_eq_add,
        ite_eq_right_iff, neg_eq_zero, and_imp]
        exact fun h_eq _ => (hij h_eq.symm).elim
      · simp [h1, h2]
  simp_rw [hdecomp, sum_add_distrib]
  rw [sum_sum_ite_eq_pair, sum_sum_ite_eq_pair]
  rcases lt_trichotomy i j with hlt | heq | hgt
  · simp [hlt, not_lt.mpr hlt.le]
  · exact (hij heq).elim
  · simp [hgt, not_lt.mpr hgt.le]

lemma weighted_sum_diag {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (ℓ : n → n → ℝ) (i : n) :
    ∑ p, ∑ q, (if p < q then ℓ p q else 0) *
        vecMulVec (e p - e q) (e p - e q) i i =
      ∑ q, (if i < q then ℓ i q else 0) +
        ∑ p, (if p < i then ℓ p i else 0) := by
  have hdecomp (p q : n) :
      (if p < q then ℓ p q else 0) * vecMulVec (e p - e q) (e p - e q) i i =
        (if p = i ∧ i < q then ℓ i q else 0) +
          (if q = i ∧ p < i then ℓ p i else 0) := by
    rw [vecMulVec_sub_single_diag]
    by_cases hpq : p = q
    · subst hpq
      have h1 : ¬ (p = i ∧ i < p) := by
        rintro ⟨rfl, hlt⟩
        exact lt_irrefl _ hlt
      have h2 : ¬ (p = i ∧ p < i) := by
        rintro ⟨rfl, hlt⟩
        exact lt_irrefl _ hlt
      simp [h1, h2]
    · by_cases hlt : p < q
      · simp only [hlt, hpq, ite_true, ite_false, mul_ite, mul_one, mul_zero]
        by_cases hip : i = p
        · subst hip
          simp [hlt]
        · by_cases hiq : i = q
          · subst hiq
            simp [hlt, hip]
          · simp [hip, hiq, eq_comm (a := p), eq_comm (a := q)]
      · have hn1 : ¬ (p = i ∧ i < q) := fun ⟨hp, hiq⟩ => hlt (hp ▸ hiq)
        have hn2 : ¬ (q = i ∧ p < i) := fun ⟨hq, hpi⟩ => hlt (hq ▸ hpi)
        simp [hlt, hn1, hn2]
  simp_rw [hdecomp, sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Fintype.sum_eq_single i]
    · simp
    · intro p hp
      exact Fintype.sum_eq_zero _ fun q => by simp [hp]
  · refine Fintype.sum_congr _ _ fun p => ?_
    rw [Fintype.sum_eq_single i]
    · simp
    · intro q hq
      simp [hq]

lemma isSymm_mulVec_one_eq_weightedLaplacian
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℝ) (hA : A.IsSymm) (h1 : A *ᵥ (1 : n → ℝ) = 0) :
    A = ∑ p, ∑ q,
      (if p < q then -(A p q) else 0) • vecMulVec (e p - e q) (e p - e q) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rcases eq_or_ne i j with hij | hij
  · subst hij
    rw [weighted_sum_diag (fun p q => -(A p q)) i]
    have hrow : ∑ c, A i c = 0 := by
      simpa [mulVec, dotProduct, mul_one] using congrArg (fun f => f i) h1
    have hsplit :
        ∑ c, (if c = i then (0 : ℝ) else A i c) =
          ∑ c, (if i < c then A i c else 0) +
            ∑ c, (if c < i then A i c else 0) := by
      have hc (c : n) :
          (if c = i then (0 : ℝ) else A i c) =
            (if i < c then A i c else 0) + (if c < i then A i c else 0) := by
        rcases lt_trichotomy c i with hlt | heq | hgt
        · simp [ne_of_lt hlt, hlt, not_lt.mpr hlt.le]
        · subst heq; simp
        · simp [ne_of_gt hgt, hgt, not_lt.mpr hgt.le]
      simp_rw [hc, sum_add_distrib]
    have hzero : A i i + ∑ c, (if c = i then 0 else A i c) = 0 := by
      have herase :
          ∑ c, (if c = i then (0 : ℝ) else A i c) =
            ∑ c ∈ Finset.univ.erase i, A i c := by
        rw [Finset.sum_ite]
        simp [Finset.filter_eq', Finset.filter_ne']
      have hsum :
          ∑ c, A i c = A i i + ∑ c ∈ Finset.univ.erase i, A i c := by
        rw [← Finset.sum_erase_add (s := Finset.univ) (a := i)]
        · abel
        · exact Finset.mem_univ i
      rw [herase, ← hsum, hrow]
    rw [hsplit] at hzero
    have hsymsum :
        ∑ p, (if p < i then -(A p i) else 0) =
          ∑ p, (if p < i then -(A i p) else 0) := by
      refine Fintype.sum_congr _ _ fun p => ?_
      simp [hA.apply i p]
    have hneg :
        ∑ q, (if i < q then -(A i q) else 0) +
            ∑ p, (if p < i then -(A i p) else 0) =
          -((∑ c, if i < c then A i c else 0) +
              ∑ c, if c < i then A i c else 0) := by
      have hnegite (P : n → Prop) [DecidablePred P] :
          ∑ c, (if P c then -(A i c) else (0 : ℝ)) =
            -∑ c, (if P c then A i c else 0) := by
        have : ∑ c, (if P c then -(A i c) else (0 : ℝ)) =
            ∑ c, -(if P c then A i c else 0) := by
          refine Fintype.sum_congr _ _ fun c => ?_
          split_ifs <;> ring
        rw [this, Finset.sum_neg_distrib]
      rw [hnegite (fun c => i < c), hnegite (fun c => c < i), neg_add]
    rw [hsymsum, hneg]
    linarith
  · rw [weighted_sum_offDiag (fun p q => -(A p q)) hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [hlt]
    · simp only [not_lt.mpr hgt.le, ↓reduceIte, hgt, neg_neg]
      exact (hA.apply i j).symm

lemma configLred_isSymm (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    (configLred s t ρ x hs hρ hγ).IsSymm := by
  ext j ℓ
  simp only [transpose_apply]
  rcases eq_or_ne j ℓ with rfl | hjl
  · rfl
  · apply neg_injective
    rw [configLred_of_ne s t ρ x hs hρ hγ hjl.symm,
      configLred_of_ne s t ρ x hs hρ hγ hjl]
    simp [mul_comm, mul_left_comm]

lemma configLred_eq_weightedLaplacian (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    configLred s t ρ x hs hρ hγ =
      ∑ j, ∑ ℓ,
        (if j < ℓ then -(configLred s t ρ x hs hρ hγ j ℓ) else 0) •
          vecMulVec (e j - e ℓ) (e j - e ℓ) :=
  isSymm_mulVec_one_eq_weightedLaplacian _
    (configLred_isSymm s t ρ x hs hρ hγ)
    (configLred_mulVec_one s t ρ x hs hρ hγ)

/-! ### SC09 — `elimSchurR` equals the Woodbury remainder -/

lemma configEEmbed_eq_elimEEmbed :
    (configEEmbed : Option (Fin k) → ConfigIdx k p) = elimEEmbed :=
  rfl

lemma configLEE_isSymm : (configLEE s t ρ x).IsSymm := by
  ext a b
  simp [configLEE, transpose_apply, submatrix_apply, configL_symm]

lemma configLET_eq_transpose : configLET s t ρ x = (configLTE s t ρ x)ᵀ := by
  ext a j
  simp [configLET, configLTE, transpose_apply, submatrix_apply, configL_symm]

lemma configLEE_nonsing_inv_mul (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    (configLEE s t ρ x)⁻¹ * configLEE s t ρ x = 1 :=
  nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1
    (configLEE_isUnit s t ρ x hs hρ hγ))

lemma configLEE_mul_nonsing_inv (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    configLEE s t ρ x * (configLEE s t ρ x)⁻¹ = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1
    (configLEE_isUnit s t ρ x hs hρ hγ))

lemma isUnit_one_add_configFE_conj (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    IsUnit
      ((1 : Matrix (Fin 3) (Fin 3) ℝ) +
        (configFE s t ρ x)ᵀ * (configLEE s t ρ x)⁻¹ * configFE s t ρ x) := by
  rw [one_add_configFE_conj_inv s t ρ x hs hρ hγ]
  exact 𝒦Mat_isUnit t (configQ s t ρ x) (configγ s t ρ x)
    (fun i => configQ_pos s t hρ x (hs i)) hγ

lemma elimEE_eq_LEE_add_FE (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    elimEE s t ρ x =
      configLEE s t ρ x + configFE s t ρ x * (configFE s t ρ x)ᵀ := by
  have hM := M_eq_configF_mul_transpose_add_configL s t ρ x hs ht hρ hx
  ext a b
  change M (Xconfig s t ρ x) (elimEEmbed a) (elimEEmbed b) =
    (configLEE s t ρ x + configFE s t ρ x * (configFE s t ρ x)ᵀ) a b
  rw [hM]
  simp only [elimEEmbed, Matrix.add_apply, mul_apply, transpose_apply, configLEE, configFE,
    transpose_submatrix, submatrix_apply, configEEmbed, id_eq]
  exact add_comm _ _

lemma elimET_eq_LET_add_FE_FT (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    elimET s t ρ x =
      configLET s t ρ x + configFE s t ρ x * (configFT s t ρ x)ᵀ := by
  have hM := M_eq_configF_mul_transpose_add_configL s t ρ x hs ht hρ hx
  ext a j
  change M (Xconfig s t ρ x) (elimEEmbed a) (elimT j) =
    (configLET s t ρ x + configFE s t ρ x * (configFT s t ρ x)ᵀ) a j
  rw [hM]
  simp only [elimEEmbed, elimT, Matrix.add_apply, mul_apply, transpose_apply, configLET, configFE,
    configFT, transpose_submatrix, submatrix_apply, configEEmbed, id_eq]
  exact add_comm _ _

lemma elimTE_eq_LTE_add_FT_FE (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    elimTE s t ρ x =
      configLTE s t ρ x + configFT s t ρ x * (configFE s t ρ x)ᵀ := by
  have hM := M_eq_configF_mul_transpose_add_configL s t ρ x hs ht hρ hx
  ext j a
  change M (Xconfig s t ρ x) (elimT j) (elimEEmbed a) =
    (configLTE s t ρ x + configFT s t ρ x * (configFE s t ρ x)ᵀ) j a
  rw [hM]
  simp only [elimT, elimEEmbed, Matrix.add_apply, mul_apply, transpose_apply, configLTE, configFT,
    configFE, transpose_submatrix, submatrix_apply, configEEmbed, id_eq]
  exact add_comm _ _

lemma elimTT_eq_LTT_add_FT_FT (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    elimTT s t ρ x =
      configLTT s t ρ x + configFT s t ρ x * (configFT s t ρ x)ᵀ := by
  have hM := M_eq_configF_mul_transpose_add_configL s t ρ x hs ht hρ hx
  ext j ℓ
  change M (Xconfig s t ρ x) (elimT j) (elimT ℓ) =
    (configLTT s t ρ x + configFT s t ρ x * (configFT s t ρ x)ᵀ) j ℓ
  rw [hM]
  simp [configLTT, configFT, Matrix.add_apply, submatrix_apply, mul_apply,
    transpose_apply, elimT]
  abel

lemma elimEE_isUnit (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    IsUnit (elimEE s t ρ x) :=
  (elimEE_posDef s t ρ x hs ht hρ hx).isUnit

lemma elimEE_nonsing_inv_mul (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    (elimEE s t ρ x)⁻¹ * elimEE s t ρ x = 1 :=
  nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1
    (elimEE_isUnit s t ρ x hs ht hρ hx))

lemma elimEE_mul_nonsing_inv (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    elimEE s t ρ x * (elimEE s t ρ x)⁻¹ = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1
    (elimEE_isUnit s t ρ x hs ht hρ hx))

lemma configLEE_inv_transpose :
    ((configLEE s t ρ x)⁻¹)ᵀ = (configLEE s t ρ x)⁻¹ := by
  rw [transpose_nonsing_inv, configLEE_isSymm s t ρ x]

lemma configTE_elim_factor (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (hγ : 0 < configγ s t ρ x) :
    configLTE s t ρ x * (configLEE s t ρ x)⁻¹ * elimEE s t ρ x +
        configU s t ρ x hs hρ hγ * (configFE s t ρ x)ᵀ =
      elimTE s t ρ x := by
  rw [elimEE_eq_LEE_add_FE s t ρ x hs ht hρ hx,
    elimTE_eq_LTE_add_FT_FE s t ρ x hs ht hρ hx]
  have hL : configLTE s t ρ x * ((configLEE s t ρ x)⁻¹ * configLEE s t ρ x) =
      configLTE s t ρ x := by
    rw [configLEE_nonsing_inv_mul s t ρ x hs hρ hγ, Matrix.mul_one]
  simp only [configU, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc]
  rw [hL]
  abel

lemma configET_elim_factor (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (hγ : 0 < configγ s t ρ x) :
    elimEE s t ρ x * (configLEE s t ρ x)⁻¹ * configLET s t ρ x +
        configFE s t ρ x * (configU s t ρ x hs hρ hγ)ᵀ =
      elimET s t ρ x := by
  rw [elimEE_eq_LEE_add_FE s t ρ x hs ht hρ hx,
    elimET_eq_LET_add_FE_FT s t ρ x hs ht hρ hx]
  simp only [configU, transpose_sub, transpose_mul]
  rw [configLEE_inv_transpose s t ρ x, configLET_eq_transpose]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  have hL :
      configLEE s t ρ x * ((configLEE s t ρ x)⁻¹ * (configLTE s t ρ x)ᵀ) =
        (configLTE s t ρ x)ᵀ := by
    rw [← Matrix.mul_assoc, configLEE_mul_nonsing_inv s t ρ x hs hρ hγ,
      Matrix.one_mul]
  rw [hL]
  abel

lemma schur_prod_expand {ε τ κ : Type*} [Fintype ε] [Fintype κ]
    [DecidableEq ε]
    (Z : Matrix τ ε ℝ) (EE : Matrix ε ε ℝ) (U : Matrix τ κ ℝ)
    (FE : Matrix ε κ ℝ) (Z' : Matrix ε τ ℝ)
    (hL : EE⁻¹ * EE = 1) (hR : EE * EE⁻¹ = 1) :
    (Z * EE + U * FEᵀ) * EE⁻¹ * (EE * Z' + FE * Uᵀ) =
      Z * EE * Z' + Z * FE * Uᵀ + U * FEᵀ * Z' +
        U * FEᵀ * EE⁻¹ * FE * Uᵀ := by
  have hR' (M : Matrix ε τ ℝ) : EE * (EE⁻¹ * M) = M := by
    rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hL' (M : Matrix ε τ ℝ) : EE⁻¹ * (EE * M) = M := by
    rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
  have hRκ (M : Matrix ε κ ℝ) : EE * (EE⁻¹ * M) = M := by
    rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  simp [hR', hL']
  abel

/-- **SC09.** -/
lemma elimSchurR_eq_woodbury (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (hγ : 0 < configγ s t ρ x) :
    elimSchurR s t ρ x =
      configLred s t ρ x hs hρ hγ +
        configU s t ρ x hs hρ hγ *
          ((1 : Matrix (Fin 3) (Fin 3) ℝ) +
              (configFE s t ρ x)ᵀ * (configLEE s t ρ x)⁻¹ * configFE s t ρ x)⁻¹ *
          (configU s t ρ x hs hρ hγ)ᵀ := by
  set Z := configLTE s t ρ x * (configLEE s t ρ x)⁻¹
  set Z' := (configLEE s t ρ x)⁻¹ * configLET s t ρ x
  set U := configU s t ρ x hs hρ hγ
  set EE := elimEE s t ρ x
  have hTE : elimTE s t ρ x = Z * EE + U * (configFE s t ρ x)ᵀ := by
    simpa [Z, EE, U, Matrix.mul_assoc] using
      (configTE_elim_factor s t ρ x hs ht hρ hx hγ).symm
  have hET : elimET s t ρ x = EE * Z' + configFE s t ρ x * Uᵀ := by
    simpa [Z', EE, U, Matrix.mul_assoc] using
      (configET_elim_factor s t ρ x hs ht hρ hx hγ).symm
  have hprod :
      elimTE s t ρ x * EE⁻¹ * elimET s t ρ x =
        Z * EE * Z' + Z * configFE s t ρ x * Uᵀ + U * (configFE s t ρ x)ᵀ * Z' +
          U * (configFE s t ρ x)ᵀ * EE⁻¹ * configFE s t ρ x * Uᵀ := by
    rw [hTE, hET]
    exact schur_prod_expand Z EE U (configFE s t ρ x) Z'
      (elimEE_nonsing_inv_mul s t ρ x hs ht hρ hx)
      (elimEE_mul_nonsing_inv s t ρ x hs ht hρ hx)
  have hLred :
      configLTT s t ρ x =
        configLred s t ρ x hs hρ hγ + Z * configLET s t ρ x := by
    simp [configLred, Z, sub_add_cancel]
  have hFT : configFT s t ρ x = U + Z * configFE s t ρ x := by
    simp [configU, U, Z, sub_add_cancel]
  have hTT : elimTT s t ρ x =
      configLred s t ρ x hs hρ hγ + U * Uᵀ + Z * EE * Z' +
        U * (configFE s t ρ x)ᵀ * Z' + Z * configFE s t ρ x * Uᵀ := by
    rw [elimTT_eq_LTT_add_FT_FT s t ρ x hs ht hρ hx, hLred, hFT]
    simp only [EE]
    rw [elimEE_eq_LEE_add_FE s t ρ x hs ht hρ hx]
    simp only [Z, Z', U, transpose_add, transpose_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, configLEE_inv_transpose s t ρ x,
      configLET_eq_transpose]
    have hInv :
        (configLEE s t ρ x)⁻¹ *
            (configLEE s t ρ x * ((configLEE s t ρ x)⁻¹ * (configLTE s t ρ x)ᵀ)) =
          (configLEE s t ρ x)⁻¹ * (configLTE s t ρ x)ᵀ := by
      rw [← Matrix.mul_assoc (configLEE s t ρ x)⁻¹,
        configLEE_nonsing_inv_mul s t ρ x hs hρ hγ, Matrix.one_mul]
    rw [hInv]
    abel
  simp only [elimSchurR]
  rw [hTT, hprod]
  have hcancel :
      configLred s t ρ x hs hρ hγ + U * Uᵀ + Z * EE * Z' +
          U * (configFE s t ρ x)ᵀ * Z' + Z * configFE s t ρ x * Uᵀ -
          (Z * EE * Z' + Z * configFE s t ρ x * Uᵀ +
            U * (configFE s t ρ x)ᵀ * Z' +
            U * (configFE s t ρ x)ᵀ * EE⁻¹ * configFE s t ρ x * Uᵀ) =
        configLred s t ρ x hs hρ hγ + U * Uᵀ -
          U * (configFE s t ρ x)ᵀ * EE⁻¹ * configFE s t ρ x * Uᵀ := by
    abel
  rw [hcancel]
  simp only [U, EE]
  rw [elimEE_eq_LEE_add_FE s t ρ x hs ht hρ hx]
  exact schurComplement_woodbury (configLEE s t ρ x)
    (configLred s t ρ x hs hρ hγ) (configFE s t ρ x)
    (configU s t ρ x hs hρ hγ) (configLEE_isUnit s t ρ x hs hρ hγ)
    (isUnit_one_add_configFE_conj s t ρ x hs hρ hγ)

/-! ### SC13 — `C₁` is completely positive -/

/-- The matrix `C₁` on the right-vector indices: `ρ j * (U (x j) ⬝ᵥ 𝒦 *ᵥ U (x ℓ)) * ρ ℓ`, a kernel
Gram matrix with parameters `configQ` and `configγ`. -/
def configC1 : Matrix (Fin p) (Fin p) ℝ :=
  fun j ℓ =>
    ρ j *
      (U t (configQ s t ρ x) (configγ s t ρ x) (x j) ⬝ᵥ
        𝒦 t (configQ s t ρ x) (configγ s t ρ x) *ᵥ
          U t (configQ s t ρ x) (configγ s t ρ x) (x ℓ)) *
      ρ ℓ

lemma configC1_eq_conj (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    configC1 s t ρ x =
      configU s t ρ x hs hρ hγ *
        ((1 : Matrix (Fin 3) (Fin 3) ℝ) +
            (configFE s t ρ x)ᵀ * (configLEE s t ρ x)⁻¹ * configFE s t ρ x)⁻¹ *
        (configU s t ρ x hs hρ hγ)ᵀ := by
  have hK :
      ((1 : Matrix (Fin 3) (Fin 3) ℝ) +
          (configFE s t ρ x)ᵀ * (configLEE s t ρ x)⁻¹ * configFE s t ρ x)⁻¹ =
        𝒦 t (configQ s t ρ x) (configγ s t ρ x) := by
    rw [one_add_configFE_conj_inv s t ρ x hs hρ hγ]
    rfl
  rw [hK]
  ext j ℓ
  have hrow := configU_apply s t ρ x hs hρ hγ j
  have hcol := configU_apply s t ρ x hs hρ hγ ℓ
  have hmul :=
    mul_mul_col_apply (configU s t ρ x hs hρ hγ)
      (𝒦 t (configQ s t ρ x) (configγ s t ρ x))
      (configU s t ρ x hs hρ hγ)ᵀ j ℓ
  rw [hmul]
  change configC1 s t ρ x j ℓ =
    configU s t ρ x hs hρ hγ j ⬝ᵥ
      (𝒦 t (configQ s t ρ x) (configγ s t ρ x) *ᵥ fun c =>
        (configU s t ρ x hs hρ hγ)ᵀ c ℓ)
  have hUℓ : (fun c => (configU s t ρ x hs hρ hγ)ᵀ c ℓ) =
      configU s t ρ x hs hρ hγ ℓ := by
    funext c
    simp [transpose_apply]
  rw [hUℓ, hrow, hcol]
  simp [configC1, dotProduct, mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_left_comm, mul_comm]

lemma isCompletelyPositive_mul_conj_diagonal {n : Type*}
    {C : Matrix n n ℝ} (hC : IsCompletelyPositive C) {d : n → ℝ}
    (hd : ∀ i, 0 ≤ d i) :
    IsCompletelyPositive fun i j => d i * C i j * d j := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  refine ⟨q, fun a i => d i * p a i, ?_, ?_⟩
  · intro a i
    exact mul_nonneg (hd i) (hp a i)
  · ext i j
    simp only [Matrix.sum_apply, vecMulVec_apply]
    calc d i * (∑ c, p c i * p c j) * d j
        = ∑ c, d i * (p c i * p c j) * d j := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ c, (d i * p c i) * (d j * p c j) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          ring

/-- **SC13.** `C₁` is completely positive. -/
lemma isCompletelyPositive_configC1 (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hmono : Monotone t) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    (hγ : 0 < configγ s t ρ x) :
    IsCompletelyPositive (configC1 s t ρ x) := by
  have hG :=
    kernel_gram_isCompletelyPositive t (configQ s t ρ x) (configγ s t ρ x)
      (fun i => configQ_pos s t hρ x (hs i)) hγ hmono ht x hx
  have hρnn : ∀ j, 0 ≤ ρ j := fun j => (hρ j).le
  unfold configC1
  exact isCompletelyPositive_mul_conj_diagonal hG hρnn

/-- Pad a CP matrix by zeros along the complement of an injection. -/
lemma isCompletelyPositive_of_submatrix_pad {ι n : Type*} [Finite ι]
    {C : Matrix n n ℝ} {D : Matrix ι ι ℝ} {e : ι → n}
    (he : Function.Injective e)
    (hCD : ∀ a b, C (e a) (e b) = D a b)
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, C i j = 0)
    (hC : C.IsSymm) (hD : IsCompletelyPositive D) :
    IsCompletelyPositive C := by
  classical
  cases nonempty_fintype ι
  obtain ⟨r, A, hA, rfl⟩ := isCompletelyPositive_iff_exists_mul_transpose.1 hD
  let A' : Matrix n (Fin r) ℝ := fun i k => ∑ a : ι, if e a = i then A a k else 0
  refine isCompletelyPositive_iff_exists_mul_transpose.2 ⟨r, A', ?nn, ?eq⟩
  · intro i k
    exact Finset.sum_nonneg fun a _ => by
      split_ifs
      · exact hA a k
      · exact le_rfl
  · ext i j
    have hite (a b : ι) (k : Fin r) :
        (if e a = i then A a k else 0) * (if e b = j then A b k else 0) =
          if e a = i ∧ e b = j then A a k * A b k else 0 := by
      split_ifs <;> simp_all
    have hsum :
        ∑ k : Fin r,
            (∑ a : ι, if e a = i then A a k else 0) *
              (∑ b : ι, if e b = j then A b k else 0) =
          ∑ a : ι, ∑ b : ι,
            if e a = i ∧ e b = j then (A * Aᵀ) a b else 0 := by
      simp_rw [Finset.sum_mul_sum, hite]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [mul_apply, transpose_apply]
    change C i j = (A' * A'ᵀ) i j
    have hAT : (A' * A'ᵀ) i j = ∑ k : Fin r, A' i k * A' j k := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hAT]
    simp only [A']
    rw [hsum]
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, ha⟩ := hi
      by_cases hj : ∃ b, e b = j
      · obtain ⟨b, hb⟩ := hj
        rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b]
        · rw [← ha, ← hb, hCD]
          simp
        · intro b' hb'
          have : e b' ≠ j := fun h => hb' (he (h.trans hb.symm))
          simp [this]
        · intro a' ha'
          have : e a' ≠ i := fun h => ha' (he (h.trans ha.symm))
          simp [this]
      · have hz : ∀ a' b' : ι, ¬ (e a' = i ∧ e b' = j) := by
          intro a' b' ⟨_, hb'⟩
          exact hj ⟨b', hb'⟩
        simp only [hz, ↓reduceIte, sum_const_zero]
        have hj' : j ∉ Set.range e := by
          simpa [Set.mem_range] using hj
        exact (hC.apply i j).symm ▸ hzero j hj' i
    · have hz : ∀ a' b' : ι, ¬ (e a' = i ∧ e b' = j) := by
        intro a' b' ⟨ha', _⟩
        exact hi ⟨a', ha'⟩
      simp only [hz, ↓reduceIte, sum_const_zero]
      have hi' : i ∉ Set.range e := by
        simpa [Set.mem_range] using hi
      exact hzero i hi' j

lemma idxY_injective_fn : Function.Injective (idxY (k := k) (p := p)) :=
  fun _ _ h => idxY_injective h

lemma extendByZeroT_isSymm {R : Matrix (Fin p) (Fin p) ℝ} (hR : R.IsSymm) :
    (extendByZeroT (k := k) R).IsSymm := by
  ext α β
  simp only [transpose_apply]
  revert β
  refine configIdx_cases (p := p)
      (P := fun α => ∀ β,
        extendByZeroT (k := k) R β α = extendByZeroT (k := k) R α β) α ?_ ?_ ?_
  · intro β
    simp [extendByZeroT_z0_left, extendByZeroT_z0_right]
  · intro i β
    simp [extendByZeroT_z_left, extendByZeroT_z_right]
  · intro j β
    refine configIdx_cases (p := p)
        (P := fun β =>
          extendByZeroT (k := k) R β (idxY j) =
            extendByZeroT (k := k) R (idxY j) β) β ?_ ?_ ?_
    · simp [extendByZeroT_z0_right, extendByZeroT_z0_left]
    · intro i
      simp [extendByZeroT_z_right, extendByZeroT_z_left]
    · intro ℓ
      simpa [extendByZeroT_y_y] using hR.apply j ℓ

lemma isCompletelyPositive_extendByZeroT {R : Matrix (Fin p) (Fin p) ℝ}
    (hR : IsCompletelyPositive R) :
    IsCompletelyPositive (extendByZeroT (k := k) R) := by
  refine isCompletelyPositive_of_submatrix_pad (n := ConfigIdx k p)
      (e := idxY (k := k) (p := p)) idxY_injective_fn ?hCD ?hzero
      (extendByZeroT_isSymm hR.isSymm) hR
  · intro j ℓ
    exact extendByZeroT_y_y (k := k) R j ℓ
  · intro α hα β
    have : ¬ ∃ j, idxY (k := k) j = α := by
      simpa [Set.mem_range] using hα
    refine configIdx_cases (p := p)
        (P := fun α =>
          (¬ ∃ j, idxY (k := k) j = α) →
            extendByZeroT (k := k) R α β = 0) α ?_ ?_ ?_ this
    · intro _
      exact extendByZeroT_z0_left (k := k) R β
    · intro i _
      exact extendByZeroT_z_left (k := k) R i β
    · intro j hj
      exact (hj ⟨j, rfl⟩).elim

lemma isCompletelyPositive_extend_configC1 (hs : ∀ i, 0 < s i)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (hγ : 0 < configγ s t ρ x) :
    IsCompletelyPositive (extendByZeroT (k := k) (configC1 s t ρ x)) :=
  isCompletelyPositive_extendByZeroT
    (isCompletelyPositive_configC1 s t ρ x hs ht hmono hρ hx hγ)

/-! ### SC17 — assembly for `γ > 0` -/

lemma extendByZeroT_add (A B : Matrix (Fin p) (Fin p) ℝ) :
    extendByZeroT (k := k) (A + B) =
      extendByZeroT (k := k) A + extendByZeroT (k := k) B := by
  ext α β
  refine configIdx_cases (p := p) (P := fun α =>
      extendByZeroT (k := k) (A + B) α β =
        (extendByZeroT (k := k) A + extendByZeroT (k := k) B) α β) α ?_ ?_ ?_
  · simp [extendByZeroT_z0_left]
  · intro i
    simp [extendByZeroT_z_left]
  · intro j
    refine configIdx_cases (p := p) (P := fun β =>
        extendByZeroT (k := k) (A + B) (idxY j) β =
          (extendByZeroT (k := k) A + extendByZeroT (k := k) B) (idxY j) β) β
      ?_ ?_ ?_
    · simp [extendByZeroT_z0_right]
    · intro i
      simp [extendByZeroT_z_right]
    · intro ℓ
      simp [extendByZeroT_y_y, Matrix.add_apply]

lemma elimSchurR_eq_C1_add_Lred (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (hγ : 0 < configγ s t ρ x) :
    elimSchurR s t ρ x =
      configC1 s t ρ x + configLred s t ρ x hs hρ hγ := by
  rw [elimSchurR_eq_woodbury s t ρ x hs ht hρ hx hγ,
    configC1_eq_conj s t ρ x hs hρ hγ]
  abel

/-- **SC17.** `M = elimC0 + extend C₁ + extend L_red`. -/
lemma M_eq_elimC0_add_C1_add_Lred (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (hγ : 0 < configγ s t ρ x) :
    M (Xconfig s t ρ x) =
      elimC0 s t ρ x +
        extendByZeroT (k := k) (configC1 s t ρ x) +
          extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ) := by
  rw [M_eq_elimC0_add_extend s t ρ x hs ht hρ hx,
    elimSchurR_eq_C1_add_Lred s t ρ x hs ht hρ hx hγ, extendByZeroT_add]
  ac_rfl

/-! ### SC18 — `cor:laplacian` on the assembled remainder -/

lemma idxY_lt_idxY_iff {j ℓ : Fin p} :
    (idxY (k := k) j : ConfigIdx k p) < idxY ℓ ↔ j < ℓ := by
  rw [Fin.lt_def, Fin.lt_def]
  simp [idxY_val]

/-- The weights `-(configLred j ℓ)` on pairs `j < ℓ` of right-vector indices, and `0` on every other
pair of `ConfigIdx k p`. -/
def configLredWeights (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) : ConfigIdx k p → ConfigIdx k p → ℝ :=
  fun α β =>
    match configIdxEquiv k p α, configIdxEquiv k p β with
    | Sum.inr j, Sum.inr ℓ =>
        if j < ℓ then -(configLred s t ρ x hs hρ hγ j ℓ) else 0
    | _, _ => 0

lemma configLredWeights_y_y (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) (j ℓ : Fin p) :
    configLredWeights s t ρ x hs hρ hγ (idxY j) (idxY ℓ) =
      if j < ℓ then -(configLred s t ρ x hs hρ hγ j ℓ) else 0 := by
  simp [configLredWeights, configIdxEquiv_idxY]

lemma configLredWeights_nonneg (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) (α β : ConfigIdx k p) (hαβ : α < β) :
    0 ≤ configLredWeights s t ρ x hs hρ hγ α β := by
  revert hαβ
  refine configIdx_cases (p := p) (P := fun α =>
      α < β → 0 ≤ configLredWeights s t ρ x hs hρ hγ α β) α ?_ ?_ ?_
  · intro _
    simp [configLredWeights, configIdxEquiv_idxZ0]
  · intro i _
    simp [configLredWeights, configIdxEquiv_idxZ]
  · intro j hlt
    refine configIdx_cases (p := p) (P := fun β =>
        idxY (k := k) j < β →
          0 ≤ configLredWeights s t ρ x hs hρ hγ (idxY j) β) β ?_ ?_ ?_ hlt
    · intro h
      exact (not_lt_idxZ0 _ h).elim
    · intro i h
      exact (not_lt.mpr (idxZ_lt_idxY i j).le h).elim
    · intro ℓ h
      have hjℓ : j < ℓ := (idxY_lt_idxY_iff (k := k)).1 h
      simp only [configLredWeights_y_y, hjℓ, ↓reduceIte, Left.nonneg_neg_iff, ge_iff_le]
      exact neg_nonneg.mp (configLred_of_ne_nonneg s t ρ x hs hρ hγ hjℓ.ne)

lemma extendByZeroT_smul (c : ℝ) (A : Matrix (Fin p) (Fin p) ℝ) :
    extendByZeroT (k := k) (c • A) = c • extendByZeroT (k := k) A := by
  ext α β
  refine configIdx_cases (p := p) (P := fun α =>
      extendByZeroT (k := k) (c • A) α β =
        (c • extendByZeroT (k := k) A) α β) α ?_ ?_ ?_
  · simp [extendByZeroT_z0_left]
  · intro i
    simp [extendByZeroT_z_left]
  · intro j
    refine configIdx_cases (p := p) (P := fun β =>
        extendByZeroT (k := k) (c • A) (idxY j) β =
          (c • extendByZeroT (k := k) A) (idxY j) β) β ?_ ?_ ?_
    · simp [extendByZeroT_z0_right]
    · intro i
      simp [extendByZeroT_z_right]
    · intro ℓ
      simp [extendByZeroT_y_y, Matrix.smul_apply]

lemma extendByZeroT_sum {ι : Type*} [Fintype ι] (f : ι → Matrix (Fin p) (Fin p) ℝ) :
    extendByZeroT (k := k) (∑ i, f i) = ∑ i, extendByZeroT (k := k) (f i) := by
  ext α β
  refine configIdx_cases (p := p) (P := fun α =>
      extendByZeroT (k := k) (∑ i, f i) α β =
        (∑ i, extendByZeroT (k := k) (f i)) α β) α ?_ ?_ ?_
  · simp [extendByZeroT_z0_left, Matrix.sum_apply]
  · intro i
    simp [extendByZeroT_z_left, Matrix.sum_apply]
  · intro j
    refine configIdx_cases (p := p) (P := fun β =>
        extendByZeroT (k := k) (∑ i, f i) (idxY j) β =
          (∑ i, extendByZeroT (k := k) (f i)) (idxY j) β) β ?_ ?_ ?_
    · simp [extendByZeroT_z0_right, Matrix.sum_apply]
    · intro i
      simp [extendByZeroT_z_right, Matrix.sum_apply]
    · intro ℓ
      simp [extendByZeroT_y_y, Matrix.sum_apply]

lemma extendByZeroT_vecMulVec_sub (j ℓ : Fin p) :
    extendByZeroT (k := k) (vecMulVec (e j - e ℓ) (e j - e ℓ)) =
      vecMulVec (e (idxY (k := k) j) - e (idxY ℓ))
        (e (idxY (k := k) j) - e (idxY ℓ)) := by
  ext α β
  refine configIdx_cases (p := p) (P := fun α =>
      extendByZeroT (k := k) (vecMulVec (e j - e ℓ) (e j - e ℓ)) α β =
        vecMulVec (e (idxY (k := k) j) - e (idxY ℓ))
          (e (idxY (k := k) j) - e (idxY ℓ)) α β) α ?_ ?_ ?_
  · simp [extendByZeroT_z0_left, vecMulVec_apply, Pi.sub_apply, e,
      Pi.single_apply, idxZ0_ne_idxY]
  · intro i
    simp [extendByZeroT_z_left, vecMulVec_apply, Pi.sub_apply, e,
      Pi.single_apply, idxZ_ne_idxY]
  · intro a
    refine configIdx_cases (p := p) (P := fun β =>
        extendByZeroT (k := k) (vecMulVec (e j - e ℓ) (e j - e ℓ)) (idxY a) β =
          vecMulVec (e (idxY (k := k) j) - e (idxY ℓ))
            (e (idxY (k := k) j) - e (idxY ℓ)) (idxY a) β) β ?_ ?_ ?_
    · simp [extendByZeroT_z0_right, vecMulVec_apply, Pi.sub_apply, e,
        Pi.single_apply, idxZ0_ne_idxY]
    · intro i
      simp [extendByZeroT_z_right, vecMulVec_apply, Pi.sub_apply, e,
        Pi.single_apply, idxZ_ne_idxY]
    · intro b
      simp [extendByZeroT_y_y, vecMulVec_apply, Pi.sub_apply, e, Pi.single_apply,
        idxY_eq_iff]

lemma extendByZeroT_configLred_eq_sum (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) :
    extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ) =
      ∑ j, ∑ ℓ,
        (if j < ℓ then -(configLred s t ρ x hs hρ hγ j ℓ) else 0) •
          vecMulVec (e (idxY (k := k) j) - e (idxY ℓ))
            (e (idxY (k := k) j) - e (idxY ℓ)) := by
  nth_rw 1 [configLred_eq_weightedLaplacian s t ρ x hs hρ hγ]
  simp_rw [extendByZeroT_sum, extendByZeroT_smul, extendByZeroT_vecMulVec_sub]

/- Pair corollary inlined: `BollobasNikiforov.CP.Pair` clashes with `BollobasNikiforov.M.Basic` on
`vecMulVec_sub_single_offDiag`. -/

section PairCopy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Move the mass of coordinate `j` of `p` onto coordinate `i`: `p i + p j` at `i`, `0` at `j`, and
`p` elsewhere. -/
def pairLeft (p : n → ℝ) (i j : n) : n → ℝ :=
  fun k => if k = i then p i + p j else if k = j then 0 else p k

/-- Move the mass of coordinate `i` of `p` onto coordinate `j`: `0` at `i`, `p i + p j` at `j`, and
`p` elsewhere. -/
def pairRight (p : n → ℝ) (i j : n) : n → ℝ :=
  fun k => if k = i then 0 else if k = j then p i + p j else p k

omit [Fintype n] in
lemma pairLeft_nonneg {p : n → ℝ} (hp : 0 ≤ p) (i j : n) : 0 ≤ pairLeft p i j := by
  intro k
  simp only [pairLeft]
  split_ifs
  · exact add_nonneg (hp i) (hp j)
  · exact le_rfl
  · exact hp k

omit [Fintype n] in
lemma pairRight_nonneg {p : n → ℝ} (hp : 0 ≤ p) (i j : n) : 0 ≤ pairRight p i j := by
  intro k
  simp only [pairRight]
  split_ifs
  · exact le_rfl
  · exact add_nonneg (hp i) (hp j)
  · exact hp k

omit [Fintype n] in
lemma pairLeft_eq (p : n → ℝ) {i j : n} (hij : i ≠ j) :
    pairLeft p i j = p + p j • (e i - e j) := by
  ext k
  change (if k = i then p i + p j else if k = j then 0 else p k) =
    p k + p j * (e i - e j) k
  rw [sub_single_apply hij]
  split_ifs with hki hkj
  · subst hki; ring
  · subst hkj; ring
  · ring

omit [Fintype n] in
lemma pairRight_eq (p : n → ℝ) {i j : n} (hij : i ≠ j) :
    pairRight p i j = p - p i • (e i - e j) := by
  ext k
  change (if k = i then 0 else if k = j then p i + p j else p k) =
    p k - p i * (e i - e j) k
  rw [sub_single_apply hij]
  split_ifs with hki hkj
  · subst hki; ring
  · subst hkj; ring
  · ring

omit [Fintype n] [DecidableEq n] in
lemma vecMulVec_add_self (x y : n → ℝ) :
    vecMulVec (x + y) (x + y) =
      vecMulVec x x + vecMulVec x y + vecMulVec y x + vecMulVec y y := by
  rw [add_vecMulVec, vecMulVec_add, vecMulVec_add]
  abel

omit [Fintype n] [DecidableEq n] in
lemma vecMulVec_sub_self (x y : n → ℝ) :
    vecMulVec (x - y) (x - y) =
      vecMulVec x x - vecMulVec x y - vecMulVec y x + vecMulVec y y := by
  rw [sub_vecMulVec, vecMulVec_sub, vecMulVec_sub]
  abel

omit [Fintype n] [DecidableEq n] in
lemma vecMulVec_smul_self (c : ℝ) (x : n → ℝ) :
    vecMulVec (c • x) (c • x) = (c * c) • vecMulVec x x := by
  rw [smul_vecMulVec, vecMulVec_smul, smul_smul]

omit [Fintype n] in
lemma rankOne_pair_identity {p : n → ℝ} {i j : n} (hij : i ≠ j)
    (hab : 0 < p i + p j) :
    vecMulVec p p + (p i * p j) • vecMulVec (e i - e j) (e i - e j) =
      (p i / (p i + p j)) • vecMulVec (pairLeft p i j) (pairLeft p i j) +
        (p j / (p i + p j)) • vecMulVec (pairRight p i j) (pairRight p i j) := by
  set a := p i
  set b := p j
  set s := a + b
  set d := e i - e j
  have hs : s ≠ 0 := hab.ne'
  have hU : pairLeft p i j = p + b • d := pairLeft_eq p hij
  have hV : pairRight p i j = p - a • d := pairRight_eq p hij
  have hUU :
      vecMulVec (pairLeft p i j) (pairLeft p i j) =
        vecMulVec p p + b • (vecMulVec p d + vecMulVec d p) +
          (b * b) • vecMulVec d d := by
    rw [hU, vecMulVec_add_self, vecMulVec_smul, smul_vecMulVec, vecMulVec_smul_self]
    rw [smul_add]
    abel
  have hVV :
      vecMulVec (pairRight p i j) (pairRight p i j) =
        vecMulVec p p - a • (vecMulVec p d + vecMulVec d p) +
          (a * a) • vecMulVec d d := by
    rw [hV, vecMulVec_sub_self, vecMulVec_smul, smul_vecMulVec, vecMulVec_smul_self]
    rw [smul_add]
    abel
  ext x y
  have h1 := congr_fun (congr_fun hUU x) y
  have h2 := congr_fun (congr_fun hVV x) y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1, h2]
  field_simp [hs]
  ring

omit [Fintype n] [DecidableEq n] in
lemma IsCompletelyPositive.sum {q : ℕ} (C : Fin q → Matrix n n ℝ)
    (hC : ∀ a, IsCompletelyPositive (C a)) :
    IsCompletelyPositive (∑ a, C a) := by
  induction q with
  | zero =>
    refine ⟨0, fun _ => 0, fun _ _ => le_rfl, ?_⟩
    simp
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    exact (hC 0).add (ih (fun a => C a.succ) fun a => hC a.succ)

lemma exists_split_of_le_sum {q : ℕ} (bound : Fin q → ℝ) (h : ℝ)
    (h0 : 0 ≤ h) (hb : ∀ a, 0 ≤ bound a) (hle : h ≤ ∑ a, bound a) :
    ∃ alloc : Fin q → ℝ,
      (∀ a, 0 ≤ alloc a) ∧ (∀ a, alloc a ≤ bound a) ∧ ∑ a, alloc a = h := by
  induction q generalizing h with
  | zero =>
    refine ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a, ?_⟩
    simp at hle ⊢
    linarith
  | succ q ih =>
    set b0 := bound 0
    set h0' := min h b0
    set h' := h - h0'
    have hh' : 0 ≤ h' := sub_nonneg.mpr (min_le_left _ _)
    have hle' : h' ≤ ∑ a : Fin q, bound a.succ := by
      rw [Fin.sum_univ_succ] at hle
      rcases le_total h b0 with hle0 | hge0
      · simp only [min_eq_left hle0, sub_self, h', h0']
        exact Finset.sum_nonneg fun a _ => hb a.succ
      · simp [h', h0', min_eq_right hge0]
        linarith
    obtain ⟨alloc', hnn, hbd, hsum⟩ :=
      ih (fun a => bound a.succ) h' hh' (fun a => hb a.succ) hle'
    refine ⟨Fin.cons h0' alloc', ?_, ?_, ?_⟩
    · intro a
      induction a using Fin.cases with
      | zero =>
        change 0 ≤ min h (bound 0)
        exact le_min_iff.2 ⟨h0, hb 0⟩
      | succ a => simpa using hnn a
    · intro a
      induction a using Fin.cases with
      | zero =>
        change min h (bound 0) ≤ bound 0
        exact min_le_right _ _
      | succ a => simpa using hbd a
    · rw [Fin.sum_univ_succ]
      simp [hsum, h']

omit [Fintype n] in
lemma interpolate_pair {p : n → ℝ} {i j : n} {h t : ℝ}
    (ht : t * (p i * p j) = h) :
    (1 - t) • vecMulVec p p +
        t • (vecMulVec p p + (p i * p j) • vecMulVec (e i - e j) (e i - e j)) =
      vecMulVec p p + h • vecMulVec (e i - e j) (e i - e j) := by
  set L := vecMulVec (e i - e j) (e i - e j)
  set P := vecMulVec p p
  calc
    (1 - t) • P + t • (P + (p i * p j) • L)
        = (1 - t) • P + t • P + t • ((p i * p j) • L) := by
          rw [smul_add, add_assoc]
    _ = (1 - t + t) • P + (t * (p i * p j)) • L := by
          rw [← add_smul, smul_smul]
    _ = P + h • L := by
          simp [ht]

omit [Fintype n] in
lemma isCompletelyPositive_vecMulVec_add_smul_sub_single {p : n → ℝ} (hp : 0 ≤ p)
    {i j : n} (hij : i ≠ j) {h : ℝ} (h0 : 0 ≤ h) (hle : h ≤ p i * p j) :
    IsCompletelyPositive
      (vecMulVec p p + h • vecMulVec (e i - e j) (e i - e j)) := by
  set a := p i
  set b := p j
  by_cases hab0 : a * b = 0
  · have hh : h = 0 := le_antisymm (hle.trans_eq hab0) h0
    simpa [hh] using isCompletelyPositive_vecMulVec hp
  · have habpos : 0 < a * b :=
      lt_of_le_of_ne (mul_nonneg (hp i) (hp j)) (Ne.symm hab0)
    have ha : 0 < a := pos_of_mul_pos_left habpos (hp j)
    have hb : 0 < b := pos_of_mul_pos_right habpos (hp i)
    have habs : 0 < a + b := add_pos ha hb
    set t := h / (a * b)
    have ht0 : 0 ≤ t := div_nonneg h0 habpos.le
    have ht1 : t ≤ 1 := (div_le_one habpos).mpr hle
    have hth : t * (a * b) = h := div_mul_cancel₀ h hab0
    have hCP :
        IsCompletelyPositive
          (vecMulVec p p + (a * b) • vecMulVec (e i - e j) (e i - e j)) := by
      rw [rankOne_pair_identity hij habs]
      refine ((isCompletelyPositive_vecMulVec (pairLeft_nonneg hp i j)).smul ?_).add
        ((isCompletelyPositive_vecMulVec (pairRight_nonneg hp i j)).smul ?_)
      · exact div_nonneg ha.le habs.le
      · exact div_nonneg hb.le habs.le
    have hleft : IsCompletelyPositive ((1 - t) • vecMulVec p p) :=
      (isCompletelyPositive_vecMulVec hp).smul (sub_nonneg.mpr ht1)
    have := hleft.add (hCP.smul ht0)
    convert this using 1
    exact (interpolate_pair (p := p) (i := i) (j := j) (h := h) (t := t) hth).symm

omit [Fintype n] in
lemma IsCompletelyPositive.add_smul_sub_single {C : Matrix n n ℝ}
    (hC : IsCompletelyPositive C) {i j : n} (hij : i ≠ j) {h : ℝ}
    (h0 : 0 ≤ h) (hle : h ≤ C i j) :
    IsCompletelyPositive (C + h • vecMulVec (e i - e j) (e i - e j)) := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  have hCij : (∑ a, vecMulVec (p a) (p a)) i j = ∑ a, p a i * p a j := by
    simp [Matrix.sum_apply, vecMulVec_apply]
  rw [hCij] at hle
  have hbnd : ∀ a, 0 ≤ p a i * p a j := fun a => mul_nonneg (hp a i) (hp a j)
  obtain ⟨alloc, hnn, hbd, hsum⟩ :=
    exists_split_of_le_sum (fun a => p a i * p a j) h h0 hbnd hle
  have hdecomp :
      (∑ a, vecMulVec (p a) (p a)) + h • vecMulVec (e i - e j) (e i - e j) =
        ∑ a, (vecMulVec (p a) (p a) +
          alloc a • vecMulVec (e i - e j) (e i - e j)) := by
    rw [← hsum, Finset.sum_smul, ← Finset.sum_add_distrib]
  rw [hdecomp]
  exact IsCompletelyPositive.sum _ fun a =>
    isCompletelyPositive_vecMulVec_add_smul_sub_single (fun k => hp a k) hij (hnn a) (hbd a)

omit [Fintype n] in
lemma pairOffDiag {p q x y : n} (hpq : p ≠ q) (hxy : x ≠ y)
    (hpair : ({p, q} : Set n) ≠ {x, y}) :
    vecMulVec (e p - e q) (e p - e q) x y = 0 := by
  rw [vecMulVec_sub_single_apply hpq]
  split_ifs with h1 h2 h3 h4
  · exact (hxy (h1.1.trans h1.2.symm)).elim
  · exact (hxy (h2.1.trans h2.2.symm)).elim
  · exact (hpair (by simp [h3.1, h3.2])).elim
  · exact (hpair (by simp [h4.1, h4.2, Set.pair_comm])).elim
  · rfl

variable [LinearOrder n]

/-- The pairs `(i, j)` with `i < j`. -/
def offDiagLt : Finset (n × n) :=
  Finset.univ.offDiag.filter (fun p => p.1 < p.2)

omit [DecidableEq n] in
lemma mem_offDiagLt {i j : n} : (i, j) ∈ offDiagLt ↔ i < j := by
  constructor
  · intro h
    simp only [offDiagLt, mem_filter, mem_offDiag, mem_univ, ne_eq, true_and] at h
    exact h.2
  · intro h
    simp [offDiagLt, Finset.mem_filter, Finset.mem_offDiag, h.ne, h]

omit [Fintype n] [DecidableEq n] in
lemma eq_of_lt_pair {a b c d : n} (hab : a < b) (hcd : c < d)
    (h : ({a, b} : Set n) = {c, d}) : a = c ∧ b = d := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact (lt_irrefl _ (hab.trans hcd)).elim

/-- The weighted Laplacian `∑_{i < j} ℓ i j • (eᵢ - eⱼ)(eᵢ - eⱼ)ᵀ`. -/
def weightedLaplacian (ℓ : n → n → ℝ) : Matrix n n ℝ :=
  ∑ p ∈ offDiagLt, ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)

lemma weightedLaplacian_apply_of_lt (ℓ : n → n → ℝ) {i j : n} (hij : i < j) :
    weightedLaplacian ℓ i j = -ℓ i j := by
  simp only [weightedLaplacian, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have himem : (i, j) ∈ offDiagLt := mem_offDiagLt.2 hij
  refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
  · intro p hp hne
    have hpq : p.1 ≠ p.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2
    have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hpair : ({p.1, p.2} : Set n) ≠ {i, j} := by
      intro h
      exact hne (Prod.ext_iff.mpr (eq_of_lt_pair hplt hij h))
    simp [pairOffDiag hpq hij.ne hpair]
  · intro h
    exact (h himem).elim
  · rw [vecMulVec_sub_single_apply hij.ne]
    simp [hij.ne, hij.ne.symm]

lemma weightedLaplacian_sum_apply_of_ne (s : Finset (n × n)) (hs : s ⊆ offDiagLt)
    (ℓ : n → n → ℝ) {i j : n} (hij : i ≠ j)
    (hmiss : ∀ p ∈ s, ({p.1, p.2} : Set n) ≠ {i, j}) :
    (∑ p ∈ s, ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)) i j = 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpq : p.1 ≠ p.2 :=
    (Finset.mem_offDiag.mp (Finset.mem_filter.mp (hs hp)).1).2.2
  simp [pairOffDiag hpq hij (hmiss p hp)]

lemma isCompletelyPositive_add_sum_pairs {C : Matrix n n ℝ} (hC : IsCompletelyPositive C)
    (ℓ : n → n → ℝ) (s : Finset (n × n)) (hs : s ⊆ offDiagLt)
    (hℓ : ∀ p ∈ s, 0 ≤ ℓ p.1 p.2) (hslack : ∀ p ∈ s, ℓ p.1 p.2 ≤ C p.1 p.2) :
    IsCompletelyPositive
      (C + ∑ p ∈ s, ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)) := by
  revert hℓ hslack hs
  refine s.induction_on ?empty ?insert
  · intro _ _ _
    simpa using hC
  · intro p s hps ih hs hℓ hslack
    have hp : p ∈ offDiagLt := hs (Finset.mem_insert_self _ _)
    have hplt : p.1 < p.2 := mem_offDiagLt.1 hp
    have hpne : p.1 ≠ p.2 := hplt.ne
    have hs' : s ⊆ offDiagLt := (Finset.subset_insert p s).trans hs
    have hℓ' : ∀ q ∈ s, 0 ≤ ℓ q.1 q.2 := fun q hq => hℓ q (Finset.mem_insert_of_mem hq)
    have hslack' : ∀ q ∈ s, ℓ q.1 q.2 ≤ C q.1 q.2 :=
      fun q hq => hslack q (Finset.mem_insert_of_mem hq)
    rw [Finset.sum_insert hps, add_comm (ℓ p.1 p.2 • _), ← add_assoc]
    refine (ih hs' hℓ' hslack').add_smul_sub_single hpne (hℓ p (Finset.mem_insert_self _ _)) ?_
    have hcur :
        (C + ∑ q ∈ s, ℓ q.1 q.2 • vecMulVec (e q.1 - e q.2) (e q.1 - e q.2)) p.1 p.2 =
          C p.1 p.2 := by
      simp only [Matrix.add_apply]
      have : (∑ q ∈ s, ℓ q.1 q.2 • vecMulVec (e q.1 - e q.2) (e q.1 - e q.2)) p.1 p.2 = 0 := by
        refine weightedLaplacian_sum_apply_of_ne s hs' ℓ hpne fun q hq hpair => ?_
        have hqlt : q.1 < q.2 := mem_offDiagLt.1 (hs' hq)
        have := eq_of_lt_pair hqlt hplt hpair
        exact hps (by simpa [Prod.ext_iff.mpr this] using hq)
      simp [this]
    simpa [hcur] using hslack p (Finset.mem_insert_self _ _)

lemma IsCompletelyPositive.add_weightedLaplacian {C : Matrix n n ℝ}
    (hC : IsCompletelyPositive C) {ℓ : n → n → ℝ} (hℓ : ∀ i j, i < j → 0 ≤ ℓ i j)
    (hCL : ∀ i j, 0 ≤ (C + weightedLaplacian ℓ) i j) :
    IsCompletelyPositive (C + weightedLaplacian ℓ) := by
  refine isCompletelyPositive_add_sum_pairs hC ℓ offDiagLt (Finset.Subset.refl _) ?_ ?_
  · intro p hp
    exact hℓ p.1 p.2 (mem_offDiagLt.1 hp)
  · intro p hp
    have hpij : p.1 < p.2 := mem_offDiagLt.1 hp
    have hnn : 0 ≤ (C + weightedLaplacian ℓ) p.1 p.2 := hCL _ _
    have hL : weightedLaplacian ℓ p.1 p.2 = -ℓ p.1 p.2 :=
      weightedLaplacian_apply_of_lt ℓ hpij
    have : 0 ≤ C p.1 p.2 - ℓ p.1 p.2 := by
      simpa [Matrix.add_apply, hL] using hnn
    linarith

end PairCopy

lemma weightedLaplacian_eq_doubleSum {n : Type*} [Fintype n] [DecidableEq n]
    [LinearOrder n] (ℓ : n → n → ℝ) :
    weightedLaplacian ℓ =
      ∑ i, ∑ j,
        (if i < j then ℓ i j else 0) • vecMulVec (e i - e j) (e i - e j) := by
  let f : n × n → Matrix n n ℝ :=
    fun p => ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)
  change ∑ p ∈ offDiagLt, f p =
    ∑ i, ∑ j, (if i < j then ℓ i j else 0) • vecMulVec (e i - e j) (e i - e j)
  have hsum : ∑ p : n × n, (if p.1 < p.2 then f p else 0) =
      ∑ p ∈ offDiagLt, f p := by
    have hite (p : n × n) :
        (if p.1 < p.2 then f p else 0) =
          if p ∈ offDiagLt then f p else 0 := by
      by_cases hlt : p.1 < p.2
      · have hp : p ∈ offDiagLt := mem_offDiagLt.2 hlt
        simp [hlt, hp]
      · have hp : p ∉ offDiagLt := by
          intro h
          exact hlt (mem_offDiagLt.1 h)
        simp [hlt, hp]
    simp_rw [hite]
    simp
  rw [← hsum, Fintype.sum_prod_type]
  simp [f]

lemma extendByZeroT_mulVec_one (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A *ᵥ (1 : Fin p → ℝ) = 0) :
    extendByZeroT (k := k) A *ᵥ (1 : ConfigIdx k p → ℝ) = 0 := by
  ext α
  refine configIdx_cases (p := p) (P := fun α =>
      (extendByZeroT (k := k) A *ᵥ 1) α = 0) α ?_ ?_ ?_
  · simp [mulVec, dotProduct, extendByZeroT_z0_left]
  · intro i
    simp [mulVec, dotProduct, extendByZeroT_z_left]
  · intro j
    have hrow : ∑ x, A j x = 0 := by
      simpa [mulVec, dotProduct, mul_one] using congrArg (fun f => f j) hA
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one]
    rw [sum_configIdx]
    simp only [extendByZeroT_z0_right, extendByZeroT_z_right, sum_const_zero, add_zero,
      extendByZeroT_y_y, zero_add]
    exact hrow

lemma extend_configLred_offDiag (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : 0 < configγ s t ρ x) {α β : ConfigIdx k p} (hlt : α < β) :
    extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ) α β =
      -configLredWeights s t ρ x hs hρ hγ α β := by
  refine configIdx_cases (p := p) (P := fun α =>
      α < β →
        extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ) α β =
          -configLredWeights s t ρ x hs hρ hγ α β) α ?_ ?_ ?_ hlt
  · intro _
    simp [extendByZeroT_z0_left, configLredWeights, configIdxEquiv_idxZ0]
  · intro i _
    simp [extendByZeroT_z_left, configLredWeights, configIdxEquiv_idxZ]
  · intro j hj
    refine configIdx_cases (p := p) (P := fun β =>
        idxY (k := k) j < β →
          extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ) (idxY j) β =
            -configLredWeights s t ρ x hs hρ hγ (idxY j) β) β ?_ ?_ ?_ hj
    · intro h
      exact (not_lt_idxZ0 _ h).elim
    · intro i h
      exact (not_lt.mpr (idxZ_lt_idxY i j).le h).elim
    · intro ℓ h
      have hjℓ : j < ℓ := (idxY_lt_idxY_iff (k := k)).1 h
      simp [extendByZeroT_y_y, configLredWeights_y_y, hjℓ]

lemma extend_configLred_eq_weightedLaplacian (hs : ∀ i, 0 < s i)
    (hρ : ∀ j, 0 < ρ j) (hγ : 0 < configγ s t ρ x) :
    extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ) =
      weightedLaplacian (configLredWeights s t ρ x hs hρ hγ) := by
  have hE :=
    isSymm_mulVec_one_eq_weightedLaplacian
      (extendByZeroT (k := k) (configLred s t ρ x hs hρ hγ))
      (extendByZeroT_isSymm (configLred_isSymm s t ρ x hs hρ hγ))
      (extendByZeroT_mulVec_one _ (configLred_mulVec_one s t ρ x hs hρ hγ))
  rw [hE, weightedLaplacian_eq_doubleSum]
  refine Fintype.sum_congr _ _ fun α => ?_
  refine Fintype.sum_congr _ _ fun β => ?_
  by_cases hlt : α < β
  · simp [hlt, extend_configLred_offDiag s t ρ x hs hρ hγ hlt]
  · simp [hlt]

/-- **SC18.** If `γ > 0` then `M(Xconfig)` is completely positive. -/
lemma isCompletelyPositive_M_Xconfig (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hmono : Monotone t) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    (hγ : 0 < configγ s t ρ x) :
    IsCompletelyPositive (M (Xconfig s t ρ x)) := by
  have hC0 : IsCompletelyPositive (elimC0 s t ρ x) :=
    isCompletelyPositive_elimC0 s t ρ x hs ht hmono hρ hx
  have hC1 : IsCompletelyPositive (extendByZeroT (k := k) (configC1 s t ρ x)) :=
    isCompletelyPositive_extend_configC1 s t ρ x hs ht hmono hρ hx hγ
  have hC : IsCompletelyPositive
      (elimC0 s t ρ x + extendByZeroT (k := k) (configC1 s t ρ x)) :=
    hC0.add hC1
  have hM := M_eq_elimC0_add_C1_add_Lred s t ρ x hs ht hρ hx hγ
  have hL := extend_configLred_eq_weightedLaplacian s t ρ x hs hρ hγ
  have hnn : ∀ α β,
      0 ≤
        (elimC0 s t ρ x + extendByZeroT (k := k) (configC1 s t ρ x) +
            weightedLaplacian (configLredWeights s t ρ x hs hρ hγ)) α β := by
    intro α β
    have : 0 ≤ M (Xconfig s t ρ x) α β :=
      M_nonneg (Xconfig_posSemidef s t ρ x) α β
    simpa [hM, hL, Matrix.add_apply] using this
  have hCP := hC.add_weightedLaplacian
    (fun α β hαβ => configLredWeights_nonneg s t ρ x hs hρ hγ α β hαβ) hnn
  rw [hM, hL]
  exact hCP

end

end BollobasNikiforov

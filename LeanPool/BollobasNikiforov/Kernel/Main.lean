/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Kernel.Bilinear
import LeanPool.BollobasNikiforov.Kernel.Signs
import LeanPool.BollobasNikiforov.Kernel.N
import LeanPool.BollobasNikiforov.CP.Basic

/-!
# The three-column kernel lemma

Package of the sign bounds `N ≥ 1`, `P ≥ 0`, `Z ≥ 0` with the bilinear
factorization of `docs/sol.tex` §3 (`lem:kernel`, `eq:factor`), and the
resulting three-column completely positive Gram of `U`.
-/

namespace BollobasNikiforov

open Matrix
open scoped Matrix

noncomputable section

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-! ### KR26: `lem:kernel` -/

/-- For `x ≥ 0`, the auxiliaries satisfy `N ≥ 1`, `P ≥ 0`, `Z ≥ 0`, and
the factorization `eq:factor` holds. -/
lemma kernel_lemma (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ)
    (htmono : Monotone t) (htpos : ∀ i, 0 < t i) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ N t q x ∧ 0 ≤ P t q x ∧ 0 ≤ Z t q γ x ∧
      ∀ y : ℝ,
        U t q γ x ⬝ᵥ 𝒦 t q γ *ᵥ U t q γ y =
          N t q x * N t q y / (Δ t q * D2 t q) +
            2 * P t q x * P t q y / (a0 t q * D2 t q) +
              Z t q γ x * Z t q γ y / (γ * a0 t q * (γ + a0 t q)) :=
  ⟨N_ge_one t q x hq hx htmono htpos,
    P_nonneg t q hq htpos htmono hx,
    Z_nonneg t q γ hq hγ hx,
    fun y ↦ 𝒦_factor t q γ hq hγ x y⟩

/-! ### KR27: finite Gram of `U` is completely positive -/

/-- Coefficient of the `N` rank-one term in `eq:factor`. -/
def kernelCoeffN : ℝ :=
  1 / (Δ t q * D2 t q)

/-- Coefficient of the `P` rank-one term in `eq:factor`. -/
def kernelCoeffP : ℝ :=
  2 / (a0 t q * D2 t q)

/-- Coefficient of the `Z` rank-one term in `eq:factor`. -/
def kernelCoeffZ (γ : ℝ) : ℝ :=
  1 / (γ * a0 t q * (γ + a0 t q))

lemma kernelCoeffN_nonneg (hq : ∀ i, 0 < q i) : 0 ≤ kernelCoeffN t q :=
  one_div_nonneg.mpr (mul_pos (Δ_pos t q hq) (D2_pos t q hq)).le

lemma kernelCoeffP_nonneg (hq : ∀ i, 0 < q i) : 0 ≤ kernelCoeffP t q :=
  div_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos (a0_pos t q hq) (D2_pos t q hq)).le

lemma kernelCoeffZ_nonneg (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    0 ≤ kernelCoeffZ t q γ :=
  one_div_nonneg.mpr
    (mul_pos (mul_pos hγ (a0_pos t q hq)) (γ_add_a0_pos t q γ hq hγ)).le

lemma kernel_gram_eq {κ : Type*}
    (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) (x : κ → ℝ) :
    (fun j ℓ ↦ U t q γ (x j) ⬝ᵥ 𝒦 t q γ *ᵥ U t q γ (x ℓ)) =
      kernelCoeffN t q • vecMulVec (fun j ↦ N t q (x j)) (fun j ↦ N t q (x j)) +
        kernelCoeffP t q • vecMulVec (fun j ↦ P t q (x j)) (fun j ↦ P t q (x j)) +
          kernelCoeffZ t q γ •
            vecMulVec (fun j ↦ Z t q γ (x j)) (fun j ↦ Z t q γ (x j)) := by
  ext j ℓ
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    kernelCoeffN, kernelCoeffP, kernelCoeffZ]
  rw [𝒦_factor t q γ hq hγ (x j) (x ℓ)]
  ring

lemma kernel_gram_isCompletelyPositive {κ : Type*}
    (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ)
    (htmono : Monotone t) (htpos : ∀ i, 0 < t i)
    (x : κ → ℝ) (hx : ∀ j, 0 ≤ x j) :
    IsCompletelyPositive
      (fun j ℓ ↦ U t q γ (x j) ⬝ᵥ 𝒦 t q γ *ᵥ U t q γ (x ℓ)) := by
  have hn : 0 ≤ fun j : κ ↦ N t q (x j) := fun j ↦
    (zero_le_one : (0 : ℝ) ≤ 1).trans
      (kernel_lemma t q γ hq hγ htmono htpos (hx j)).1
  have hp : 0 ≤ fun j : κ ↦ P t q (x j) := fun j ↦
    (kernel_lemma t q γ hq hγ htmono htpos (hx j)).2.1
  have hz : 0 ≤ fun j : κ ↦ Z t q γ (x j) := fun j ↦
    (kernel_lemma t q γ hq hγ htmono htpos (hx j)).2.2.1
  rw [kernel_gram_eq t q γ hq hγ x]
  exact
    (((isCompletelyPositive_vecMulVec hn).smul (kernelCoeffN_nonneg t q hq)).add
      ((isCompletelyPositive_vecMulVec hp).smul (kernelCoeffP_nonneg t q hq))).add
      ((isCompletelyPositive_vecMulVec hz).smul (kernelCoeffZ_nonneg t q γ hq hγ))

end

end BollobasNikiforov

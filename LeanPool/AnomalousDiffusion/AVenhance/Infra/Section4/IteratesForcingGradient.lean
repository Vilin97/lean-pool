/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion

/-! Explicit spatial Leibniz expansions for the actual increment forcing.
The differentiated forcing is computed rather than supplied as an equation. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Divergence of the coefficient/gradient flux, with both Leibniz terms. -/
theorem iterate_matrix_forcing_formula
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec 2) :
    vecDiv (fun y => (A y).mulVec (spaceGrad v y)) x =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (spaceGrad (fun y => A y i j) x i * spaceGrad v x j +
        A x i j * spaceGrad (fun y => spaceGrad v y j) x i) := by
  let α : Fin 2 → Fin 2 → Vec 2 → ℝ := fun i j y => A y i j
  have ha (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (α i j) :=
    contDiff_pi.mp (contDiff_pi.mp hA i) j
  have hg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => spaceGrad v y j) :=
    contDiff_pi.mp (iterate_gradient_smooth hv) j
  unfold vecDiv
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => ∑ j : Fin 2, α i j y * spaceGrad v y j) x (basisVec i) =
    ∑ j : Fin 2, (spaceGrad (α i j) x i * spaceGrad v x j +
      α i j x * spaceGrad (fun y => spaceGrad v y j) x i)
  rw [fderiv_fun_sum (A := fun j y => α i j y * spaceGrad v y j)
    (fun j _ => ((ha i j).differentiable (by simp)).differentiableAt.mul
    ((hg j).differentiable (by simp)).differentiableAt)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul ((ha i j).differentiable (by simp)).differentiableAt
    ((hg j).differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul, spaceGrad]
  ring

theorem IteratesForcingGradient.forcing_product_abs_le {a b D G : ℝ}
    (ha : |a| ≤ D) (hb : |b| ≤ G) : |a * b| ≤ D * G := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem IteratesForcingGradient.forcing_four_abs_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h₁ := abs_add_le a b
  have h₂ := abs_add_le (a + b) c
  have h₃ := abs_add_le (a + b + c) d
  linarith only [h₁, h₂, h₃]

theorem IteratesForcingGradient.forcing_four_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

end AVenhance.Infra.Section4

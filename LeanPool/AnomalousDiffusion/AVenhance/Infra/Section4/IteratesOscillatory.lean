/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPrimitive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.DirectionalCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-! Space-time bounds for the primitive/material pairings in l.V.
Conditional material inputs refer to the actual material derivative fields. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Openness of the energy cell, independent of corrector tensors. -/
theorem iterate_timeCube_isOpen : IsOpen timeCube := by
  unfold timeCube unitCube
  exact isOpen_Ioo.prod (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))

/-- Dimension-two entrywise control for the matrix products in Err4,1/2. -/
theorem iterate_matrix_product_entry_bound
    (Q G : Matrix (Fin 2) (Fin 2) ℝ) {D B : ℝ}
    (hQ : ∀ i j, |Q i j| ≤ D) (hG : ∀ i j, |G i j| ≤ B) (i j : Fin 2) :
    |(Q * G) i j| ≤ 2 * D * B := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hQ 0 0)
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ p : Fin 2, |Q i p * G p j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 2, D * B := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul]
      exact mul_le_mul (hQ i p) (hG p j) (abs_nonneg _) hD
    _ = _ := by simp; ring

/-- The material equation comes from the actual classical PDE. -/
theorem iterate_material_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    amnrMaterial b u t x = κ * spaceLap (u t) x + F t x := by
  have h := hsol.2.2.2 t ht x
  change deriv (fun s => u s x) t - κ * spaceLap (u t) x +
    vecDot (b t x) (spaceGrad (u t) x) = F t x at h
  unfold amnrMaterial
  linarith only [h]

end AVenhance.Infra.Section4

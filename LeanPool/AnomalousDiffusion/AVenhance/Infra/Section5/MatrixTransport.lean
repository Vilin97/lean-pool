/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Product-rule cancellation for a matrix transported along a flow. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- Expand a directional derivative in the coordinate basis. -/
theorem fderiv_scalar_eq_sum_spaceGrad
    {f : Vec 2 → ℝ} {x v : Vec 2} :
    fderiv ℝ f x v =
      ∑ p : Fin 2, v p * spaceGrad f x p := by
  have hv : v = ∑ p : Fin 2, v p • basisVec p := by
    funext p
    fin_cases p <;> simp [basisVec, Fin.sum_univ_two]
  rw [hv, map_sum]
  simp [spaceGrad, Fin.sum_univ_two]

/-- A component of the directional derivative of a vector field is the
corresponding row-Jacobian contraction. -/
theorem fderiv_vector_component_eq_sum_gradMatrix
    {F : Vec 2 → Vec 2} {x v : Vec 2}
    (hF : DifferentiableAt ℝ F x) (j : Fin 2) :
    fderiv ℝ F x v j =
      ∑ p : Fin 2, v p * gradMatrix F x p j := by
  calc
    fderiv ℝ F x v j = fderiv ℝ (fun y => F y j) x v := by
      rw [fderiv_apply hF j]
      simp [ContinuousLinearMap.comp_apply]
    _ = ∑ p : Fin 2, v p * gradMatrix F x p j := by
      simpa [gradMatrix, Matrix.of_apply, spaceGrad] using
        fderiv_scalar_eq_sum_spaceGrad
          (f := fun y => F y j) (x := x) (v := v)

/-- Differentiating `A g` cancels the two velocity-gradient terms when `A`
obeys the variational equation and `g` the material-gradient equation. -/
theorem hasDerivAt_matrixVec_mul_transport
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {g : ℝ → Vec 2}
    {C : Matrix (Fin 2) (Fin 2) ℝ} {h : Vec 2} {t : ℝ}
    (i : Fin 2)
    (hA : ∀ j : Fin 2, HasDerivAt (fun r => A r i j)
      (∑ p : Fin 2, A t i p * C p j) t)
    (hg : ∀ j : Fin 2, HasDerivAt (fun r => g r j)
      (h j - ∑ p : Fin 2, C j p * g t p) t)
    :
    HasDerivAt (fun r => (A r).mulVec (g r) i)
      ((A t).mulVec h i) t := by
  have hP (j : Fin 2) : HasDerivAt (fun r => A r i j * g r j)
      ((∑ p : Fin 2, A t i p * C p j) * g t j +
        A t i j * (h j - ∑ p : Fin 2, C j p * g t p)) t := by
    exact (hA j).mul (hg j)
  have hsum : HasDerivAt
      (fun r => A r i 0 * g r 0 + A r i 1 * g r 1)
      (((∑ p : Fin 2, A t i p * C p 0) * g t 0 +
          A t i 0 * (h 0 - ∑ p : Fin 2, C 0 p * g t p)) +
        ((∑ p : Fin 2, A t i p * C p 1) * g t 1 +
          A t i 1 * (h 1 - ∑ p : Fin 2, C 1 p * g t p))) t := by
    convert (hP 0).add (hP 1) using 1
  have hvalue :
      ((∑ p : Fin 2, A t i p * C p 0) * g t 0 +
          A t i 0 * (h 0 - ∑ p : Fin 2, C 0 p * g t p)) +
        ((∑ p : Fin 2, A t i p * C p 1) * g t 1 +
          A t i 1 * (h 1 - ∑ p : Fin 2, C 1 p * g t p)) =
        (A t).mulVec h i := by
    simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  convert hsum using 1
  · funext r
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · exact hvalue.symm

end AVenhance.Infra.Section5

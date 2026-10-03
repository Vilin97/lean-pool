/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordCoefficientSplit

/-! Actual differentiated flux pairings on the periodic cell. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Smoothness of each expanded flux follows from the exact word identity. -/
theorem iterateWordFlux_smooth
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) : ContDiff ℝ (⊤ : ℕ∞) (iterateWordFlux A v w) := by
  have hF := iterate_matrix_gradient_smooth hA hv
  apply contDiff_pi.mpr
  intro i
  have he := iterateSpatialWord_matrix_flux hA hv w i
  exact he ▸ iterateSpatialWord_smooth (contDiff_pi.mp hF i) w

/-- Periodicity of every expanded flux is inherited from the actual factors. -/
theorem iterateWordFlux_periodic
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hAp : IsZ2Periodic A) (hvp : IsZ2Periodic v) (w : List (Fin 2)) :
    IsZ2Periodic (iterateWordFlux A v w) := by
  have hF := iterate_matrix_gradient_smooth hA hv
  have hp := iterate_matrix_gradient_periodic hv hAp hvp
  intro k x
  funext i
  have hpi : IsZ2Periodic (fun y => (A y).mulVec (spaceGrad v y) i) := by
    intro l y
    exact congrFun (hp l y) i
  have hwi := iterateSpatialWord_periodic (contDiff_pi.mp hF i) hpi w
  rw [← congrFun (iterateSpatialWord_matrix_flux hA hv w i) (x + latticeShift k),
    ← congrFun (iterateSpatialWord_matrix_flux hA hv w i) x]
  exact hwi k x

/-- The principal stream flux cancels pointwise with its own gradient. -/
theorem iterate_stream_principal_pairing_zero (ψ : Vec 2 → ℝ)
    (u : Vec 2 → ℝ) (x : Vec 2) :
    vecDot (spaceGrad u x) ((ψ x • sigmaMat).mulVec (spaceGrad u x)) = 0 := by
  simp [vecDot, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section4

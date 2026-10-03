/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialOperatorBounds

/-! Arbitrary-order actual velocity-Jacobian operator rates from the stream-regularity estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Spatial differentiation of the actual Jacobian commutes with its
coordinate projection. This is an exact operator identity at every order. -/
theorem amnr_velocityJacobian_iteratedFDeriv_coordinate {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) (n : ℕ) (t : ℝ) (x : Vec 2)
    (v : Fin n → Vec 2) (i p : Fin 2) :
    iteratedFDeriv ℝ n (fun y => jointSpatialFDeriv b t y) x v (basisVec p) i =
      iteratedFDeriv ℝ n
        (fun y => amnrVelocityGradient (fun z => b z.1 z.2) i p (t, y)) x v := by
  let J := fun y => jointSpatialFDeriv b t y
  let P : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec p))
  have hs : ContDiff ℝ (⊤ : ℕ∞) (b t) := hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := by
    simpa only [J, jointSpatialFDeriv_eq_slice hb] using hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have heq : P ∘ J = fun y => amnrVelocityGradient (fun z => b z.1 z.2) i p (t, y) := by
    funext y
    dsimp [P, J]
    rw [jointSpatialFDeriv_eq_slice hb]
    unfold amnrVelocityGradient AVenhance.spaceGrad
    rw [fderiv_apply (hs.differentiable (by simp) y) i]
    rfl
  have hh := P.iteratedFDeriv_comp_left (hJ.contDiffAt (x := x)) (i := n) (by simp)
  rw [heq] at hh
  exact (congrArg (fun L => L v) hh).symm

end AVenhance.Infra.Section4

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Orthogonality of gradients of functions sharing one scalar coordinate. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- If two scalar fields are both functions of one scalar coordinate, their
gradients are parallel; the rotated gradient pairing therefore vanishes. -/
theorem composed_gradients_sigma_orthogonal
    {η : Vec 2 → ℝ} {f g : ℝ → ℝ} {x : Vec 2}
    {L : Vec 2 →L[ℝ] ℝ} {f' g' : ℝ}
    (hη : HasFDerivAt η L x)
    (hf : HasDerivAt f f' (η x)) (hg : HasDerivAt g g' (η x)) :
    vecDot (spaceGrad (fun y => f (η y)) x)
      (sigmaMat.mulVec (spaceGrad (fun y => g (η y)) x)) = 0 := by
  let v : Vec 2 := fun i => L (basisVec i)
  have hF := hf.hasFDerivAt.comp x hη
  have hG := hg.hasFDerivAt.comp x hη
  have hgradF : spaceGrad (fun y => f (η y)) x = f' • v := by
    funext i
    change fderiv ℝ (f ∘ η) x (basisVec i) = _
    rw [hF.fderiv]
    simp [v, ContinuousLinearMap.comp_apply]
    ring
  have hgradG : spaceGrad (fun y => g (η y)) x = g' • v := by
    funext i
    change fderiv ℝ (g ∘ η) x (basisVec i) = _
    rw [hG.fderiv]
    simp [v, ContinuousLinearMap.comp_apply]
    ring
  rw [hgradF, hgradG]
  simp [vecDot, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section5

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ShearDiffusionOperator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamVelocityIncrement

/-! The divergence-form diffusion split for the actual stream velocity. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- For the velocity recursion, the new-scale advection-diffusion
operator splits into old-stream transport and the exact `ψTilde_m` divergence
form diffusion. -/
theorem frozen_stream_advDiffOp_divergence_split
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κ : ℝ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (hu : ContDiffAt ℝ 2 (u t) x) :
    advDiffOp (streamVel (Φ m)) κ u t x =
      (deriv (fun s => u s x) t +
        vecDot (streamVel (Φ (m - 1)) t x) (spaceGrad (u t) x)) -
        vecDiv (fun y =>
          (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
              psiTilde I hΦ m t y • sigmaMat).mulVec
            (spaceGrad (u t) y)) x := by
  apply advDiffOp_shear_divergence_split
  · exact streamSeq_velocity_increment_eq_psiTilde I hΦ m hm t x
  · exact streamSeq_psiTilde_differentiableAt I hΦ m hm t x
  · exact hu

end AVenhance.Infra.Section5

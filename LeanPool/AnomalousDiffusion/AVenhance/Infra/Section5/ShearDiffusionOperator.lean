/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OperatorSplit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DiffusionDivergence

/-! The velocity increment turns the new-scale diffusion into divergence form. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- If the velocity increment is the perpendicular gradient of a scalar
potential, the operator splits into old-scale transport and the exact
divergence-form diffusion used in Section 5.1. -/
theorem advDiffOp_shear_divergence_split
    {b₀ b₁ : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {ψ : Vec 2 → ℝ} {t : ℝ} {x : Vec 2}
    (hvelocity : b₁ t x - b₀ t x = sigmaMat.mulVec (spaceGrad ψ x))
    (hψ : DifferentiableAt ℝ ψ x)
    (hu : ContDiffAt ℝ 2 (u t) x) :
    advDiffOp b₁ κ u t x =
      (deriv (fun s => u s x) t + vecDot (b₀ t x) (spaceGrad (u t) x)) -
        vecDiv (fun y =>
          (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ψ y • sigmaMat).mulVec
            (spaceGrad (u t) y)) x := by
  rw [advDiffOp_split]
  rw [hvelocity]
  have hdiff := shear_diffusion_eq_negative_div κ hψ hu
  change (deriv (fun s => u s x) t +
      vecDot (b₀ t x) (spaceGrad (u t) x)) +
    (-κ * spaceLap (u t) x +
      vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (spaceGrad (u t) x)) = _
  rw [hdiff]
  ring

end AVenhance.Infra.Section5

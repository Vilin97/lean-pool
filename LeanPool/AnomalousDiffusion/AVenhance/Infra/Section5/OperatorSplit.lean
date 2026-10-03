/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Exact algebraic splitting of the Section 5 advection-diffusion operator. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- Split the new-scale operator into old-scale transport and the velocity
increment. -/
theorem advDiffOp_split
    {b₀ b₁ : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {t : ℝ} {x : Vec 2} :
    advDiffOp b₁ κ u t x =
      (deriv (fun s => u s x) t +
        vecDot (b₀ t x) (spaceGrad (u t) x)) +
      (-κ * spaceLap (u t) x +
        vecDot (b₁ t x - b₀ t x) (spaceGrad (u t) x)) := by
  unfold advDiffOp
  simp [vecDot, Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section5

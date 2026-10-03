/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothWordEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.AdvDiffOp

/-! Pointwise advection-diffusion equation for the unit-slab Galerkin limit. -/

@[expose] public section

noncomputable section

open Set
open Homogenization

namespace AVenhance.Infra.Classical

/-- The real smooth Galerkin limit solves the advection-diffusion equation in the open
unit time slab. -/
theorem classicalGalerkinUnitLimit_advDiffOp
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Vec 2) :
    AVenhance.advDiffOp (AVenhance.streamVel φ) κ
      (fun s y => classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp s) y) t x = F t x := by
  let θ : ℝ → Vec 2 → ℝ := fun s y =>
    classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp s) y
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩
  have hcl : classicalGalerkinUnitSlabClamp t =
      ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ := by
    apply Subtype.ext
    simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt ht.1),
      min_eq_right (le_of_lt ht.2)]
  have htime := classicalGalerkinWordPointwise_hasDerivAt
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [] x ht
  have htime' : HasDerivAt (fun s => θ s x)
      (F t x + κ * AVenhance.spaceLap u x -
        classicalTransport (AVenhance.streamVel φ t) u x) t := by
    simpa [θ, u, hcl, classicalWordDerivative] using htime
  have hslice : θ t = u := by
    funext y
    simp [θ, u, hcl]
  have hslice' : (fun y => classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp t) y) = u := hslice
  simp only [AVenhance.advDiffOp]
  rw [htime'.deriv, hslice']
  simp only [classicalTransport]
  dsimp [Homogenization.vecDot]
  ring

end AVenhance.Infra.Classical

end

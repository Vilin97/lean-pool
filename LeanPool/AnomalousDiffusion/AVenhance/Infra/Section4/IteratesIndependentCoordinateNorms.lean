/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesNormComponents

/-! # Iterates Independent Coordinate Norms

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Quarter-energy bounds control independently chosen scalar and gradient
coordinate words. This matches the two separate maxima in the source norm. -/
theorem iterate_independent_coordinate_norms {e g κ H : ℝ}
    (he : 0 ≤ e) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (hH : 0 ≤ H)
    (heH : e ≤ H ^ 2 / 4) (hgH : κ * g ≤ H ^ 2 / 4) :
    Real.sqrt e + Real.sqrt κ * Real.sqrt g ≤ H := by
  have hs : (Real.sqrt κ * Real.sqrt g) ^ 2 = κ * g := by
    rw [mul_pow, Real.sq_sqrt hκ, Real.sq_sqrt hg]
  have hse := Real.sq_sqrt he
  have h0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg _
  have h1 : 0 ≤ Real.sqrt κ * Real.sqrt g := by positivity
  have hehalf : Real.sqrt e ≤ H / 2 := by nlinarith only [heH, hse, h0, hH]
  have hghalf : Real.sqrt κ * Real.sqrt g ≤ H / 2 := by nlinarith only [hgH, hs, h1, hH]
  linarith only [hehalf, hghalf]

end AVenhance.Infra.Section4

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth

/-!
# Backward Gaussian test functions

The backward test function used in the local energy calculation is recorded
together with its nonnegativity.
-/

@[expose] public section

open scoped Topology


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- Rescaled backward heat test function centered at time `r ^ 2`. -/
def backwardHeatTestFunction (r : ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  r ^ 2 * heatKernel x (r ^ 2 - t)

lemma backwardHeatTestFunction_nonneg {r : ℝ} {x : Vec3} {t : ℝ}
    (_ : 0 < r) (_ : t < r ^ 2) :
    0 ≤ backwardHeatTestFunction r x t := by
  rw [backwardHeatTestFunction]
  exact mul_nonneg (sq_nonneg r) (heatKernel_nonneg _ _)

end CKN.Foundation.Heat

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.KStatistic
import LeanPool.Feige.Reduction
import LeanPool.Feige.SimplexMeasure

/-!
# From simplex geometry to the exponential statistic

The paper defines `Kₙ` by normalized simplex volume in (2.1).  The
formalization also uses an equivalent independent-exponential
representation.  This file records their identification and proves that
the `α = 0` centroid-halfspace theorem supplies the `δ = 1`
`LargeSumBridge` consumed by the final reduction.
-/

namespace Feige

/-- Equality of the simplex-volume and exponential presentations of the
Dirichlet statistic. -/
def SimplexExponentialIdentification (n : ℕ) : Prop :=
  ∀ y : Fin n → ℝ, dirichletK y = simplexK y

/-- The `δ = 1` geometric estimate in §2.2 for `dirichletK`, reduced to
the distributional identification and the simplex centroid-halfspace
bound. -/
theorem dirichletK_largeSumBridge_of_simplex
    {n : ℕ} (hid : SimplexExponentialIdentification n)
    (hcentroid : SimplexCentroidHalfspaceProperty (ι := Fin n)) :
    LargeSumBridge (dirichletK : (Fin n → ℝ) → ℝ) := by
  intro y hy hsum
  rw [hid y]
  simpa using
    (simplex_largeSumBridge hcentroid y hy (by simpa using hsum))

end Feige

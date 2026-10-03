/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarPointsRho.Points
public import LeanPool.Zeta32.FstarPointsRho.Ell

/-! The `ℓ` and `ρ` parts of `FstarPoints`: `ℓ(a) ≤ −159/100` uniformly on
`[a₋, a₊]` (`FstarPointsRho/Ell.lean`) and `Rlow k ≤ ρ_{a₋}(x_{k+1})` for all 15 points
(`FstarPointsRho/Points.lean`, one declaration per point). Generic lemmas:
`FstarPointsRho/Basic.lean`. -/

public section

namespace Zeta32.Fstar

theorem pointsRho : (∀ a ∈ Set.Icc aMinus aPlus, ellA a ≤ -159/100) ∧
    ∀ k : Fin 15, ((Rlow k : ℚ) : ℝ) ≤ rhoA aMinus (xk (k.val + 1)) :=
  ⟨fun _ ha => B2.ell_upper ha.1 ha.2, B2.rho_all⟩

end Zeta32.Fstar

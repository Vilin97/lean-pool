/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarPointsW.Points
public import LeanPool.Zeta32.FstarPointsW.MassLog

/-! Root of the point checks for `F* ≤ -6`: the mass bracket, the
`log 3` lower bound and the 15 lower bounds for `Wt` at `x_k = aMinus·k/16` (index `k : Fin 15`
stands for `x_(k+1)`). No `sorry`, no new axioms, no `native_decide`. -/

public section

namespace Zeta32.Fstar

theorem pointsW : massA aMinus < 1 ∧ 1 < massA aPlus ∧ (549/500 : ℝ) < Real.log 3 ∧
    ∀ k : Fin 15, ((Wlow k : ℚ) : ℝ) ≤ Wt (xk (k.val + 1)) := by
  refine ⟨PW.mass_minus_lt_one, PW.one_lt_mass_plus, PW.log_three_gt, ?_⟩
  intro k
  fin_cases k
  exacts [PW.Wt_x1, PW.Wt_x2, PW.Wt_x3, PW.Wt_x4, PW.Wt_x5, PW.Wt_x6, PW.Wt_x7, PW.Wt_x8,
    PW.Wt_x9, PW.Wt_x10, PW.Wt_x11, PW.Wt_x12, PW.Wt_x13, PW.Wt_x14, PW.Wt_x15]

end Zeta32.Fstar

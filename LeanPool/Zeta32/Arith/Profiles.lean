/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Family
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Zeta32 — Arith — Profiles. -/

public section

namespace Zeta32.ArithSum
/-- The fractional-part profile controlling the arithmetic valuation bound. -/
@[expose]
noncomputable def psiL (x : ℝ) : ℝ :=
  let a := Int.fract (1/x); let b := Int.fract (5/x); let g := Int.fract (3/x)
  6 + x*g*(1-g) - 3*(4*a-b) + x/4*(16*a + b - 8*min a b - (4*a-b)^2)
/-- The piecewise affine profile controlling the outer-prime contribution. -/
@[expose]
noncomputable def phiL (x : ℝ) : ℝ :=
  if x ≤ 5/2 then 6 - x else if x ≤ 3 then 24 - 7*x else if x ≤ 4 then 18 - 5*x else 2 - x

/- The theorem `Zeta32.ArithSum.arith_sum` is proved in `Zeta32/Arith/Sum/Main.lean`, which
imports the
definitions above. -/

end Zeta32.ArithSum

end

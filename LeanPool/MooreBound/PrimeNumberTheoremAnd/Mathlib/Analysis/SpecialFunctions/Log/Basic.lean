/-
Copyright (c) 2026 PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PrimeNumberTheoremAnd contributors
-/

module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Ported for Lean Pool from PrimeNumberTheoremAnd commit
0c7abf7be7765dc5ffd21afc1c37b018199ec3c9, via wewantmoore commit
d59bd80ea93fabb9faf769e790ab47692645e022 (both Apache-2.0).
The port adds the MooreBound namespace and updates Mathlib APIs and proof style.
Wiener and Consequences retain the PNT and prime-interval dependency closure;
unrelated later developments and LeanArchitect annotations are omitted.
-/

public section

namespace MooreBound

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end MooreBound

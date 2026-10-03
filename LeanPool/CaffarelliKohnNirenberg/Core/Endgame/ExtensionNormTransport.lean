/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Transport of an Lp norm estimate to its actual functions

Finite Lp representatives retain their literal extended-valued seminorms.
Consequently a real norm estimate between the representatives gives the
same numerical estimate on the original functions, for any exponent.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace CKN.Core.Endgame

/-- A norm estimate for two actual `MemLp` representatives gives the same
extended-valued seminorm estimate for the original functions. -/
theorem eLpNorm_le_of_toLp_norm_le
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {p : ℝ≥0∞} {f : α → E} {g : α → F}
    (hf : MemLp f p μ) (hg : MemLp g p μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ‖hg.toLp g‖ ≤ C * ‖hf.toLp f‖) :
    eLpNorm g p μ ≤ ENNReal.ofReal C * eLpNorm f p μ := by
  rw [Lp.norm_toLp, Lp.norm_toLp] at hbound
  have h := ENNReal.ofReal_le_ofReal hbound
  simpa only [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hg.eLpNorm_ne_top,
    ENNReal.ofReal_toReal hf.eLpNorm_ne_top] using h

end CKN.Core.Endgame

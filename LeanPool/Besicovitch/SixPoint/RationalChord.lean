/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# The rational chord of the retargeted six-point argument

The six-point analysis computes the sharp constant `sStar`, but a Lean proof of
`sigmaOne ≤ sStar` needs that endpoint to be attained exactly, and the resulting tightness is what
makes the finite certificates expensive.  The argument is carried out instead at the rational
threshold `barS = 6934 / 10000`, which still improves on the published `0.7` and leaves the weighted
score a margin of about `3 * 10 ^ -3` rather than `10 ^ -8`.

The routing and exclusion modules use a chord only through the two facts below: that it lies
between one and two, and that it lies in an explicit rational box.  Both are immediate here.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- Twice the rational threshold: the chord length of the retargeted argument. -/
def barC : ℝ := 3467 / 2500

/-- The rational density threshold certified by the retargeted argument. -/
def barS : ℝ := barC / 2

/-- The rational threshold is `0.6934`. -/
theorem barS_eq : barS = 6934 / 10000 := by
  norm_num [barS, barC]

/-- The rational chord lies in an explicit isolation box. -/
theorem barC_mem_isolation_box :
    13867999999999999 / 10 ^ 16 < barC ∧ barC < 13868000000000001 / 10 ^ 16 := by
  constructor <;> norm_num [barC]

/-- The rational chord is a genuine chord of the unit disk. -/
theorem one_lt_barC_and_barC_lt_two : 1 < barC ∧ barC < 2 := by
  constructor <;> norm_num [barC]

/-- The rational chord is positive. -/
theorem barC_pos : 0 < barC := by
  norm_num [barC]

/-- The rational threshold lies in an explicit isolation box. -/
theorem barS_mem_isolation_box :
    6933999999999999 / 10 ^ 16 ≤ barS ∧ barS < 6934000000000001 / 10 ^ 16 := by
  constructor <;> norm_num [barS, barC]

/-- The rational threshold lies strictly between one half and one. -/
theorem half_lt_barS_and_barS_lt_one : 1 / 2 < barS ∧ barS < 1 := by
  constructor <;> norm_num [barS, barC]

/-- The rational threshold exceeds one half. -/
theorem half_lt_barS : 1 / 2 < barS := half_lt_barS_and_barS_lt_one.1

/-- The rational threshold is below one. -/
theorem barS_lt_one : barS < 1 := half_lt_barS_and_barS_lt_one.2

/-- The rational threshold is positive. -/
theorem barS_pos : 0 < barS := by
  norm_num [barS, barC]

/-- The rational threshold is below the previous record. -/
theorem barS_lt_seven_tenths : barS < 7 / 10 := by
  norm_num [barS, barC]

end LeanPool.Besicovitch

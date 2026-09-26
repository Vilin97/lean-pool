/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal.OutputBounds

/-!
# Output-length bounds

A deterministic machine can change only the output cell currently under its
head. Consequently, a run of `t` transitions from a blank output tape can
produce at most `t` output bits.

## Main results

- `TM.reachesIn_output_cells_far` — sufficiently distant output cells are unchanged
- `TM.output_length_le_of_reachesIn` — a run bounds its output length
- `TM.ComputesInTime.output_length_le` — a time bound also bounds output length
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Cells beyond the output head's maximum reach are never changed. -/
theorem reachesIn_output_cells_far {tm : TM n} {t : ℕ}
    {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (j : ℕ) (hj : c.output.head + t < j) :
    c'.output.cells j = c.output.cells j := by
  exact reachesIn_output_cells_far_internal hreach j hj

/-- A run from an initial configuration needs at least one transition for
each bit present in its final output string. -/
theorem output_length_le_of_reachesIn {tm : TM n} {x y : List Bool}
    {c' : Cfg n tm.Q} {t : ℕ}
    (hreach : tm.reachesIn t (tm.initCfg x) c')
    (hout : c'.output.HasOutput y) : y.length ≤ t := by
  exact output_length_le_of_reachesIn_internal hreach hout

/-- The output of a time-bounded function computation is no longer than the
advertised running-time bound. -/
theorem ComputesInTime.output_length_le {tm : TM n}
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (h : tm.ComputesInTime f T) (x : List Bool) :
    (f x).length ≤ T x.length := by
  exact computesInTime_output_length_le_internal h x

end TM

end Complexity

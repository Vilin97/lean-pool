/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal.CopyOutput

/-!
# Input-to-output copy subroutine

Public correctness theorem for `TM.copyInputToOutputTM`. The machine copies
its Boolean input verbatim to its output tape in the exact linear bound
`|x| + 2`, without using the contents of its fixed work-tape bank.

## Main result

- `TM.copyInputToOutputTM_computesInTime` — the copy machine computes `id`
  within time `m + 2`
-/


public section

namespace Complexity

namespace TM

/-- The input-to-output copy machine computes the identity function within
the exact linear time bound `m + 2`. -/
theorem copyInputToOutputTM_computesInTime (n : ℕ) :
    (copyInputToOutputTM (n := n)).ComputesInTime id (fun m => m + 2) := by
  exact copyInputToOutputTM_computesInTime_internal n

end TM

end Complexity

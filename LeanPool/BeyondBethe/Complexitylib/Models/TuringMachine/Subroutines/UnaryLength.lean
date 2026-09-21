/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.UnaryLength.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.UnaryLength.Internal

/-!
# Unary input-length transducer

Public correctness theorem for `TM.unaryLengthTM`. On input `x`, the machine
emits `List.replicate x.length true` within the linear bound `|x| + 2`.

## Main result

- `TM.unaryLengthTM_computesInTime` — unary input-length computation in
  linear time
-/


public section

namespace Complexity

namespace TM

/-- The unary input-length transducer computes `List.replicate |x| true`
within the linear time bound `m + 2`. -/
theorem unaryLengthTM_computesInTime (n : ℕ) :
    (unaryLengthTM (n := n)).ComputesInTime
      (fun x => List.replicate x.length true) (fun m => m + 2) := by
  exact unaryLengthTM_computesInTime_internal n

end TM

end Complexity

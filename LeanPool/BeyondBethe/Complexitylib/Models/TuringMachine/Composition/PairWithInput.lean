/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.PairWithInput.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.PairWithInput.Internal

/-!
# Pair a computed value with the original input

This module exposes a generic deterministic fanout combinator. If `tmF`
computes `f`, then `pairWithInputTM tmF` computes `x ↦ pair (f x) x` while
retaining a concrete polynomial-preserving time bound.

## Main result

- `TM.pairWithInputTM_computesInTime` — computation paired with original input
-/


public section

namespace Complexity

namespace TM

variable {nf : ℕ}

/-- Pairing a computed string with the unchanged original input costs at most
five source-time budgets, one linear input scan, and constant seam overhead. -/
theorem pairWithInputTM_computesInTime
    {tmF : TM nf} {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : tmF.ComputesInTime f T) :
    (pairWithInputTM tmF).ComputesInTime
      (fun x => pair (f x) x) (pairWithInputTime T) :=
  pairWithInputTM_computesInTime_internal hcomp

end TM

end Complexity

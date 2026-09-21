/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Internal

/-!
# Sequential composition after function computation

`TM.compositionTM tmF tmG` is an executable deterministic machine that runs
`tmF`, copies its delimited output onto a fresh virtual-input tape, and then
runs `tmG` on that output. Work tapes of the two machines occupy disjoint
blocks, and the intermediate raw output may contain arbitrary junk after its
first delimiter.

## Main result

- `TM.compositionTM_computesInTime` — correctness with a monotone coarse time bound
- `TM.compositionTM_decidesInTime` — function computation followed by a decider
-/


public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

/-- Sequential deterministic function composition. The first computation,
two copy/rewind passes, four phase transitions, and the second computation fit
within `4 * TF(n) + 11 + TG(TF(n))` whenever `TG` is monotone. -/
theorem compositionTM_computesInTime
    {tmF : TM nf} {tmG : TM ng}
    {f g : List Bool → List Bool} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF)
    (hG : tmG.ComputesInTime g TG)
    (hmono : Monotone TG) :
    (compositionTM tmF tmG).ComputesInTime (g ∘ f)
      (fun n => 4 * TF n + 11 + TG (TF n)) :=
  compositionTM_computesInTime_internal hF hG hmono

/-- Sequential deterministic preprocessing followed by a language decider.
The composite decides the preimage language with the same coarse monotone time
bound as function composition. -/
theorem compositionTM_decidesInTime
    {tmF : TM nf} {tmG : TM ng}
    {f : List Bool → List Bool} {L : Language} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF)
    (hG : tmG.DecidesInTime L TG)
    (hmono : Monotone TG) :
    (compositionTM tmF tmG).DecidesInTime (f ⁻¹' L)
      (fun n => 4 * TF n + 11 + TG (TF n)) :=
  compositionTM_decidesInTime_preimage_internal hF hG hmono

end TM

end Complexity

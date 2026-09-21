/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Internal.Preimage

/-!
# Closure of P under FP preimages

## Main result

- `mem_P_preimage` — polynomial-time preprocessing preserves membership in `P`
-/


public section

namespace Complexity

/-- If `f` is polynomial-time computable and `L` is polynomial-time
decidable, then the preimage language `{x | f x ∈ L}` is in `P`. -/
theorem mem_P_preimage {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : L ∈ P) : f ⁻¹' L ∈ P :=
  mem_P_preimage_internal hf hL

end Complexity

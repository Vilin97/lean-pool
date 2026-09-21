/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Internal.Composition

/-!
# Closure of FP under composition

## Main result

- `mem_FP_comp` — polynomial-time string functions are closed under composition
-/


public section

namespace Complexity

/-- The composition of two polynomial-time string functions is polynomial-time. -/
theorem mem_FP_comp {f g : List Bool → List Bool}
    (hf : f ∈ FP) (hg : g ∈ FP) : (g ∘ f) ∈ FP := by
  exact mem_FP_comp_internal hf hg

end Complexity

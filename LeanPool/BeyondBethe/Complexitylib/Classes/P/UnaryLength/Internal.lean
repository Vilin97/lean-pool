/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.UnaryLength

/-!
# Polynomial-time unary input length — proof internals
-/


public section

namespace Complexity

/-- Internal proof that materializing unary input length is in `FP`. -/
theorem unaryLength_mem_FP_internal :
    (fun x : List Bool => List.replicate x.length true) ∈ FP := by
  refine ⟨1, 0, TM.unaryLengthTM,
    (fun n => n + 2), TM.unaryLengthTM_computesInTime 0, ?_⟩
  have hn : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  exact BigO.add hn (BigO.const_le_pow 2 1)

end Complexity

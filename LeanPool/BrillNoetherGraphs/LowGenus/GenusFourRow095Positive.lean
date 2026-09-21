/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095CaseOne
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095CasesTwoThree
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095CaseThreeProof
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095Symmetry

/-!
# Unconditional existence on genus-four Core 095

This file assembles the three Atanasov--Ranganathan length comparisons and
then removes the normalization `L₀ ≤ L₅` by the exact Core-095
involution.  The result is a kernel-checked degree-three rank-one divisor for
every positive integral subdivision of the public row-095 core.
-/

namespace LowGenus.GenusFourRow095
open Utilities.Certificate

open Utilities

/-- The three signed-window branches cover every normalized positive length
assignment. -/
theorem bnExists_one_three_normalized
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)
    (hNorm : length 0 ≤ length 5) :
    BNExists (Spec length hLength).graph 1 3 := by
  by_cases hBC : C length ≤ B length
  · exact CaseOne.bnExists_one_three length hLength hNorm hBC
  · have hBCLt : B length < C length := by omega
    by_cases hLarge :
        CaseTwo.m length ≤ CaseTwo.Y length
    · exact CaseTwo.bnExists_one_three length hLength hNorm hBCLt hLarge
    · have hYSmall :
          CaseThree.Y length < min (X length) (Delta length) := by
        simpa [CaseTwo.m, CaseTwo.Y, CaseThree.Y] using
          (Nat.lt_of_not_ge hLarge)
      exact CaseThree.bnExists_one_three length hLength hNorm hBCLt
        hYSmall

/-- Every positive integral subdivision of catalog Core 095 carries a
degree-three rank-one divisor. -/
theorem bnExists_one_three
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    BNExists (Spec length hLength).graph 1 3 := by
  apply BNExists_of_normalized
    (fun normalized normalizedPos hNorm =>
      bnExists_one_three_normalized normalized normalizedPos hNorm)

end LowGenus.GenusFourRow095

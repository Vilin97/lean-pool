/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerCompare
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalArithmetic

/-!
# Polynomial-time comparison of unreduced rationals

Positive denominators allow comparison by signed cross multiplication.  The
two cross-products are exactly the products already used by rational addition;
the final comparison is the verified signed-integer machine.
-/

namespace BeyondBethe

open Complexity

def machineRawRatLeBit (word : List Bool) : List Bool :=
  machineIntegerLeCode
    (pair (machineRawAddLeftScaledNumerator word)
      (machineRawAddRightScaledNumerator word))

theorem machineRawRatLeBit_mem_FP : machineRawRatLeBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineRawAddLeftScaledNumerator_mem_FP
    machineRawAddRightScaledNumerator_mem_FP
  simpa only [machineRawRatLeBit] using!
    machineCompose_mem_FP hpair machineIntegerLeCode_mem_FP

theorem machineRawRatLeBit_cross_encode (q r : RawRat) :
    machineRawRatLeBit
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      [decide
        (q.num * (r.den : ℤ) ≤ r.num * (q.den : ℤ))] := by
  rw [machineRawRatLeBit, machineRawAddLeftScaledNumerator_encode,
    machineRawAddRightScaledNumerator_encode,
    machineIntegerLeCode_encode]

theorem rawRat_value_le_iff_cross (q r : RawRat) :
    q.value ≤ r.value ↔
      q.num * (r.den : ℤ) ≤ r.num * (q.den : ℤ) := by
  constructor
  · intro h
    have hdiv : (q.num : ℚ) / (q.den : ℚ) ≤
        (r.num : ℚ) / (r.den : ℚ) := by
      simpa only [RawRat.value] using! h
    have hcross :=
      (div_le_div_iff₀ (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)
        (by exact_mod_cast r.den_pos : (0 : ℚ) < r.den)).1 hdiv
    exact_mod_cast hcross
  · intro h
    have hcross : (q.num : ℚ) * (r.den : ℚ) ≤
        (r.num : ℚ) * (q.den : ℚ) := by
      exact_mod_cast h
    have hdiv : (q.num : ℚ) / (q.den : ℚ) ≤
        (r.num : ℚ) / (r.den : ℚ) :=
      (div_le_div_iff₀ (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)
        (by exact_mod_cast r.den_pos : (0 : ℚ) < r.den)).2 hcross
    simpa only [RawRat.value] using! hdiv

theorem machineRawRatLeBit_encode (q r : RawRat) :
    machineRawRatLeBit
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      [decide (q.value ≤ r.value)] := by
  rw [machineRawRatLeBit_cross_encode]
  by_cases hcross : q.num * (r.den : ℤ) ≤ r.num * (q.den : ℤ)
  · have hvalue := (rawRat_value_le_iff_cross q r).2 hcross
    simp [hcross, hvalue]
  · have hvalue : ¬ q.value ≤ r.value := by
      exact fun h => hcross ((rawRat_value_le_iff_cross q r).1 h)
    simp [hcross, hvalue]

end BeyondBethe

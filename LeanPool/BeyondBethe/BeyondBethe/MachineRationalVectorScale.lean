/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalizedDirection

/-!
# Polynomial-time rational vector scaling

The input is a raw rational scalar followed by a canonically encoded rational
vector.  We reduce scaling to the verified row-division machine: division by
`1 / s` is multiplication by `s`, including at `s = 0` under the field's total
inverse convention.  The reciprocal remains an unreduced `RawRat` word, so
the composition performs no decoding or hidden rational arithmetic.
-/

namespace BeyondBethe

open Complexity

def rationalVectorScale {d : ℕ}
    (s : ℚ) (v : Fin d → ℚ) : Fin d → ℚ :=
  fun i ↦ s * v i

def machineRationalVectorScaleReciprocalCode
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (rawRatBinaryCode RawRat.one) (machinePairFirst word))

def machineRationalVectorScaleCode
    (word : List Bool) : List Bool :=
  machineRationalRowDivide
    (pair (machineRationalVectorScaleReciprocalCode word)
      (machinePairSecond word))

theorem machineRationalVectorScaleReciprocalCode_mem_FP :
    machineRationalVectorScaleReciprocalCode ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machinePairFirst_mem_FP
  simpa only [machineRationalVectorScaleReciprocalCode] using
    machineCompose_mem_FP hinput machineRawRatDivCode_mem_FP

theorem machineRationalVectorScaleCode_mem_FP :
    machineRationalVectorScaleCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalVectorScaleReciprocalCode_mem_FP machinePairSecond_mem_FP
  simpa only [machineRationalVectorScaleCode] using
    machineCompose_mem_FP hinput machineRationalRowDivide_mem_FP

theorem rationalRowDivideValues_reciprocal_ofFn {d : ℕ}
    (s : RawRat) (v : Fin d → ℚ) :
    rationalRowDivideValues (RawRat.one.div s) (List.ofFn v) =
      List.ofFn (rationalVectorScale s.value v) := by
  rw [rationalRowDivideValues, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [rationalVectorScale, binaryNormalizeRawRat_eq_value,
    RawRat.value_div, RawRat.value_one, rawRatOfRat_value]
  ring

@[simp] theorem machineRationalVectorScaleCode_encode {d : ℕ}
    (s : RawRat) (v : Fin d → ℚ) :
    machineRationalVectorScaleCode
        (pair (rawRatBinaryCode s) (rationalFiniteVectorCode v)) =
      rationalFiniteVectorCode (rationalVectorScale s.value v) := by
  rw [machineRationalVectorScaleCode,
    machineRationalVectorScaleReciprocalCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    machineRawRatDivCode_encode]
  change machineRationalRowDivide
      (machineRationalRowDivideCanonicalInput
        (RawRat.one.div s) (List.ofFn v)) = _
  rw [machineRationalRowDivide_encode,
    rationalRowDivideValues_reciprocal_ofFn]
  rfl

end BeyondBethe

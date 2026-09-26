/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidScalars
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalRowDivide

/-!
# Polynomial-time rational normalization of a cut direction

The center update uses the vector `b / sum_i |b_i|`.  The scalar is computed
by the verified `ℓ1` fold and is passed, still as an unreduced rational word,
to the verified row-division fold.  Thus the composition performs no decoding
and no hidden field arithmetic.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Divides every rational direction coordinate by the cut's L1 scale. -/
def rationalNormalizedDirection {d : ℕ}
    (b : Fin d → ℚ) : Fin d → ℚ :=
  fun i ↦ b i / cutL1Scale b

/-- Divides the encoded rational vector by its raw L1 norm to obtain its normalized direction. -/
def machineRationalNormalizedDirectionCode
    (word : List Bool) : List Bool :=
  machineRationalRowDivide
    (pair (machineRationalVectorL1RawCode word) word)

theorem machineRationalNormalizedDirectionCode_mem_FP :
    machineRationalNormalizedDirectionCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalVectorL1RawCode_mem_FP id_mem_FP
  simpa only [machineRationalNormalizedDirectionCode] using!
    machineCompose_mem_FP hinput machineRationalRowDivide_mem_FP

theorem rationalRowDivideValues_l1_ofFn {d : ℕ}
    (b : Fin d → ℚ) :
    rationalRowDivideValues
        (rawRatListL1Sum RawRat.zero (List.ofFn b)) (List.ofFn b) =
      List.ofFn (rationalNormalizedDirection b) := by
  rw [rationalRowDivideValues, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [rationalNormalizedDirection, binaryNormalizeRawRat_eq_value,
    RawRat.value_div, rawRatOfRat_value, rawRatListL1Sum_ofFn_value,
    cutL1Scale]

@[simp] theorem machineRationalNormalizedDirectionCode_encode {d : ℕ}
    (b : Fin d → ℚ) :
    machineRationalNormalizedDirectionCode (rationalFiniteVectorCode b) =
      rationalFiniteVectorCode (rationalNormalizedDirection b) := by
  rw [machineRationalNormalizedDirectionCode,
    machineRationalVectorL1RawCode_encode]
  change machineRationalRowDivide
      (machineRationalRowDivideCanonicalInput
        (rawRatListL1Sum RawRat.zero (List.ofFn b)) (List.ofFn b)) = _
  rw [machineRationalRowDivide_encode,
    rationalRowDivideValues_l1_ofFn]
  rfl

theorem rationalNormalizedDirection_apply {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    rationalNormalizedDirection b i = b i / cutL1Scale b := rfl

end BeyondBethe

/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryGCD
import LeanPool.BeyondBethe.BeyondBethe.MachineOutputEncoding
import LeanPool.BeyondBethe.BeyondBethe.RawRational

/-!
# Signed integers at the rational-arithmetic boundary

The project encoding follows Lean's constructors: `Int.ofNat n` is
`false :: n.bits`, whereas `Int.negSucc n` is `true :: n.bits`.  Thus the
payload of a negative integer is one less than its absolute value.  The
machines below perform the required conversion explicitly.
-/

namespace BeyondBethe

open Complexity

def machineIntegerNegativeAbsBits (word : List Bool) : List Bool :=
  machineBinaryAddBits (pair word.tail [true])

/-- Canonical absolute-value bits from an `integerBinaryCode`. -/
def machineIntegerNatAbsBits (word : List Bool) : List Bool :=
  machineIfHead word (machineIntegerNegativeAbsBits word) word.tail

def machineIntegerNegativePayloadBits (absBits : List Bool) : List Bool :=
  machineBinarySubBits (pair absBits [true])

/-- Input is `pair originalIntegerCode absoluteValueBits`.  The output has the
sign of the original integer and the supplied absolute value. -/
def machineIntegerCodeFromSignedAbs (word : List Bool) : List Bool :=
  let signCode := machinePairFirst word
  let absBits := machinePairSecond word
  machineIfHead signCode
    (true :: machineIntegerNegativePayloadBits absBits)
    (false :: absBits)

theorem machineIntegerNegativeAbsBits_mem_FP :
    machineIntegerNegativeAbsBits ∈ Complexity.FP := by
  have hpair : (fun word : List Bool => pair word.tail [true]) ∈
      Complexity.FP :=
    machinePair_mem_FP machineTail_mem_FP (machineConst_mem_FP [true])
  simpa only [machineIntegerNegativeAbsBits] using
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineIntegerNatAbsBits_mem_FP :
    machineIntegerNatAbsBits ∈ Complexity.FP := by
  simpa only [machineIntegerNatAbsBits] using
    machineIfHead_mem_FP id_mem_FP machineIntegerNegativeAbsBits_mem_FP
      machineTail_mem_FP

theorem machineIntegerNegativePayloadBits_mem_FP :
    machineIntegerNegativePayloadBits ∈ Complexity.FP := by
  have hpair : (fun absBits : List Bool => pair absBits [true]) ∈
      Complexity.FP :=
    machinePair_mem_FP id_mem_FP (machineConst_mem_FP [true])
  simpa only [machineIntegerNegativePayloadBits] using
    machineCompose_mem_FP hpair machineBinarySubBits_mem_FP

theorem machineIntegerCodeFromSignedAbs_mem_FP :
    machineIntegerCodeFromSignedAbs ∈ Complexity.FP := by
  have hnegativePayload := machineCompose_mem_FP machinePairSecond_mem_FP
    machineIntegerNegativePayloadBits_mem_FP
  have hnegative := machineCompose_mem_FP hnegativePayload
    (machinePrepend_mem_FP true)
  have hpositive := machineCompose_mem_FP machinePairSecond_mem_FP
    (machinePrepend_mem_FP false)
  simpa only [machineIntegerCodeFromSignedAbs] using
    machineIfHead_mem_FP machinePairFirst_mem_FP hnegative hpositive

theorem machineIntegerNatAbsBits_encode (z : ℤ) :
    machineIntegerNatAbsBits (integerBinaryCode z) = z.natAbs.bits := by
  cases z with
  | ofNat n => simp [machineIntegerNatAbsBits, integerBinaryCode]
  | negSucc n =>
      simp only [machineIntegerNatAbsBits, integerBinaryCode,
        machineIfHead_true, machineIntegerNegativeAbsBits, List.tail_cons]
      simpa using machineBinaryAddBits_pair_natBits n 1

theorem machineIntegerCodeFromSignedAbs_ofNat (n magnitude : ℕ) :
    machineIntegerCodeFromSignedAbs
        (pair (integerBinaryCode (Int.ofNat n)) magnitude.bits) =
      integerBinaryCode (Int.ofNat magnitude) := by
  simp [machineIntegerCodeFromSignedAbs, integerBinaryCode]

theorem machineIntegerCodeFromSignedAbs_negSucc (n magnitude : ℕ)
    (hmagnitude : 0 < magnitude) :
    machineIntegerCodeFromSignedAbs
        (pair (integerBinaryCode (Int.negSucc n)) magnitude.bits) =
      integerBinaryCode (-(magnitude : ℤ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmagnitude.ne'
  simp only [machineIntegerCodeFromSignedAbs, machinePairFirst_pair,
    machinePairSecond_pair, integerBinaryCode, machineIfHead_true,
    machineIntegerNegativePayloadBits]
  rw [show ([true] : List Bool) = (1 : ℕ).bits by rfl]
  rw [machineBinarySubBits_pair_natBits]
  have hneg : -((k + 1 : ℕ) : ℤ) = Int.negSucc k := by omega
  rw [hneg]
  rfl

/-- Restoring the sign after exact division agrees with the semantic signed
division routine used by `binaryNormalizeRawRat`. -/
theorem machineIntegerCodeFromSignedAbs_div (z : ℤ) (d : ℕ)
    (hd : 0 < d) (hdvd : d ∣ z.natAbs) :
    machineIntegerCodeFromSignedAbs
        (pair (integerBinaryCode z) (z.natAbs / d).bits) =
      integerBinaryCode (binaryIntDivNat z d) := by
  cases z with
  | ofNat n =>
      rw [machineIntegerCodeFromSignedAbs_ofNat]
      by_cases hn : n = 0
      · subst n
        simp [binaryIntDivNat, binaryLongDiv_eq_div_mod]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp [binaryIntDivNat, binaryLongDiv_eq_div_mod]
  | negSucc n =>
      have hle : d ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
      have hquotPos : 0 < (n + 1) / d := Nat.div_pos hle hd
      change machineIntegerCodeFromSignedAbs
          (pair (integerBinaryCode (Int.negSucc n)) ((n + 1) / d).bits) = _
      rw [machineIntegerCodeFromSignedAbs_negSucc n ((n + 1) / d) hquotPos]
      simp [binaryIntDivNat, binaryLongDiv_eq_div_mod]

end BeyondBethe

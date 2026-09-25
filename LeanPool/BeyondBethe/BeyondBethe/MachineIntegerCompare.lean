/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerArithmetic

/-!
# Polynomial-time signed-integer comparison

Canonical integer codes carry one sign bit followed by the `Int.negSucc`
payload.  We first convert both operands to true absolute values.  Equal-sign
comparisons then reduce to natural comparison; for two negative operands the
order of the magnitudes is reversed.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineIntegerLeftSign (word : List Bool) : List Bool :=
  machineHeadBit (machinePairFirst word)

def machineIntegerRightSign (word : List Bool) : List Bool :=
  machineHeadBit (machinePairSecond word)

def machineIntegerLeftAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits (machinePairFirst word)

def machineIntegerRightAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits (machinePairSecond word)

def machineIntegerPositiveLeBit (word : List Bool) : List Bool :=
  machineBinaryNatLeBit
    (pair (machineIntegerLeftAbsBits word) (machineIntegerRightAbsBits word))

def machineIntegerNegativeLeBit (word : List Bool) : List Bool :=
  machineBinaryNatLeBit
    (pair (machineIntegerRightAbsBits word) (machineIntegerLeftAbsBits word))

/-- One-bit test for `z ≤ w` on a pair of canonical integer encodings. -/
def machineIntegerLeCode (word : List Bool) : List Bool :=
  machineIfHead (machineIntegerLeftSign word)
    (machineIfHead (machineIntegerRightSign word)
      (machineIntegerNegativeLeBit word) [true])
    (machineIfHead (machineIntegerRightSign word)
      [false] (machineIntegerPositiveLeBit word))

theorem machineIntegerLeftSign_mem_FP :
    machineIntegerLeftSign ∈ Complexity.FP := by
  simpa only [machineIntegerLeftSign] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machineHeadBit_mem_FP

theorem machineIntegerRightSign_mem_FP :
    machineIntegerRightSign ∈ Complexity.FP := by
  simpa only [machineIntegerRightSign] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machineHeadBit_mem_FP

theorem machineIntegerLeftAbsBits_mem_FP :
    machineIntegerLeftAbsBits ∈ Complexity.FP := by
  simpa only [machineIntegerLeftAbsBits] using!
    machineCompose_mem_FP machinePairFirst_mem_FP
      machineIntegerNatAbsBits_mem_FP

theorem machineIntegerRightAbsBits_mem_FP :
    machineIntegerRightAbsBits ∈ Complexity.FP := by
  simpa only [machineIntegerRightAbsBits] using!
    machineCompose_mem_FP machinePairSecond_mem_FP
      machineIntegerNatAbsBits_mem_FP

theorem machineIntegerPositiveLeBit_mem_FP :
    machineIntegerPositiveLeBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineIntegerLeftAbsBits_mem_FP
    machineIntegerRightAbsBits_mem_FP
  simpa only [machineIntegerPositiveLeBit] using!
    machineCompose_mem_FP hpair machineBinaryNatLeBit_mem_FP

theorem machineIntegerNegativeLeBit_mem_FP :
    machineIntegerNegativeLeBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineIntegerRightAbsBits_mem_FP
    machineIntegerLeftAbsBits_mem_FP
  simpa only [machineIntegerNegativeLeBit] using!
    machineCompose_mem_FP hpair machineBinaryNatLeBit_mem_FP

theorem machineIntegerLeCode_mem_FP : machineIntegerLeCode ∈ Complexity.FP := by
  have hnegativeLeft := machineIfHead_mem_FP machineIntegerRightSign_mem_FP
    machineIntegerNegativeLeBit_mem_FP (machineConst_mem_FP [true])
  have hpositiveLeft := machineIfHead_mem_FP machineIntegerRightSign_mem_FP
    (machineConst_mem_FP [false]) machineIntegerPositiveLeBit_mem_FP
  exact machineIfHead_mem_FP machineIntegerLeftSign_mem_FP
    hnegativeLeft hpositiveLeft

theorem machineIntegerLeCode_encode (z w : ℤ) :
    machineIntegerLeCode
        (pair (integerBinaryCode z) (integerBinaryCode w)) =
      [decide (z ≤ w)] := by
  cases z <;> cases w <;>
    simp only [machineIntegerLeCode, machineIntegerLeftSign,
      machineIntegerRightSign, machineIntegerPositiveLeBit,
      machineIntegerNegativeLeBit, machineIntegerLeftAbsBits,
      machineIntegerRightAbsBits, machinePairFirst_pair,
      machinePairSecond_pair, machineIntegerNatAbsBits_encode] <;>
    simp [integerBinaryCode, machineBinaryNatLeBit_pair_natBits] <;>
    omega

end BeyondBethe

/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalization

/-!
# Polynomial-time signed integer arithmetic

The arithmetic core uses a pair `(sign, absolute value)`, with a one-bit sign.
Conversion back to `integerBinaryCode` forces the sign to be nonnegative when
the magnitude is zero, avoiding the `Int.negSucc` negative-zero pitfall.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def signedMagnitudeValue (negative : Bool) (magnitude : ℕ) : ℤ :=
  if negative then -(magnitude : ℤ) else magnitude

def machineCanonicalIntegerFromSignedAbs (word : List Bool) : List Bool :=
  machineIfEmpty (machinePairSecond word) [false]
    (machineIntegerCodeFromSignedAbs word)

def machineIntegerSignedMagnitude (word : List Bool) : List Bool :=
  pair (machineHeadBit word) (machineIntegerNatAbsBits word)

def machineSignedLeftSign (word : List Bool) : List Bool :=
  machinePairFirst (machinePairFirst word)

def machineSignedLeftAbs (word : List Bool) : List Bool :=
  machinePairSecond (machinePairFirst word)

def machineSignedRightSign (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond word)

def machineSignedRightAbs (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond word)

def machineSignedSameSign (word : List Bool) : List Bool :=
  machineNotBit
    (machineXorBit (machineSignedLeftSign word) (machineSignedRightSign word))

def machineSignedAbsSum (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineSignedLeftAbs word) (machineSignedRightAbs word))

def machineSignedLeftAbsGe (word : List Bool) : List Bool :=
  machineBinaryNatLeBit
    (pair (machineSignedRightAbs word) (machineSignedLeftAbs word))

def machineSignedAbsLeftDiff (word : List Bool) : List Bool :=
  machineBinarySubBits
    (pair (machineSignedLeftAbs word) (machineSignedRightAbs word))

def machineSignedAbsRightDiff (word : List Bool) : List Bool :=
  machineBinarySubBits
    (pair (machineSignedRightAbs word) (machineSignedLeftAbs word))

def machineSignedDifferentAbs (word : List Bool) : List Bool :=
  machineIfHead (machineSignedLeftAbsGe word)
    (machineSignedAbsLeftDiff word) (machineSignedAbsRightDiff word)

def machineSignedDifferentSign (word : List Bool) : List Bool :=
  machineIfHead (machineSignedLeftAbsGe word)
    (machineSignedLeftSign word) (machineSignedRightSign word)

/-- Addition on two signed-magnitude pairs. -/
def machineSignedMagnitudeAdd (word : List Bool) : List Bool :=
  let sign := machineIfHead (machineSignedSameSign word)
    (machineSignedLeftSign word) (machineSignedDifferentSign word)
  let magnitude := machineIfHead (machineSignedSameSign word)
    (machineSignedAbsSum word) (machineSignedDifferentAbs word)
  machineCanonicalIntegerFromSignedAbs (pair sign magnitude)

/-- Addition on a pair of canonical `integerBinaryCode`s. -/
def machineIntegerAddCode (word : List Bool) : List Bool :=
  machineSignedMagnitudeAdd
    (pair (machineIntegerSignedMagnitude (machinePairFirst word))
      (machineIntegerSignedMagnitude (machinePairSecond word)))

def machineSignedAbsProduct (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineSignedLeftAbs word) (machineSignedRightAbs word))

def machineSignedProductSign (word : List Bool) : List Bool :=
  machineXorBit (machineSignedLeftSign word) (machineSignedRightSign word)

def machineSignedMagnitudeMul (word : List Bool) : List Bool :=
  machineCanonicalIntegerFromSignedAbs
    (pair (machineSignedProductSign word) (machineSignedAbsProduct word))

/-- Multiplication on a pair of canonical `integerBinaryCode`s. -/
def machineIntegerMulCode (word : List Bool) : List Bool :=
  machineSignedMagnitudeMul
    (pair (machineIntegerSignedMagnitude (machinePairFirst word))
      (machineIntegerSignedMagnitude (machinePairSecond word)))

/-- Negation of one canonical `integerBinaryCode`. -/
def machineIntegerNegCode (word : List Bool) : List Bool :=
  let signed := machineIntegerSignedMagnitude word
  machineCanonicalIntegerFromSignedAbs
    (pair (machineNotBit (machinePairFirst signed))
      (machinePairSecond signed))

theorem machineCanonicalIntegerFromSignedAbs_mem_FP :
    machineCanonicalIntegerFromSignedAbs ∈ Complexity.FP := by
  simpa only [machineCanonicalIntegerFromSignedAbs] using!
    machineIfEmpty_mem_FP machinePairSecond_mem_FP
      (machineConst_mem_FP [false]) machineIntegerCodeFromSignedAbs_mem_FP

theorem machineIntegerSignedMagnitude_mem_FP :
    machineIntegerSignedMagnitude ∈ Complexity.FP := by
  simpa only [machineIntegerSignedMagnitude] using!
    machinePair_mem_FP machineHeadBit_mem_FP machineIntegerNatAbsBits_mem_FP

theorem machineSignedLeftSign_mem_FP : machineSignedLeftSign ∈ Complexity.FP := by
  simpa only [machineSignedLeftSign] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machinePairFirst_mem_FP

theorem machineSignedLeftAbs_mem_FP : machineSignedLeftAbs ∈ Complexity.FP := by
  simpa only [machineSignedLeftAbs] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machinePairSecond_mem_FP

theorem machineSignedRightSign_mem_FP : machineSignedRightSign ∈ Complexity.FP := by
  simpa only [machineSignedRightSign] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineSignedRightAbs_mem_FP : machineSignedRightAbs ∈ Complexity.FP := by
  simpa only [machineSignedRightAbs] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineSignedSameSign_mem_FP : machineSignedSameSign ∈ Complexity.FP := by
  exact machineNotBit_mem_FP
    (machineXorBit_mem_FP machineSignedLeftSign_mem_FP
      machineSignedRightSign_mem_FP)

theorem machineSignedAbsSum_mem_FP : machineSignedAbsSum ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSignedLeftAbs_mem_FP
    machineSignedRightAbs_mem_FP
  simpa only [machineSignedAbsSum] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineSignedLeftAbsGe_mem_FP : machineSignedLeftAbsGe ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSignedRightAbs_mem_FP
    machineSignedLeftAbs_mem_FP
  simpa only [machineSignedLeftAbsGe] using!
    machineCompose_mem_FP hpair machineBinaryNatLeBit_mem_FP

theorem machineSignedAbsLeftDiff_mem_FP :
    machineSignedAbsLeftDiff ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSignedLeftAbs_mem_FP
    machineSignedRightAbs_mem_FP
  simpa only [machineSignedAbsLeftDiff] using!
    machineCompose_mem_FP hpair machineBinarySubBits_mem_FP

theorem machineSignedAbsRightDiff_mem_FP :
    machineSignedAbsRightDiff ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSignedRightAbs_mem_FP
    machineSignedLeftAbs_mem_FP
  simpa only [machineSignedAbsRightDiff] using!
    machineCompose_mem_FP hpair machineBinarySubBits_mem_FP

theorem machineSignedDifferentAbs_mem_FP :
    machineSignedDifferentAbs ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineSignedLeftAbsGe_mem_FP
    machineSignedAbsLeftDiff_mem_FP machineSignedAbsRightDiff_mem_FP

theorem machineSignedDifferentSign_mem_FP :
    machineSignedDifferentSign ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineSignedLeftAbsGe_mem_FP
    machineSignedLeftSign_mem_FP machineSignedRightSign_mem_FP

theorem machineSignedMagnitudeAdd_mem_FP :
    machineSignedMagnitudeAdd ∈ Complexity.FP := by
  have hsign := machineIfHead_mem_FP machineSignedSameSign_mem_FP
    machineSignedLeftSign_mem_FP machineSignedDifferentSign_mem_FP
  have hmagnitude := machineIfHead_mem_FP machineSignedSameSign_mem_FP
    machineSignedAbsSum_mem_FP machineSignedDifferentAbs_mem_FP
  have hpair := machinePair_mem_FP hsign hmagnitude
  simpa only [machineSignedMagnitudeAdd] using!
    machineCompose_mem_FP hpair machineCanonicalIntegerFromSignedAbs_mem_FP

theorem machineIntegerAddCode_mem_FP : machineIntegerAddCode ∈ Complexity.FP := by
  have hleft := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerSignedMagnitude_mem_FP
  have hright := machineCompose_mem_FP machinePairSecond_mem_FP
    machineIntegerSignedMagnitude_mem_FP
  have hpair := machinePair_mem_FP hleft hright
  simpa only [machineIntegerAddCode] using!
    machineCompose_mem_FP hpair machineSignedMagnitudeAdd_mem_FP

theorem machineSignedAbsProduct_mem_FP :
    machineSignedAbsProduct ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSignedLeftAbs_mem_FP
    machineSignedRightAbs_mem_FP
  simpa only [machineSignedAbsProduct] using!
    machineCompose_mem_FP hpair machineBinaryMulBits_mem_FP

theorem machineSignedProductSign_mem_FP :
    machineSignedProductSign ∈ Complexity.FP := by
  exact machineXorBit_mem_FP machineSignedLeftSign_mem_FP
    machineSignedRightSign_mem_FP

theorem machineSignedMagnitudeMul_mem_FP :
    machineSignedMagnitudeMul ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSignedProductSign_mem_FP
    machineSignedAbsProduct_mem_FP
  simpa only [machineSignedMagnitudeMul] using!
    machineCompose_mem_FP hpair machineCanonicalIntegerFromSignedAbs_mem_FP

theorem machineIntegerMulCode_mem_FP : machineIntegerMulCode ∈ Complexity.FP := by
  have hleft := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerSignedMagnitude_mem_FP
  have hright := machineCompose_mem_FP machinePairSecond_mem_FP
    machineIntegerSignedMagnitude_mem_FP
  have hpair := machinePair_mem_FP hleft hright
  simpa only [machineIntegerMulCode] using!
    machineCompose_mem_FP hpair machineSignedMagnitudeMul_mem_FP

theorem machineIntegerNegCode_mem_FP : machineIntegerNegCode ∈ Complexity.FP := by
  have hsigned := machineIntegerSignedMagnitude_mem_FP
  have hsignProjection := machineCompose_mem_FP hsigned machinePairFirst_mem_FP
  have hsign := machineNotBit_mem_FP hsignProjection
  have habs := machineCompose_mem_FP hsigned machinePairSecond_mem_FP
  have hpair := machinePair_mem_FP hsign habs
  simpa only [machineIntegerNegCode] using!
    machineCompose_mem_FP hpair machineCanonicalIntegerFromSignedAbs_mem_FP

@[simp] theorem machineCanonicalIntegerFromSignedAbs_pair
    (negative : Bool) (magnitude : ℕ) :
    machineCanonicalIntegerFromSignedAbs (pair [negative] magnitude.bits) =
      integerBinaryCode (signedMagnitudeValue negative magnitude) := by
  cases negative with
  | false =>
      cases magnitude with
      | zero =>
          rfl
      | succ k =>
          rw [machineCanonicalIntegerFromSignedAbs]
          simp only [machinePairSecond_pair]
          rw [machineIfEmpty_of_ne_nil (k + 1).bits [false]
            (machineIntegerCodeFromSignedAbs (pair [false] (k + 1).bits))
            (natBits_ne_nil_of_ne_zero (by omega))]
          simp only [machineIntegerCodeFromSignedAbs, machinePairFirst_pair,
            machinePairSecond_pair, machineIfHead_false,
            signedMagnitudeValue]
          change false :: (k + 1).bits =
            integerBinaryCode (Int.ofNat (k + 1))
          rfl
  | true =>
      cases magnitude with
      | zero =>
          rfl
      | succ k =>
          rw [machineCanonicalIntegerFromSignedAbs]
          simp only [machinePairSecond_pair]
          rw [machineIfEmpty_of_ne_nil (k + 1).bits [false]
            (machineIntegerCodeFromSignedAbs (pair [true] (k + 1).bits))
            (natBits_ne_nil_of_ne_zero (by omega))]
          simp only [signedMagnitudeValue, if_true]
          simpa only [show ([true] : List Bool) =
              integerBinaryCode (Int.negSucc 0) by rfl] using
            machineIntegerCodeFromSignedAbs_negSucc 0 (k + 1) (by omega)

theorem machineIntegerSignedMagnitude_encode (z : ℤ) :
    machineIntegerSignedMagnitude (integerBinaryCode z) =
      match z with
      | .ofNat n => pair [false] n.bits
      | .negSucc n => pair [true] (n + 1).bits := by
  rw [machineIntegerSignedMagnitude]
  cases z with
  | ofNat n =>
      rw [machineIntegerNatAbsBits_encode]
      simp [integerBinaryCode]
  | negSucc n =>
      rw [machineIntegerNatAbsBits_encode]
      simp [integerBinaryCode]

theorem machineSignedMagnitudeAdd_pair
    (leftNegative rightNegative : Bool) (leftAbs rightAbs : ℕ) :
    machineSignedMagnitudeAdd
        (pair (pair [leftNegative] leftAbs.bits)
          (pair [rightNegative] rightAbs.bits)) =
      integerBinaryCode
        (signedMagnitudeValue leftNegative leftAbs +
          signedMagnitudeValue rightNegative rightAbs) := by
  cases leftNegative <;> cases rightNegative
  · simp [machineSignedMagnitudeAdd, machineSignedSameSign,
      machineSignedLeftSign, machineSignedRightSign,
      machineSignedLeftAbs, machineSignedRightAbs,
      machineSignedAbsSum, machineBinaryAddBits_pair_natBits,
      signedMagnitudeValue]
  · by_cases h : rightAbs ≤ leftAbs
    · simp [machineSignedMagnitudeAdd, machineSignedSameSign,
        machineSignedLeftSign, machineSignedRightSign,
        machineSignedLeftAbs, machineSignedRightAbs,
        machineSignedLeftAbsGe, machineSignedAbsLeftDiff,
        machineSignedAbsRightDiff, machineSignedDifferentAbs,
        machineSignedDifferentSign, machineBinaryNatLeBit_pair_natBits,
      machineBinarySubBits_pair_natBits, signedMagnitudeValue, h]
      congr 1
    · have hlt : leftAbs < rightAbs := Nat.lt_of_not_ge h
      simp [machineSignedMagnitudeAdd, machineSignedSameSign,
        machineSignedLeftSign, machineSignedRightSign,
        machineSignedLeftAbs, machineSignedRightAbs,
        machineSignedLeftAbsGe, machineSignedAbsLeftDiff,
        machineSignedAbsRightDiff, machineSignedDifferentAbs,
        machineSignedDifferentSign, machineBinaryNatLeBit_pair_natBits,
        machineBinarySubBits_pair_natBits, signedMagnitudeValue, h]
      congr 1
      omega
  · by_cases h : rightAbs ≤ leftAbs
    · simp [machineSignedMagnitudeAdd, machineSignedSameSign,
        machineSignedLeftSign, machineSignedRightSign,
        machineSignedLeftAbs, machineSignedRightAbs,
        machineSignedLeftAbsGe, machineSignedAbsLeftDiff,
        machineSignedAbsRightDiff, machineSignedDifferentAbs,
        machineSignedDifferentSign, machineBinaryNatLeBit_pair_natBits,
        machineBinarySubBits_pair_natBits, signedMagnitudeValue, h]
      congr 1
      omega
    · have hlt : leftAbs < rightAbs := Nat.lt_of_not_ge h
      simp [machineSignedMagnitudeAdd, machineSignedSameSign,
        machineSignedLeftSign, machineSignedRightSign,
        machineSignedLeftAbs, machineSignedRightAbs,
        machineSignedLeftAbsGe, machineSignedAbsLeftDiff,
        machineSignedAbsRightDiff, machineSignedDifferentAbs,
        machineSignedDifferentSign, machineBinaryNatLeBit_pair_natBits,
        machineBinarySubBits_pair_natBits, signedMagnitudeValue, h]
      congr 1
      omega
  · simp [machineSignedMagnitudeAdd, machineSignedSameSign,
      machineSignedLeftSign, machineSignedRightSign,
      machineSignedLeftAbs, machineSignedRightAbs,
      machineSignedAbsSum, machineBinaryAddBits_pair_natBits,
      signedMagnitudeValue]
    congr 1
    omega

theorem machineIntegerAddCode_encode (z w : ℤ) :
    machineIntegerAddCode (pair (integerBinaryCode z) (integerBinaryCode w)) =
      integerBinaryCode (z + w) := by
  cases z with
  | ofNat n =>
      cases w with
      | ofNat m =>
          simp [machineIntegerAddCode, machineIntegerSignedMagnitude_encode,
            machineSignedMagnitudeAdd_pair, signedMagnitudeValue]
      | negSucc m =>
          rw [machineIntegerAddCode]
          simp only [machinePairFirst_pair, machinePairSecond_pair,
          machineIntegerSignedMagnitude_encode,
          machineSignedMagnitudeAdd_pair, signedMagnitudeValue]
          congr 1
  | negSucc n =>
      cases w with
      | ofNat m =>
          rw [machineIntegerAddCode]
          simp only [machinePairFirst_pair, machinePairSecond_pair,
          machineIntegerSignedMagnitude_encode,
          machineSignedMagnitudeAdd_pair, signedMagnitudeValue]
          congr 1
      | negSucc m =>
          rw [machineIntegerAddCode]
          simp only [machinePairFirst_pair, machinePairSecond_pair,
          machineIntegerSignedMagnitude_encode,
          machineSignedMagnitudeAdd_pair, signedMagnitudeValue]
          congr 1

theorem machineSignedMagnitudeMul_pair
    (leftNegative rightNegative : Bool) (leftAbs rightAbs : ℕ) :
    machineSignedMagnitudeMul
        (pair (pair [leftNegative] leftAbs.bits)
          (pair [rightNegative] rightAbs.bits)) =
      integerBinaryCode
        (signedMagnitudeValue leftNegative leftAbs *
          signedMagnitudeValue rightNegative rightAbs) := by
  cases leftNegative <;> cases rightNegative <;>
    simp [machineSignedMagnitudeMul, machineSignedProductSign,
      machineSignedLeftSign, machineSignedRightSign,
      machineSignedLeftAbs, machineSignedRightAbs,
      machineSignedAbsProduct, machineBinaryMulBits_pair_natBits,
      signedMagnitudeValue] <;>
    congr 1 <;> ring

theorem machineIntegerMulCode_encode (z w : ℤ) :
    machineIntegerMulCode (pair (integerBinaryCode z) (integerBinaryCode w)) =
      integerBinaryCode (z * w) := by
  cases z <;> cases w <;>
    rw [machineIntegerMulCode] <;>
    simp only [machinePairFirst_pair, machinePairSecond_pair,
      machineIntegerSignedMagnitude_encode,
      machineSignedMagnitudeMul_pair, signedMagnitudeValue] <;>
    congr 1 <;> ring

theorem machineIntegerNegCode_encode (z : ℤ) :
    machineIntegerNegCode (integerBinaryCode z) = integerBinaryCode (-z) := by
  cases z with
  | ofNat n =>
      simp [machineIntegerNegCode, machineIntegerSignedMagnitude_encode,
        signedMagnitudeValue]
  | negSucc n =>
      rw [Int.neg_negSucc]
      rw [machineIntegerNegCode, machineIntegerSignedMagnitude_encode]
      simp only [machinePairFirst_pair, machinePairSecond_pair,
        machineNotBit_one, Bool.not_true]
      simpa only [signedMagnitudeValue, ite_false] using!
        machineCanonicalIntegerFromSignedAbs_pair false (n + 1)

end BeyondBethe

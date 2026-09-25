/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalUnary

/-!
# A bounded polynomial-time rational power loop

The exponent is a unary ruler.  Each state also retains a quadratic-width
clamp computed from the original input.  The clamp makes the total machine
polynomial-time even on malformed strings; a separate bit-growth proof shows
that it never truncates a well-formed unreduced power.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def rawRatOneCode : List Bool := rawRatBinaryCode RawRat.one

def machineRawRatPowerPack (acc base bound : List Bool) : List Bool :=
  pair acc (pair base bound)

def machineRawRatPowerAccField (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRawRatPowerBaseField (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRawRatPowerBoundField (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineRawRatPowerCandidate (state : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineRawRatPowerAccField state)
      (machineRawRatPowerBaseField state))

def machineRawRatPowerNextAcc (state : List Bool) : List Bool :=
  (machineRawRatPowerCandidate state).take
    (machineRawRatPowerBoundField state).length

def machineRawRatPowerStep (state : List Bool) : List Bool :=
  machineRawRatPowerPack (machineRawRatPowerNextAcc state)
    (machineRawRatPowerBaseField state)
    (machineRawRatPowerBoundField state)

def machineRawRatPowerInputRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRawRatPowerInputBase (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRawRatPowerInputBound (word : List Bool) : List Bool :=
  let square := machineBinaryMulWidth word
  square ++ (square ++ (square ++ square))

def machineRawRatPowerInit (word : List Bool) : List Bool :=
  machineRawRatPowerPack rawRatOneCode
    (machineRawRatPowerInputBase word)
    (machineRawRatPowerInputBound word)

def machineRawRatPowerWidth (word : List Bool) : List Bool :=
  let bound := machineRawRatPowerInputBound word
  machineRawRatPowerPack bound bound bound

def machineRawRatPowerFinalState (word : List Bool) : List Bool :=
  (machineRawRatPowerStep)^[(machineRawRatPowerInputRuler word).length]
    (machineRawRatPowerInit word)

def machineRawRatPowerCode (word : List Bool) : List Bool :=
  machineRawRatPowerAccField (machineRawRatPowerFinalState word)

def machineRationalPowerCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatPowerCode word)

theorem machineRawRatPowerAccField_mem_FP :
    machineRawRatPowerAccField ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineRawRatPowerBaseField_mem_FP :
    machineRawRatPowerBaseField ∈ Complexity.FP := by
  simpa only [machineRawRatPowerBaseField] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRawRatPowerBoundField_mem_FP :
    machineRawRatPowerBoundField ∈ Complexity.FP := by
  simpa only [machineRawRatPowerBoundField] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineRawRatPowerCandidate_mem_FP :
    machineRawRatPowerCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineRawRatPowerAccField_mem_FP
    machineRawRatPowerBaseField_mem_FP
  simpa only [machineRawRatPowerCandidate] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineRawRatPowerNextAcc_mem_FP :
    machineRawRatPowerNextAcc ∈ Complexity.FP := by
  simpa only [machineRawRatPowerNextAcc] using!
    machineTake_mem_FP machineRawRatPowerBoundField_mem_FP
      machineRawRatPowerCandidate_mem_FP

theorem machineRawRatPowerStep_mem_FP :
    machineRawRatPowerStep ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRawRatPowerNextAcc_mem_FP
    (machinePair_mem_FP machineRawRatPowerBaseField_mem_FP
      machineRawRatPowerBoundField_mem_FP)

theorem machineRawRatPowerInputRuler_mem_FP :
    machineRawRatPowerInputRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineRawRatPowerInputBase_mem_FP :
    machineRawRatPowerInputBase ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineRawRatPowerInputBound_mem_FP :
    machineRawRatPowerInputBound ∈ Complexity.FP :=
  by
    have hdouble := machineAppend_mem_FP machineBinaryMulWidth_mem_FP
      machineBinaryMulWidth_mem_FP
    have htriple := machineAppend_mem_FP machineBinaryMulWidth_mem_FP hdouble
    have hquadruple := machineAppend_mem_FP machineBinaryMulWidth_mem_FP htriple
    simpa only [machineRawRatPowerInputBound] using!
      hquadruple

theorem machineRawRatPowerInit_mem_FP :
    machineRawRatPowerInit ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP rawRatOneCode)
    (machinePair_mem_FP machineRawRatPowerInputBase_mem_FP
      machineRawRatPowerInputBound_mem_FP)

theorem machineRawRatPowerWidth_mem_FP :
    machineRawRatPowerWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRawRatPowerInputBound_mem_FP
    (machinePair_mem_FP machineRawRatPowerInputBound_mem_FP
      machineRawRatPowerInputBound_mem_FP)

@[simp] theorem machineRawRatPowerAccField_pack (acc base bound) :
    machineRawRatPowerAccField (machineRawRatPowerPack acc base bound) = acc := by
  simp [machineRawRatPowerAccField, machineRawRatPowerPack]

@[simp] theorem machineRawRatPowerBaseField_pack (acc base bound) :
    machineRawRatPowerBaseField (machineRawRatPowerPack acc base bound) = base := by
  simp [machineRawRatPowerBaseField, machineRawRatPowerPack]

@[simp] theorem machineRawRatPowerBoundField_pack (acc base bound) :
    machineRawRatPowerBoundField (machineRawRatPowerPack acc base bound) = bound := by
  simp [machineRawRatPowerBoundField, machineRawRatPowerPack]

/-- Total clamped accumulator used to prove the machine's arbitrary-input
length bound. -/
def clampedRawRatPowerAcc (word : List Bool) : ℕ → List Bool
  | 0 => rawRatOneCode
  | k + 1 =>
      (machineRawRatMulCode
        (pair (clampedRawRatPowerAcc word k)
          (machineRawRatPowerInputBase word))).take
        (machineRawRatPowerInputBound word).length

theorem machineRawRatPowerStep_semantics (word : List Bool) (k : ℕ) :
    machineRawRatPowerStep
        (machineRawRatPowerPack (clampedRawRatPowerAcc word k)
          (machineRawRatPowerInputBase word)
          (machineRawRatPowerInputBound word)) =
      machineRawRatPowerPack (clampedRawRatPowerAcc word (k + 1))
        (machineRawRatPowerInputBase word)
        (machineRawRatPowerInputBound word) := by
  simp [machineRawRatPowerStep, machineRawRatPowerNextAcc,
    machineRawRatPowerCandidate, clampedRawRatPowerAcc]

theorem machineRawRatPowerIterate_semantics (word : List Bool) : ∀ k,
    (machineRawRatPowerStep)^[k] (machineRawRatPowerInit word) =
      machineRawRatPowerPack (clampedRawRatPowerAcc word k)
        (machineRawRatPowerInputBase word)
        (machineRawRatPowerInputBound word) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        machineRawRatPowerStep_semantics]

theorem machineRawRatPowerInputBase_length_le_bound (word : List Bool) :
    (machineRawRatPowerInputBase word).length ≤
      (machineRawRatPowerInputBound word).length := by
  have hbase := machinePairSecond_length_le word
  simp only [machineRawRatPowerInputBase, machineRawRatPowerInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  nlinarith

theorem clampedRawRatPowerAcc_length_le_bound (word : List Bool) : ∀ k,
    (clampedRawRatPowerAcc word k).length ≤
      (machineRawRatPowerInputBound word).length := by
  intro k
  cases k with
  | zero =>
      simp [clampedRawRatPowerAcc, rawRatOneCode, rawRatBinaryCode,
        RawRat.one, integerBinaryCode, machineRawRatPowerInputBound,
        machineBinaryMulWidth]
      nlinarith
  | succ k =>
      simp only [clampedRawRatPowerAcc]
      apply List.length_take_le

theorem machineRawRatPowerIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineRawRatPowerInputRuler word).length) :
    ((machineRawRatPowerStep)^[iterations]
      (machineRawRatPowerInit word)).length ≤
        (machineRawRatPowerWidth word).length := by
  rw [machineRawRatPowerIterate_semantics]
  simp only [machineRawRatPowerPack, machineRawRatPowerWidth, pair_length]
  have hacc := clampedRawRatPowerAcc_length_le_bound word iterations
  have hbase := machineRawRatPowerInputBase_length_le_bound word
  omega

theorem machineRawRatPowerFinalState_mem_FP :
    machineRawRatPowerFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineRawRatPowerStep_mem_FP
    machineRawRatPowerInit_mem_FP machineRawRatPowerInputRuler_mem_FP
    machineRawRatPowerWidth_mem_FP
    machineRawRatPowerIterate_length_le_width

theorem machineRawRatPowerCode_mem_FP :
    machineRawRatPowerCode ∈ Complexity.FP := by
  simpa only [machineRawRatPowerCode] using!
    machineCompose_mem_FP machineRawRatPowerFinalState_mem_FP
      machineRawRatPowerAccField_mem_FP

theorem machineRationalPowerCode_mem_FP :
    machineRationalPowerCode ∈ Complexity.FP := by
  simpa only [machineRationalPowerCode] using!
    machineCompose_mem_FP machineRawRatPowerCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

private theorem integerNatAbs_size_le_code_length (z : ℤ) :
    z.natAbs.size ≤ (integerBinaryCode z).length := by
  cases z with
  | ofNat n =>
      simp [integerBinaryCode, Nat.size_eq_bits_len]
  | negSucc n =>
      have hs : (n + 1).size ≤ n.size + 1 := by
        rw [Nat.size_le]
        have hle : n + 1 ≤ 2 ^ n.size :=
          Nat.succ_le_iff.mpr (Nat.lt_size_self n)
        have hlt : 2 ^ n.size < 2 ^ (n.size + 1) := by
          rw [pow_succ]
          have hpos : 0 < 2 ^ n.size := by positivity
          omega
        exact hle.trans_lt hlt
      simpa [integerBinaryCode, Nat.size_eq_bits_len,
        Nat.add_comm] using! hs

private theorem rawRatWidth_le_code_length (q : RawRat) :
    rawRatWidth q ≤ (rawRatBinaryCode q).length := by
  rw [rawRatWidth, rawRatBinaryCode, pair_length]
  apply max_le
  · have h := integerNatAbs_size_le_code_length q.num
    omega
  · rw [Nat.size_eq_bits_len]
    omega

private theorem rawRatBinaryCode_length_le_width (q : RawRat) :
    (rawRatBinaryCode q).length ≤ 4 + 3 * rawRatWidth q := by
  rw [rawRatBinaryCode, pair_length]
  have hnum : (integerBinaryCode q.num).length ≤
      1 + rawRatWidth q := by
    cases hqnum : q.num with
    | ofNat n =>
        simp only [integerBinaryCode, List.length_cons,
          Nat.size_eq_bits_len]
        have habs := rawRat_num_size_le_width q
        simp only [hqnum, Int.natAbs_ofNat'] at habs
        omega
    | negSucc n =>
        simp only [integerBinaryCode, List.length_cons,
          Nat.size_eq_bits_len]
        have hsize : n.size ≤ (n + 1).size :=
          Nat.size_le_size (Nat.le_succ n)
        have habs : (n + 1).size ≤ rawRatWidth q := by
          simpa only [hqnum, Int.natAbs_negSucc] using!
            rawRat_num_size_le_width q
        have hnwidth : n.size ≤ rawRatWidth q := hsize.trans habs
        omega
  have hden := rawRat_den_size_le_width q
  have hdenBits : q.den.bits.length ≤ rawRatWidth q := by
    rw [Nat.size_eq_bits_len]
    exact hden
  omega

private theorem rawRatPowerCode_length_le_inputBound
    (q : RawRat) (total k : ℕ) (hk : k ≤ total) :
    (rawRatBinaryCode (q.pow k)).length ≤
      (machineRawRatPowerInputBound
        (pair (List.replicate total true) (rawRatBinaryCode q))).length := by
  let word := pair (List.replicate total true) (rawRatBinaryCode q)
  have hcode := rawRatBinaryCode_length_le_width (q.pow k)
  have hpow := RawRat.width_pow_le q k
  have hqwidth := rawRatWidth_le_code_length q
  have hraw : (rawRatBinaryCode q).length ≤ word.length := by
    simp only [word, pair_length, List.length_replicate]
    omega
  have htotal : total ≤ word.length := by
    simp only [word, pair_length, List.length_replicate]
    omega
  have hproduct : k * rawRatWidth q ≤ word.length * word.length :=
    Nat.mul_le_mul (hk.trans htotal) (hqwidth.trans hraw)
  calc
    (rawRatBinaryCode (q.pow k)).length
        ≤ 4 + 3 * rawRatWidth (q.pow k) := hcode
    _ ≤ 4 + 3 * (1 + k * rawRatWidth q) := by omega
    _ ≤ 4 * ((16 + word.length) * (16 + word.length)) := by nlinarith
    _ = (machineRawRatPowerInputBound word).length := by
      simp [machineRawRatPowerInputBound, machineBinaryMulWidth]
      ring

theorem clampedRawRatPowerAcc_encode (q : RawRat) (total : ℕ) :
    ∀ k ≤ total,
      clampedRawRatPowerAcc
          (pair (List.replicate total true) (rawRatBinaryCode q)) k =
        rawRatBinaryCode (q.pow k) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [clampedRawRatPowerAcc, ih (by omega)]
      simp only [machineRawRatPowerInputBase, machinePairSecond_pair,
        machineRawRatMulCode_encode]
      exact (List.take_eq_self_iff _).2
        (rawRatPowerCode_length_le_inputBound q total (k + 1) hk)

theorem machineRawRatPowerCode_encode (q : RawRat) (k : ℕ) :
    machineRawRatPowerCode
        (pair (List.replicate k true) (rawRatBinaryCode q)) =
      rawRatBinaryCode (q.pow k) := by
  simp only [machineRawRatPowerCode, machineRawRatPowerFinalState,
    machineRawRatPowerInputRuler, machinePairFirst_pair,
    List.length_replicate, machineRawRatPowerIterate_semantics,
    machineRawRatPowerAccField_pack]
  exact clampedRawRatPowerAcc_encode q k k le_rfl

theorem machineRationalPowerCode_encode (q : RawRat) (k : ℕ) :
    machineRationalPowerCode
        (pair (List.replicate k true) (rawRatBinaryCode q)) =
      rationalBinaryCode (binaryNormalizeRawRat (q.pow k)) := by
  rw [machineRationalPowerCode, machineRawRatPowerCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

end BeyondBethe

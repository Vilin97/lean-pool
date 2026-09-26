/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.BinaryRationalFloor
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalArithmetic

/-!
# Polynomial-time dyadic floor

The precision is represented by a unary ruler: its value is the ruler's
length.  This is essential for an honest `FP` statement, since a dyadic output
with denominator `2^p` has `p + 1` denominator bits.  The machine shifts the
absolute numerator by the ruler length, performs verified long division, and
implements Euclidean flooring explicitly for negative inputs.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary precision ruler from a dyadic-rounding request. -/
def machineDyadicPrecisionRuler (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the raw rational code from a dyadic-rounding request. -/
def machineDyadicRawCode (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extracts the signed numerator code from the raw rational payload of a dyadic-rounding
request. -/
def machineDyadicNumeratorCode (word : List Bool) : List Bool :=
  machinePairFirst (machineDyadicRawCode word)

/-- Extracts the denominator bits from the raw rational payload of a dyadic-rounding request. -/
def machineDyadicDenominatorBits (word : List Bool) : List Bool :=
  machinePairSecond (machineDyadicRawCode word)

/-- Reads the sign bit of the encoded numerator in a dyadic-rounding request. -/
def machineDyadicNumeratorSign (word : List Bool) : List Bool :=
  machineHeadBit (machineDyadicNumeratorCode word)

/-- Computes the binary absolute value of the numerator in a dyadic-rounding request. -/
def machineDyadicNumeratorAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits (machineDyadicNumeratorCode word)

/-- Builds a zero-bit word whose length equals the requested unary precision. -/
def machineDyadicPrecisionZeroBits (word : List Bool) : List Bool :=
  List.replicate (machineDyadicPrecisionRuler word).length false

/-- Scales the numerator magnitude by the requested power of two using leading low-order zero
bits, preserving the empty zero encoding. -/
def machineDyadicScaledAbsBits (word : List Bool) : List Bool :=
  machineIfEmpty (machineDyadicNumeratorAbsBits word) []
    (machineDyadicPrecisionZeroBits word ++
      machineDyadicNumeratorAbsBits word)

/-- Divides the scaled numerator magnitude by the denominator and returns the encoded
quotient-remainder pair. -/
def machineDyadicDivModBits (word : List Bool) : List Bool :=
  machineBinaryDivModBits
    (pair (machineDyadicScaledAbsBits word)
      (machineDyadicDenominatorBits word))

/-- Extracts the binary quotient from scaled numerator division. -/
def machineDyadicQuotientBits (word : List Bool) : List Bool :=
  machinePairFirst (machineDyadicDivModBits word)

/-- Extracts the binary remainder from scaled numerator division. -/
def machineDyadicRemainderBits (word : List Bool) : List Bool :=
  machinePairSecond (machineDyadicDivModBits word)

/-- Adds one to the binary quotient from scaled numerator division. -/
def machineDyadicQuotientSuccBits (word : List Bool) : List Bool :=
  machineBinaryAddBits (pair (machineDyadicQuotientBits word) [true])

/-- Uses the quotient magnitude for exact negative division and its successor when a nonzero
remainder requires rounding downward. -/
def machineDyadicNegativeFloorAbsBits (word : List Bool) : List Bool :=
  machineIfEmpty (machineDyadicRemainderBits word)
    (machineDyadicQuotientBits word)
    (machineDyadicQuotientSuccBits word)

/-- Selects the adjusted negative magnitude or ordinary quotient according to the numerator
sign. -/
def machineDyadicFloorAbsBits (word : List Bool) : List Bool :=
  machineIfHead (machineDyadicNumeratorSign word)
    (machineDyadicNegativeFloorAbsBits word)
    (machineDyadicQuotientBits word)

/-- Combines the original numerator sign and the selected floor magnitude into a canonical
integer code. -/
def machineDyadicFloorIntegerCode (word : List Bool) : List Bool :=
  machineCanonicalIntegerFromSignedAbs
    (pair (machineDyadicNumeratorSign word)
      (machineDyadicFloorAbsBits word))

/-- Encodes the denominator `2^p` as `p` low-order zero bits followed by one. -/
def machineDyadicPowerDenominatorBits (word : List Bool) : List Bool :=
  machineDyadicPrecisionZeroBits word ++ [true]

/-- Unreduced dyadic-floor output, with denominator `2^p`. -/
def machineRawDyadicFloorCode (word : List Bool) : List Bool :=
  pair (machineDyadicFloorIntegerCode word)
    (machineDyadicPowerDenominatorBits word)

/-- Canonical public rational encoding of the dyadic floor. -/
def machineDyadicFloorCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawDyadicFloorCode word)

theorem machineDyadicPrecisionRuler_mem_FP :
    machineDyadicPrecisionRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineDyadicRawCode_mem_FP :
    machineDyadicRawCode ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineDyadicNumeratorCode_mem_FP :
    machineDyadicNumeratorCode ∈ Complexity.FP := by
  simpa only [machineDyadicNumeratorCode] using!
    machineCompose_mem_FP machineDyadicRawCode_mem_FP machinePairFirst_mem_FP

theorem machineDyadicDenominatorBits_mem_FP :
    machineDyadicDenominatorBits ∈ Complexity.FP := by
  simpa only [machineDyadicDenominatorBits] using!
    machineCompose_mem_FP machineDyadicRawCode_mem_FP machinePairSecond_mem_FP

theorem machineDyadicNumeratorSign_mem_FP :
    machineDyadicNumeratorSign ∈ Complexity.FP := by
  simpa only [machineDyadicNumeratorSign] using!
    machineCompose_mem_FP machineDyadicNumeratorCode_mem_FP
      machineHeadBit_mem_FP

theorem machineDyadicNumeratorAbsBits_mem_FP :
    machineDyadicNumeratorAbsBits ∈ Complexity.FP := by
  simpa only [machineDyadicNumeratorAbsBits] using!
    machineCompose_mem_FP machineDyadicNumeratorCode_mem_FP
      machineIntegerNatAbsBits_mem_FP

theorem machineDyadicPrecisionZeroBits_mem_FP :
    machineDyadicPrecisionZeroBits ∈ Complexity.FP := by
  simpa only [machineDyadicPrecisionZeroBits,
    machineDyadicPrecisionRuler] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machineZeroBlock_mem_FP

theorem machineDyadicScaledAbsBits_mem_FP :
    machineDyadicScaledAbsBits ∈ Complexity.FP := by
  have happend := machineAppend_mem_FP machineDyadicPrecisionZeroBits_mem_FP
    machineDyadicNumeratorAbsBits_mem_FP
  exact machineIfEmpty_mem_FP machineDyadicNumeratorAbsBits_mem_FP
    (machineConst_mem_FP []) happend

theorem machineDyadicDivModBits_mem_FP :
    machineDyadicDivModBits ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDyadicScaledAbsBits_mem_FP
    machineDyadicDenominatorBits_mem_FP
  simpa only [machineDyadicDivModBits] using!
    machineCompose_mem_FP hpair machineBinaryDivModBits_mem_FP

theorem machineDyadicQuotientBits_mem_FP :
    machineDyadicQuotientBits ∈ Complexity.FP := by
  simpa only [machineDyadicQuotientBits] using!
    machineCompose_mem_FP machineDyadicDivModBits_mem_FP
      machinePairFirst_mem_FP

theorem machineDyadicRemainderBits_mem_FP :
    machineDyadicRemainderBits ∈ Complexity.FP := by
  simpa only [machineDyadicRemainderBits] using!
    machineCompose_mem_FP machineDyadicDivModBits_mem_FP
      machinePairSecond_mem_FP

theorem machineDyadicQuotientSuccBits_mem_FP :
    machineDyadicQuotientSuccBits ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDyadicQuotientBits_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineDyadicQuotientSuccBits] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineDyadicNegativeFloorAbsBits_mem_FP :
    machineDyadicNegativeFloorAbsBits ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineDyadicRemainderBits_mem_FP
    machineDyadicQuotientBits_mem_FP machineDyadicQuotientSuccBits_mem_FP

theorem machineDyadicFloorAbsBits_mem_FP :
    machineDyadicFloorAbsBits ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineDyadicNumeratorSign_mem_FP
    machineDyadicNegativeFloorAbsBits_mem_FP
    machineDyadicQuotientBits_mem_FP

theorem machineDyadicFloorIntegerCode_mem_FP :
    machineDyadicFloorIntegerCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDyadicNumeratorSign_mem_FP
    machineDyadicFloorAbsBits_mem_FP
  simpa only [machineDyadicFloorIntegerCode] using!
    machineCompose_mem_FP hpair machineCanonicalIntegerFromSignedAbs_mem_FP

theorem machineDyadicPowerDenominatorBits_mem_FP :
    machineDyadicPowerDenominatorBits ∈ Complexity.FP := by
  exact machineAppend_mem_FP machineDyadicPrecisionZeroBits_mem_FP
    (machineConst_mem_FP [true])

theorem machineRawDyadicFloorCode_mem_FP :
    machineRawDyadicFloorCode ∈ Complexity.FP := by
  exact machinePair_mem_FP machineDyadicFloorIntegerCode_mem_FP
    machineDyadicPowerDenominatorBits_mem_FP

theorem machineDyadicFloorCode_mem_FP : machineDyadicFloorCode ∈ Complexity.FP := by
  simpa only [machineDyadicFloorCode] using!
    machineCompose_mem_FP machineRawDyadicFloorCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

private theorem natBits_mul_pow_two_of_ne_zero (n p : ℕ) (hn : n ≠ 0) :
    (n * 2 ^ p).bits = List.replicate p false ++ n.bits := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hproduct : n * 2 ^ p ≠ 0 := mul_ne_zero hn (pow_ne_zero _ (by decide))
      have hrearrange : n * 2 ^ (p + 1) = 2 * (n * 2 ^ p) := by ring
      rw [hrearrange, Nat.bit0_bits _ hproduct, ih]
      simp [List.replicate_succ]

private theorem shiftedNatBits (n p : ℕ) :
    (if n.bits = [] then [] else List.replicate p false ++ n.bits) =
      (n * 2 ^ p).bits := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right (natBits_ne_nil_of_ne_zero hn),
      natBits_mul_pow_two_of_ne_zero n p hn]

/-- Computes the integer floor of the scaled raw rational using binary long division, increasing
the negative magnitude when the remainder is nonzero. -/
def binaryRawDyadicFloorInt (p : ℕ) (q : RawRat) : ℤ :=
  let qr := binaryLongDiv (q.num.natAbs * 2 ^ p) q.den
  match q.num with
  | .ofNat _ => (qr.1 : ℤ)
  | .negSucc _ =>
      if qr.2 = 0 then -(qr.1 : ℤ)
      else -((qr.1 + 1 : ℕ) : ℤ)

/-- Pairs the binary-computed floor of `2^p * q` with the positive denominator `2^p`. -/
def binaryRawDyadicFloor (p : ℕ) (q : RawRat) : RawRat :=
  ⟨binaryRawDyadicFloorInt p q, 2 ^ p, by positivity⟩

theorem binaryRawDyadicFloorInt_eq_ediv (p : ℕ) (q : RawRat) :
    binaryRawDyadicFloorInt p q =
      (q.num * (2 ^ p : ℕ)) / (q.den : ℤ) := by
  rw [binaryRawDyadicFloorInt, binaryLongDiv_eq_div_mod]
  simp only [Prod.fst, Prod.snd]
  cases hnum : q.num with
  | ofNat n =>
      simp [hnum, Int.ediv]
  | negSucc n =>
      have hden : 0 < q.den := q.den_pos
      let a := (n + 1) * 2 ^ p
      have hrepr : Int.negSucc n * (2 ^ p : ℕ) = -((a : ℕ) : ℤ) := by
        have hnrepr : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hnrepr]
        simp only [a]
        push_cast
        ring
      by_cases hrem : a % q.den = 0
      · simp only [hnum, Int.natAbs_negSucc]
        change (if a % q.den = 0 then -((a / q.den : ℕ) : ℤ)
          else -(((a / q.den : ℕ) + 1 : ℕ) : ℤ)) = _
        rw [ite_eq_left hrem, hrepr]
        have hdvdNat : q.den ∣ a := Nat.dvd_of_mod_eq_zero hrem
        have hdvdInt : (q.den : ℤ) ∣ (a : ℤ) := by
          exact_mod_cast hdvdNat
        rw [Int.neg_ediv_of_dvd hdvdInt]
        norm_num
      · simp only [hnum, Int.natAbs_negSucc]
        change (if a % q.den = 0 then -((a / q.den : ℕ) : ℤ)
          else -(((a / q.den : ℕ) + 1 : ℕ) : ℤ)) = _
        rw [ite_eq_right hrem, hrepr]
        have hndvdNat : ¬ q.den ∣ a := by
          rwa [Nat.dvd_iff_mod_eq_zero]
        have hndvdInt : ¬ (q.den : ℤ) ∣ (a : ℤ) := by
          exact_mod_cast hndvdNat
        rw [Int.neg_ediv, ite_eq_right hndvdInt,
          Int.sign_eq_one_of_pos (by exact_mod_cast hden)]
        norm_num [Nat.add_comm]
        ring

theorem binaryRawDyadicFloorInt_eq_floor (p : ℕ) (q : RawRat) :
    binaryRawDyadicFloorInt p q = Int.floor (q.value * (2 : ℚ) ^ p) := by
  rw [binaryRawDyadicFloorInt_eq_ediv]
  have hvalue : q.value * (2 : ℚ) ^ p =
      ((q.num * (2 ^ p : ℕ) : ℤ) : ℚ) / (q.den : ℚ) := by
    rw [RawRat.value]
    push_cast
    ring
  rw [hvalue, Rat.floor_intCast_div_natCast]

theorem binaryRawDyadicFloor_value (p : ℕ) (q : RawRat) :
    (binaryRawDyadicFloor p q).value = binaryDyadicFloor p q.value := by
  simp only [binaryRawDyadicFloor, RawRat.value]
  rw [binaryDyadicFloor, binaryRatFloor_eq_floor]
  have hfloor := binaryRawDyadicFloorInt_eq_floor p q
  simp only [RawRat.value] at hfloor
  rw [← hfloor]
  norm_num

theorem machineDyadicScaledAbsBits_encode (p : ℕ) (q : RawRat) :
    machineDyadicScaledAbsBits
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      (q.num.natAbs * 2 ^ p).bits := by
  simp only [machineDyadicScaledAbsBits, machineDyadicNumeratorAbsBits,
    machineDyadicNumeratorCode, machineDyadicRawCode,
    machineDyadicPrecisionZeroBits, machineDyadicPrecisionRuler,
    machinePairFirst_pair, machinePairSecond_pair, rawRatBinaryCode,
    machineIntegerNatAbsBits_encode, List.length_replicate]
  cases hbits : q.num.natAbs.bits with
  | nil => simpa [hbits] using! shiftedNatBits q.num.natAbs p
  | cons bit rest => simpa [hbits] using! shiftedNatBits q.num.natAbs p

theorem machineDyadicDivModBits_encode (p : ℕ) (q : RawRat) :
    machineDyadicDivModBits
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      pair
        ((q.num.natAbs * 2 ^ p) / q.den).bits
        ((q.num.natAbs * 2 ^ p) % q.den).bits := by
  rw [machineDyadicDivModBits, machineDyadicScaledAbsBits_encode]
  simp only [machineDyadicDenominatorBits, machineDyadicRawCode,
    machinePairSecond_pair, rawRatBinaryCode]
  rw [machineBinaryDivModBits_pair_natBits]

theorem machineDyadicFloorIntegerCode_encode (p : ℕ) (q : RawRat) :
    machineDyadicFloorIntegerCode
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      integerBinaryCode (binaryRawDyadicFloorInt p q) := by
  have hsign : machineDyadicNumeratorSign
      (pair (List.replicate p true) (rawRatBinaryCode q)) =
      match q.num with
      | .ofNat _ => [false]
      | .negSucc _ => [true] := by
    simp only [machineDyadicNumeratorSign, machineDyadicNumeratorCode,
      machineDyadicRawCode, machinePairFirst_pair, machinePairSecond_pair,
      rawRatBinaryCode]
    cases q.num <;> simp [integerBinaryCode]
  have hquot : machineDyadicQuotientBits
      (pair (List.replicate p true) (rawRatBinaryCode q)) =
      ((q.num.natAbs * 2 ^ p) / q.den).bits := by
    rw [machineDyadicQuotientBits, machineDyadicDivModBits_encode]
    simp only [machinePairFirst_pair]
  have hrembits : machineDyadicRemainderBits
      (pair (List.replicate p true) (rawRatBinaryCode q)) =
      ((q.num.natAbs * 2 ^ p) % q.den).bits := by
    rw [machineDyadicRemainderBits, machineDyadicDivModBits_encode]
    simp only [machinePairSecond_pair]
  have hsucc : machineDyadicQuotientSuccBits
      (pair (List.replicate p true) (rawRatBinaryCode q)) =
      (((q.num.natAbs * 2 ^ p) / q.den) + 1).bits := by
    rw [machineDyadicQuotientSuccBits, hquot]
    simpa using! machineBinaryAddBits_pair_natBits
      ((q.num.natAbs * 2 ^ p) / q.den) 1
  rw [machineDyadicFloorIntegerCode]
  cases hnum : q.num with
  | ofNat n =>
      have hsignFalse : machineDyadicNumeratorSign
          (pair (List.replicate p true) (rawRatBinaryCode q)) = [false] := by
        simpa [hnum] using! hsign
      simp only [machineDyadicFloorAbsBits, hsignFalse,
        machineIfHead_false, hquot]
      rw [machineCanonicalIntegerFromSignedAbs_pair]
      simp [binaryRawDyadicFloorInt, hnum, binaryLongDiv_eq_div_mod,
        signedMagnitudeValue]
  | negSucc n =>
      have hsignTrue : machineDyadicNumeratorSign
          (pair (List.replicate p true) (rawRatBinaryCode q)) = [true] := by
        simpa [hnum] using! hsign
      simp only [machineDyadicFloorAbsBits, hsignTrue, machineIfHead_true,
        machineDyadicNegativeFloorAbsBits, hrembits, hquot, hsucc,
        hnum, Int.natAbs_negSucc]
      by_cases hrem : (n + 1) * 2 ^ p % q.den = 0
      · rw [show ((n + 1) * 2 ^ p % q.den).bits = [] by simp [hrem]]
        simp only [machineIfEmpty_nil]
        rw [machineCanonicalIntegerFromSignedAbs_pair]
        simp [binaryRawDyadicFloorInt, hnum, binaryLongDiv_eq_div_mod,
          hrem, signedMagnitudeValue]
      · rw [machineIfEmpty_of_ne_nil
          (((n + 1) * 2 ^ p % q.den).bits)
          (((n + 1) * 2 ^ p / q.den).bits)
          ((((n + 1) * 2 ^ p / q.den) + 1).bits)
          (natBits_ne_nil_of_ne_zero hrem)]
        rw [machineCanonicalIntegerFromSignedAbs_pair]
        simp [binaryRawDyadicFloorInt, hnum, binaryLongDiv_eq_div_mod,
          hrem, signedMagnitudeValue]

theorem machineDyadicPowerDenominatorBits_encode (p : ℕ) (q : RawRat) :
    machineDyadicPowerDenominatorBits
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      (2 ^ p).bits := by
  simp [machineDyadicPowerDenominatorBits,
    machineDyadicPrecisionZeroBits, machineDyadicPrecisionRuler,
    show List.replicate p false ++ [true] = (2 ^ p).bits by
      simpa using! (natBits_mul_pow_two_of_ne_zero 1 p (by decide)).symm]

theorem machineRawDyadicFloorCode_encode (p : ℕ) (q : RawRat) :
    machineRawDyadicFloorCode
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      rawRatBinaryCode (binaryRawDyadicFloor p q) := by
  rw [machineRawDyadicFloorCode, machineDyadicFloorIntegerCode_encode,
    machineDyadicPowerDenominatorBits_encode]
  rfl

theorem machineDyadicFloorCode_encode (p : ℕ) (q : RawRat) :
    machineDyadicFloorCode
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      rationalBinaryCode (binaryNormalizeRawRat (binaryRawDyadicFloor p q)) := by
  rw [machineDyadicFloorCode, machineRawDyadicFloorCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

theorem machineDyadicFloorCode_binaryDyadicFloor (p : ℕ) (q : RawRat) :
    machineDyadicFloorCode
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      rationalBinaryCode (binaryDyadicFloor p q.value) := by
  rw [machineDyadicFloorCode_encode,
    binaryNormalizeRawRat_eq_value, binaryRawDyadicFloor_value]

end BeyondBethe

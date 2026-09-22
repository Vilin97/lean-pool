/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalFloor
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalPower
import LeanPool.BeyondBethe.BeyondBethe.BinaryDirectedElementary

/-!
# Polynomial-time rational logarithm-series loop

The iteration count is a unary ruler.  A state stores the partial sum, the
current odd power, the fixed square of the input, the current odd denominator,
and a quartic-width guard.  The guard makes the function polynomial-time on
arbitrary strings.  The semantic part below proves that none of the three
guarded updates is truncated on a well-formed input.
-/

namespace BeyondBethe

open Complexity

def rawRatZeroCode : List Bool := rawRatBinaryCode RawRat.zero

def machineLogSeriesPack
    (sum power square odd bound : List Bool) : List Bool :=
  pair sum (pair power (pair square (pair odd bound)))

def machineLogSeriesSumField (state : List Bool) : List Bool :=
  machinePairFirst state

def machineLogSeriesPowerField (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineLogSeriesSquareField (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineLogSeriesOddField (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineLogSeriesBoundField (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineLogSeriesOddRawRatCode (state : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode (machineLogSeriesOddField state)) [true]

def machineLogSeriesTermCandidate (state : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineLogSeriesPowerField state)
      (machineLogSeriesOddRawRatCode state))

def machineLogSeriesSumCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineLogSeriesSumField state)
      (machineLogSeriesTermCandidate state))

def machineLogSeriesPowerCandidate (state : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineLogSeriesPowerField state)
      (machineLogSeriesSquareField state))

def machineLogSeriesOddCandidate (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineLogSeriesOddField state) [false, true])

def machineLogSeriesClamp
    (candidate : List Bool → List Bool) (state : List Bool) : List Bool :=
  (candidate state).take (machineLogSeriesBoundField state).length

def machineLogSeriesStep (state : List Bool) : List Bool :=
  machineLogSeriesPack
    (machineLogSeriesClamp machineLogSeriesSumCandidate state)
    (machineLogSeriesClamp machineLogSeriesPowerCandidate state)
    (machineLogSeriesSquareField state)
    (machineLogSeriesClamp machineLogSeriesOddCandidate state)
    (machineLogSeriesBoundField state)

def machineLogSeriesInputRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineLogSeriesInputBase (word : List Bool) : List Bool :=
  machinePairSecond word

/-- A quartic guard.  Its length dominates the cubic bit growth of every
well-formed partial sum while remaining polynomial on arbitrary inputs. -/
def machineLogSeriesInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth word)

def machineLogSeriesInitialSquareCandidate (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineLogSeriesInputBase word)
      (machineLogSeriesInputBase word))

def machineLogSeriesInit (word : List Bool) : List Bool :=
  let bound := machineLogSeriesInputBound word
  machineLogSeriesPack rawRatZeroCode
    (List.take bound.length (machineLogSeriesInputBase word))
    (List.take bound.length (machineLogSeriesInitialSquareCandidate word))
    [true] bound

def machineLogSeriesWidth (word : List Bool) : List Bool :=
  let bound := machineLogSeriesInputBound word
  machineLogSeriesPack bound bound bound bound bound

def machineLogSeriesFinalState (word : List Bool) : List Bool :=
  (machineLogSeriesStep)^[(machineLogSeriesInputRuler word).length]
    (machineLogSeriesInit word)

def machineRawRationalLogSeriesSumCode (word : List Bool) : List Bool :=
  machineLogSeriesSumField (machineLogSeriesFinalState word)

def machineRationalLogSeriesSumCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRationalLogSeriesSumCode word)

theorem machineLogSeriesSumField_mem_FP :
    machineLogSeriesSumField ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineLogSeriesPowerField_mem_FP :
    machineLogSeriesPowerField ∈ Complexity.FP := by
  simpa only [machineLogSeriesPowerField] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineLogSeriesSquareField_mem_FP :
    machineLogSeriesSquareField ∈ Complexity.FP := by
  have hrest := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineLogSeriesSquareField] using!
    machineCompose_mem_FP hrest machinePairFirst_mem_FP

theorem machineLogSeriesOddField_mem_FP :
    machineLogSeriesOddField ∈ Complexity.FP := by
  have hrest2 := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have hrest3 := machineCompose_mem_FP hrest2 machinePairSecond_mem_FP
  simpa only [machineLogSeriesOddField] using!
    machineCompose_mem_FP hrest3 machinePairFirst_mem_FP

theorem machineLogSeriesBoundField_mem_FP :
    machineLogSeriesBoundField ∈ Complexity.FP := by
  have hrest2 := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have hrest3 := machineCompose_mem_FP hrest2 machinePairSecond_mem_FP
  simpa only [machineLogSeriesBoundField] using!
    machineCompose_mem_FP hrest3 machinePairSecond_mem_FP

theorem machineLogSeriesOddRawRatCode_mem_FP :
    machineLogSeriesOddRawRatCode ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineLogSeriesOddField_mem_FP
    (machinePrepend_mem_FP false)
  exact machinePair_mem_FP hnum (machineConst_mem_FP [true])

theorem machineLogSeriesTermCandidate_mem_FP :
    machineLogSeriesTermCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineLogSeriesPowerField_mem_FP
    machineLogSeriesOddRawRatCode_mem_FP
  simpa only [machineLogSeriesTermCandidate] using!
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineLogSeriesSumCandidate_mem_FP :
    machineLogSeriesSumCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineLogSeriesSumField_mem_FP
    machineLogSeriesTermCandidate_mem_FP
  simpa only [machineLogSeriesSumCandidate] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineLogSeriesPowerCandidate_mem_FP :
    machineLogSeriesPowerCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineLogSeriesPowerField_mem_FP
    machineLogSeriesSquareField_mem_FP
  simpa only [machineLogSeriesPowerCandidate] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineLogSeriesOddCandidate_mem_FP :
    machineLogSeriesOddCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineLogSeriesOddField_mem_FP
    (machineConst_mem_FP [false, true])
  simpa only [machineLogSeriesOddCandidate] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineLogSeriesClamp_mem_FP
    {candidate : List Bool → List Bool} (hcandidate : candidate ∈ Complexity.FP) :
    (fun state => machineLogSeriesClamp candidate state) ∈ Complexity.FP := by
  simpa only [machineLogSeriesClamp] using!
    machineTake_mem_FP machineLogSeriesBoundField_mem_FP hcandidate

theorem machineLogSeriesStep_mem_FP :
    machineLogSeriesStep ∈ Complexity.FP := by
  exact machinePair_mem_FP
    (machineLogSeriesClamp_mem_FP machineLogSeriesSumCandidate_mem_FP)
    (machinePair_mem_FP
      (machineLogSeriesClamp_mem_FP machineLogSeriesPowerCandidate_mem_FP)
      (machinePair_mem_FP machineLogSeriesSquareField_mem_FP
        (machinePair_mem_FP
          (machineLogSeriesClamp_mem_FP machineLogSeriesOddCandidate_mem_FP)
          machineLogSeriesBoundField_mem_FP)))

theorem machineLogSeriesInputRuler_mem_FP :
    machineLogSeriesInputRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineLogSeriesInputBase_mem_FP :
    machineLogSeriesInputBase ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineLogSeriesInputBound_mem_FP :
    machineLogSeriesInputBound ∈ Complexity.FP := by
  simpa only [machineLogSeriesInputBound] using!
    machineCompose_mem_FP machineBinaryMulWidth_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineLogSeriesInitialSquareCandidate_mem_FP :
    machineLogSeriesInitialSquareCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineLogSeriesInputBase_mem_FP
    machineLogSeriesInputBase_mem_FP
  simpa only [machineLogSeriesInitialSquareCandidate] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineLogSeriesInit_mem_FP : machineLogSeriesInit ∈ Complexity.FP := by
  have hbase := machineTake_mem_FP machineLogSeriesInputBound_mem_FP
    machineLogSeriesInputBase_mem_FP
  have hsquare := machineTake_mem_FP machineLogSeriesInputBound_mem_FP
    machineLogSeriesInitialSquareCandidate_mem_FP
  simpa only [machineLogSeriesInit, machineLogSeriesPack] using!
    machinePair_mem_FP (machineConst_mem_FP rawRatZeroCode)
      (machinePair_mem_FP hbase
        (machinePair_mem_FP hsquare
          (machinePair_mem_FP (machineConst_mem_FP [true])
            machineLogSeriesInputBound_mem_FP)))

theorem machineLogSeriesWidth_mem_FP :
    machineLogSeriesWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineLogSeriesInputBound_mem_FP
    (machinePair_mem_FP machineLogSeriesInputBound_mem_FP
      (machinePair_mem_FP machineLogSeriesInputBound_mem_FP
        (machinePair_mem_FP machineLogSeriesInputBound_mem_FP
          machineLogSeriesInputBound_mem_FP)))

def MachineLogSeriesStateBound (word state : List Bool) : Prop :=
  state = machineLogSeriesPack
      (machineLogSeriesSumField state)
      (machineLogSeriesPowerField state)
      (machineLogSeriesSquareField state)
      (machineLogSeriesOddField state)
      (machineLogSeriesBoundField state) ∧
  (machineLogSeriesSumField state).length ≤
      (machineLogSeriesInputBound word).length ∧
  (machineLogSeriesPowerField state).length ≤
      (machineLogSeriesInputBound word).length ∧
  (machineLogSeriesSquareField state).length ≤
      (machineLogSeriesInputBound word).length ∧
  (machineLogSeriesOddField state).length ≤
      (machineLogSeriesInputBound word).length ∧
  (machineLogSeriesBoundField state).length ≤
      (machineLogSeriesInputBound word).length

@[simp] theorem machineLogSeriesFields_pack
    (sum power square odd bound : List Bool) :
    machineLogSeriesSumField
        (machineLogSeriesPack sum power square odd bound) = sum ∧
      machineLogSeriesPowerField
        (machineLogSeriesPack sum power square odd bound) = power ∧
      machineLogSeriesSquareField
        (machineLogSeriesPack sum power square odd bound) = square ∧
      machineLogSeriesOddField
        (machineLogSeriesPack sum power square odd bound) = odd ∧
      machineLogSeriesBoundField
        (machineLogSeriesPack sum power square odd bound) = bound := by
  simp [machineLogSeriesPack, machineLogSeriesSumField,
    machineLogSeriesPowerField, machineLogSeriesSquareField,
    machineLogSeriesOddField, machineLogSeriesBoundField]

theorem machineLogSeriesInputBound_nontrivial (word : List Bool) :
    5 ≤ (machineLogSeriesInputBound word).length := by
  simp [machineLogSeriesInputBound, machineBinaryMulWidth]
  nlinarith

theorem machineLogSeriesInit_bound (word : List Bool) :
    MachineLogSeriesStateBound word (machineLogSeriesInit word) := by
  simp only [MachineLogSeriesStateBound, machineLogSeriesInit,
    machineLogSeriesFields_pack]
  have hbound := machineLogSeriesInputBound_nontrivial word
  constructor
  · trivial
  constructor
  · simp [rawRatZeroCode, rawRatBinaryCode, RawRat.zero,
      integerBinaryCode]
    omega
  constructor
  · exact List.length_take_le _ _
  constructor
  · exact List.length_take_le _ _
  constructor
  · simp
    omega
  · exact le_rfl

theorem machineLogSeriesStep_bound {word state : List Bool}
    (hstate : MachineLogSeriesStateBound word state) :
    MachineLogSeriesStateBound word (machineLogSeriesStep state) := by
  rcases hstate with ⟨_, hsum, hpower, hsquare, hodd, hbound⟩
  simp only [MachineLogSeriesStateBound, machineLogSeriesStep,
    machineLogSeriesFields_pack]
  constructor
  · trivial
  constructor
  · exact (List.length_take_le _ _).trans hbound
  constructor
  · exact (List.length_take_le _ _).trans hbound
  constructor
  · exact hsquare
  constructor
  · exact (List.length_take_le _ _).trans hbound
  · exact hbound

theorem machineLogSeriesIterate_bound (word : List Bool) : ∀ k,
    MachineLogSeriesStateBound word
      ((machineLogSeriesStep)^[k] (machineLogSeriesInit word)) := by
  intro k
  induction k with
  | zero => exact machineLogSeriesInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineLogSeriesStep_bound ih

theorem machineLogSeriesPack_length_le_width
    (word state : List Bool) (hstate : MachineLogSeriesStateBound word state) :
    state.length ≤ (machineLogSeriesWidth word).length := by
  rcases hstate with ⟨hdecomp, hsum, hpower, hsquare, hodd, hbound⟩
  rw [hdecomp]
  simp only [machineLogSeriesPack, machineLogSeriesWidth, pair_length]
  omega

theorem machineLogSeriesIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineLogSeriesInputRuler word).length) :
    ((machineLogSeriesStep)^[iterations]
      (machineLogSeriesInit word)).length ≤
        (machineLogSeriesWidth word).length :=
  machineLogSeriesPack_length_le_width word _
    (machineLogSeriesIterate_bound word iterations)

theorem machineLogSeriesFinalState_mem_FP :
    machineLogSeriesFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineLogSeriesStep_mem_FP
    machineLogSeriesInit_mem_FP machineLogSeriesInputRuler_mem_FP
    machineLogSeriesWidth_mem_FP machineLogSeriesIterate_length_le_width

theorem machineRawRationalLogSeriesSumCode_mem_FP :
    machineRawRationalLogSeriesSumCode ∈ Complexity.FP := by
  simpa only [machineRawRationalLogSeriesSumCode] using!
    machineCompose_mem_FP machineLogSeriesFinalState_mem_FP
      machineLogSeriesSumField_mem_FP

theorem machineRationalLogSeriesSumCode_mem_FP :
    machineRationalLogSeriesSumCode ∈ Complexity.FP := by
  simpa only [machineRationalLogSeriesSumCode] using!
    machineCompose_mem_FP machineRawRationalLogSeriesSumCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

/-! ## Exact semantics on well-formed inputs -/

namespace RawRat

def ofNat (n : ℕ) : RawRat := ⟨n, 1, by omega⟩

@[simp] theorem value_ofNat (n : ℕ) : (ofNat n).value = n := by
  simp [ofNat, value]

/-- The odd powers `x, x^3, x^5, ...`, maintained by multiplication by the
fixed square. -/
def logOddPower (x : RawRat) : ℕ → RawRat
  | 0 => x
  | k + 1 => (logOddPower x k).mul (x.mul x)

/-- Unreduced partial sums of the odd logarithm series. -/
def logSeriesSum (x : RawRat) : ℕ → RawRat
  | 0 => zero
  | k + 1 =>
      (logSeriesSum x k).add
        ((logOddPower x k).div (ofNat (2 * k + 1)))

@[simp] theorem value_logOddPower (x : RawRat) : ∀ k,
    (logOddPower x k).value = x.value ^ (2 * k + 1) := by
  intro k
  induction k with
  | zero => simp [logOddPower]
  | succ k ih =>
      rw [logOddPower, value_mul, ih, value_mul]
      calc
        x.value ^ (2 * k + 1) * (x.value * x.value) =
            x.value ^ (2 * k + 1) * x.value ^ 2 := by rw [pow_two]
        _ = x.value ^ ((2 * k + 1) + 2) := (pow_add _ _ _).symm
        _ = x.value ^ (2 * (k + 1) + 1) := by congr 1 <;> omega

@[simp] theorem value_logSeriesSum (x : RawRat) : ∀ k,
    (logSeriesSum x k).value = binaryRationalLogSeriesSum x.value k := by
  intro k
  induction k with
  | zero => simp [logSeriesSum, binaryRationalLogSeriesSum]
  | succ k ih =>
      rw [logSeriesSum, value_add, value_div, value_logOddPower,
        value_ofNat, binaryRationalLogSeriesSum, binaryRatAdd_eq_add,
        binaryRatDiv_eq_div, binaryRatPow_eq_pow, ih]
      push_cast
      rfl

theorem width_ofNat_le (n : ℕ) : rawRatWidth (ofNat n) ≤ n + 1 := by
  have hpow : n < 2 ^ (n + 1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        have hpos : 0 < 2 ^ (n + 1) := by positivity
        omega
  rw [rawRatWidth, ofNat]
  simp only [Int.natAbs_ofNat', Nat.size_one]
  exact max_le (Nat.size_le.mpr hpow) (by omega)

theorem width_logOddPower_le (x : RawRat) : ∀ k,
    rawRatWidth (logOddPower x k) ≤ (2 * k + 1) * rawRatWidth x := by
  intro k
  induction k with
  | zero => simp [logOddPower]
  | succ k ih =>
      rw [logOddPower]
      have hsquare := rawRatWidth_mul_le x x
      exact (rawRatWidth_mul_le _ _).trans (by nlinarith)

theorem width_logSeriesSum_le (x : RawRat) : ∀ k,
    rawRatWidth (logSeriesSum x k) ≤
      1 + k * ((2 * k + 1) * rawRatWidth x + 2 * k + 4) := by
  intro k
  induction k with
  | zero => simp [logSeriesSum, rawRatWidth_zero]
  | succ k ih =>
      rw [logSeriesSum]
      have hp := width_logOddPower_le x k
      have hn := width_ofNat_le (2 * k + 1)
      have ht := rawRatWidth_div_le (logOddPower x k)
        (ofNat (2 * k + 1))
      have ha := rawRatWidth_add_le (logSeriesSum x k)
        ((logOddPower x k).div (ofNat (2 * k + 1)))
      nlinarith

end RawRat

private theorem logSeriesIntegerNatAbs_size_le_code_length (z : ℤ) :
    z.natAbs.size ≤ (integerBinaryCode z).length := by
  cases z with
  | ofNat n => simp [integerBinaryCode, Nat.size_eq_bits_len]
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

private theorem logSeriesRawRatWidth_le_code_length (q : RawRat) :
    rawRatWidth q ≤ (rawRatBinaryCode q).length := by
  rw [rawRatWidth, rawRatBinaryCode, pair_length]
  apply max_le
  · have h := logSeriesIntegerNatAbs_size_le_code_length q.num
    omega
  · rw [Nat.size_eq_bits_len]
    omega

private theorem logSeriesRawRatCode_length_le_width (q : RawRat) :
    (rawRatBinaryCode q).length ≤ 4 + 3 * rawRatWidth q := by
  rw [rawRatBinaryCode, pair_length]
  have hnum : (integerBinaryCode q.num).length ≤ 1 + rawRatWidth q := by
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
        omega
  have hden := rawRat_den_size_le_width q
  have hdenbits : q.den.bits.length ≤ rawRatWidth q := by
    simpa only [Nat.size_eq_bits_len] using! hden
  omega

private theorem logSeriesCode_length_le_inputBound
    (q r : RawRat) (total k : ℕ) (hk : k ≤ total)
    (hr : rawRatWidth r ≤
      1 + (k + 1) *
        ((2 * (k + 1) + 1) * rawRatWidth q + 2 * (k + 1) + 4)) :
    (rawRatBinaryCode r).length ≤
      (machineLogSeriesInputBound
        (pair (List.replicate total true) (rawRatBinaryCode q))).length := by
  let word := pair (List.replicate total true) (rawRatBinaryCode q)
  have hcode := logSeriesRawRatCode_length_le_width r
  have htotal : total ≤ word.length := by
    simp only [word, pair_length, List.length_replicate]
    omega
  have hqcode : (rawRatBinaryCode q).length ≤ word.length := by
    simp only [word, pair_length, List.length_replicate]
    omega
  have hqwidth := (logSeriesRawRatWidth_le_code_length q).trans hqcode
  have hkword : k ≤ word.length := hk.trans htotal
  have hrword : rawRatWidth r ≤
      1 + (word.length + 1) *
        ((2 * (word.length + 1) + 1) * word.length +
          2 * (word.length + 1) + 4) := by
    have hk1 : k + 1 ≤ word.length + 1 := by omega
    have hfirst : 2 * (k + 1) + 1 ≤ 2 * (word.length + 1) + 1 := by omega
    have hmul : (2 * (k + 1) + 1) * rawRatWidth q ≤
        (2 * (word.length + 1) + 1) * word.length :=
      Nat.mul_le_mul hfirst hqwidth
    have hinner :
        (2 * (k + 1) + 1) * rawRatWidth q + 2 * (k + 1) + 4 ≤
          (2 * (word.length + 1) + 1) * word.length +
            2 * (word.length + 1) + 4 := by omega
    have hproduct := Nat.mul_le_mul hk1 hinner
    exact hr.trans (Nat.add_le_add_left hproduct 1)
  calc
    (rawRatBinaryCode r).length ≤ 4 + 3 * rawRatWidth r := hcode
    _ ≤ 4 + 3 * (1 + (word.length + 1) *
        ((2 * (word.length + 1) + 1) * word.length +
          2 * (word.length + 1) + 4)) := by omega
    _ ≤ (machineLogSeriesInputBound word).length := by
      simp [machineLogSeriesInputBound, machineBinaryMulWidth]
      nlinarith [sq_nonneg (word.length * word.length *
        (word.length + 1))]

private theorem logSeriesSumCode_length_le_inputBound
    (q : RawRat) (total k : ℕ) (hk : k ≤ total) :
    (rawRatBinaryCode (RawRat.logSeriesSum q k)).length ≤
      (machineLogSeriesInputBound
        (pair (List.replicate total true) (rawRatBinaryCode q))).length :=
  logSeriesCode_length_le_inputBound q _ total k hk
    ((RawRat.width_logSeriesSum_le q k).trans (by nlinarith))

private theorem logSeriesPowerCode_length_le_inputBound
    (q : RawRat) (total k : ℕ) (hk : k ≤ total) :
    (rawRatBinaryCode (RawRat.logOddPower q k)).length ≤
      (machineLogSeriesInputBound
        (pair (List.replicate total true) (rawRatBinaryCode q))).length := by
  apply logSeriesCode_length_le_inputBound q _ total k hk
  have hp := RawRat.width_logOddPower_le q k
  exact hp.trans (by nlinarith)

private theorem logSeriesSquareCode_length_le_inputBound
    (q : RawRat) (total : ℕ) :
    (rawRatBinaryCode (q.mul q)).length ≤
      (machineLogSeriesInputBound
        (pair (List.replicate total true) (rawRatBinaryCode q))).length := by
  apply logSeriesCode_length_le_inputBound q _ total 0 (by omega)
  have hsquare := rawRatWidth_mul_le q q
  exact hsquare.trans (by nlinarith)

private theorem logSeriesOddBits_length_le_inputBound
    (q : RawRat) (total k : ℕ) (hk : k ≤ total) :
    (2 * k + 1).bits.length ≤
      (machineLogSeriesInputBound
        (pair (List.replicate total true) (rawRatBinaryCode q))).length := by
  have hsize : (2 * k + 1).bits.length ≤ 2 * k + 2 := by
    have hw := RawRat.width_ofNat_le (2 * k + 1)
    rw [rawRatWidth, RawRat.ofNat] at hw
    simp only [Int.natAbs_ofNat', Nat.size_one] at hw
    have hs := (le_max_left (2 * k + 1).size 1).trans hw
    simpa only [Nat.size_eq_bits_len] using! hs
  let word := pair (List.replicate total true) (rawRatBinaryCode q)
  have htotal : total ≤ word.length := by
    simp only [word, pair_length, List.length_replicate]
    omega
  have hkword : k ≤ word.length := hk.trans htotal
  have hlarge : 2 * word.length + 2 ≤
      (machineLogSeriesInputBound word).length := by
    simp [machineLogSeriesInputBound, machineBinaryMulWidth]
    nlinarith
  exact hsize.trans ((by omega : 2 * k + 2 ≤ 2 * word.length + 2).trans hlarge)

def rawLogSeriesMachineState (q : RawRat) (total k : ℕ) : List Bool :=
  let word := pair (List.replicate total true) (rawRatBinaryCode q)
  machineLogSeriesPack
    (rawRatBinaryCode (RawRat.logSeriesSum q k))
    (rawRatBinaryCode (RawRat.logOddPower q k))
    (rawRatBinaryCode (q.mul q))
    (2 * k + 1).bits
    (machineLogSeriesInputBound word)

theorem machineLogSeriesInit_encode (q : RawRat) (total : ℕ) :
    machineLogSeriesInit
        (pair (List.replicate total true) (rawRatBinaryCode q)) =
      rawLogSeriesMachineState q total 0 := by
  let word := pair (List.replicate total true) (rawRatBinaryCode q)
  have hbase : (rawRatBinaryCode q).length ≤
      (machineLogSeriesInputBound word).length := by
    simpa only [RawRat.logOddPower] using!
      logSeriesPowerCode_length_le_inputBound q total 0 (by omega)
  have hsquare := logSeriesSquareCode_length_le_inputBound q total
  rw [machineLogSeriesInit]
  simp only [machineLogSeriesInputBase, machinePairSecond_pair,
    machineLogSeriesInitialSquareCandidate,
    machineRawRatMulCode_encode]
  rw [(List.take_eq_self_iff _).2 hbase,
    (List.take_eq_self_iff _).2 hsquare]
  simp [rawLogSeriesMachineState, rawRatZeroCode,
    RawRat.logSeriesSum, RawRat.logOddPower]

@[simp] theorem machineLogSeriesOddRawRatCode_encode
    (q : RawRat) (total k : ℕ) :
    machineLogSeriesOddRawRatCode (rawLogSeriesMachineState q total k) =
      rawRatBinaryCode (RawRat.ofNat (2 * k + 1)) := by
  rw [machineLogSeriesOddRawRatCode]
  simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
  rw [machineNaturalIntegerCode_natBits]
  simp [rawRatBinaryCode, RawRat.ofNat]

@[simp] theorem machineLogSeriesTermCandidate_encode
    (q : RawRat) (total k : ℕ) :
    machineLogSeriesTermCandidate (rawLogSeriesMachineState q total k) =
      rawRatBinaryCode
        ((RawRat.logOddPower q k).div (RawRat.ofNat (2 * k + 1))) := by
  rw [machineLogSeriesTermCandidate,
    machineLogSeriesOddRawRatCode_encode]
  simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
  rw [machineRawRatDivCode_encode]

@[simp] theorem machineLogSeriesSumCandidate_encode
    (q : RawRat) (total k : ℕ) :
    machineLogSeriesSumCandidate (rawLogSeriesMachineState q total k) =
      rawRatBinaryCode (RawRat.logSeriesSum q (k + 1)) := by
  rw [machineLogSeriesSumCandidate,
    machineLogSeriesTermCandidate_encode]
  simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
  rw [machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineLogSeriesPowerCandidate_encode
    (q : RawRat) (total k : ℕ) :
    machineLogSeriesPowerCandidate (rawLogSeriesMachineState q total k) =
      rawRatBinaryCode (RawRat.logOddPower q (k + 1)) := by
  rw [machineLogSeriesPowerCandidate]
  simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack,
    machineRawRatMulCode_encode]
  rw [RawRat.logOddPower]

@[simp] theorem machineLogSeriesOddCandidate_encode
    (q : RawRat) (total k : ℕ) :
    machineLogSeriesOddCandidate (rawLogSeriesMachineState q total k) =
      (2 * (k + 1) + 1).bits := by
  rw [machineLogSeriesOddCandidate]
  simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
  have htwo : ([false, true] : List Bool) = (2 : ℕ).bits := by rfl
  rw [htwo, machineBinaryAddBits_pair_natBits]
  congr 1

theorem machineLogSeriesStep_encode
    (q : RawRat) (total k : ℕ) (hk : k + 1 ≤ total) :
    machineLogSeriesStep (rawLogSeriesMachineState q total k) =
      rawLogSeriesMachineState q total (k + 1) := by
  let word := pair (List.replicate total true) (rawRatBinaryCode q)
  have hsum := logSeriesSumCode_length_le_inputBound q total (k + 1) hk
  have hpower := logSeriesPowerCode_length_le_inputBound q total (k + 1) hk
  have hodd := logSeriesOddBits_length_le_inputBound q total (k + 1) hk
  have hsumClamp :
      machineLogSeriesClamp machineLogSeriesSumCandidate
          (rawLogSeriesMachineState q total k) =
        rawRatBinaryCode (RawRat.logSeriesSum q (k + 1)) := by
    rw [machineLogSeriesClamp, machineLogSeriesSumCandidate_encode]
    simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
    exact (List.take_eq_self_iff _).2 hsum
  have hpowerClamp :
      machineLogSeriesClamp machineLogSeriesPowerCandidate
          (rawLogSeriesMachineState q total k) =
        rawRatBinaryCode (RawRat.logOddPower q (k + 1)) := by
    rw [machineLogSeriesClamp, machineLogSeriesPowerCandidate_encode]
    simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
    exact (List.take_eq_self_iff _).2 hpower
  have hoddClamp :
      machineLogSeriesClamp machineLogSeriesOddCandidate
          (rawLogSeriesMachineState q total k) =
        (2 * (k + 1) + 1).bits := by
    rw [machineLogSeriesClamp, machineLogSeriesOddCandidate_encode]
    simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]
    exact (List.take_eq_self_iff _).2 hodd
  rw [machineLogSeriesStep, hsumClamp, hpowerClamp, hoddClamp]
  simp only [rawLogSeriesMachineState, machineLogSeriesFields_pack]

theorem machineLogSeriesIterate_encode (q : RawRat) (total : ℕ) :
    ∀ k ≤ total,
      (machineLogSeriesStep)^[k]
          (machineLogSeriesInit
            (pair (List.replicate total true) (rawRatBinaryCode q))) =
        rawLogSeriesMachineState q total k := by
  intro k hk
  induction k with
  | zero => exact machineLogSeriesInit_encode q total
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineLogSeriesStep_encode q total k hk

theorem machineRawRationalLogSeriesSumCode_encode
    (q : RawRat) (N : ℕ) :
    machineRawRationalLogSeriesSumCode
        (pair (List.replicate N true) (rawRatBinaryCode q)) =
      rawRatBinaryCode (RawRat.logSeriesSum q N) := by
  rw [machineRawRationalLogSeriesSumCode,
    machineLogSeriesFinalState]
  simp only [machineLogSeriesInputRuler, machinePairFirst_pair,
    List.length_replicate]
  rw [machineLogSeriesIterate_encode q N N le_rfl]
  simp [rawLogSeriesMachineState]

theorem machineRationalLogSeriesSumCode_encode
    (q : RawRat) (N : ℕ) :
    machineRationalLogSeriesSumCode
        (pair (List.replicate N true) (rawRatBinaryCode q)) =
      rationalBinaryCode (binaryRationalLogSeriesSum q.value N) := by
  rw [machineRationalLogSeriesSumCode,
    machineRawRationalLogSeriesSumCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_logSeriesSum]

end BeyondBethe

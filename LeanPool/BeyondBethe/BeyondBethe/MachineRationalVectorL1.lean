/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorSum
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidEncoding

/-!
# Polynomial-time rational `ℓ1` norms

The rational ellipsoid update normalizes a pulled-back cut by
`sum i, |b i|`.  This module implements that quantity directly on the
right-nested finite-word encoding of a rational vector.  The accumulator is
an unreduced rational.  As in the other rational folds, a quadratic clamp
makes the transducer polynomially bounded on malformed words, while the
semantic invariant proves that the clamp is inactive on canonical inputs.
-/

namespace BeyondBethe

open Complexity

namespace RawRat

/-- Replace the signed numerator by its absolute value without changing the
positive denominator. -/
def magnitude (q : RawRat) : RawRat :=
  ⟨Int.ofNat q.num.natAbs, q.den, q.den_pos⟩

@[simp] theorem magnitude_value (q : RawRat) :
    q.magnitude.value = abs q.value := by
  rcases q with ⟨num, den, hden⟩
  cases num with
  | ofNat n =>
      have hdenQ : (0 : ℚ) < den := by exact_mod_cast hden
      simp [magnitude, value, abs_div, abs_of_pos hdenQ]
  | negSucc n =>
      have hdenQ : (0 : ℚ) < den := by exact_mod_cast hden
      simp only [magnitude, value, Int.natAbs_negSucc, Int.cast_ofNat,
        Int.cast_negSucc, Nat.cast_add, Nat.cast_one, abs_div,
        abs_of_pos hdenQ]
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℚ) ≤ n + 1)]
      norm_num

@[simp] theorem width_magnitude (q : RawRat) :
    rawRatWidth q.magnitude = rawRatWidth q := by
  rcases q with ⟨num, den, hden⟩
  cases num with
  | ofNat n => simp [magnitude, rawRatWidth]
  | negSucc n =>
      simp only [magnitude, rawRatWidth, Int.natAbs_negSucc]
      simp only [Int.natAbs_ofNat']

end RawRat

/-- Exact finite-word absolute value for an unreduced rational entry. -/
def machineRawRatMagnitudeCode (word : List Bool) : List Bool :=
  pair
    (machineCanonicalIntegerFromSignedAbs
      (pair [false]
        (machineIntegerNatAbsBits (machinePairFirst word))))
    (machinePairSecond word)

theorem machineRawRatMagnitudeCode_mem_FP :
    machineRawRatMagnitudeCode ∈ FP := by
  have habs := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerNatAbsBits_mem_FP
  have hsigned := machinePair_mem_FP (machineConst_mem_FP [false]) habs
  have hnum := machineCompose_mem_FP hsigned
    machineCanonicalIntegerFromSignedAbs_mem_FP
  exact machinePair_mem_FP hnum machinePairSecond_mem_FP

@[simp] theorem machineRawRatMagnitudeCode_encode (q : RawRat) :
    machineRawRatMagnitudeCode (rawRatBinaryCode q) =
      rawRatBinaryCode q.magnitude := by
  rw [machineRawRatMagnitudeCode, rawRatBinaryCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    machineIntegerNatAbsBits_encode, RawRat.magnitude]
  rw [machineCanonicalIntegerFromSignedAbs_pair]
  simp [signedMagnitudeValue, rawRatBinaryCode]

def machineRationalVectorL1Pack
    (current acc bound : List Bool) : List Bool :=
  pair current (pair acc bound)

def machineRationalVectorL1Current (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRationalVectorL1Acc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRationalVectorL1Bound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineRationalVectorL1Entry (state : List Bool) : List Bool :=
  machineListHead (machineRationalVectorL1Current state)

def machineRationalVectorL1Magnitude (state : List Bool) : List Bool :=
  machineRawRatMagnitudeCode (machineRationalVectorL1Entry state)

def machineRationalVectorL1Candidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineRationalVectorL1Acc state)
      (machineRationalVectorL1Magnitude state))

def machineRationalVectorL1NextAcc (state : List Bool) : List Bool :=
  (machineRationalVectorL1Candidate state).take
    (machineRationalVectorL1Bound state).length

def machineRationalVectorL1Advance (state : List Bool) : List Bool :=
  machineRationalVectorL1Pack
    (machineListTail (machineRationalVectorL1Current state))
    (machineRationalVectorL1NextAcc state)
    (machineRationalVectorL1Bound state)

def machineRationalVectorL1Step (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalVectorL1Current state) state
    (machineRationalVectorL1Advance state)

def machineRationalVectorL1InputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineRationalVectorL1Init (word : List Bool) : List Bool :=
  machineRationalVectorL1Pack word (rawRatBinaryCode RawRat.zero)
    (machineRationalVectorL1InputBound word)

def machineRationalVectorL1Width (word : List Bool) : List Bool :=
  let bound := machineRationalVectorL1InputBound word
  machineRationalVectorL1Pack word bound bound

def machineRationalVectorL1FinalState (word : List Bool) : List Bool :=
  (machineRationalVectorL1Step)^[word.length]
    (machineRationalVectorL1Init word)

/-- Unreduced rational word for the exact `ℓ1` norm. -/
def machineRationalVectorL1RawCode (word : List Bool) : List Bool :=
  machineRationalVectorL1Acc (machineRationalVectorL1FinalState word)

/-- Canonical rational-entry word for the exact `ℓ1` norm. -/
def machineRationalVectorL1EntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode (machineRationalVectorL1RawCode word)

theorem machineRationalVectorL1Current_mem_FP :
    machineRationalVectorL1Current ∈ FP := machinePairFirst_mem_FP

theorem machineRationalVectorL1Acc_mem_FP :
    machineRationalVectorL1Acc ∈ FP := by
  simpa only [machineRationalVectorL1Acc] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRationalVectorL1Bound_mem_FP :
    machineRationalVectorL1Bound ∈ FP := by
  simpa only [machineRationalVectorL1Bound] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineRationalVectorL1Entry_mem_FP :
    machineRationalVectorL1Entry ∈ FP := by
  simpa only [machineRationalVectorL1Entry] using
    machineCompose_mem_FP machineRationalVectorL1Current_mem_FP
      machineListHead_mem_FP

theorem machineRationalVectorL1Magnitude_mem_FP :
    machineRationalVectorL1Magnitude ∈ FP := by
  simpa only [machineRationalVectorL1Magnitude] using
    machineCompose_mem_FP machineRationalVectorL1Entry_mem_FP
      machineRawRatMagnitudeCode_mem_FP

theorem machineRationalVectorL1Candidate_mem_FP :
    machineRationalVectorL1Candidate ∈ FP := by
  have hp := machinePair_mem_FP machineRationalVectorL1Acc_mem_FP
    machineRationalVectorL1Magnitude_mem_FP
  simpa only [machineRationalVectorL1Candidate] using
    machineCompose_mem_FP hp machineRawRatAddCode_mem_FP

theorem machineRationalVectorL1NextAcc_mem_FP :
    machineRationalVectorL1NextAcc ∈ FP := by
  simpa only [machineRationalVectorL1NextAcc] using
    machineTake_mem_FP machineRationalVectorL1Bound_mem_FP
      machineRationalVectorL1Candidate_mem_FP

theorem machineRationalVectorL1Advance_mem_FP :
    machineRationalVectorL1Advance ∈ FP := by
  have htail := machineCompose_mem_FP machineRationalVectorL1Current_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalVectorL1NextAcc_mem_FP
      machineRationalVectorL1Bound_mem_FP)

theorem machineRationalVectorL1Step_mem_FP :
    machineRationalVectorL1Step ∈ FP := by
  exact machineIfEmpty_mem_FP machineRationalVectorL1Current_mem_FP
    id_mem_FP machineRationalVectorL1Advance_mem_FP

theorem machineRationalVectorL1InputBound_mem_FP :
    machineRationalVectorL1InputBound ∈ FP :=
  machineBinaryMulWidth_mem_FP

theorem machineRationalVectorL1Init_mem_FP :
    machineRationalVectorL1Init ∈ FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
      machineRationalVectorL1InputBound_mem_FP)

theorem machineRationalVectorL1Width_mem_FP :
    machineRationalVectorL1Width ∈ FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineRationalVectorL1InputBound_mem_FP
      machineRationalVectorL1InputBound_mem_FP)

@[simp] theorem machineRationalVectorL1Current_pack (current acc bound) :
    machineRationalVectorL1Current
      (machineRationalVectorL1Pack current acc bound) = current := by
  simp [machineRationalVectorL1Current, machineRationalVectorL1Pack]

@[simp] theorem machineRationalVectorL1Acc_pack (current acc bound) :
    machineRationalVectorL1Acc
      (machineRationalVectorL1Pack current acc bound) = acc := by
  simp [machineRationalVectorL1Acc, machineRationalVectorL1Pack]

@[simp] theorem machineRationalVectorL1Bound_pack (current acc bound) :
    machineRationalVectorL1Bound
      (machineRationalVectorL1Pack current acc bound) = bound := by
  simp [machineRationalVectorL1Bound, machineRationalVectorL1Pack]

def MachineRationalVectorL1StateBound
    (word state : List Bool) : Prop :=
  state = machineRationalVectorL1Pack
      (machineRationalVectorL1Current state)
      (machineRationalVectorL1Acc state)
      (machineRationalVectorL1Bound state) ∧
    (machineRationalVectorL1Current state).length ≤ word.length ∧
    (machineRationalVectorL1Acc state).length ≤
      (machineRationalVectorL1InputBound word).length ∧
    machineRationalVectorL1Bound state =
      machineRationalVectorL1InputBound word

theorem machineRationalVectorL1Init_bound (word : List Bool) :
    MachineRationalVectorL1StateBound word
      (machineRationalVectorL1Init word) := by
  simp only [MachineRationalVectorL1StateBound,
    machineRationalVectorL1Init, machineRationalVectorL1Current_pack,
    machineRationalVectorL1Acc_pack, machineRationalVectorL1Bound_pack]
  refine ⟨trivial, le_rfl, ?_, trivial⟩
  simp [machineRationalVectorL1InputBound, machineBinaryMulWidth,
    rawRatBinaryCode, RawRat.zero, integerBinaryCode]
  nlinarith [sq_nonneg (word.length + 16)]

theorem machineRationalVectorL1Step_bound {word state : List Bool}
    (hs : MachineRationalVectorL1StateBound word state) :
    MachineRationalVectorL1StateBound word
      (machineRationalVectorL1Step state) := by
  rcases hs with ⟨hdecomp, hcurrent, hacc, hbound⟩
  by_cases hnil : machineRationalVectorL1Current state = []
  · rw [machineRationalVectorL1Step, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hcurrent, hacc, hbound⟩
  · cases hcode : machineRationalVectorL1Current state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineRationalVectorL1Step, hcode, machineIfEmpty_cons,
          machineRationalVectorL1Advance]
        simp only [MachineRationalVectorL1StateBound,
          machineRationalVectorL1Current_pack,
          machineRationalVectorL1Acc_pack,
          machineRationalVectorL1Bound_pack]
        refine ⟨trivial, ?_, ?_, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalVectorL1Current state)).trans hcurrent
        · rw [machineRationalVectorL1NextAcc, hbound]
          exact List.length_take_le _ _

theorem machineRationalVectorL1Iterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalVectorL1StateBound word
      ((machineRationalVectorL1Step)^[k]
        (machineRationalVectorL1Init word)) := by
  intro k
  induction k with
  | zero => exact machineRationalVectorL1Init_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalVectorL1Step_bound ih

theorem machineRationalVectorL1Iterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalVectorL1Step)^[iterations]
      (machineRationalVectorL1Init word)).length ≤
        (machineRationalVectorL1Width word).length := by
  rcases machineRationalVectorL1Iterate_bound word iterations with
    ⟨hdecomp, hcurrent, hacc, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalVectorL1Pack,
    machineRationalVectorL1Width, pair_length]
  omega

theorem machineRationalVectorL1FinalState_mem_FP :
    machineRationalVectorL1FinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalVectorL1Step_mem_FP
    machineRationalVectorL1Init_mem_FP id_mem_FP
    machineRationalVectorL1Width_mem_FP
    machineRationalVectorL1Iterate_length_le_width

theorem machineRationalVectorL1RawCode_mem_FP :
    machineRationalVectorL1RawCode ∈ FP := by
  simpa only [machineRationalVectorL1RawCode] using
    machineCompose_mem_FP machineRationalVectorL1FinalState_mem_FP
      machineRationalVectorL1Acc_mem_FP

theorem machineRationalVectorL1EntryCode_mem_FP :
    machineRationalVectorL1EntryCode ∈ FP := by
  simpa only [machineRationalVectorL1EntryCode] using
    machineCompose_mem_FP machineRationalVectorL1RawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

/-! ## Exact semantics -/

def rawRatListL1Sum : RawRat → List ℚ → RawRat
  | acc, [] => acc
  | acc, q :: qs =>
      rawRatListL1Sum (acc.add (rawRatOfRat q).magnitude) qs

theorem rawRatWidth_listL1Sum_le (acc : RawRat) : ∀ xs : List ℚ,
    rawRatWidth (rawRatListL1Sum acc xs) ≤
      rawRatWidth acc + rawRatListCost xs := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRatListL1Sum, rawRatListCost]
  | cons q qs ih =>
      rw [rawRatListL1Sum]
      have hadd := rawRatWidth_add_le acc (rawRatOfRat q).magnitude
      rw [RawRat.width_magnitude] at hadd
      have htail := ih (acc.add (rawRatOfRat q).magnitude)
      simp only [rawRatListCost, List.map_cons, List.sum_cons] at htail ⊢
      omega

structure RationalVectorL1SemState where
  current : List ℚ
  acc : RawRat

def rationalVectorL1SemStep
    (s : RationalVectorL1SemState) : RationalVectorL1SemState :=
  match s.current with
  | q :: qs => ⟨qs, s.acc.add (rawRatOfRat q).magnitude⟩
  | [] => s

def rationalVectorL1SemCode (bound : List Bool)
    (s : RationalVectorL1SemState) : List Bool :=
  machineRationalVectorL1Pack
    (binaryListCode rationalEntryBinaryCode s.current)
    (rawRatBinaryCode s.acc) bound

def RationalVectorL1SemInvariant (budget : ℕ)
    (s : RationalVectorL1SemState) : Prop :=
  rawRatWidth s.acc + rawRatListCost s.current ≤ budget

theorem rationalVectorL1SemStep_invariant {budget : ℕ}
    {s : RationalVectorL1SemState}
    (hs : RationalVectorL1SemInvariant budget s) :
    RationalVectorL1SemInvariant budget (rationalVectorL1SemStep s) := by
  rcases s with ⟨current, acc⟩
  cases current with
  | nil => exact hs
  | cons q qs =>
      have hadd := rawRatWidth_add_le acc (rawRatOfRat q).magnitude
      rw [RawRat.width_magnitude] at hadd
      simp only [RationalVectorL1SemInvariant, rationalVectorL1SemStep,
        rawRatListCost, List.map_cons, List.sum_cons] at hs ⊢
      omega

theorem rationalVectorL1Bound_large (word : List Bool) :
    4 + 3 * (1 + word.length) ≤
      (machineRationalVectorL1InputBound word).length := by
  simp only [machineRationalVectorL1InputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  nlinarith

theorem machineRationalVectorL1Step_semantics
    (word : List Bool) (s : RationalVectorL1SemState)
    (hs : RationalVectorL1SemInvariant (1 + word.length) s) :
    machineRationalVectorL1Step
        (rationalVectorL1SemCode
          (machineRationalVectorL1InputBound word) s) =
      rationalVectorL1SemCode
        (machineRationalVectorL1InputBound word)
        (rationalVectorL1SemStep s) := by
  rcases s with ⟨current, acc⟩
  cases current with
  | nil =>
      simp [rationalVectorL1SemCode, rationalVectorL1SemStep,
        machineRationalVectorL1Step, binaryListCode]
  | cons q qs =>
      have hnext :
          rawRatWidth (acc.add (rawRatOfRat q).magnitude) ≤
            1 + word.length := by
        have hinv := rationalVectorL1SemStep_invariant hs
        have hinv' :
            rawRatWidth (acc.add (rawRatOfRat q).magnitude) +
                rawRatListCost qs ≤ 1 + word.length := by
          simpa only [RationalVectorL1SemInvariant,
            rationalVectorL1SemStep] using hinv
        omega
      have hcode :
          (rawRatBinaryCode
            (acc.add (rawRatOfRat q).magnitude)).length ≤
              (machineRationalVectorL1InputBound word).length :=
        (rawRatBinaryCode_length_le_width _).trans
          ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnext) 4).trans
            (rationalVectorL1Bound_large word))
      rw [rationalVectorL1SemCode, rationalVectorL1SemStep,
        machineRationalVectorL1Step]
      simp only [machineRationalVectorL1Current_pack]
      rw [machineIfEmpty_of_ne_nil_matrix _ _ _
        (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
      simp only [machineRationalVectorL1Advance,
        machineRationalVectorL1Current_pack,
        machineRationalVectorL1Acc_pack,
        machineRationalVectorL1Bound_pack,
        machineListTail_cons, machineRationalVectorL1NextAcc,
        machineRationalVectorL1Candidate,
        machineRationalVectorL1Magnitude,
        machineRationalVectorL1Entry, machineListHead_cons]
      rw [← rawRatBinaryCode_rawRatOfRat q,
        machineRawRatMagnitudeCode_encode,
        machineRawRatAddCode_encode,
        (List.take_eq_self_iff _).mpr hcode]
      rfl

theorem machineRationalVectorL1Iterate_semantics
    (word : List Bool) (s : RationalVectorL1SemState)
    (hs : RationalVectorL1SemInvariant (1 + word.length) s) : ∀ k,
    (machineRationalVectorL1Step)^[k]
        (rationalVectorL1SemCode
          (machineRationalVectorL1InputBound word) s) =
      rationalVectorL1SemCode
        (machineRationalVectorL1InputBound word)
        ((rationalVectorL1SemStep)^[k] s) := by
  intro k
  have hinv : ∀ t : ℕ,
      RationalVectorL1SemInvariant (1 + word.length)
        ((rationalVectorL1SemStep)^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact rationalVectorL1SemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineRationalVectorL1Step_semantics word _ (hinv k)

theorem rationalVectorL1Sem_process : ∀ (xs : List ℚ) (acc : RawRat),
    (rationalVectorL1SemStep)^[xs.length] ⟨xs, acc⟩ =
      ⟨[], rawRatListL1Sum acc xs⟩ := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons q qs ih =>
      intro acc
      rw [List.length_cons, Function.iterate_succ_apply,
        rationalVectorL1SemStep, ih]
      rfl

theorem machineRationalVectorL1_done_iterate
    (extra : ℕ) (acc : RawRat) (bound : List Bool) :
    (machineRationalVectorL1Step)^[extra]
      (machineRationalVectorL1Pack [] (rawRatBinaryCode acc) bound) =
    machineRationalVectorL1Pack [] (rawRatBinaryCode acc) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalVectorL1Step]

theorem machineRationalVectorL1FinalState_encode {n : ℕ}
    (v : Fin n → ℚ) :
    let word := rationalFiniteVectorCode v
    machineRationalVectorL1FinalState word =
      machineRationalVectorL1Pack []
        (rawRatBinaryCode
          (rawRatListL1Sum RawRat.zero (List.ofFn v)))
        (machineRationalVectorL1InputBound word) := by
  let xs := List.ofFn v
  let word := rationalFiniteVectorCode v
  let s : RationalVectorL1SemState := ⟨xs, RawRat.zero⟩
  have hcode :
      (binaryListCode rationalEntryBinaryCode xs).length = word.length := by
    simp [word, xs, rationalFiniteVectorCode]
  have hinv : RationalVectorL1SemInvariant (1 + word.length) s := by
    simp only [RationalVectorL1SemInvariant, s, rawRatWidth_zero]
    have hcost := rawRatListCost_le_codeLength xs
    omega
  have hn : n ≤ word.length := by
    have hlist := list_length_le_binaryListCode_length
      rationalEntryBinaryCode xs
    simpa only [xs, List.length_ofFn, hcode] using hlist
  have hsplit : word.length = (word.length - n) + n := by omega
  have hinit : machineRationalVectorL1Init word =
      rationalVectorL1SemCode
        (machineRationalVectorL1InputBound word) s := by
    simp [machineRationalVectorL1Init, rationalVectorL1SemCode,
      s, word, xs, rationalFiniteVectorCode]
  have hprocess :
      (rationalVectorL1SemStep)^[n] s =
        ⟨[], rawRatListL1Sum RawRat.zero xs⟩ := by
    simpa [s, xs] using rationalVectorL1Sem_process xs RawRat.zero
  change machineRationalVectorL1FinalState word = _
  rw [machineRationalVectorL1FinalState, hsplit,
    Function.iterate_add_apply, hinit,
    machineRationalVectorL1Iterate_semantics word s hinv, hprocess]
  simp only [rationalVectorL1SemCode, binaryListCode]
  rw [machineRationalVectorL1_done_iterate]

@[simp] theorem machineRationalVectorL1RawCode_encode {n : ℕ}
    (v : Fin n → ℚ) :
    machineRationalVectorL1RawCode (rationalFiniteVectorCode v) =
      rawRatBinaryCode
        (rawRatListL1Sum RawRat.zero (List.ofFn v)) := by
  rw [machineRationalVectorL1RawCode,
    machineRationalVectorL1FinalState_encode]
  simp

theorem rawRatListL1Sum_value (acc : RawRat) : ∀ xs : List ℚ,
    (rawRatListL1Sum acc xs).value =
      acc.value + (xs.map abs).sum := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRatListL1Sum]
  | cons q qs ih =>
      rw [rawRatListL1Sum, ih]
      simp [RawRat.value_add, rawRatOfRat_value, add_assoc]

theorem rawRatListL1Sum_ofFn_value {n : ℕ} (v : Fin n → ℚ) :
    (rawRatListL1Sum RawRat.zero (List.ofFn v)).value =
      ∑ i, abs (v i) := by
  rw [rawRatListL1Sum_value, RawRat.value_zero, zero_add]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

@[simp] theorem machineRationalVectorL1EntryCode_encode {n : ℕ}
    (v : Fin n → ℚ) :
    machineRationalVectorL1EntryCode (rationalFiniteVectorCode v) =
      rationalEntryBinaryCode (cutL1Scale v) := by
  rw [machineRationalVectorL1EntryCode,
    machineRationalVectorL1RawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawRatListL1Sum_ofFn_value, cutL1Scale]

end BeyondBethe

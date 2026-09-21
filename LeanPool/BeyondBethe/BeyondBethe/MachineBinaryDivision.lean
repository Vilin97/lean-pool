/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryCompare
import LeanPool.BeyondBethe.BeyondBethe.BinaryLongDivision

/-!
# Polynomial-time binary long division

The machine reverses the little-endian dividend and performs the usual
most-significant-bit-first long-division recurrence.  Its state stores the
unread bits, the fixed divisor, quotient, and remainder.  All arithmetic and
tests are the previously verified `FP` bitstring routines.
-/

namespace BeyondBethe

open Complexity

def machineBinaryDivPack
    (remaining divisor quotient remainder : List Bool) : List Bool :=
  pair remaining (pair divisor (pair quotient remainder))

def machineBinaryDivRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineBinaryDivDivisor (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineBinaryDivQuotient (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineBinaryDivRemainder (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineBinaryDivDoubleQuotient (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineBinaryDivQuotient state)
      (machineBinaryDivQuotient state))

def machineBinaryDivDoubleRemainder (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineBinaryDivRemainder state)
      (machineBinaryDivRemainder state))

def machineBinaryDivTrial (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineBinaryDivRemaining state))
    (machineBinaryAddBits
      (pair (machineBinaryDivDoubleRemainder state) [true]))
    (machineBinaryDivDoubleRemainder state)

def machineBinaryDivTake (state : List Bool) : List Bool :=
  machineIfEmpty (machineBinaryDivDivisor state) [false]
    (machineBinaryNatLeBit
      (pair (machineBinaryDivDivisor state) (machineBinaryDivTrial state)))

def machineBinaryDivIncrementedQuotient (state : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineBinaryDivDoubleQuotient state) [true])

def machineBinaryDivNextQuotient (state : List Bool) : List Bool :=
  machineIfEmpty (machineBinaryDivDivisor state) []
    (machineIfHead (machineBinaryDivTake state)
      (machineBinaryDivIncrementedQuotient state)
      (machineBinaryDivDoubleQuotient state))

def machineBinaryDivNextRemainder (state : List Bool) : List Bool :=
  machineIfHead (machineBinaryDivTake state)
    (machineBinarySubBits
      (pair (machineBinaryDivTrial state) (machineBinaryDivDivisor state)))
    (machineBinaryDivTrial state)

def machineBinaryDivStep (state : List Bool) : List Bool :=
  machineBinaryDivPack (machineBinaryDivRemaining state).tail
    (machineBinaryDivDivisor state)
    (machineBinaryDivNextQuotient state)
    (machineBinaryDivNextRemainder state)

def machineBinaryDivInit (word : List Bool) : List Bool :=
  machineBinaryDivPack (machinePairFirst word).reverse
    (machinePairSecond word) [] []

def machineBinaryDivRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineBinaryDivWidth (word : List Bool) : List Bool :=
  let padded := List.replicate 16 false ++ word
  List.replicate (padded.length * padded.length) false

def machineBinaryDivFinalState (word : List Bool) : List Bool :=
  machineBinaryDivStep^[(machineBinaryDivRuler word).length]
    (machineBinaryDivInit word)

/-- Paired canonical quotient and remainder words. -/
def machineBinaryDivModBits (word : List Bool) : List Bool :=
  pair (machineBinaryDivQuotient (machineBinaryDivFinalState word))
    (machineBinaryDivRemainder (machineBinaryDivFinalState word))

theorem machineBinaryDivRemaining_mem_FP :
    machineBinaryDivRemaining ∈ Complexity.FP := by
  simpa only [machineBinaryDivRemaining] using machinePairFirst_mem_FP

theorem machineBinaryDivDivisor_mem_FP :
    machineBinaryDivDivisor ∈ Complexity.FP := by
  simpa only [machineBinaryDivDivisor] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBinaryDivQuotient_mem_FP :
    machineBinaryDivQuotient ∈ Complexity.FP := by
  have hsecond2 : (fun word => machinePairSecond (machinePairSecond word)) ∈
      Complexity.FP :=
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineBinaryDivQuotient] using
    machineCompose_mem_FP hsecond2 machinePairFirst_mem_FP

theorem machineBinaryDivRemainder_mem_FP :
    machineBinaryDivRemainder ∈ Complexity.FP := by
  have hsecond2 : (fun word => machinePairSecond (machinePairSecond word)) ∈
      Complexity.FP :=
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineBinaryDivRemainder] using
    machineCompose_mem_FP hsecond2 machinePairSecond_mem_FP

theorem machineBinaryDivPack_mem_FP
    {remaining divisor quotient remainder : List Bool → List Bool}
    (hremaining : remaining ∈ Complexity.FP)
    (hdivisor : divisor ∈ Complexity.FP)
    (hquotient : quotient ∈ Complexity.FP)
    (hremainder : remainder ∈ Complexity.FP) :
    (fun word => machineBinaryDivPack (remaining word) (divisor word)
      (quotient word) (remainder word)) ∈ Complexity.FP := by
  exact machinePair_mem_FP hremaining
    (machinePair_mem_FP hdivisor
      (machinePair_mem_FP hquotient hremainder))

theorem machineBinaryDivDoubleQuotient_mem_FP :
    machineBinaryDivDoubleQuotient ∈ Complexity.FP := by
  have hpair : (fun state => pair (machineBinaryDivQuotient state)
      (machineBinaryDivQuotient state)) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryDivQuotient_mem_FP
      machineBinaryDivQuotient_mem_FP
  simpa only [machineBinaryDivDoubleQuotient] using
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineBinaryDivDoubleRemainder_mem_FP :
    machineBinaryDivDoubleRemainder ∈ Complexity.FP := by
  have hpair : (fun state => pair (machineBinaryDivRemainder state)
      (machineBinaryDivRemainder state)) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryDivRemainder_mem_FP
      machineBinaryDivRemainder_mem_FP
  simpa only [machineBinaryDivDoubleRemainder] using
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineBinaryDivTrial_mem_FP :
    machineBinaryDivTrial ∈ Complexity.FP := by
  have hflag : (fun state => machineHeadBit
      (machineBinaryDivRemaining state)) ∈ Complexity.FP :=
    machineCompose_mem_FP machineBinaryDivRemaining_mem_FP
      machineHeadBit_mem_FP
  have hpair : (fun state => pair
      (machineBinaryDivDoubleRemainder state) [true]) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryDivDoubleRemainder_mem_FP
      (machineConst_mem_FP [true])
  have hone := machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP
  simpa only [machineBinaryDivTrial] using
    machineIfHead_mem_FP hflag hone machineBinaryDivDoubleRemainder_mem_FP

theorem machineBinaryDivTake_mem_FP :
    machineBinaryDivTake ∈ Complexity.FP := by
  have hpair : (fun state => pair (machineBinaryDivDivisor state)
      (machineBinaryDivTrial state)) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryDivDivisor_mem_FP
      machineBinaryDivTrial_mem_FP
  have hle := machineCompose_mem_FP hpair machineBinaryNatLeBit_mem_FP
  simpa only [machineBinaryDivTake] using
    machineIfEmpty_mem_FP machineBinaryDivDivisor_mem_FP
      (machineConst_mem_FP [false]) hle

theorem machineBinaryDivIncrementedQuotient_mem_FP :
    machineBinaryDivIncrementedQuotient ∈ Complexity.FP := by
  have hpair : (fun state => pair
      (machineBinaryDivDoubleQuotient state) [true]) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryDivDoubleQuotient_mem_FP
      (machineConst_mem_FP [true])
  simpa only [machineBinaryDivIncrementedQuotient] using
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineBinaryDivNextQuotient_mem_FP :
    machineBinaryDivNextQuotient ∈ Complexity.FP := by
  have hnonzero := machineIfHead_mem_FP machineBinaryDivTake_mem_FP
    machineBinaryDivIncrementedQuotient_mem_FP
    machineBinaryDivDoubleQuotient_mem_FP
  simpa only [machineBinaryDivNextQuotient] using
    machineIfEmpty_mem_FP machineBinaryDivDivisor_mem_FP
      (machineConst_mem_FP []) hnonzero

theorem machineBinaryDivNextRemainder_mem_FP :
    machineBinaryDivNextRemainder ∈ Complexity.FP := by
  have hpair : (fun state => pair (machineBinaryDivTrial state)
      (machineBinaryDivDivisor state)) ∈ Complexity.FP :=
    machinePair_mem_FP machineBinaryDivTrial_mem_FP
      machineBinaryDivDivisor_mem_FP
  have hsub := machineCompose_mem_FP hpair machineBinarySubBits_mem_FP
  simpa only [machineBinaryDivNextRemainder] using
    machineIfHead_mem_FP machineBinaryDivTake_mem_FP hsub
      machineBinaryDivTrial_mem_FP

theorem machineBinaryDivStep_mem_FP :
    machineBinaryDivStep ∈ Complexity.FP := by
  exact machineBinaryDivPack_mem_FP
    (machineCompose_mem_FP machineBinaryDivRemaining_mem_FP machineTail_mem_FP)
    machineBinaryDivDivisor_mem_FP machineBinaryDivNextQuotient_mem_FP
    machineBinaryDivNextRemainder_mem_FP

theorem machineBinaryDivInit_mem_FP :
    machineBinaryDivInit ∈ Complexity.FP := by
  have hreverse := machineCompose_mem_FP machinePairFirst_mem_FP
    machineReverse_mem_FP
  exact machineBinaryDivPack_mem_FP hreverse machinePairSecond_mem_FP
    (machineConst_mem_FP []) (machineConst_mem_FP [])

theorem machineBinaryDivRuler_mem_FP :
    machineBinaryDivRuler ∈ Complexity.FP := by
  simpa only [machineBinaryDivRuler] using machinePairFirst_mem_FP

theorem machineBinaryDivWidth_mem_FP :
    machineBinaryDivWidth ∈ Complexity.FP := by
  let padded : List Bool → List Bool :=
    fun word => List.replicate 16 false ++ word
  have hpadded : padded ∈ Complexity.FP :=
    machineAppend_mem_FP (machineConst_mem_FP (List.replicate 16 false))
      id_mem_FP
  simpa only [machineBinaryDivWidth, padded] using
    Cobham.mulLenFn_mem_FP hpadded hpadded

@[simp] theorem machineBinaryDivRemaining_pack (remaining divisor quotient remainder) :
    machineBinaryDivRemaining
      (machineBinaryDivPack remaining divisor quotient remainder) =
        remaining := by simp [machineBinaryDivRemaining, machineBinaryDivPack]

@[simp] theorem machineBinaryDivDivisor_pack (remaining divisor quotient remainder) :
    machineBinaryDivDivisor
      (machineBinaryDivPack remaining divisor quotient remainder) =
        divisor := by simp [machineBinaryDivDivisor, machineBinaryDivPack]

@[simp] theorem machineBinaryDivQuotient_pack (remaining divisor quotient remainder) :
    machineBinaryDivQuotient
      (machineBinaryDivPack remaining divisor quotient remainder) =
        quotient := by simp [machineBinaryDivQuotient, machineBinaryDivPack]

@[simp] theorem machineBinaryDivRemainder_pack (remaining divisor quotient remainder) :
    machineBinaryDivRemainder
      (machineBinaryDivPack remaining divisor quotient remainder) =
        remainder := by simp [machineBinaryDivRemainder, machineBinaryDivPack]

def MachineBinaryDivReachable
    (dividend divisor : List Bool) (iterations : ℕ)
    (state : List Bool) : Prop :=
  ∃ remaining quotient remainder,
    state = machineBinaryDivPack remaining divisor quotient remainder ∧
    remaining.length ≤ dividend.length ∧
    quotient.length ≤ 2 * iterations ∧
    remainder.length ≤ divisor.length + 2 * iterations

theorem machineIfEmpty_length_le_max (test whenEmpty whenNonempty : List Bool) :
    (machineIfEmpty test whenEmpty whenNonempty).length ≤
      max whenEmpty.length whenNonempty.length := by
  cases test with
  | nil => simp
  | cons bit tail => simp

theorem machineIfEmpty_of_ne_nil (test whenEmpty whenNonempty : List Bool)
    (htest : test ≠ []) :
    machineIfEmpty test whenEmpty whenNonempty = whenNonempty := by
  cases test with
  | nil => exact False.elim (htest rfl)
  | cons bit tail => simp

theorem machineIfHead_length_le_max (flag whenTrue whenFalse : List Bool) :
    (machineIfHead flag whenTrue whenFalse).length ≤
      max whenTrue.length whenFalse.length := by
  cases flag with
  | nil => simp [machineIfHead, Cobham.selectHead]
  | cons bit tail => cases bit <;> simp

theorem machineBinaryDivInit_reachable (word : List Bool) :
    MachineBinaryDivReachable (machinePairFirst word)
      (machinePairSecond word) 0 (machineBinaryDivInit word) := by
  refine ⟨(machinePairFirst word).reverse, [], [], rfl, ?_, by simp, by simp⟩
  simp

theorem machineBinaryDivDoubleQuotient_length_le
    (remaining divisor quotient remainder : List Bool) :
    (machineBinaryDivDoubleQuotient
      (machineBinaryDivPack remaining divisor quotient remainder)).length ≤
        quotient.length + 1 := by
  simp only [machineBinaryDivDoubleQuotient, machineBinaryDivQuotient_pack]
  simpa using machineBinaryAddBits_pair_length_le quotient quotient

theorem machineBinaryDivDoubleRemainder_length_le
    (remaining divisor quotient remainder : List Bool) :
    (machineBinaryDivDoubleRemainder
      (machineBinaryDivPack remaining divisor quotient remainder)).length ≤
        remainder.length + 1 := by
  simp only [machineBinaryDivDoubleRemainder, machineBinaryDivRemainder_pack]
  simpa using machineBinaryAddBits_pair_length_le remainder remainder

theorem machineBinaryDivTrial_length_le
    (remaining divisor quotient remainder : List Bool) :
    (machineBinaryDivTrial
      (machineBinaryDivPack remaining divisor quotient remainder)).length ≤
        remainder.length + 2 := by
  cases remaining with
  | nil =>
      simp [machineBinaryDivTrial]
      have h := machineBinaryDivDoubleRemainder_length_le
        [] divisor quotient remainder
      omega
  | cons bit remaining =>
      cases bit with
      | false =>
          simp [machineBinaryDivTrial]
          have h := machineBinaryDivDoubleRemainder_length_le
            (false :: remaining) divisor quotient remainder
          omega
      | true =>
          simp only [machineBinaryDivTrial, machineBinaryDivRemaining_pack,
            machineHeadBit_cons, machineIfHead_true]
          have hdouble := machineBinaryDivDoubleRemainder_length_le
            (true :: remaining) divisor quotient remainder
          have hadd := machineBinaryAddBits_pair_length_le
            (machineBinaryDivDoubleRemainder
              (machineBinaryDivPack (true :: remaining) divisor quotient remainder))
            [true]
          have hmax : max
              (machineBinaryDivDoubleRemainder
                (machineBinaryDivPack (true :: remaining) divisor quotient remainder)).length
              [true].length ≤ remainder.length + 1 := by
            apply max_le
            · exact hdouble
            · simp
          omega

theorem machineBinaryDivStep_reachable
    {dividend divisor : List Bool} {iterations : ℕ} {state : List Bool}
    (hstate : MachineBinaryDivReachable dividend divisor iterations state) :
    MachineBinaryDivReachable dividend divisor (iterations + 1)
      (machineBinaryDivStep state) := by
  obtain ⟨remaining, quotient, remainder, rfl, hremaining, hquotient,
    hremainder⟩ := hstate
  simp only [machineBinaryDivStep, machineBinaryDivRemaining_pack,
    machineBinaryDivDivisor_pack]
  refine ⟨remaining.tail,
    machineBinaryDivNextQuotient
      (machineBinaryDivPack remaining divisor quotient remainder),
    machineBinaryDivNextRemainder
      (machineBinaryDivPack remaining divisor quotient remainder),
    rfl, ?_, ?_, ?_⟩
  · have htail : remaining.tail.length ≤ remaining.length := by
      cases remaining <;> simp
    exact htail.trans hremaining
  · simp only [machineBinaryDivNextQuotient, machineBinaryDivDivisor_pack]
    have hdouble := machineBinaryDivDoubleQuotient_length_le
      remaining divisor quotient remainder
    have hinc := machineBinaryAddBits_pair_length_le
      (machineBinaryDivDoubleQuotient
        (machineBinaryDivPack remaining divisor quotient remainder)) [true]
    have hmaxDouble : max
        (machineBinaryDivDoubleQuotient
          (machineBinaryDivPack remaining divisor quotient remainder)).length
        [true].length ≤ quotient.length + 1 := by
      apply max_le
      · exact hdouble
      · simp
    have hinc' :
        (machineBinaryDivIncrementedQuotient
          (machineBinaryDivPack remaining divisor quotient remainder)).length ≤
          quotient.length + 2 := by
      simpa only [machineBinaryDivIncrementedQuotient] using
        hinc.trans (Nat.add_le_add_right hmaxDouble 1)
    have hnonzero := machineIfHead_length_le_max
      (machineBinaryDivTake
        (machineBinaryDivPack remaining divisor quotient remainder))
      (machineBinaryDivIncrementedQuotient
        (machineBinaryDivPack remaining divisor quotient remainder))
      (machineBinaryDivDoubleQuotient
        (machineBinaryDivPack remaining divisor quotient remainder))
    have houter := machineIfEmpty_length_le_max divisor []
      (machineIfHead
        (machineBinaryDivTake
          (machineBinaryDivPack remaining divisor quotient remainder))
        (machineBinaryDivIncrementedQuotient
          (machineBinaryDivPack remaining divisor quotient remainder))
        (machineBinaryDivDoubleQuotient
          (machineBinaryDivPack remaining divisor quotient remainder)))
    simp only [List.length_nil, zero_le, max_eq_right] at houter
    omega
  · simp only [machineBinaryDivNextRemainder, machineBinaryDivDivisor_pack]
    have htrial := machineBinaryDivTrial_length_le
      remaining divisor quotient remainder
    have hsub := machineBinarySubBits_pair_length_le
      (machineBinaryDivTrial
        (machineBinaryDivPack remaining divisor quotient remainder)) divisor
    have hsub' :
        (machineBinarySubBits
          (pair (machineBinaryDivTrial
            (machineBinaryDivPack remaining divisor quotient remainder))
            divisor)).length ≤ divisor.length + 2 * (iterations + 1) := by
      apply hsub.trans
      apply max_le
      · omega
      · omega
    have hselect := machineIfHead_length_le_max
      (machineBinaryDivTake
        (machineBinaryDivPack remaining divisor quotient remainder))
      (machineBinarySubBits
        (pair (machineBinaryDivTrial
          (machineBinaryDivPack remaining divisor quotient remainder)) divisor))
      (machineBinaryDivTrial
        (machineBinaryDivPack remaining divisor quotient remainder))
    have htrial' :
        (machineBinaryDivTrial
          (machineBinaryDivPack remaining divisor quotient remainder)).length ≤
          divisor.length + 2 * (iterations + 1) := by omega
    exact hselect.trans (max_le hsub' htrial')

theorem machineBinaryDivIterate_reachable (word : List Bool) :
    ∀ iterations,
      MachineBinaryDivReachable (machinePairFirst word)
        (machinePairSecond word) iterations
        (machineBinaryDivStep^[iterations] (machineBinaryDivInit word)) := by
  intro iterations
  induction iterations with
  | zero => exact machineBinaryDivInit_reachable word
  | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.succ_eq_add_one] using machineBinaryDivStep_reachable ih

theorem machineBinaryDivIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (machineBinaryDivRuler word).length) :
    (machineBinaryDivStep^[iterations]
      (machineBinaryDivInit word)).length ≤
        (machineBinaryDivWidth word).length := by
  obtain ⟨remaining, quotient, remainder, hstate, hremaining,
    hquotient, hremainder⟩ := machineBinaryDivIterate_reachable word iterations
  rw [hstate]
  have hdividend := machinePairFirst_length_le word
  have hdivisor := machinePairSecond_length_le word
  have hit : iterations ≤ word.length := hiterations.trans hdividend
  simp only [machineBinaryDivPack, pair_length, machineBinaryDivWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineBinaryDivFinalState_mem_FP :
    machineBinaryDivFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBinaryDivStep_mem_FP
    machineBinaryDivInit_mem_FP machineBinaryDivRuler_mem_FP
    machineBinaryDivWidth_mem_FP machineBinaryDivIterate_length_le_width

theorem machineBinaryDivModBits_mem_FP :
    machineBinaryDivModBits ∈ Complexity.FP := by
  have hquotient := machineCompose_mem_FP machineBinaryDivFinalState_mem_FP
    machineBinaryDivQuotient_mem_FP
  have hremainder := machineCompose_mem_FP machineBinaryDivFinalState_mem_FP
    machineBinaryDivRemainder_mem_FP
  simpa only [machineBinaryDivModBits] using
    machinePair_mem_FP hquotient hremainder

/-- Forward form of the semantic recurrence, on most-significant-first bits. -/
def binaryLongDivForward (divisor : ℕ) :
    List Bool → ℕ × ℕ → ℕ × ℕ
  | [], qr => qr
  | bit :: remaining, qr =>
      binaryLongDivForward divisor remaining
        (binaryLongDivStep divisor bit qr)

theorem binaryLongDivForward_append (divisor : ℕ)
    (first second : List Bool) (qr : ℕ × ℕ) :
    binaryLongDivForward divisor (first ++ second) qr =
      binaryLongDivForward divisor second
        (binaryLongDivForward divisor first qr) := by
  induction first generalizing qr with
  | nil => rfl
  | cons bit remaining ih =>
      simp only [List.cons_append, binaryLongDivForward]
      exact ih (binaryLongDivStep divisor bit qr)

theorem binaryLongDivForward_reverse (divisor : ℕ) (bits : List Bool) :
    binaryLongDivForward divisor bits.reverse (0, 0) =
      binaryLongDivBits divisor bits := by
  induction bits with
  | nil => rfl
  | cons bit remaining ih =>
      rw [List.reverse_cons, binaryLongDivForward_append]
      simp only [binaryLongDivForward]
      rw [ih]
      rfl

theorem natBits_ne_nil_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.bits ≠ [] := by
  intro hbits
  have hlen : n.bits.length = 0 := by simp [hbits]
  have hsize : n.size = 0 := by
    simpa only [Nat.size_eq_bits_len] using hlen
  exact hn (Nat.size_eq_zero.mp hsize)

@[simp] theorem machineBinaryDivDoubleQuotient_pack_natBits
    (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivDoubleQuotient
        (machineBinaryDivPack remaining divisor.bits quotient.bits remainder.bits) =
      (quotient + quotient).bits := by
  simp only [machineBinaryDivDoubleQuotient, machineBinaryDivQuotient_pack]
  exact machineBinaryAddBits_pair_natBits quotient quotient

@[simp] theorem machineBinaryDivDoubleRemainder_pack_natBits
    (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivDoubleRemainder
        (machineBinaryDivPack remaining divisor.bits quotient.bits remainder.bits) =
      (remainder + remainder).bits := by
  simp only [machineBinaryDivDoubleRemainder, machineBinaryDivRemainder_pack]
  exact machineBinaryAddBits_pair_natBits remainder remainder

@[simp] theorem machineBinaryDivTrial_pack_natBits
    (bit : Bool) (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivTrial
        (machineBinaryDivPack (bit :: remaining) divisor.bits
          quotient.bits remainder.bits) =
      (remainder + remainder + bitValue bit).bits := by
  cases bit with
  | false => simp [machineBinaryDivTrial, bitValue]
  | true =>
      simp only [machineBinaryDivTrial, machineBinaryDivRemaining_pack,
        machineHeadBit_cons, machineIfHead_true,
        machineBinaryDivDoubleRemainder_pack_natBits, bitValue]
      simpa using machineBinaryAddBits_pair_natBits (remainder + remainder) 1

@[simp] theorem machineBinaryDivTake_pack_natBits
    (bit : Bool) (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivTake
        (machineBinaryDivPack (bit :: remaining) divisor.bits
          quotient.bits remainder.bits) =
      if divisor = 0 then [false]
      else [(divisor ≤ remainder + remainder + bitValue bit)] := by
  by_cases hdivisor : divisor = 0
  · subst divisor
    simp [machineBinaryDivTake]
  · simp only [machineBinaryDivTake, machineBinaryDivDivisor_pack,
      machineBinaryDivTrial_pack_natBits]
    rw [machineIfEmpty_of_ne_nil divisor.bits [false]
      (machineBinaryNatLeBit
        (pair divisor.bits
          (remainder + remainder + bitValue bit).bits))
      (natBits_ne_nil_of_ne_zero hdivisor)]
    rw [machineBinaryNatLeBit_pair_natBits]
    simp [hdivisor]

@[simp] theorem machineBinaryDivIncrementedQuotient_pack_natBits
    (bit : Bool) (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivIncrementedQuotient
        (machineBinaryDivPack (bit :: remaining) divisor.bits
          quotient.bits remainder.bits) =
      (quotient + quotient + 1).bits := by
  simp only [machineBinaryDivIncrementedQuotient,
    machineBinaryDivDoubleQuotient_pack_natBits]
  simpa using machineBinaryAddBits_pair_natBits (quotient + quotient) 1

@[simp] theorem machineBinaryDivNextQuotient_pack_natBits
    (bit : Bool) (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivNextQuotient
        (machineBinaryDivPack (bit :: remaining) divisor.bits
          quotient.bits remainder.bits) =
      if divisor = 0 then []
      else if divisor ≤ remainder + remainder + bitValue bit then
        (quotient + quotient + 1).bits
      else (quotient + quotient).bits := by
  by_cases hdivisor : divisor = 0
  · subst divisor
    simp [machineBinaryDivNextQuotient]
  · simp only [machineBinaryDivNextQuotient, machineBinaryDivDivisor_pack]
    rw [machineIfEmpty_of_ne_nil divisor.bits []
      (machineIfHead
        (machineBinaryDivTake
          (machineBinaryDivPack (bit :: remaining) divisor.bits
            quotient.bits remainder.bits))
        (machineBinaryDivIncrementedQuotient
          (machineBinaryDivPack (bit :: remaining) divisor.bits
            quotient.bits remainder.bits))
        (machineBinaryDivDoubleQuotient
          (machineBinaryDivPack (bit :: remaining) divisor.bits
            quotient.bits remainder.bits)))
      (natBits_ne_nil_of_ne_zero hdivisor)]
    by_cases htake : divisor ≤ remainder + remainder + bitValue bit
    · simp [hdivisor, htake]
    · simp [hdivisor, htake]

@[simp] theorem machineBinaryDivNextRemainder_pack_natBits
    (bit : Bool) (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivNextRemainder
        (machineBinaryDivPack (bit :: remaining) divisor.bits
          quotient.bits remainder.bits) =
      if divisor = 0 then
        (remainder + remainder + bitValue bit).bits
      else if divisor ≤ remainder + remainder + bitValue bit then
        (remainder + remainder + bitValue bit - divisor).bits
      else (remainder + remainder + bitValue bit).bits := by
  rw [machineBinaryDivNextRemainder,
    machineBinaryDivTake_pack_natBits,
    machineBinaryDivTrial_pack_natBits]
  by_cases hdivisor : divisor = 0
  · simp [hdivisor]
  · by_cases htake : divisor ≤ remainder + remainder + bitValue bit
    · simp only [hdivisor, ite_false]
      simp only [htake, decide_true, machineIfHead_true,
        machineBinaryDivDivisor_pack, if_true]
      rw [machineBinarySubBits_pair_natBits]
    · simp [hdivisor, htake]

theorem machineBinaryDivStep_pack_natBits
    (bit : Bool) (remaining : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivStep
        (machineBinaryDivPack (bit :: remaining) divisor.bits
          quotient.bits remainder.bits) =
      let next := binaryLongDivStep divisor bit (quotient, remainder)
      machineBinaryDivPack remaining divisor.bits next.1.bits next.2.bits := by
  simp only [machineBinaryDivStep, machineBinaryDivRemaining_pack,
    machineBinaryDivDivisor_pack, List.tail_cons,
    machineBinaryDivNextQuotient_pack_natBits,
    machineBinaryDivNextRemainder_pack_natBits]
  by_cases hdivisor : divisor = 0
  · simp [binaryLongDivStep, hdivisor, two_mul]
  · by_cases htake : divisor ≤ remainder + remainder + bitValue bit
    · simp [binaryLongDivStep, hdivisor, htake, two_mul]
    · simp [binaryLongDivStep, hdivisor, htake, two_mul]

theorem machineBinaryDivIterate_natBits
    (bits : List Bool) (divisor quotient remainder : ℕ) :
    machineBinaryDivStep^[bits.length]
        (machineBinaryDivPack bits divisor.bits quotient.bits remainder.bits) =
      let final := binaryLongDivForward divisor bits (quotient, remainder)
      machineBinaryDivPack [] divisor.bits final.1.bits final.2.bits := by
  induction bits generalizing quotient remainder with
  | nil => rfl
  | cons bit remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        machineBinaryDivStep_pack_natBits]
      let next := binaryLongDivStep divisor bit (quotient, remainder)
      simpa only [binaryLongDivForward] using ih next.1 next.2

/-- Exact quotient/remainder correctness, including the zero-divisor
convention inherited from `Nat.div` and `Nat.mod`. -/
theorem machineBinaryDivModBits_pair_natBits (dividend divisor : ℕ) :
    machineBinaryDivModBits (pair dividend.bits divisor.bits) =
      pair (dividend / divisor).bits (dividend % divisor).bits := by
  simp only [machineBinaryDivModBits, machineBinaryDivFinalState,
    machineBinaryDivRuler, machineBinaryDivInit, machinePairFirst_pair,
    machinePairSecond_pair]
  rw [← @List.length_reverse Bool dividend.bits]
  change pair
      (machineBinaryDivQuotient
        (machineBinaryDivStep^[dividend.bits.reverse.length]
          (machineBinaryDivPack dividend.bits.reverse divisor.bits
            (0 : ℕ).bits (0 : ℕ).bits)))
      (machineBinaryDivRemainder
        (machineBinaryDivStep^[dividend.bits.reverse.length]
          (machineBinaryDivPack dividend.bits.reverse divisor.bits
            (0 : ℕ).bits (0 : ℕ).bits))) = _
  rw [machineBinaryDivIterate_natBits dividend.bits.reverse divisor 0 0]
  simp only [machineBinaryDivQuotient_pack, machineBinaryDivRemainder_pack]
  rw [binaryLongDivForward_reverse, binaryLongDivBits_eq_div_mod]
  simp only [Prod.fst, Prod.snd, Nat.fromBitsLE_bits]

end BeyondBethe

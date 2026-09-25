/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedAffineGradientEntry
public import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryGridGenerator

/-!
# Finite-word directed affine-gradient vectors

This file instantiates the reusable unary grid generator with the verified
four-corner gradient entry.  It also proves an explicit ordinary-binary size
bound for the complete `m^2`-coordinate vector, so the generator's totalizing
accumulator clamp is inactive on every canonical input.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineDirectedAffineGradientEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineDirectedAffineGradientEntryRawCode word)

theorem machineDirectedAffineGradientEntryCode_mem_FP :
    machineDirectedAffineGradientEntryCode ∈ FP := by
  simpa only [machineDirectedAffineGradientEntryCode] using!
    machineCompose_mem_FP machineDirectedAffineGradientEntryRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

@[simp] theorem machineDirectedAffineGradientEntryCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientEntryCode
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      rationalEntryBinaryCode
        (affinePullbackGradient
          (directedNegativeGradientLowerMatrix tau A
            (betheAffineMatrixQ y) p) a b) := by
  rw [machineDirectedAffineGradientEntryCode,
    machineDirectedAffineGradientEntryRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawDirectedAffineGradientEntry_value]

def machineDirectedAffineGradientVectorBound (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 6 word

def machineDirectedAffineGradientVectorGeneratorInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedObjectiveSumDimension word)
    (pair (machineDirectedAffineGradientVectorBound word) word)

def machineDirectedAffineGradientVectorCode (word : List Bool) : List Bool :=
  machineUnaryGridGeneratorCode machineDirectedAffineGradientEntryCode
    (machineDirectedAffineGradientVectorGeneratorInput word)

theorem machineDirectedAffineGradientVectorBound_mem_FP :
    machineDirectedAffineGradientVectorBound ∈ FP :=
  machineIteratedBinaryWidth_mem_FP 6

theorem machineDirectedAffineGradientVectorGeneratorInput_mem_FP :
    machineDirectedAffineGradientVectorGeneratorInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumDimension_mem_FP
    (machinePair_mem_FP machineDirectedAffineGradientVectorBound_mem_FP
      id_mem_FP)

theorem machineDirectedAffineGradientVectorCode_mem_FP :
    machineDirectedAffineGradientVectorCode ∈ FP := by
  have hgenerator := machineUnaryGridGeneratorCode_mem_FP
    machineDirectedAffineGradientEntryCode_mem_FP
  simpa only [machineDirectedAffineGradientVectorCode] using!
    machineCompose_mem_FP
      machineDirectedAffineGradientVectorGeneratorInput_mem_FP hgenerator

def directedAffineGradientVector {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) : Fin (m * m) → ℚ :=
  squareMatrixToVector
    (affinePullbackGradient
      (directedNegativeGradientLowerMatrix tau A
        (betheAffineMatrixQ y) p))

def rawDirectedGradientCoordinateWidthBudget
    (tau a x : ℚ) (p : ℕ) : ℕ :=
  2 * rawRatWidth (rawRatOfRat tau) +
    rawRatWidth (rawScheduledLogUpper a p) +
    rawRatWidth (rawScheduledLogLower x p) +
    rawRatWidth (rawScheduledLogLower (1 - x) p) + 9

theorem rawDirectedNegativeGradientLower_width_le
    (tau a x : ℚ) (p : ℕ) :
    rawRatWidth (rawDirectedNegativeGradientLower tau a x p) ≤
      rawDirectedGradientCoordinateWidthBudget tau a x p := by
  let rawTau := rawRatOfRat tau
  let logA := rawScheduledLogUpper a p
  let logX := rawScheduledLogLower x p
  let logComplement := rawScheduledLogLower (1 - x) p
  have hone : rawRatWidth RawRat.one = 1 := rawRatWidth_one
  have honeTau := rawRatWidth_add_le RawRat.one rawTau
  rw [hone] at honeTau
  have hscaled := rawRatWidth_mul_le (RawRat.one.add rawTau) logX
  have hnegA : rawRatWidth logA.neg = rawRatWidth logA :=
    rawRatWidth_neg logA
  have hfirst := rawRatWidth_add_le logA.neg
    ((RawRat.one.add rawTau).mul logX)
  rw [hnegA] at hfirst
  have hthree := rawRatWidth_add_le
    (logA.neg.add ((RawRat.one.add rawTau).mul logX)) logComplement
  have htwoTauInner := rawRatWidth_add_le RawRat.one rawTau
  rw [hone] at htwoTauInner
  have htwoTau := rawRatWidth_add_le RawRat.one
    (RawRat.one.add rawTau)
  rw [hone] at htwoTau
  have htotal := rawRatWidth_add_le
    ((logA.neg.add ((RawRat.one.add rawTau).mul logX)).add logComplement)
    (RawRat.one.add (RawRat.one.add rawTau))
  have honeTau' : rawRatWidth (RawRat.one.add rawTau) ≤
      rawRatWidth rawTau + 2 := by omega
  have hscaled' :
      rawRatWidth ((RawRat.one.add rawTau).mul logX) ≤
        rawRatWidth rawTau + rawRatWidth logX + 2 := by omega
  have hfirst' :
      rawRatWidth (logA.neg.add
        ((RawRat.one.add rawTau).mul logX)) ≤
        rawRatWidth logA + rawRatWidth rawTau +
          rawRatWidth logX + 3 := by omega
  have hthree' :
      rawRatWidth
        ((logA.neg.add ((RawRat.one.add rawTau).mul logX)).add
          logComplement) ≤
        rawRatWidth logA + rawRatWidth rawTau +
          rawRatWidth logX + rawRatWidth logComplement + 4 := by
    omega
  have htwoTau' :
      rawRatWidth (RawRat.one.add (RawRat.one.add rawTau)) ≤
        rawRatWidth rawTau + 4 := by omega
  have htotal' :
      rawRatWidth
        (((logA.neg.add ((RawRat.one.add rawTau).mul logX)).add
          logComplement).add
            (RawRat.one.add (RawRat.one.add rawTau))) ≤
        2 * rawRatWidth rawTau + rawRatWidth logA +
          rawRatWidth logX + rawRatWidth logComplement + 9 := by
    omega
  simp only [rawDirectedGradientCoordinateWidthBudget]
  simpa only [rawDirectedNegativeGradientLower, rawTau, logA, logX,
    logComplement] using! htotal'

theorem rawDirectedNegativeGradientEntry_width_le_word_budget {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    rawRatWidth
        (rawDirectedNegativeGradientLower tau (A i j)
          (betheAffineMatrixQ y i j) p) ≤
      rawDirectedObjectiveCoordinateWordBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  let x := betheAffineMatrixQ y i j
  let WX := rawDirectedObjectiveCoordinateWordXBudget m L
  let WC := rawDirectedObjectiveCoordinateWordComplementBudget m L
  have hp : p ≤ L := directedObjectiveSum_precision_le_word tau A y p
  have htau : rawRatWidth (rawRatOfRat tau) ≤ L :=
    rawDirectedObjectiveSum_tau_width_le_word tau A y p
  have ha : rawRatWidth (rawRatOfRat (A i j)) ≤ L :=
    rawDirectedObjectiveSum_A_width_le_word tau A y p i j
  have hx : rawRatWidth (rawRatOfRat x) ≤ WX := by
    simpa only [x, WX, L,
      rawDirectedObjectiveCoordinateWordXBudget] using!
      rawBetheAffineMatrixQ_width_le_word tau A y p i j
  have hc0 := rawRatWidth_complement_le x
  have hc : rawRatWidth (rawRatOfRat (1 - x)) ≤ WC := by
    simp only [WC, rawDirectedObjectiveCoordinateWordComplementBudget]
    omega
  have hlogA := rawRatWidth_scheduledLogUpper_of_bounds_le
    (A i j) hp ha
  have hlogX := rawRatWidth_scheduledLogLower_of_bounds_le x hp hx
  have hlogC := rawRatWidth_scheduledLogLower_of_bounds_le (1 - x) hp hc
  have hraw := rawDirectedNegativeGradientLower_width_le tau (A i j) x p
  simp only [rawDirectedGradientCoordinateWidthBudget] at hraw
  have hLX : L + 116 ≤ WX := by
    simp only [WX, rawDirectedObjectiveCoordinateWordXBudget,
      rawBetheAffineEntryWidthBudget]
    omega
  have hfinal :
      rawRatWidth
          (rawDirectedNegativeGradientLower tau (A i j) x p) ≤
        2 * WX + L + WC +
          rawScheduledLogWordBudget L L +
          rawScheduledLogWordBudget L WX +
          rawScheduledLogWordBudget L WC + 4 := by
    simp only [rawScheduledLogWordBudget]
    omega
  simp only [rawDirectedObjectiveCoordinateWordBudget]
  exact hfinal

theorem rawDirectedAffineGradientEntry_width_le_word_budget {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    rawRatWidth (rawDirectedAffineGradientEntry tau A y p a b) ≤
      4 * rawDirectedObjectiveCoordinateWordBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length + 3 := by
  let G := fun i j => rawDirectedNegativeGradientLower tau (A i j)
    (betheAffineMatrixQ y i j) p
  let B := rawDirectedObjectiveCoordinateWordBudget m
    (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  have h₁ : rawRatWidth (G a.castSucc b.castSucc) ≤ B :=
    rawDirectedNegativeGradientEntry_width_le_word_budget tau A y p _ _
  have h₂ : rawRatWidth (G a.castSucc (Fin.last m)) ≤ B :=
    rawDirectedNegativeGradientEntry_width_le_word_budget tau A y p _ _
  have h₃ : rawRatWidth (G (Fin.last m) b.castSucc) ≤ B :=
    rawDirectedNegativeGradientEntry_width_le_word_budget tau A y p _ _
  have h₄ : rawRatWidth (G (Fin.last m) (Fin.last m)) ≤ B :=
    rawDirectedNegativeGradientEntry_width_le_word_budget tau A y p _ _
  have hsubOne := rawRatWidth_sub_le
    (G a.castSucc b.castSucc) (G a.castSucc (Fin.last m))
  have hsubTwo := rawRatWidth_sub_le
    ((G a.castSucc b.castSucc).sub (G a.castSucc (Fin.last m)))
    (G (Fin.last m) b.castSucc)
  have hadd := rawRatWidth_add_le
    (((G a.castSucc b.castSucc).sub (G a.castSucc (Fin.last m))).sub
      (G (Fin.last m) b.castSucc))
    (G (Fin.last m) (Fin.last m))
  simpa only [rawDirectedAffineGradientEntry, G, B] using! hadd.trans (by omega)

theorem directedAffineGradient_entry_code_length_le {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    (rationalEntryBinaryCode
      (affinePullbackGradient
        (directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p) a b)).length ≤
      172 + 144 * rawDirectedObjectiveCoordinateWordBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let raw := rawDirectedAffineGradientEntry tau A y p a b
  have hcanonical := rationalEntryBinaryCode_binaryNormalizeRawRat_length_le raw
  rw [binaryNormalizeRawRat_eq_value,
    rawDirectedAffineGradientEntry_value] at hcanonical
  have hraw := rawDirectedAffineGradientEntry_width_le_word_budget
    tau A y p a b
  calc
    _ ≤ 64 + 36 * rawRatWidth raw := hcanonical
    _ ≤ 64 + 36 *
        (4 * rawDirectedObjectiveCoordinateWordBudget m
          (machineDirectedObjectiveSumCanonicalWord tau A y p).length + 3) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 36 hraw) 64
    _ = 172 + 144 * rawDirectedObjectiveCoordinateWordBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by ring

theorem directedAffineGradient_vector_code_length_le_bound {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    (rationalFiniteVectorCode
      (directedAffineGradientVector tau A y p)).length ≤
      (machineDirectedAffineGradientVectorBound
        (machineDirectedObjectiveSumCanonicalWord tau A y p)).length := by
  let word := machineDirectedObjectiveSumCanonicalWord tau A y p
  let L := word.length
  let T := L + 16
  let B := rawDirectedObjectiveCoordinateWordBudget m L
  let E := 172 + 144 * B
  have hmL : m ≤ L := by
    simp only [L, word, machineDirectedObjectiveSumCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have hB : B ≤ T ^ 20 := by
    simpa only [B, T] using!
      rawDirectedObjectiveCoordinateWordBudget_le_pow hmL
  have hE : E ≤ 316 * T ^ 20 := by
    have hpow : 1 ≤ T ^ 20 := one_le_pow₀ (by simp [T])
    dsimp only [E]
    omega
  have heach : ∀ q ∈ List.ofFn (directedAffineGradientVector tau A y p),
      (rationalEntryBinaryCode q).length ≤ E := by
    intro q hq
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
    let ij := finProdFinEquiv.symm k
    simpa only [directedAffineGradientVector, squareMatrixToVector, ij, E,
      B, L, word] using!
      directedAffineGradient_entry_code_length_le tau A y p ij.1 ij.2
  have hsum := List.sum_le_card_nsmul
    ((List.ofFn (directedAffineGradientVector tau A y p)).map
      fun q => 2 * (rationalEntryBinaryCode q).length + 2)
    (2 * E + 2) (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      have hq' := heach q hq
      omega)
  have hmT : m ≤ T := hmL.trans (by simp [T])
  have hlenCoarse :
      (rationalFiniteVectorCode
        (directedAffineGradientVector tau A y p)).length ≤
        634 * T ^ 22 := by
    rw [rationalFiniteVectorCode, binaryListCode_length_eq_sum]
    simp only [List.length_map, List.length_ofFn, Nat.nsmul_eq_mul] at hsum
    have hmm := Nat.mul_le_mul hmT hmT
    have hfactor : 2 * E + 2 ≤ 634 * T ^ 20 := by
      have hpow : 1 ≤ T ^ 20 := one_le_pow₀ (by simp [T])
      omega
    have hmul := Nat.mul_le_mul hmm hfactor
    calc
      _ ≤ m * m * (2 * E + 2) := hsum
      _ ≤ T * T * (634 * T ^ 20) := hmul
      _ = 634 * T ^ 22 := by ring
  have hcoeff : 634 ≤ T ^ 42 := by
    have hbase : 16 ≤ T := by simp [T]
    have hpow := Nat.pow_le_pow_left hbase 42
    exact (by norm_num : 634 ≤ 16 ^ 42).trans hpow
  have hmul := Nat.mul_le_mul_right (T ^ 22) hcoeff
  have hpower :
      (rationalFiniteVectorCode
        (directedAffineGradientVector tau A y p)).length ≤ T ^ 64 := by
    calc
      _ ≤ 634 * T ^ 22 := hlenCoarse
      _ ≤ T ^ 42 * T ^ 22 := hmul
      _ = T ^ 64 := by ring
  rw [machineDirectedAffineGradientVectorBound,
    machineIteratedBinaryWidth_length]
  exact hpower.trans (by
    simpa only [T, L, word] using!
      certificateExpGuardWidth_pow_lower 5
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length)

theorem unaryGridValues_directedAffineGradient {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    unaryGridValues
        (fun a b => affinePullbackGradient
          (directedNegativeGradientLowerMatrix tau A
            (betheAffineMatrixQ y) p) a b) =
      List.ofFn (directedAffineGradientVector tau A y p) := by
  rfl

@[simp] theorem machineDirectedAffineGradientVectorCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedAffineGradientVectorCode
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rationalFiniteVectorCode (directedAffineGradientVector tau A y p) := by
  let payload := machineDirectedObjectiveSumCanonicalWord tau A y p
  let bound := machineDirectedAffineGradientVectorBound payload
  let f := fun a b => affinePullbackGradient
    (directedNegativeGradientLowerMatrix tau A
      (betheAffineMatrixQ y) p) a b
  have hinput : machineDirectedAffineGradientVectorGeneratorInput payload =
      machineUnaryGridGeneratorCanonicalWord m bound payload := by
    simp [machineDirectedAffineGradientVectorGeneratorInput, payload, bound,
      machineUnaryGridGeneratorCanonicalWord]
  rw [machineDirectedAffineGradientVectorCode, hinput]
  have hentry : ∀ a b,
      machineDirectedAffineGradientEntryCode
          (pair (List.replicate a.1 true)
            (pair (List.replicate b.1 true) payload)) =
        rationalEntryBinaryCode (f a b) := by
    intro a b
    simpa only [payload, f,
      machineDirectedAffineGradientEntryCanonicalWord] using!
      machineDirectedAffineGradientEntryCode_encode tau A y p a b
  have hbound :
      (binaryListCode rationalEntryBinaryCode (unaryGridValues f)).length ≤
        bound.length := by
    rw [unaryGridValues_directedAffineGradient]
    simpa only [rationalFiniteVectorCode, f, bound, payload] using!
      directedAffineGradient_vector_code_length_le_bound tau A y p
  rw [machineUnaryGridGeneratorCode_encode_of_bound
    machineDirectedAffineGradientEntryCode f bound payload hentry hbound,
    unaryGridValues_directedAffineGradient]
  rfl

end BeyondBethe

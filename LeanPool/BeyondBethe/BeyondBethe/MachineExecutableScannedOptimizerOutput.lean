/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.ExecutableScannedBetheOptimizer
public import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryMatrixGenerator
public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerMatrixBitBound
public import LeanPool.BeyondBethe.BeyondBethe.OptimizerOutputEncoding

/-!
# Finite-word output of the executable scanned optimizer

This file turns the accepted epigraph point into the canonical matrix and
potential words consumed by the certificate evaluator.  The first stage is
the complete recovered Birkhoff matrix.  Its entries are generated directly
in row-major order and normalized before being inserted into the nested row
encoding.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## A normalized recovered-matrix entry -/

def machineExecutableMatrixEntryRow (word : List Bool) : List Bool :=
  machinePairFirst word

def machineExecutableMatrixEntryRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineExecutableMatrixEntryColumn (word : List Bool) : List Bool :=
  machinePairFirst (machineExecutableMatrixEntryRest word)

def machineExecutableMatrixEntryPayload (word : List Bool) : List Bool :=
  machinePairSecond (machineExecutableMatrixEntryRest word)

def machineExecutableMatrixEntryBaseDimension
    (word : List Bool) : List Bool :=
  machinePairFirst (machineExecutableMatrixEntryPayload word)

def machineExecutableMatrixEntryPoint (word : List Bool) : List Bool :=
  machinePairSecond (machineExecutableMatrixEntryPayload word)

def machineExecutableMatrixEntryRawInput (word : List Bool) : List Bool :=
  pair (machineExecutableMatrixEntryBaseDimension word)
    (pair (machineExecutableMatrixEntryRow word)
      (pair (machineExecutableMatrixEntryColumn word)
        (machineExecutableMatrixEntryPoint word)))

def machineExecutableMatrixEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineBetheAffineEntryRawCode
      (machineExecutableMatrixEntryRawInput word))

theorem machineExecutableMatrixEntryRow_mem_FP :
    machineExecutableMatrixEntryRow ∈ FP := machinePairFirst_mem_FP

theorem machineExecutableMatrixEntryRest_mem_FP :
    machineExecutableMatrixEntryRest ∈ FP := machinePairSecond_mem_FP

theorem machineExecutableMatrixEntryColumn_mem_FP :
    machineExecutableMatrixEntryColumn ∈ FP := by
  simpa only [machineExecutableMatrixEntryColumn] using!
    machineCompose_mem_FP machineExecutableMatrixEntryRest_mem_FP
      machinePairFirst_mem_FP

theorem machineExecutableMatrixEntryPayload_mem_FP :
    machineExecutableMatrixEntryPayload ∈ FP := by
  simpa only [machineExecutableMatrixEntryPayload] using!
    machineCompose_mem_FP machineExecutableMatrixEntryRest_mem_FP
      machinePairSecond_mem_FP

theorem machineExecutableMatrixEntryBaseDimension_mem_FP :
    machineExecutableMatrixEntryBaseDimension ∈ FP := by
  simpa only [machineExecutableMatrixEntryBaseDimension] using!
    machineCompose_mem_FP machineExecutableMatrixEntryPayload_mem_FP
      machinePairFirst_mem_FP

theorem machineExecutableMatrixEntryPoint_mem_FP :
    machineExecutableMatrixEntryPoint ∈ FP := by
  simpa only [machineExecutableMatrixEntryPoint] using!
    machineCompose_mem_FP machineExecutableMatrixEntryPayload_mem_FP
      machinePairSecond_mem_FP

theorem machineExecutableMatrixEntryRawInput_mem_FP :
    machineExecutableMatrixEntryRawInput ∈ FP :=
  machinePair_mem_FP machineExecutableMatrixEntryBaseDimension_mem_FP
    (machinePair_mem_FP machineExecutableMatrixEntryRow_mem_FP
      (machinePair_mem_FP machineExecutableMatrixEntryColumn_mem_FP
        machineExecutableMatrixEntryPoint_mem_FP))

theorem machineExecutableMatrixEntryCode_mem_FP :
    machineExecutableMatrixEntryCode ∈ FP := by
  have hraw := machineCompose_mem_FP
    machineExecutableMatrixEntryRawInput_mem_FP
    machineBetheAffineEntryRawCode_mem_FP
  simpa only [machineExecutableMatrixEntryCode] using!
    machineCompose_mem_FP hraw machineNormalizeRawRatEntryCode_mem_FP

@[simp] theorem machineExecutableMatrixEntryCode_encode {m : ℕ}
    (y : Fin (m * m) → ℚ) (i j : Fin (m + 1)) :
    machineExecutableMatrixEntryCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (pair (List.replicate m true)
              (rationalFiniteVectorCode y)))) =
      rationalEntryBinaryCode (betheAffineMatrixQ y i j) := by
  rw [machineExecutableMatrixEntryCode,
    machineExecutableMatrixEntryRawInput]
  simp only [machineExecutableMatrixEntryBaseDimension,
    machineExecutableMatrixEntryPoint,
    machineExecutableMatrixEntryPayload,
    machineExecutableMatrixEntryRow,
    machineExecutableMatrixEntryColumn,
    machineExecutableMatrixEntryRest,
    machinePairFirst_pair, machinePairSecond_pair]
  change machineNormalizeRawRatEntryCode
      (machineBetheAffineEntryRawCode
        (machineBetheAffineEntryCanonicalWord i j y)) = _
  rw [machineBetheAffineEntryRawCode_encode,
    machineNormalizeRawRatEntryCode_encode]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value, rawBetheAffineEntry_value]

/-! ## Uniform matrix-output program -/

def machineExecutableOptimizerBaseDimensionUnary
    (word : List Bool) : List Bool :=
  (machineMatrixDimensionUnary word).tail

def machineExecutableOptimizerPointCode
    (word : List Bool) : List Bool :=
  machineExplicitBetheOptimizerPointCode word

def machineExecutableOptimizerBasePointCode
    (word : List Bool) : List Bool :=
  machineBinaryListInit (machineExecutableOptimizerPointCode word)

def machineExecutableOptimizerMatrixPayload
    (word : List Bool) : List Bool :=
  pair (machineExecutableOptimizerBaseDimensionUnary word)
    (machineExecutableOptimizerBasePointCode word)

/-- The seed is exactly the canonical directed-objective word at `tau = 0`
and precision zero.  Reusing that word lets the existing raw-entry width proof
serve as the matrix generator's bit analysis. -/
def machineExecutableOptimizerMatrixSeed
    (word : List Bool) : List Bool :=
  pair (machineExecutableOptimizerBaseDimensionUnary word)
    (pair [] (pair (rawRatBinaryCode (rawRatOfRat 0))
      (pair word (machineExecutableOptimizerBasePointCode word))))

def machineExecutableOptimizerMatrixBound
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 2
    (machineExecutableOptimizerMatrixSeed word ++
      List.replicate 1024 false)

def machineExecutableOptimizerMatrixGeneratorInput
    (word : List Bool) : List Bool :=
  pair (machineMatrixDimensionUnary word)
    (pair (machineExecutableOptimizerMatrixBound word)
      (machineExecutableOptimizerMatrixPayload word))

def machineExecutableOptimizerMatrixRowsCode
    (word : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorRowsCode machineExecutableMatrixEntryCode
    (machineExecutableOptimizerMatrixGeneratorInput word)

def machineExecutableOptimizerMatrixCode
    (word : List Bool) : List Bool :=
  pair (machineMatrixDimensionWord word)
    (machineExecutableOptimizerMatrixRowsCode word)

theorem machineExecutableOptimizerBaseDimensionUnary_mem_FP :
    machineExecutableOptimizerBaseDimensionUnary ∈ FP := by
  simpa only [machineExecutableOptimizerBaseDimensionUnary] using!
    machineCompose_mem_FP machineMatrixDimensionUnary_mem_FP
      machineTail_mem_FP

theorem machineExecutableOptimizerPointCode_mem_FP :
    machineExecutableOptimizerPointCode ∈ FP := by
  simpa only [machineExecutableOptimizerPointCode] using!
    machineExplicitBetheOptimizerPointCode_mem_FP

theorem machineExecutableOptimizerBasePointCode_mem_FP :
    machineExecutableOptimizerBasePointCode ∈ FP := by
  simpa only [machineExecutableOptimizerBasePointCode] using!
    machineCompose_mem_FP machineExecutableOptimizerPointCode_mem_FP
      machineBinaryListInit_mem_FP

theorem machineExecutableOptimizerMatrixPayload_mem_FP :
    machineExecutableOptimizerMatrixPayload ∈ FP :=
  machinePair_mem_FP machineExecutableOptimizerBaseDimensionUnary_mem_FP
    machineExecutableOptimizerBasePointCode_mem_FP

theorem machineExecutableOptimizerMatrixSeed_mem_FP :
    machineExecutableOptimizerMatrixSeed ∈ FP :=
  machinePair_mem_FP machineExecutableOptimizerBaseDimensionUnary_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode (rawRatOfRat 0)))
        (machinePair_mem_FP id_mem_FP
          machineExecutableOptimizerBasePointCode_mem_FP)))

theorem machineExecutableOptimizerMatrixBound_mem_FP :
    machineExecutableOptimizerMatrixBound ∈ FP := by
  have hpadded := machineAppend_mem_FP
    machineExecutableOptimizerMatrixSeed_mem_FP
    (machineConst_mem_FP (List.replicate 1024 false))
  simpa only [machineExecutableOptimizerMatrixBound] using!
    machineCompose_mem_FP hpadded (machineIteratedBinaryWidth_mem_FP 2)

theorem machineExecutableOptimizerMatrixGeneratorInput_mem_FP :
    machineExecutableOptimizerMatrixGeneratorInput ∈ FP :=
  machinePair_mem_FP machineMatrixDimensionUnary_mem_FP
    (machinePair_mem_FP machineExecutableOptimizerMatrixBound_mem_FP
      machineExecutableOptimizerMatrixPayload_mem_FP)

theorem machineExecutableOptimizerMatrixRowsCode_mem_FP :
    machineExecutableOptimizerMatrixRowsCode ∈ FP := by
  have hgenerator := machineUnaryMatrixGeneratorRowsCode_mem_FP
    machineExecutableMatrixEntryCode_mem_FP
  simpa only [machineExecutableOptimizerMatrixRowsCode] using!
    machineCompose_mem_FP
      machineExecutableOptimizerMatrixGeneratorInput_mem_FP hgenerator

theorem machineExecutableOptimizerMatrixCode_mem_FP :
    machineExecutableOptimizerMatrixCode ∈ FP :=
  machinePair_mem_FP machineMatrixDimensionWord_mem_FP
    machineExecutableOptimizerMatrixRowsCode_mem_FP

/-! ## Canonical semantics and the explicit output bound -/

@[simp] theorem machineExecutableOptimizerBaseDimensionUnary_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    machineExecutableOptimizerBaseDimensionUnary
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      List.replicate m true := by
  rw [machineExecutableOptimizerBaseDimensionUnary,
    machineMatrixDimensionUnary_encode]
  simp

@[simp] theorem machineExecutableOptimizerMatrixSeed_encode
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ)
    (hpoint : machineExecutableOptimizerBasePointCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalFiniteVectorCode y) :
    machineExecutableOptimizerMatrixSeed
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      machineDirectedObjectiveSumCanonicalWord 0 A y 0 := by
  simp [machineExecutableOptimizerMatrixSeed, hpoint,
    machineDirectedObjectiveSumCanonicalWord]

theorem unaryMatrixCode_length_le_of_entry_bound {n E : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ)
    (hentry : ∀ i j, (rationalEntryBinaryCode (X i j)).length ≤ E) :
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixRows X)).length ≤
      n * (2 * (n * (2 * E + 2)) + 2) := by
  rw [binaryListCode_length_eq_sum]
  simp only [rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  calc
    ∑ i : Fin n,
        (2 * (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j => X i j)).length + 2) ≤
        ∑ _i : Fin n, (2 * (n * (2 * E + 2)) + 2) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [binaryListCode_length_eq_sum]
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
      have hrow :
          ∑ j : Fin n,
              (2 * (rationalEntryBinaryCode (X i j)).length + 2) ≤
            ∑ _j : Fin n, (2 * E + 2) := by
        apply Finset.sum_le_sum
        intro j _hj
        have hij := hentry i j
        omega
      have hrow' :
          ∑ j : Fin n,
              (2 * (rationalEntryBinaryCode (X i j)).length + 2) ≤
            n * (2 * E + 2) := by simpa using! hrow
      omega
    _ = n * (2 * (n * (2 * E + 2)) + 2) := by simp

theorem executableOptimizerMatrix_entryCode_length_le {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (i j : Fin (m + 1)) :
    let L := (machineDirectedObjectiveSumCanonicalWord 0 A y 0).length
    (rationalEntryBinaryCode (betheAffineMatrixQ y i j)).length ≤
      64 + 36 * rawBetheAffineEntryWidthBudget m L := by
  intro L
  rw [← rawRatBinaryCode_rawRatOfRat]
  have hcode := rawRatBinaryCode_length_le_width
    (rawRatOfRat (betheAffineMatrixQ y i j))
  have hwidth := rawBetheAffineMatrixQ_width_le_word
    (tau := (0 : ℚ)) A y 0 i j
  exact hcode.trans (by
    simp only [L]
    omega)

theorem executableOptimizerMatrix_rowsCode_fits_bound {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) :
    let seed := machineDirectedObjectiveSumCanonicalWord 0 A y 0
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixRows (betheAffineMatrixQ y))).length ≤
      (machineIteratedBinaryWidth 2
        (seed ++ List.replicate 1024 false)).length := by
  intro seed
  let L := seed.length
  let E := 64 + 36 * rawBetheAffineEntryWidthBudget m L
  have hentry : ∀ i j,
      (rationalEntryBinaryCode (betheAffineMatrixQ y i j)).length ≤ E := by
    intro i j
    simpa only [E, L, seed] using!
      executableOptimizerMatrix_entryCode_length_le A y i j
  have hmatrix := unaryMatrixCode_length_le_of_entry_bound
    (betheAffineMatrixQ y) hentry
  have hsource :
      (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩).length ≤ L := by
    simp [L, seed, machineDirectedObjectiveSumCanonicalWord]
    omega
  have hsquare : (m + 1) ^ 2 ≤ L := by
    have hcount :
        ((rationalMatrixRows A).map List.length).sum = (m + 1) ^ 2 := by
      simp only [rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
        Function.comp_apply, List.length_ofFn]
      simp
      ring
    rw [← hcount]
    apply (rationalRowsEntryCount_le_codeLength
      (rationalMatrixRows A)).trans
    have hrows :
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows A)).length ≤
          (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩).length := by
      change _ ≤ (pair (m + 1).bits
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows A))).length
      simpa only [machinePairSecond_pair] using!
        machinePairSecond_length_le
          (pair (m + 1).bits
            (binaryListCode (binaryListCode rationalEntryBinaryCode)
              (rationalMatrixRows A)))
    exact hrows.trans hsource
  have hm2 : m * m ≤ L := by nlinarith
  have hm : m ≤ L := by nlinarith
  have hE : E ≤ 512 * (L + 16) ^ 2 := by
    simp only [E, rawBetheAffineEntryWidthBudget]
    nlinarith [sq_nonneg (L + 16)]
  have hmatrix' :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows (betheAffineMatrixQ y))).length ≤
        4096 * (L + 16) ^ 3 := by
    apply hmatrix.trans
    have hn2 : (m + 1) * (m + 1) ≤ L := by
      simpa [pow_two] using! hsquare
    have hbase : 1 ≤ L + 16 := by omega
    nlinarith [Nat.mul_le_mul_left (4 * L) hE,
      sq_nonneg (L + 16)]
  have hpow : 4096 * (L + 16) ^ 3 ≤
      (L + 1024 + 16) ^ 4 := by
    nlinarith [sq_nonneg (L + 16), sq_nonneg (L + 1040)]
  calc
    _ ≤ 4096 * (L + 16) ^ 3 := hmatrix'
    _ ≤ (L + 1024 + 16) ^ 4 := hpow
    _ ≤ certificateExpGuardWidth 2 (L + 1024) := by
      simpa only [show 2 ^ (1 + 1) = 4 by norm_num] using!
        certificateExpGuardWidth_pow_lower 1 (L + 1024)
    _ = _ := by
      rw [machineIteratedBinaryWidth_length]
      simp only [List.length_append, List.length_replicate, L]

@[simp] theorem machineExecutableOptimizerMatrixRowsCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableOptimizerMatrixRowsCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows
          (executableScannedBetheOptimizerMatrix A)) := by
  let word := rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩
  let q := executableScannedBetheOptimizerPoint A
  let y := epigraphBase q
  have hpointFull : machineExecutableOptimizerPointCode word =
      rationalFiniteVectorCode q := by
    simpa only [machineExecutableOptimizerPointCode, word, q] using!
      machineExplicitBetheOptimizerPointCode_encode hm A hApos hAupper
  have hpoint : machineExecutableOptimizerBasePointCode word =
      rationalFiniteVectorCode y := by
    rw [machineExecutableOptimizerBasePointCode, hpointFull,
      rationalFiniteVectorCode, ofFn_epigraph_center_split,
      machineBinaryListInit_encode]
    rfl
  have hseed := machineExecutableOptimizerMatrixSeed_encode A y hpoint
  rw [machineExecutableOptimizerMatrixRowsCode,
    machineExecutableOptimizerMatrixGeneratorInput]
  have hdimension : machineMatrixDimensionUnary word =
      List.replicate (m + 1) true := machineMatrixDimensionUnary_encode A
  have hpayload : machineExecutableOptimizerMatrixPayload word =
      pair (List.replicate m true) (rationalFiniteVectorCode y) := by
    simp [machineExecutableOptimizerMatrixPayload, hpoint, word]
  have hbound : machineExecutableOptimizerMatrixBound word =
      machineIteratedBinaryWidth 2
        (machineDirectedObjectiveSumCanonicalWord 0 A y 0 ++
          List.replicate 1024 false) := by
    rw [machineExecutableOptimizerMatrixBound]
    rw [show machineExecutableOptimizerMatrixSeed word =
        machineDirectedObjectiveSumCanonicalWord 0 A y 0 by
      simpa only [word] using! hseed]
  rw [hdimension, hpayload, hbound]
  change machineUnaryMatrixGeneratorRowsCode machineExecutableMatrixEntryCode
      (machineUnaryMatrixGeneratorCanonicalWord (m + 1)
        (machineIteratedBinaryWidth 2
          (machineDirectedObjectiveSumCanonicalWord 0 A y 0 ++
            List.replicate 1024 false))
        (pair (List.replicate m true) (rationalFiniteVectorCode y))) = _
  rw [machineUnaryMatrixGeneratorRowsCode_encode_of_bound
    machineExecutableMatrixEntryCode (betheAffineMatrixQ y)
      (machineIteratedBinaryWidth 2
        (machineDirectedObjectiveSumCanonicalWord 0 A y 0 ++
          List.replicate 1024 false))
      (pair (List.replicate m true) (rationalFiniteVectorCode y))]
  · rfl
  · intro i j
    exact machineExecutableMatrixEntryCode_encode y i j
  · simpa only [unaryMatrixRows, rationalMatrixRows] using!
      executableOptimizerMatrix_rowsCode_fits_bound A y

@[simp] theorem machineExecutableOptimizerMatrixCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableOptimizerMatrixCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalMatrixBinaryEncoding.encode
        ⟨m + 1, executableScannedBetheOptimizerMatrix A⟩ := by
  rw [machineExecutableOptimizerMatrixCode,
    machineMatrixDimensionWord_encode,
    machineExecutableOptimizerMatrixRowsCode_encode hm A hApos hAupper]
  rfl

/-! ## Normalized potential entries -/

/-- The matrix generator supplies a dummy row, the vector coordinate as its
column, and then the immutable directed-objective seed. -/
def machineExecutablePotentialIndex (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond word)

def machineExecutablePotentialPayload (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond word)

def machineExecutablePotentialGradientInput
    (row column : List Bool → List Bool) (word : List Bool) : List Bool :=
  pair (row word)
    (pair (column word) (machineExecutablePotentialPayload word))

def machineExecutableRowPotentialGradientInput
    (word : List Bool) : List Bool :=
  machineExecutablePotentialGradientInput machineExecutablePotentialIndex
    (fun _ => []) word

def machineExecutableColumnPotentialGradientInput
    (word : List Bool) : List Bool :=
  machineExecutablePotentialGradientInput (fun _ => [])
    machineExecutablePotentialIndex word

def machineExecutableOriginGradientInput
    (word : List Bool) : List Bool :=
  machineExecutablePotentialGradientInput (fun _ => []) (fun _ => []) word

def machineExecutableTwoPlusTauRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineDirectedObjectiveSumTau
        (machineExecutablePotentialPayload word)))

def machineExecutableRowPotentialRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair
      (machineRawRatNegCode
        (machineDirectedNegativeGradientEntryRawCode
          (machineExecutableRowPotentialGradientInput word)))
      (machineExecutableTwoPlusTauRawCode word))

def machineExecutableColumnPotentialRawCode (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair
      (machineDirectedNegativeGradientEntryRawCode
        (machineExecutableOriginGradientInput word))
      (machineDirectedNegativeGradientEntryRawCode
        (machineExecutableColumnPotentialGradientInput word)))

def machineExecutableRowPotentialEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineExecutableRowPotentialRawCode word)

def machineExecutableColumnPotentialEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineExecutableColumnPotentialRawCode word)

theorem machineExecutablePotentialIndex_mem_FP :
    machineExecutablePotentialIndex ∈ FP := by
  simpa only [machineExecutablePotentialIndex] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineExecutablePotentialPayload_mem_FP :
    machineExecutablePotentialPayload ∈ FP := by
  simpa only [machineExecutablePotentialPayload] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineExecutablePotentialGradientInput_mem_FP
    {row column : List Bool → List Bool}
    (hrow : row ∈ FP) (hcolumn : column ∈ FP) :
    machineExecutablePotentialGradientInput row column ∈ FP :=
  machinePair_mem_FP hrow
    (machinePair_mem_FP hcolumn machineExecutablePotentialPayload_mem_FP)

theorem machineExecutableRowPotentialGradientInput_mem_FP :
    machineExecutableRowPotentialGradientInput ∈ FP := by
  simpa only [machineExecutableRowPotentialGradientInput] using!
    machineExecutablePotentialGradientInput_mem_FP
      machineExecutablePotentialIndex_mem_FP (machineConst_mem_FP [])

theorem machineExecutableColumnPotentialGradientInput_mem_FP :
    machineExecutableColumnPotentialGradientInput ∈ FP := by
  simpa only [machineExecutableColumnPotentialGradientInput] using!
    machineExecutablePotentialGradientInput_mem_FP (machineConst_mem_FP [])
      machineExecutablePotentialIndex_mem_FP

theorem machineExecutableOriginGradientInput_mem_FP :
    machineExecutableOriginGradientInput ∈ FP := by
  simpa only [machineExecutableOriginGradientInput] using!
    machineExecutablePotentialGradientInput_mem_FP
      (machineConst_mem_FP []) (machineConst_mem_FP [])

theorem machineExecutableTwoPlusTauRawCode_mem_FP :
    machineExecutableTwoPlusTauRawCode ∈ FP := by
  have htau := machineCompose_mem_FP
    machineExecutablePotentialPayload_mem_FP
    machineDirectedObjectiveSumTau_mem_FP
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo)) htau
  simpa only [machineExecutableTwoPlusTauRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineExecutableRowPotentialRawCode_mem_FP :
    machineExecutableRowPotentialRawCode ∈ FP := by
  have hgradient := machineCompose_mem_FP
    machineExecutableRowPotentialGradientInput_mem_FP
    machineDirectedNegativeGradientEntryRawCode_mem_FP
  have hneg := machineCompose_mem_FP hgradient machineRawRatNegCode_mem_FP
  have hpair := machinePair_mem_FP hneg
    machineExecutableTwoPlusTauRawCode_mem_FP
  simpa only [machineExecutableRowPotentialRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineExecutableColumnPotentialRawCode_mem_FP :
    machineExecutableColumnPotentialRawCode ∈ FP := by
  have horigin := machineCompose_mem_FP
    machineExecutableOriginGradientInput_mem_FP
    machineDirectedNegativeGradientEntryRawCode_mem_FP
  have hcolumn := machineCompose_mem_FP
    machineExecutableColumnPotentialGradientInput_mem_FP
    machineDirectedNegativeGradientEntryRawCode_mem_FP
  have hpair := machinePair_mem_FP horigin hcolumn
  simpa only [machineExecutableColumnPotentialRawCode] using!
    machineCompose_mem_FP hpair machineRawRatSubCode_mem_FP

theorem machineExecutableRowPotentialEntryCode_mem_FP :
    machineExecutableRowPotentialEntryCode ∈ FP := by
  simpa only [machineExecutableRowPotentialEntryCode] using!
    machineCompose_mem_FP machineExecutableRowPotentialRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineExecutableColumnPotentialEntryCode_mem_FP :
    machineExecutableColumnPotentialEntryCode ∈ FP := by
  simpa only [machineExecutableColumnPotentialEntryCode] using!
    machineCompose_mem_FP machineExecutableColumnPotentialRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

@[simp] theorem machineExecutableRowPotentialGradientInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (dummy i : Fin (m + 1)) :
    machineExecutableRowPotentialGradientInput
        (pair (List.replicate dummy.1 true)
          (pair (List.replicate i.1 true)
            (machineDirectedObjectiveSumCanonicalWord tau A y p))) =
      machineDirectedGradientEntryCanonicalWord tau A y p i 0 := by
  simp [machineExecutableRowPotentialGradientInput,
    machineExecutablePotentialGradientInput,
    machineExecutablePotentialIndex, machineExecutablePotentialPayload,
    machineDirectedGradientEntryCanonicalWord]

@[simp] theorem machineExecutableColumnPotentialGradientInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (dummy j : Fin (m + 1)) :
    machineExecutableColumnPotentialGradientInput
        (pair (List.replicate dummy.1 true)
          (pair (List.replicate j.1 true)
            (machineDirectedObjectiveSumCanonicalWord tau A y p))) =
      machineDirectedGradientEntryCanonicalWord tau A y p 0 j := by
  simp [machineExecutableColumnPotentialGradientInput,
    machineExecutablePotentialGradientInput,
    machineExecutablePotentialIndex, machineExecutablePotentialPayload,
    machineDirectedGradientEntryCanonicalWord]

@[simp] theorem machineExecutableOriginGradientInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (dummy j : Fin (m + 1)) :
    machineExecutableOriginGradientInput
        (pair (List.replicate dummy.1 true)
          (pair (List.replicate j.1 true)
            (machineDirectedObjectiveSumCanonicalWord tau A y p))) =
      machineDirectedGradientEntryCanonicalWord tau A y p 0 0 := by
  simp [machineExecutableOriginGradientInput,
    machineExecutablePotentialGradientInput,
    machineExecutablePotentialPayload,
    machineDirectedGradientEntryCanonicalWord]

@[simp] theorem machineExecutableTwoPlusTauRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (dummy i : Fin (m + 1)) :
    machineExecutableTwoPlusTauRawCode
        (pair (List.replicate dummy.1 true)
          (pair (List.replicate i.1 true)
            (machineDirectedObjectiveSumCanonicalWord tau A y p))) =
      rawRatBinaryCode
        (rawOptimizerTwo.add (rawRatOfRat tau)) := by
  rw [machineExecutableTwoPlusTauRawCode]
  simp only [machineExecutablePotentialPayload, machinePairSecond_pair,
    machineDirectedObjectiveSumTau_encode, machineRawRatAddCode_encode]

@[simp] theorem machineExecutableRowPotentialEntryCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (dummy i : Fin (m + 1)) :
    machineExecutableRowPotentialEntryCode
        (pair (List.replicate dummy.1 true)
          (pair (List.replicate i.1 true)
            (machineDirectedObjectiveSumCanonicalWord tau A y p))) =
      rationalEntryBinaryCode
        (-directedNegativeGradientLowerMatrix tau A
            (betheAffineMatrixQ y) p i 0 + (2 + tau)) := by
  rw [machineExecutableRowPotentialEntryCode,
    machineExecutableRowPotentialRawCode,
    machineExecutableRowPotentialGradientInput_encode,
    machineExecutableTwoPlusTauRawCode_encode,
    machineDirectedNegativeGradientEntryRawCode_encode,
    machineRawRatNegCode_encode, machineRawRatAddCode_encode,
    machineNormalizeRawRatEntryCode_encode]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value, RawRat.value_add,
    RawRat.value_neg, machineDirectedNegativeGradientEntry_value,
    RawRat.value_add, rawRatOfRat_value]
  norm_num [rawOptimizerTwo, RawRat.ofNat, RawRat.value]

@[simp] theorem machineExecutableColumnPotentialEntryCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (dummy j : Fin (m + 1)) :
    machineExecutableColumnPotentialEntryCode
        (pair (List.replicate dummy.1 true)
          (pair (List.replicate j.1 true)
            (machineDirectedObjectiveSumCanonicalWord tau A y p))) =
      rationalEntryBinaryCode
        (-(directedNegativeGradientLowerMatrix tau A
            (betheAffineMatrixQ y) p 0 j -
          directedNegativeGradientLowerMatrix tau A
            (betheAffineMatrixQ y) p 0 0)) := by
  rw [machineExecutableColumnPotentialEntryCode,
    machineExecutableColumnPotentialRawCode,
    machineExecutableOriginGradientInput_encode,
    machineExecutableColumnPotentialGradientInput_encode,
    machineDirectedNegativeGradientEntryRawCode_encode,
    machineDirectedNegativeGradientEntryRawCode_encode,
    machineRawRatSubCode_encode, machineNormalizeRawRatEntryCode_encode]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value, RawRat.value_sub,
    machineDirectedNegativeGradientEntry_value,
    machineDirectedNegativeGradientEntry_value]
  ring

/-! ## Canonical directed-gradient seed -/

def machineExecutableOptimizerTauCanonicalCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode (machineOptimizerTauRawCode word)

def machineExecutableOptimizerGradientSeed
    (word : List Bool) : List Bool :=
  pair (machineExecutableOptimizerBaseDimensionUnary word)
    (pair (machineExplicitOptimizerPrecisionRuler word)
      (pair (machineExecutableOptimizerTauCanonicalCode word)
        (pair word (machineExecutableOptimizerBasePointCode word))))

theorem machineExecutableOptimizerTauCanonicalCode_mem_FP :
    machineExecutableOptimizerTauCanonicalCode ∈ FP := by
  simpa only [machineExecutableOptimizerTauCanonicalCode] using!
    machineCompose_mem_FP machineOptimizerTauRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineExecutableOptimizerGradientSeed_mem_FP :
    machineExecutableOptimizerGradientSeed ∈ FP :=
  machinePair_mem_FP machineExecutableOptimizerBaseDimensionUnary_mem_FP
    (machinePair_mem_FP machineExplicitOptimizerPrecisionRuler_mem_FP
      (machinePair_mem_FP
        machineExecutableOptimizerTauCanonicalCode_mem_FP
        (machinePair_mem_FP id_mem_FP
          machineExecutableOptimizerBasePointCode_mem_FP)))

@[simp] theorem machineExecutableOptimizerTauCanonicalCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExecutableOptimizerTauCanonicalCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawRatOfRat (explicitRegularizationScale n)) := by
  rw [machineExecutableOptimizerTauCanonicalCode,
    machineOptimizerTauRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value, rawOptimizerTau_value]

@[simp] theorem machineExecutableOptimizerBasePointCode_encode {m : ℕ}
    (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableOptimizerBasePointCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalFiniteVectorCode
        (epigraphBase (executableScannedBetheOptimizerPoint A)) := by
  let q := executableScannedBetheOptimizerPoint A
  have hpointFull : machineExecutableOptimizerPointCode
      (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalFiniteVectorCode q := by
    simpa only [machineExecutableOptimizerPointCode, q] using!
      machineExplicitBetheOptimizerPointCode_encode hm A hApos hAupper
  rw [machineExecutableOptimizerBasePointCode, hpointFull,
    rationalFiniteVectorCode, ofFn_epigraph_center_split,
    machineBinaryListInit_encode]
  rfl

@[simp] theorem machineExecutableOptimizerGradientSeed_encode {m : ℕ}
    (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableOptimizerGradientSeed
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      machineDirectedObjectiveSumCanonicalWord
        (explicitRegularizationScale (m + 1)) A
        (epigraphBase (executableScannedBetheOptimizerPoint A))
        (explicitOptimizerPrecision A) := by
  simp [machineExecutableOptimizerGradientSeed,
    machineDirectedObjectiveSumCanonicalWord,
    machineExecutableOptimizerBasePointCode_encode hm A hApos hAupper]

/-! ## Bounded repeated-row generators for the potential vectors -/

def machineExecutableOptimizerPotentialBound
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 6
    (machineExecutableOptimizerGradientSeed word ++
      List.replicate 4096 false)

def machineExecutableOptimizerPotentialGeneratorInput
    (word : List Bool) : List Bool :=
  pair (machineMatrixDimensionUnary word)
    (pair (machineExecutableOptimizerPotentialBound word)
      (machineExecutableOptimizerGradientSeed word))

def machineExecutableOptimizerRowPotentialRowsCode
    (word : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorRowsCode
    machineExecutableRowPotentialEntryCode
    (machineExecutableOptimizerPotentialGeneratorInput word)

def machineExecutableOptimizerColumnPotentialRowsCode
    (word : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorRowsCode
    machineExecutableColumnPotentialEntryCode
    (machineExecutableOptimizerPotentialGeneratorInput word)

def machineExecutableOptimizerRowPotentialCode
    (word : List Bool) : List Bool :=
  machineListHead (machineExecutableOptimizerRowPotentialRowsCode word)

def machineExecutableOptimizerColumnPotentialCode
    (word : List Bool) : List Bool :=
  machineListHead (machineExecutableOptimizerColumnPotentialRowsCode word)

theorem machineExecutableOptimizerPotentialBound_mem_FP :
    machineExecutableOptimizerPotentialBound ∈ FP := by
  have hpadded := machineAppend_mem_FP
    machineExecutableOptimizerGradientSeed_mem_FP
    (machineConst_mem_FP (List.replicate 4096 false))
  simpa only [machineExecutableOptimizerPotentialBound] using!
    machineCompose_mem_FP hpadded (machineIteratedBinaryWidth_mem_FP 6)

theorem machineExecutableOptimizerPotentialGeneratorInput_mem_FP :
    machineExecutableOptimizerPotentialGeneratorInput ∈ FP :=
  machinePair_mem_FP machineMatrixDimensionUnary_mem_FP
    (machinePair_mem_FP machineExecutableOptimizerPotentialBound_mem_FP
      machineExecutableOptimizerGradientSeed_mem_FP)

theorem machineExecutableOptimizerRowPotentialRowsCode_mem_FP :
    machineExecutableOptimizerRowPotentialRowsCode ∈ FP := by
  have hgenerator := machineUnaryMatrixGeneratorRowsCode_mem_FP
    machineExecutableRowPotentialEntryCode_mem_FP
  simpa only [machineExecutableOptimizerRowPotentialRowsCode] using!
    machineCompose_mem_FP
      machineExecutableOptimizerPotentialGeneratorInput_mem_FP hgenerator

theorem machineExecutableOptimizerColumnPotentialRowsCode_mem_FP :
    machineExecutableOptimizerColumnPotentialRowsCode ∈ FP := by
  have hgenerator := machineUnaryMatrixGeneratorRowsCode_mem_FP
    machineExecutableColumnPotentialEntryCode_mem_FP
  simpa only [machineExecutableOptimizerColumnPotentialRowsCode] using!
    machineCompose_mem_FP
      machineExecutableOptimizerPotentialGeneratorInput_mem_FP hgenerator

theorem machineExecutableOptimizerRowPotentialCode_mem_FP :
    machineExecutableOptimizerRowPotentialCode ∈ FP := by
  simpa only [machineExecutableOptimizerRowPotentialCode] using!
    machineCompose_mem_FP
      machineExecutableOptimizerRowPotentialRowsCode_mem_FP
      machineListHead_mem_FP

theorem machineExecutableOptimizerColumnPotentialCode_mem_FP :
    machineExecutableOptimizerColumnPotentialCode ∈ FP := by
  simpa only [machineExecutableOptimizerColumnPotentialCode] using!
    machineCompose_mem_FP
      machineExecutableOptimizerColumnPotentialRowsCode_mem_FP
      machineListHead_mem_FP

/-! ## Ordinary bit bounds for the potential output -/

def rawExecutableRowPotential {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (i : Fin (m + 1)) : RawRat :=
  (rawDirectedNegativeGradientLower tau (A i 0)
      (betheAffineMatrixQ y i 0) p).neg.add
    (rawOptimizerTwo.add (rawRatOfRat tau))

def rawExecutableColumnPotential {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (j : Fin (m + 1)) : RawRat :=
  (rawDirectedNegativeGradientLower tau (A 0 0)
      (betheAffineMatrixQ y 0 0) p).sub
    (rawDirectedNegativeGradientLower tau (A 0 j)
      (betheAffineMatrixQ y 0 j) p)

@[simp] theorem rawExecutableRowPotential_value {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (i : Fin (m + 1)) :
    (rawExecutableRowPotential tau A y p i).value =
      -directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p i 0 + (2 + tau) := by
  rw [rawExecutableRowPotential, RawRat.value_add, RawRat.value_neg,
    machineDirectedNegativeGradientEntry_value, RawRat.value_add,
    rawRatOfRat_value]
  norm_num [rawOptimizerTwo, RawRat.ofNat, RawRat.value]

@[simp] theorem rawExecutableColumnPotential_value {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (j : Fin (m + 1)) :
    (rawExecutableColumnPotential tau A y p j).value =
      -(directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p 0 j -
        directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p 0 0) := by
  rw [rawExecutableColumnPotential, RawRat.value_sub,
    machineDirectedNegativeGradientEntry_value,
    machineDirectedNegativeGradientEntry_value]
  ring

theorem rawExecutableRowPotential_width_le_word_budget {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (i : Fin (m + 1)) :
    let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
    let B := rawDirectedObjectiveCoordinateWordBudget m L
    rawRatWidth (rawExecutableRowPotential tau A y p i) ≤
      B + L + 4 := by
  intro L B
  have hgradient := rawDirectedNegativeGradientEntry_width_le_word_budget
    tau A y p i 0
  have htau := rawDirectedObjectiveSum_tau_width_le_word tau A y p
  have htwo : rawRatWidth rawOptimizerTwo = 2 := by
    decide
  have htwoTau := rawRatWidth_add_le rawOptimizerTwo (rawRatOfRat tau)
  rw [htwo] at htwoTau
  have hsum := rawRatWidth_add_le
    (rawDirectedNegativeGradientLower tau (A i 0)
      (betheAffineMatrixQ y i 0) p).neg
    (rawOptimizerTwo.add (rawRatOfRat tau))
  rw [rawRatWidth_neg] at hsum
  simpa only [rawExecutableRowPotential, L, B] using! hsum.trans (by omega)

theorem rawExecutableColumnPotential_width_le_word_budget {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (j : Fin (m + 1)) :
    let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
    let B := rawDirectedObjectiveCoordinateWordBudget m L
    rawRatWidth (rawExecutableColumnPotential tau A y p j) ≤
      2 * B + 1 := by
  intro L B
  have horigin := rawDirectedNegativeGradientEntry_width_le_word_budget
    tau A y p 0 0
  have hcolumn := rawDirectedNegativeGradientEntry_width_le_word_budget
    tau A y p 0 j
  have hsub := rawRatWidth_sub_le
    (rawDirectedNegativeGradientLower tau (A 0 0)
      (betheAffineMatrixQ y 0 0) p)
    (rawDirectedNegativeGradientLower tau (A 0 j)
      (betheAffineMatrixQ y 0 j) p)
  simpa only [rawExecutableColumnPotential, L, B] using! hsub.trans (by omega)

theorem executableRowPotential_entryCode_length_le {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (i : Fin (m + 1)) :
    let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
    let B := rawDirectedObjectiveCoordinateWordBudget m L
    (rationalEntryBinaryCode
      (-directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p i 0 + (2 + tau))).length ≤
      208 + 36 * B + 36 * L := by
  intro L B
  let raw := rawExecutableRowPotential tau A y p i
  have hcanonical := rationalEntryBinaryCode_binaryNormalizeRawRat_length_le raw
  rw [binaryNormalizeRawRat_eq_value,
    rawExecutableRowPotential_value] at hcanonical
  have hraw := rawExecutableRowPotential_width_le_word_budget tau A y p i
  calc
    _ ≤ 64 + 36 * rawRatWidth raw := hcanonical
    _ ≤ 64 + 36 * (B + L + 4) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 36 hraw) 64
    _ = 208 + 36 * B + 36 * L := by ring

theorem executableColumnPotential_entryCode_length_le {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (j : Fin (m + 1)) :
    let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
    let B := rawDirectedObjectiveCoordinateWordBudget m L
    (rationalEntryBinaryCode
      (-(directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p 0 j -
        directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p 0 0))).length ≤
      100 + 72 * B := by
  intro L B
  let raw := rawExecutableColumnPotential tau A y p j
  have hcanonical := rationalEntryBinaryCode_binaryNormalizeRawRat_length_le raw
  rw [binaryNormalizeRawRat_eq_value,
    rawExecutableColumnPotential_value] at hcanonical
  have hraw := rawExecutableColumnPotential_width_le_word_budget tau A y p j
  calc
    _ ≤ 64 + 36 * rawRatWidth raw := hcanonical
    _ ≤ 64 + 36 * (2 * B + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 36 hraw) 64
    _ = 100 + 72 * B := by ring

theorem executableRepeatedPotential_rowsCode_fits_bound {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (v : Fin (m + 1) → ℚ)
    (hentry : ∀ j,
      let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
      let B := rawDirectedObjectiveCoordinateWordBudget m L
      (rationalEntryBinaryCode (v j)).length ≤
        208 + 72 * B + 36 * L) :
    let seed := machineDirectedObjectiveSumCanonicalWord tau A y p
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (unaryMatrixRows (fun _ j ↦ v j))).length ≤
      (machineIteratedBinaryWidth 6
        (seed ++ List.replicate 4096 false)).length := by
  intro seed
  let L := seed.length
  let T := L + 16
  let B := rawDirectedObjectiveCoordinateWordBudget m L
  let E := 208 + 72 * B + 36 * L
  have hmL : m ≤ L := by
    simp only [L, seed, machineDirectedObjectiveSumCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have hnL : m + 1 ≤ L := by
    simp only [L, seed, machineDirectedObjectiveSumCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have hB : B ≤ T ^ 20 := by
    simpa only [B, T] using!
      rawDirectedObjectiveCoordinateWordBudget_le_pow hmL
  have hTpos : 0 < T := by simp [T]
  have hpow19 : 1 ≤ T ^ 19 := one_le_pow₀ (by omega)
  have hTpow20 : T ≤ T ^ 20 := by
    rw [show 20 = 19 + 1 by omega, pow_succ]
    nlinarith
  have hLpow20 : L ≤ T ^ 20 :=
    (by simp [T] : L ≤ T).trans hTpow20
  have hpow20 : 1 ≤ T ^ 20 := one_le_pow₀ (by omega)
  have hE : E ≤ 128 * T ^ 20 := by
    dsimp only [E]
    omega
  have hmatrix := unaryMatrixCode_length_le_of_entry_bound
    (X := fun _ j ↦ v j) (E := E) (by
      intro i j
      simpa only [E, B, L, seed] using! hentry j)
  have hnT : m + 1 ≤ T := hnL.trans (by simp [T])
  have hfactor : 2 * E + 2 ≤ 258 * T ^ 20 := by omega
  have hn2 := Nat.mul_le_mul hnT hnT
  have hmain := Nat.mul_le_mul hn2 hfactor
  have hTpow22 : T ≤ T ^ 22 := by
    have hpow21 : 1 ≤ T ^ 21 := one_le_pow₀ (by omega)
    rw [show 22 = 21 + 1 by omega, pow_succ]
    nlinarith
  have hcoarse :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows (fun _ j ↦ v j))).length ≤
        518 * T ^ 22 := by
    apply hmatrix.trans
    have hmain' :
        (m + 1) * (m + 1) * (2 * E + 2) ≤
          258 * T ^ 22 := by
      calc
        _ ≤ T * T * (258 * T ^ 20) := hmain
        _ = 258 * T ^ 22 := by ring
    calc
      (m + 1) * (2 * ((m + 1) * (2 * E + 2)) + 2) =
          2 * ((m + 1) * (m + 1) * (2 * E + 2)) +
            2 * (m + 1) := by ring
      _ ≤ 2 * (258 * T ^ 22) + 2 * T ^ 22 := by omega
      _ = 518 * T ^ 22 := by ring
  have hcoeff : 518 ≤ T ^ 3 := by
    have hbase : 16 ≤ T := by simp [T]
    have hpow := Nat.pow_le_pow_left hbase 3
    exact (by norm_num : 518 ≤ 16 ^ 3).trans hpow
  have hpower25 :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows (fun _ j ↦ v j))).length ≤ T ^ 25 := by
    calc
      _ ≤ 518 * T ^ 22 := hcoarse
      _ ≤ T ^ 3 * T ^ 22 := Nat.mul_le_mul_right _ hcoeff
      _ = T ^ 25 := by ring
  have hpower :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows (fun _ j ↦ v j))).length ≤ T ^ 64 :=
    hpower25.trans (Nat.pow_le_pow_right hTpos (by omega))
  rw [machineIteratedBinaryWidth_length]
  apply hpower.trans
  have hbase : L + 16 ≤ L + 4096 + 16 := by omega
  have hpowBase := Nat.pow_le_pow_left hbase 64
  exact hpowBase.trans (by
    simpa only [show 2 ^ (5 + 1) = 64 by norm_num,
      List.length_append, List.length_replicate, T, L, seed] using!
      certificateExpGuardWidth_pow_lower 5 (L + 4096))

theorem executableRowPotential_rowsCode_fits_bound {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    let seed := machineDirectedObjectiveSumCanonicalWord tau A y p
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (unaryMatrixRows
        (fun _ i ↦ -directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p i 0 + (2 + tau)))).length ≤
      (machineIteratedBinaryWidth 6
        (seed ++ List.replicate 4096 false)).length := by
  apply executableRepeatedPotential_rowsCode_fits_bound
  intro i L B
  have h := executableRowPotential_entryCode_length_le tau A y p i
  simpa only [L, B] using! h.trans (by omega)

theorem executableColumnPotential_rowsCode_fits_bound {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    let seed := machineDirectedObjectiveSumCanonicalWord tau A y p
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (unaryMatrixRows
        (fun _ j ↦ -(directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p 0 j -
          directedNegativeGradientLowerMatrix tau A
            (betheAffineMatrixQ y) p 0 0)))).length ≤
      (machineIteratedBinaryWidth 6
        (seed ++ List.replicate 4096 false)).length := by
  apply executableRepeatedPotential_rowsCode_fits_bound
  intro j L B
  have h := executableColumnPotential_entryCode_length_le tau A y p j
  simpa only [L, B] using! h.trans (by omega)

@[simp] theorem machineListHead_unaryMatrixRows_repeated {n : ℕ}
    (hn : 0 < n) (v : Fin n → ℚ) :
    machineListHead
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (unaryMatrixRows (fun _ j ↦ v j))) =
      rationalVectorBinaryCode v := by
  cases n with
  | zero => omega
  | succ n =>
      simp [unaryMatrixRows, rationalVectorBinaryCode,
        List.ofFn_succ, machineListHead_cons]

@[simp] theorem machineExecutableOptimizerRowPotentialCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableOptimizerRowPotentialCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalVectorBinaryCode
        (executableScannedBetheOptimizerRowPotential A) := by
  let word := rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩
  let tau := explicitRegularizationScale (m + 1)
  let p := explicitOptimizerPrecision A
  let y := epigraphBase (executableScannedBetheOptimizerPoint A)
  let seed := machineDirectedObjectiveSumCanonicalWord tau A y p
  let bound := machineIteratedBinaryWidth 6
    (seed ++ List.replicate 4096 false)
  let f : Fin (m + 1) → Fin (m + 1) → ℚ :=
    fun _ i ↦ -directedNegativeGradientLowerMatrix tau A
      (betheAffineMatrixQ y) p i 0 + (2 + tau)
  have hseed : machineExecutableOptimizerGradientSeed word = seed := by
    simpa only [word, seed, tau, y, p] using!
      machineExecutableOptimizerGradientSeed_encode hm A hApos hAupper
  have hinput : machineExecutableOptimizerPotentialGeneratorInput word =
      machineUnaryMatrixGeneratorCanonicalWord (m + 1) bound seed := by
    rw [machineExecutableOptimizerPotentialGeneratorInput]
    rw [show machineMatrixDimensionUnary word =
        List.replicate (m + 1) true by
      simpa only [word] using! machineMatrixDimensionUnary_encode A]
    rw [machineExecutableOptimizerPotentialBound, hseed]
    rfl
  have hentry : ∀ i j,
      machineExecutableRowPotentialEntryCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true) seed)) =
        rationalEntryBinaryCode (f i j) := by
    intro i j
    simpa only [seed, tau, y, p, f] using!
      machineExecutableRowPotentialEntryCode_encode tau A y p i j
  have hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length ≤ bound.length := by
    simpa only [f, bound, seed] using!
      executableRowPotential_rowsCode_fits_bound tau A y p
  rw [machineExecutableOptimizerRowPotentialCode,
    machineExecutableOptimizerRowPotentialRowsCode, hinput,
    machineUnaryMatrixGeneratorRowsCode_encode_of_bound
      machineExecutableRowPotentialEntryCode f bound seed hentry hbound,
    machineListHead_unaryMatrixRows_repeated (by omega)]
  rfl

@[simp] theorem machineExecutableOptimizerColumnPotentialCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableOptimizerColumnPotentialCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalVectorBinaryCode
        (executableScannedBetheOptimizerColumnPotential A) := by
  let word := rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩
  let tau := explicitRegularizationScale (m + 1)
  let p := explicitOptimizerPrecision A
  let y := epigraphBase (executableScannedBetheOptimizerPoint A)
  let seed := machineDirectedObjectiveSumCanonicalWord tau A y p
  let bound := machineIteratedBinaryWidth 6
    (seed ++ List.replicate 4096 false)
  let f : Fin (m + 1) → Fin (m + 1) → ℚ :=
    fun _ j ↦ -(directedNegativeGradientLowerMatrix tau A
      (betheAffineMatrixQ y) p 0 j -
      directedNegativeGradientLowerMatrix tau A
        (betheAffineMatrixQ y) p 0 0)
  have hseed : machineExecutableOptimizerGradientSeed word = seed := by
    simpa only [word, seed, tau, y, p] using!
      machineExecutableOptimizerGradientSeed_encode hm A hApos hAupper
  have hinput : machineExecutableOptimizerPotentialGeneratorInput word =
      machineUnaryMatrixGeneratorCanonicalWord (m + 1) bound seed := by
    rw [machineExecutableOptimizerPotentialGeneratorInput]
    rw [show machineMatrixDimensionUnary word =
        List.replicate (m + 1) true by
      simpa only [word] using! machineMatrixDimensionUnary_encode A]
    rw [machineExecutableOptimizerPotentialBound, hseed]
    rfl
  have hentry : ∀ i j,
      machineExecutableColumnPotentialEntryCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true) seed)) =
        rationalEntryBinaryCode (f i j) := by
    intro i j
    simpa only [seed, tau, y, p, f] using!
      machineExecutableColumnPotentialEntryCode_encode tau A y p i j
  have hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length ≤ bound.length := by
    simpa only [f, bound, seed] using!
      executableColumnPotential_rowsCode_fits_bound tau A y p
  rw [machineExecutableOptimizerColumnPotentialCode,
    machineExecutableOptimizerColumnPotentialRowsCode, hinput,
    machineUnaryMatrixGeneratorRowsCode_encode_of_bound
      machineExecutableColumnPotentialEntryCode f bound seed hentry hbound,
    machineListHead_unaryMatrixRows_repeated (by omega)]
  rfl

/-! ## Complete optimizer output word -/

def executableScannedOptimizerOutput {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    RationalOptimizerOutput (m + 1) where
  matrix := executableScannedBetheOptimizerMatrix A
  rowPotential := executableScannedBetheOptimizerRowPotential A
  columnPotential := executableScannedBetheOptimizerColumnPotential A

def machineExecutableScannedOptimizerOutputCode
    (word : List Bool) : List Bool :=
  pair (machineExecutableOptimizerMatrixCode word)
    (pair (machineExecutableOptimizerRowPotentialCode word)
      (machineExecutableOptimizerColumnPotentialCode word))

theorem machineExecutableScannedOptimizerOutputCode_mem_FP :
    machineExecutableScannedOptimizerOutputCode ∈ FP :=
  machinePair_mem_FP machineExecutableOptimizerMatrixCode_mem_FP
    (machinePair_mem_FP machineExecutableOptimizerRowPotentialCode_mem_FP
      machineExecutableOptimizerColumnPotentialCode_mem_FP)

@[simp] theorem machineExecutableScannedOptimizerOutputCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExecutableScannedOptimizerOutputCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalOptimizerOutputCode (executableScannedOptimizerOutput A) := by
  rw [machineExecutableScannedOptimizerOutputCode,
    machineExecutableOptimizerMatrixCode_encode hm A hApos hAupper,
    machineExecutableOptimizerRowPotentialCode_encode hm A hApos hAupper,
    machineExecutableOptimizerColumnPotentialCode_encode hm A hApos hAupper]
  rfl

/-- Dimension-at-least-two specialization used by the positive routine. -/
def executableLargeOptimizerOutput (m : ℕ)
    (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ) :
    RationalOptimizerOutput (m + 2) :=
  executableScannedOptimizerOutput (m := m + 1) B

def ExecutableLargeOptimizerStringRealizes
    (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    (∀ i j, 0 < B i j) → (∀ i j, B i j ≤ 1) →
    F (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩) =
      rationalOptimizerOutputCode (executableLargeOptimizerOutput m B)

theorem machineExecutableScannedOptimizerOutputCode_realizes :
    ExecutableLargeOptimizerStringRealizes
      machineExecutableScannedOptimizerOutputCode := by
  intro m B hBpos hBupper
  simpa only [executableLargeOptimizerOutput, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using!
    machineExecutableScannedOptimizerOutputCode_encode
      (m := m + 1) (by omega) B hBpos hBupper

end BeyondBethe

/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part17

/-! # GapCVP proof, part 18 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Comparator

open GapCVP.Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal
open GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine
open GapCVP.Factor400PaperVariableArityFinitePNormUnconditional
open GapCVP.Factor400PaperVariableArityNearestUnconditional

private theorem classicalDecide_eq_true_iff (proposition : Prop) :
    @decide proposition (Classical.propDecidable proposition) = true ↔
      proposition := by
  constructor
  · exact @of_decide_eq_true proposition
      (Classical.propDecidable proposition)
  · exact @decide_eq_true proposition
      (Classical.propDecidable proposition)

private theorem classicalDecide_congr {first second : Prop}
    (equivalent : first ↔ second) :
    @decide first (Classical.propDecidable first) = true ↔
      @decide second (Classical.propDecidable second) = true :=
  (classicalDecide_eq_true_iff first).trans
    (equivalent.trans (classicalDecide_eq_true_iff second).symm)

private structure Instance where
  dimension : ℕ
  basis : Matrix (Fin dimension) (Fin dimension) ℤ
  target : Fin dimension → ℚ
  radius : ℚ

export GapCVP.BinaryEncoding
  (lengthPrefixedWord
   readUnaryPrefix
   readUnaryPrefix_replicate
   readLengthPrefixedWord
   readLengthPrefixedWord_append
   encodeAtomic
   readAtomic
   readAtomic_append
   encodeFinValues
   readFinValues
   readFinValues_append
   encodeMatrixRows
   readMatrixRows
   readMatrixRows_append)

export GapCVP (BitLanguage bitEncoding pairBitEncoding IsNP)

private def encodeInstance (I : Instance) : List Bool :=
  encodeAtomic I.dimension ++
    encodeAtomic I.radius ++
    encodeFinValues I.dimension I.target ++
    encodeMatrixRows I.dimension I.dimension I.basis

private def decodeInstance (bits : List Bool) : Option Instance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (dimension, afterDimension) =>
      match (readAtomic afterDimension : Option (ℚ × List Bool)) with
      | none => none
      | some (radius, afterRadius) =>
          match (readFinValues dimension afterRadius :
            Option ((Fin dimension → ℚ) × List Bool)) with
          | none => none
          | some (target, afterTarget) =>
              match readMatrixRows dimension dimension afterTarget with
              | some (basis, []) =>
                  some { dimension, basis, target, radius }
              | _ => none

@[simp] private theorem decodeInstance_encode (record : Instance) :
    decodeInstance (encodeInstance record) = some record := by
  cases record with
  | mk dimension basis target radius =>
      have matrix :
          readMatrixRows dimension dimension
              (encodeMatrixRows dimension dimension basis) =
            some (basis, []) := by
        change
          readMatrixRows dimension dimension
              (encodeMatrixRows dimension dimension
                (fun row column => basis row column)) =
            some ((fun row column => basis row column), [])
        simpa only [List.append_nil] using
          readMatrixRows_append (fun row column => basis row column) []
      simp only [decodeInstance, encodeInstance, List.append_assoc, readAtomic_append,
          readFinValues_append, matrix]

private theorem encodeInstance_injective : Function.Injective encodeInstance := by
  intro first second same
  simpa only [decodeInstance_encode, Option.some.injEq] using congrArg decodeInstance same

private def wellFormed (record : Instance) : Bool :=
  @decide
    (0 < record.dimension ∧ record.basis.det ≠ 0 ∧ 0 < record.radius)
    (Classical.propDecidable _)

private def hasIntegerTarget (record : Instance) : Bool :=
  @decide
    (∀ index : Fin record.dimension,
      ∃ value : ℤ, record.target index = (value : ℚ))
    (Classical.propDecidable _)

private noncomputable def distanceSquared (I : Instance)
    (vector : Fin I.dimension → ℤ) : ℝ :=
  ∑ i : Fin I.dimension,
    (((∑ j : Fin I.dimension,
      (I.basis i j : ℝ) * (vector j : ℝ)) -
        (I.target i : ℝ)) ^ 2)

private noncomputable def gapFactor400 (I : Instance) : ℝ :=
  (I.dimension : ℝ) ^ ((1 : ℝ) / 400)

private def gapYES400 (record : Instance) : Bool :=
  @decide
    (wellFormed record ∧
      ∃ vector : Fin record.dimension → ℤ,
        distanceSquared record vector ≤ (record.radius : ℝ) ^ 2)
    (Classical.propDecidable _)

private def gapNO400 (record : Instance) : Bool :=
  @decide
    (wellFormed record ∧
      ∀ vector : Fin record.dimension → ℤ,
        (gapFactor400 record * (record.radius : ℝ)) ^ 2 <
          distanceSquared record vector)
    (Classical.propDecidable _)

private theorem gapYES400_not_gapNO400 (record : Instance)
    (positive : gapYES400 record) (negative : gapNO400 record) : False := by
  have positive' :
      wellFormed record = true ∧
        ∃ vector : Fin record.dimension → ℤ,
          distanceSquared record vector ≤ (record.radius : ℝ) ^ 2 := by
    apply (classicalDecide_eq_true_iff _).mp
    exact positive
  have negative' :
      wellFormed record = true ∧
        ∀ vector : Fin record.dimension → ℤ,
          (gapFactor400 record * (record.radius : ℝ)) ^ 2 <
            distanceSquared record vector := by
    apply (classicalDecide_eq_true_iff _).mp
    exact negative
  have well :
      0 < record.dimension ∧ record.basis.det ≠ 0 ∧
        0 < record.radius := by
    apply (classicalDecide_eq_true_iff _).mp
    exact positive'.1
  obtain ⟨dimension, _, radius⟩ := well
  obtain ⟨vector, close⟩ := positive'.2
  have factor : 1 ≤ gapFactor400 record := by
    unfold gapFactor400
    apply Real.one_le_rpow
    · exact_mod_cast dimension
    · norm_num
  have radiusReal : 0 < (record.radius : ℝ) := by
    exact_mod_cast radius
  have scaled :
      (record.radius : ℝ) ≤
        gapFactor400 record * (record.radius : ℝ) := by
    nlinarith
  have squares :
      (record.radius : ℝ) ^ 2 ≤
        (gapFactor400 record * (record.radius : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (gapFactor400 record * (record.radius : ℝ)),
      sq_nonneg (record.radius : ℝ)]
  linarith [negative'.2 vector]

private def yesLanguage (bits : List Bool) : Bool :=
  @decide
    (∃ record : Instance,
      encodeInstance record = bits ∧
        hasIntegerTarget record ∧ gapYES400 record)
    (Classical.propDecidable _)

private def noLanguage (bits : List Bool) : Bool :=
  @decide
    (∃ record : Instance,
      encodeInstance record = bits ∧
        hasIntegerTarget record ∧ gapNO400 record)
    (Classical.propDecidable _)

private structure PromiseProblem where
  yes : BitLanguage
  no : BitLanguage
  disjoint : ∀ bits, yes bits → no bits → False

/-- GapCVP reduction support. -/
def gapCVP400Promise : PromiseProblem where
  yes := yesLanguage
  no := noLanguage
  disjoint bits positive negative := by
    simp only [yesLanguage, noLanguage, classicalDecide_eq_true_iff]
      at positive negative
    obtain ⟨first, hfirst, _, hyes⟩ := positive
    obtain ⟨second, hsecond, _, hno⟩ := negative
    have same := encodeInstance_injective (hfirst.trans hsecond.symm)
    subst second
    exact gapYES400_not_gapNO400 first hyes hno

private structure BinaryNearestCodewordInstance where
  blockLength : ℕ
  generatorRank : ℕ
  generator : Fin blockLength → Fin generatorRank → ZMod 2
  target : Fin blockLength → ZMod 2
  radius : ℕ

private structure BinarySyndromeDecodingInstance where
  checkCount : ℕ
  blockLength : ℕ
  parityCheck : Fin checkCount → Fin blockLength → ZMod 2
  syndrome : Fin checkCount → ZMod 2
  radius : ℕ

private def encodeBinaryNearestCodewordInstance
    (record : BinaryNearestCodewordInstance) : List Bool :=
  encodeAtomic record.blockLength ++
    encodeAtomic record.generatorRank ++
    encodeAtomic record.radius ++
    encodeFinValues record.blockLength
      (fun index => ((record.target index).val : ℤ)) ++
    encodeMatrixRows record.blockLength record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))

private def encodeBinarySyndromeDecodingInstance
    (record : BinarySyndromeDecodingInstance) : List Bool :=
  encodeAtomic record.checkCount ++
    encodeAtomic record.blockLength ++
    encodeAtomic record.radius ++
    encodeFinValues record.checkCount
      (fun row => ((record.syndrome row).val : ℤ)) ++
    encodeMatrixRows record.checkCount record.blockLength
      (fun row column => ((record.parityCheck row column).val : ℤ))

private theorem binaryIntegerRepresentative_cast (value : ZMod 2) :
    (((value.val : ℕ) : ℤ) : ZMod 2) = value := by
  rw [Int.cast_natCast]
  exact ZMod.natCast_zmod_val value

private def decodeBinaryNearestCodewordInstance
    (bits : List Bool) : Option BinaryNearestCodewordInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (blockLength, afterBlockLength) =>
      match (readAtomic afterBlockLength : Option (ℕ × List Bool)) with
      | none => none
      | some (generatorRank, afterGeneratorRank) =>
          match (readAtomic afterGeneratorRank : Option (ℕ × List Bool)) with
          | none => none
          | some (radius, afterRadius) =>
              match (readFinValues blockLength afterRadius :
                Option ((Fin blockLength → ℤ) × List Bool)) with
              | none => none
              | some (target, afterTarget) =>
                  match readMatrixRows blockLength generatorRank afterTarget with
                  | some (generator, []) =>
                      some {
                        blockLength
                        generatorRank
                        generator := fun row column =>
                          (generator row column : ZMod 2)
                        target := fun index => (target index : ZMod 2)
                        radius
                      }
                  | _ => none

@[simp] private theorem decodeBinaryNearestCodewordInstance_encode
    (record : BinaryNearestCodewordInstance) :
    decodeBinaryNearestCodewordInstance
      (encodeBinaryNearestCodewordInstance record) = some record := by
  cases record with
  | mk blockLength generatorRank generator target radius =>
      have matrix :
          readMatrixRows blockLength generatorRank
              (encodeMatrixRows blockLength generatorRank
                (fun row column => ((generator row column).val : ℤ))) =
            some ((fun row column => ((generator row column).val : ℤ)), []) := by
        simpa only [ZMod.natCast_val, List.append_nil] using
            readMatrixRows_append (fun row column => ((generator row column).val : ℤ)) []
      simp only [decodeBinaryNearestCodewordInstance,
        encodeBinaryNearestCodewordInstance, List.append_assoc,
        readAtomic_append, readFinValues_append, matrix,
        binaryIntegerRepresentative_cast]

private theorem encodeBinaryNearestCodewordInstance_injective :
    Function.Injective encodeBinaryNearestCodewordInstance := by
  intro first second same
  simpa only [decodeBinaryNearestCodewordInstance_encode, Option.some.injEq] using
      congrArg decodeBinaryNearestCodewordInstance same

private def decodeBinarySyndromeDecodingInstance
    (bits : List Bool) : Option BinarySyndromeDecodingInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (checkCount, afterCheckCount) =>
      match (readAtomic afterCheckCount : Option (ℕ × List Bool)) with
      | none => none
      | some (blockLength, afterBlockLength) =>
          match (readAtomic afterBlockLength : Option (ℕ × List Bool)) with
          | none => none
          | some (radius, afterRadius) =>
              match (readFinValues checkCount afterRadius :
                Option ((Fin checkCount → ℤ) × List Bool)) with
              | none => none
              | some (syndrome, afterSyndrome) =>
                  match readMatrixRows checkCount blockLength afterSyndrome with
                  | some (parityCheck, []) =>
                      some {
                        checkCount
                        blockLength
                        parityCheck := fun row column =>
                          (parityCheck row column : ZMod 2)
                        syndrome := fun row => (syndrome row : ZMod 2)
                        radius
                      }
                  | _ => none

@[simp] private theorem decodeBinarySyndromeDecodingInstance_encode
    (record : BinarySyndromeDecodingInstance) :
    decodeBinarySyndromeDecodingInstance
      (encodeBinarySyndromeDecodingInstance record) = some record := by
  cases record with
  | mk checkCount blockLength parityCheck syndrome radius =>
      have matrix :
          readMatrixRows checkCount blockLength
              (encodeMatrixRows checkCount blockLength
                (fun row column => ((parityCheck row column).val : ℤ))) =
            some ((fun row column => ((parityCheck row column).val : ℤ)), []) := by
        simpa only [ZMod.natCast_val, List.append_nil] using
            readMatrixRows_append (fun row column => ((parityCheck row column).val : ℤ)) []
      simp only [decodeBinarySyndromeDecodingInstance,
        encodeBinarySyndromeDecodingInstance, List.append_assoc,
        readAtomic_append, readFinValues_append, matrix,
        binaryIntegerRepresentative_cast]

private theorem encodeBinarySyndromeDecodingInstance_injective :
    Function.Injective encodeBinarySyndromeDecodingInstance := by
  intro first second same
  simpa only [decodeBinarySyndromeDecodingInstance_encode, Option.some.injEq] using
      congrArg decodeBinarySyndromeDecodingInstance same

private def binaryNearestCodeword
    (record : BinaryNearestCodewordInstance)
    (coefficients : Fin record.generatorRank → ZMod 2) :
    Fin record.blockLength → ZMod 2 :=
  fun index => ∑ column : Fin record.generatorRank,
    record.generator index column * coefficients column

private def binaryNearestTarget (record : BinaryNearestCodewordInstance) :
    Fin record.blockLength → ZMod 2 :=
  record.target

private def binarySyndromeProduct
    (record : BinarySyndromeDecodingInstance)
    (word : Fin record.blockLength → ZMod 2) :
    Fin record.checkCount → ZMod 2 :=
  fun row => ∑ column : Fin record.blockLength,
    record.parityCheck row column * word column

private def binarySyndromeTarget (record : BinarySyndromeDecodingInstance) :
    Fin record.checkCount → ZMod 2 :=
  record.syndrome

private noncomputable def binaryCodeGapFactor (blockLength : ℕ) : ℝ :=
  (blockLength : ℝ) ^ ((1 : ℝ) / 200)

/-- GapCVP reduction support. -/
noncomputable def binaryNearestCodewordPromise : PromiseProblem where
  yes bits :=
    @decide
      (∃ record : BinaryNearestCodewordInstance,
        encodeBinaryNearestCodewordInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        ∃ coefficients : Fin record.generatorRank → ZMod 2,
          hammingNorm
            (binaryNearestTarget record -
              binaryNearestCodeword record coefficients) ≤ record.radius)
      (Classical.propDecidable _)
  no bits :=
    @decide
      (∃ record : BinaryNearestCodewordInstance,
        encodeBinaryNearestCodewordInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        ∀ coefficients : Fin record.generatorRank → ZMod 2,
          binaryCodeGapFactor record.blockLength *
              (record.radius : ℝ) <
            (hammingNorm
              (binaryNearestTarget record -
                binaryNearestCodeword record coefficients) : ℝ))
      (Classical.propDecidable _)
  disjoint bits positive negative := by
    simp only [classicalDecide_eq_true_iff] at positive negative
    obtain ⟨first, hfirst, dimension, _, coefficients, close⟩ := positive
    obtain ⟨second, hsecond, _, _, far⟩ := negative
    have same :=
      encodeBinaryNearestCodewordInstance_injective
        (hfirst.trans hsecond.symm)
    subst second
    have factor : 1 ≤ binaryCodeGapFactor first.blockLength := by
      unfold binaryCodeGapFactor
      apply Real.one_le_rpow
      · exact_mod_cast dimension
      · norm_num
    have radius : (0 : ℝ) ≤ (first.radius : ℝ) := by positivity
    have closeReal :
        (hammingNorm
          (binaryNearestTarget first -
            binaryNearestCodeword first coefficients) : ℝ) ≤
          (first.radius : ℝ) := by
      exact_mod_cast close
    nlinarith [far coefficients]

/-- GapCVP reduction support. -/
noncomputable def binarySyndromeDecodingPromise : PromiseProblem where
  yes bits :=
    @decide
      (∃ record : BinarySyndromeDecodingInstance,
        encodeBinarySyndromeDecodingInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        ∃ word : Fin record.blockLength → ZMod 2,
          binarySyndromeProduct record word = binarySyndromeTarget record ∧
            hammingNorm word ≤ record.radius)
      (Classical.propDecidable _)
  no bits :=
    @decide
      (∃ record : BinarySyndromeDecodingInstance,
        encodeBinarySyndromeDecodingInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        (∃ word : Fin record.blockLength → ZMod 2,
          binarySyndromeProduct record word = binarySyndromeTarget record) ∧
        ∀ word : Fin record.blockLength → ZMod 2,
          binarySyndromeProduct record word = binarySyndromeTarget record →
            binaryCodeGapFactor record.blockLength *
                (record.radius : ℝ) < (hammingNorm word : ℝ))
      (Classical.propDecidable _)
  disjoint bits positive negative := by
    simp only [classicalDecide_eq_true_iff] at positive negative
    obtain ⟨first, hfirst, dimension, _, word, solution, close⟩ := positive
    obtain ⟨second, hsecond, _, _, _, far⟩ := negative
    have same :=
      encodeBinarySyndromeDecodingInstance_injective
        (hfirst.trans hsecond.symm)
    subst second
    have factor : 1 ≤ binaryCodeGapFactor first.blockLength := by
      unfold binaryCodeGapFactor
      apply Real.one_le_rpow
      · exact_mod_cast dimension
      · norm_num
    have radius : (0 : ℝ) ≤ (first.radius : ℝ) := by positivity
    have closeReal : (hammingNorm word : ℝ) ≤ (first.radius : ℝ) := by
      exact_mod_cast close
    nlinarith [far word solution]

private noncomputable def finitePNorm (p : ℚ) {n : ℕ} (vector : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, |vector i| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹)

private noncomputable def finitePLatticeDiscrepancy (I : Instance)
    (vector : Fin I.dimension → ℤ) : Fin I.dimension → ℝ := fun i =>
  (I.target i : ℝ) -
    ∑ j : Fin I.dimension, (I.basis i j : ℝ) * (vector j : ℝ)

private noncomputable def finitePLatticeDistance (p : ℚ) (I : Instance)
    (vector : Fin I.dimension → ℤ) : ℝ :=
  finitePNorm p (finitePLatticeDiscrepancy I vector)

private noncomputable def finitePGapFactor (p : ℚ) (I : Instance) : ℝ :=
  (I.dimension : ℝ) ^ (((200 : ℝ) * (p : ℝ))⁻¹)

/-- GapCVP reduction support. -/
noncomputable def finitePGapCVPPromise (p : ℚ) (hp : 1 ≤ p) : PromiseProblem where
  yes bits :=
    @decide
      (∃ I : Instance,
        encodeInstance I = bits ∧
          wellFormed I ∧
          ∃ vector : Fin I.dimension → ℤ,
            finitePLatticeDistance p I vector ≤ (I.radius : ℝ))
      (Classical.propDecidable _)
  no bits :=
    @decide
      (∃ I : Instance,
        encodeInstance I = bits ∧
          wellFormed I ∧
          ∀ vector : Fin I.dimension → ℤ,
            finitePGapFactor p I * (I.radius : ℝ) <
              finitePLatticeDistance p I vector)
      (Classical.propDecidable _)
  disjoint bits positive negative := by
    have positive' :
        ∃ record : Instance,
          encodeInstance record = bits ∧
            wellFormed record = true ∧
              ∃ vector : Fin record.dimension → ℤ,
                finitePLatticeDistance p record vector ≤
                  (record.radius : ℝ) := by
      apply (classicalDecide_eq_true_iff _).mp
      exact positive
    have negative' :
        ∃ record : Instance,
          encodeInstance record = bits ∧
            wellFormed record = true ∧
              ∀ vector : Fin record.dimension → ℤ,
                finitePGapFactor p record * (record.radius : ℝ) <
                  finitePLatticeDistance p record vector := by
      apply (classicalDecide_eq_true_iff _).mp
      exact negative
    obtain ⟨first, hfirst, wellDecision, vector, close⟩ := positive'
    obtain ⟨second, hsecond, _, far⟩ := negative'
    have well :
        0 < first.dimension ∧ first.basis.det ≠ 0 ∧
          0 < first.radius := by
      apply (classicalDecide_eq_true_iff _).mp
      exact wellDecision
    have same := encodeInstance_injective (hfirst.trans hsecond.symm)
    subst second
    have exponent : 0 ≤ (((200 : ℝ) * (p : ℝ))⁻¹) := by
      have parameter : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hp)
      positivity
    have factor : 1 ≤ finitePGapFactor p first := by
      unfold finitePGapFactor
      apply Real.one_le_rpow
      · exact_mod_cast well.1
      · exact exponent
    have radius : 0 < (first.radius : ℝ) := by
      exact_mod_cast well.2.2
    nlinarith [far vector]

private structure PromiseReduction (language : BitLanguage) (problem : PromiseProblem) where
  map : List Bool → List Bool
  polynomial_time : Nonempty
    (BitTM map)
  completeness : ∀ input, language input → problem.yes (map input)
  soundness : ∀ input, ¬ language input → problem.no (map input)

/-- GapCVP reduction support. -/
def IsNPHardPromise (problem : PromiseProblem) : Bool :=
  @decide
    (∀ language : BitLanguage,
      IsNP language → Nonempty (PromiseReduction language problem))
    (Classical.propDecidable _)

private def toOriginal (I : Instance) : GapCVP.GapCVPInstance :=
  ⟨I.dimension, I.basis, I.target, I.radius⟩

private def ofOriginal (I : GapCVP.GapCVPInstance) : Instance :=
  ⟨I.dimension, I.basis, I.target, I.radius⟩

@[simp] private theorem toOriginal_ofOriginal (I : GapCVP.GapCVPInstance) :
    toOriginal (ofOriginal I) = I := rfl

private def toOriginalNearest (record : BinaryNearestCodewordInstance) :
    GapCVP.Factor400BinaryDecodingPromiseReduction.BinaryNearestCodewordInstance :=
  ⟨record.blockLength, record.generatorRank, record.generator,
    record.target, record.radius⟩

private def ofOriginalNearest
    (record : GapCVP.Factor400BinaryDecodingPromiseReduction.BinaryNearestCodewordInstance) :
    BinaryNearestCodewordInstance :=
  ⟨record.blockLength, record.generatorRank, record.generator,
    record.target, record.radius⟩

@[simp] private theorem toOriginalNearest_ofOriginalNearest
    (record : GapCVP.Factor400BinaryDecodingPromiseReduction.BinaryNearestCodewordInstance) :
    toOriginalNearest (ofOriginalNearest record) = record := rfl

private def toOriginalSyndrome (record : BinarySyndromeDecodingInstance) :
    GapCVP.Factor400BinaryDecodingPromiseReduction.BinarySyndromeDecodingInstance :=
  ⟨record.checkCount, record.blockLength, record.parityCheck,
    record.syndrome, record.radius⟩

private def ofOriginalSyndrome
    (record : GapCVP.Factor400BinaryDecodingPromiseReduction.BinarySyndromeDecodingInstance) :
    BinarySyndromeDecodingInstance :=
  ⟨record.checkCount, record.blockLength, record.parityCheck,
    record.syndrome, record.radius⟩

@[simp] private theorem toOriginalSyndrome_ofOriginalSyndrome
    (record : GapCVP.Factor400BinaryDecodingPromiseReduction.BinarySyndromeDecodingInstance) :
    toOriginalSyndrome (ofOriginalSyndrome record) = record := rfl

private theorem yesLanguage_iff_original (bits : List Bool) :
    yesLanguage bits ↔
      integerTargetGapCVP400Promise.yes
          bits := by
  simp only [yesLanguage, hasIntegerTarget, gapYES400, wellFormed,
    integerTargetGapCVP400Promise, HasIntegerTarget,
    GapCVP.gapYES400, GapCVP.gapCVPWellFormed]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [encodeInstance, toOriginal]
    rfl

private theorem noLanguage_iff_original (bits : List Bool) :
    noLanguage bits ↔
      integerTargetGapCVP400Promise.no
          bits := by
  simp only [noLanguage, hasIntegerTarget, gapNO400, wellFormed,
    integerTargetGapCVP400Promise, HasIntegerTarget,
    GapCVP.gapNO400, GapCVP.gapCVPWellFormed]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [encodeInstance, toOriginal]
    rfl

private theorem binaryNearestCodeword_yes_iff_original (bits : List Bool) :
    binaryNearestCodewordPromise.yes bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise.yes bits := by
  simp only [binaryNearestCodewordPromise,
    GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginalNearest_ofOriginalNearest).exists]
  exact exists_congr fun _ => by
    simp only [encodeBinaryNearestCodewordInstance, toOriginalNearest,
      GapCVP.Factor400BinaryDecodingPromiseReduction.encodeBinaryNearestCodewordInstance]
    rfl

private theorem binaryNearestCodeword_no_iff_original (bits : List Bool) :
    binaryNearestCodewordPromise.no bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise.no bits := by
  simp only [binaryNearestCodewordPromise,
    GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginalNearest_ofOriginalNearest).exists]
  exact exists_congr fun _ => by
    simp only [encodeBinaryNearestCodewordInstance, toOriginalNearest,
      GapCVP.Factor400BinaryDecodingPromiseReduction.encodeBinaryNearestCodewordInstance]
    rfl

private theorem binarySyndromeDecoding_yes_iff_original (bits : List Bool) :
    binarySyndromeDecodingPromise.yes bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise.yes bits := by
  simp only [binarySyndromeDecodingPromise,
    GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginalSyndrome_ofOriginalSyndrome).exists]
  exact exists_congr fun _ => by
    simp only [encodeBinarySyndromeDecodingInstance, toOriginalSyndrome,
      GapCVP.Factor400BinaryDecodingPromiseReduction.encodeBinarySyndromeDecodingInstance]
    rfl

private theorem binarySyndromeDecoding_no_iff_original (bits : List Bool) :
    binarySyndromeDecodingPromise.no bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise.no bits := by
  simp only [binarySyndromeDecodingPromise,
    GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginalSyndrome_ofOriginalSyndrome).exists]
  exact exists_congr fun _ => by
    simp only [encodeBinarySyndromeDecodingInstance, toOriginalSyndrome,
      GapCVP.Factor400BinaryDecodingPromiseReduction.encodeBinarySyndromeDecodingInstance]
    rfl

private theorem finiteP_yes_iff_original (p : ℚ) (hp : 1 ≤ p)
    (bits : List Bool) :
    (finitePGapCVPPromise p hp).yes bits ↔
      (GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise p hp).yes bits := by
  simp only [finitePGapCVPPromise, wellFormed,
    GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise,
    GapCVP.gapCVPWellFormed]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [GapCVP.binaryFinEncoding, encodeInstance, toOriginal]
    rfl

private theorem finiteP_no_iff_original (p : ℚ) (hp : 1 ≤ p)
    (bits : List Bool) :
    (finitePGapCVPPromise p hp).no bits ↔
      (GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise p hp).no bits := by
  simp only [finitePGapCVPPromise, wellFormed,
    GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise,
    GapCVP.gapCVPWellFormed]
  apply classicalDecide_congr
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [GapCVP.binaryFinEncoding, encodeInstance, toOriginal]
    rfl

private theorem isNPHardPromise_of_original
    {problem : PromiseProblem} {original : GapCVP.PromiseProblem}
    (hyes : ∀ bits, problem.yes bits ↔ original.yes bits)
    (hno : ∀ bits, problem.no bits ↔ original.no bits)
    (hard : GapCVP.NPHardPromise original) :
    IsNPHardPromise problem := by
  unfold IsNPHardPromise
  apply (classicalDecide_eq_true_iff _).mpr
  intro language hnp
  have original_hnp : GapCVP.IsNP language := hnp
  have original_hard :
      ∀ language : GapCVP.BitLanguage,
        GapCVP.IsNP language →
          Nonempty (GapCVP.PromiseReduction language original) := by
    apply (classicalDecide_eq_true_iff _).mp
    exact hard
  obtain ⟨reduction⟩ := original_hard language original_hnp
  exact ⟨{
    map := reduction.map
    polynomial_time := reduction.polynomial_time
    completeness := fun input hinput =>
      (hyes _).mpr (reduction.completeness input hinput)
    soundness := fun input hinput =>
      (hno _).mpr (reduction.soundness input hinput)
  }⟩

theorem gapCVP400IsNPHard : IsNPHardPromise gapCVP400Promise :=
  isNPHardPromise_of_original yesLanguage_iff_original noLanguage_iff_original
    paperVariableArityPhysicalIntegerTargetNPHardPromise

theorem binaryNearestCodewordIsNPHard :
    IsNPHardPromise binaryNearestCodewordPromise :=
  isNPHardPromise_of_original
    binaryNearestCodeword_yes_iff_original
    binaryNearestCodeword_no_iff_original
    binaryNearestCodeword_nphard_unconditional

theorem binarySyndromeDecodingIsNPHard :
    IsNPHardPromise binarySyndromeDecodingPromise :=
  isNPHardPromise_of_original
    binarySyndromeDecoding_yes_iff_original
    binarySyndromeDecoding_no_iff_original
    binarySyndromeDecoding_nphard_unconditional

theorem finitePNormGapCVPIsNPHard (p : ℚ) (hp : 1 ≤ p) :
    IsNPHardPromise (finitePGapCVPPromise p hp) :=
  isNPHardPromise_of_original
    (finiteP_yes_iff_original p hp)
    (finiteP_no_iff_original p hp)
    (paperVariableArityFinitePNPHardPromise p hp)

end Comparator

end GapCVP

end

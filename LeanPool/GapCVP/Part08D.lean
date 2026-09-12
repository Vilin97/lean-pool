/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part08C

/-! # GapCVP proof, part 08, continuation 04 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction

open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceUniformTuringTM

open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatStructuralRecordWorkerTM

open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFUnaryPairIndexTM

open GapCVP.CNFPairedSourceGridDescriptorTM GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.CNFAnnotatedSourceClausePairPreparationTM

private noncomputable def flatIndexedGadgetNegateLeadingBitComputable :
    BitTM
      flatIndexedGadgetNegateLeadingBitWord where
  tm := flatIndexedGadgetNegateLeadingBitMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun input := {
    steps := 1
    evals_in_steps := by
      rw [Function.iterate_one, Option.bind_eq_bind]
      simp only [flip]
      rw [Option.bind_some]
      simpa only [FinTM2.step, Equiv.invFun_as_coe, Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun,
          Option.map_some] using
            flatIndexedGadgetNegateLeadingBitMachine_step input
    steps_le_m := by simp only [id_eq, Polynomial.eval_one, Std.le_refl]
  }

private def flatIndexedGadgetSourcePayloadWord
    (state : List Bool) : List Bool :=
  firstFieldContents (flatAnnotatedSourceFieldAt 3 state)

private noncomputable def flatIndexedGadgetSourcePayloadComputable :
    BitTM
      flatIndexedGadgetSourcePayloadWord := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 3)
    firstFieldContentsComputable
  change BitTM
    (fun state : List Bool =>
      firstFieldContents (flatAnnotatedSourceFieldAt 3 state))
  simpa only [Function.comp_def] using physical

private def flatIndexedGadgetSourceDescriptorWord
    (negated : Bool) (state : List Bool) : List Bool :=
  lengthPrefixedWord
    (if negated then
      flatIndexedGadgetNegateLeadingBitWord
        (flatIndexedGadgetSourcePayloadWord state)
    else
      flatIndexedGadgetSourcePayloadWord state)

private noncomputable def flatIndexedGadgetSourceDescriptorComputable
    (negated : Bool) :
    BitTM
      (flatIndexedGadgetSourceDescriptorWord negated) := by
  cases negated with
  | false =>
      have physical := GapCVP.TMComposition.computableInPolyTime
        flatIndexedGadgetSourcePayloadComputable
        structuralPrefixWriterComputable
      change BitTM
        (fun state : List Bool =>
          lengthPrefixedWord (flatIndexedGadgetSourcePayloadWord state))
      simpa only [Function.comp_def] using physical
  | true =>
      have negate := GapCVP.TMComposition.computableInPolyTime
        flatIndexedGadgetSourcePayloadComputable
        flatIndexedGadgetNegateLeadingBitComputable
      have physical := GapCVP.TMComposition.computableInPolyTime
        negate structuralPrefixWriterComputable
      change BitTM
        (fun state : List Bool => lengthPrefixedWord
          (flatIndexedGadgetNegateLeadingBitWord
            (flatIndexedGadgetSourcePayloadWord state)))
      simpa only [Function.comp_def] using physical

private def flatIndexedGadgetAccumulatorPairWord
    (next : Bool) (state : List Bool) : List Bool :=
  (flatAnnotatedSourceFieldAt 0 state ++ [false]) ++
    ((if next then flatAnnotatedSourceFieldAt 1 state
      else (flatAnnotatedSourceFieldAt 1 state).tail) ++ [false])

private noncomputable def flatIndexedGadgetAccumulatorPairComputable
    (next : Bool) :
    BitTM
      (flatIndexedGadgetAccumulatorPairWord next) := by
  have first := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable 0)
    (constantWordComputable [false])
  cases next with
  | false =>
      have predecessor := GapCVP.TMComposition.computableInPolyTime
        (annotatedSourceFieldAtComputable 1)
        dropHeadComputable
      have second := pointwiseAppendComputable
        predecessor (constantWordComputable [false])
      have physical := pointwiseAppendComputable first second
      change BitTM
        (fun state : List Bool =>
          (flatAnnotatedSourceFieldAt 0 state ++ [false]) ++
            ((flatAnnotatedSourceFieldAt 1 state).tail ++ [false]))
      simpa only [Function.comp_def] using physical
  | true =>
      have second := pointwiseAppendComputable
        (annotatedSourceFieldAtComputable 1)
        (constantWordComputable [false])
      have physical := pointwiseAppendComputable first second
      change BitTM
        (fun state : List Bool =>
          (flatAnnotatedSourceFieldAt 0 state ++ [false]) ++
            (flatAnnotatedSourceFieldAt 1 state ++ [false]))
      simpa only [Function.comp_def] using physical

private def flatIndexedGadgetAccumulatorDescriptorWord
    (next sign : Bool) (state : List Bool) : List Bool :=
  pairedAccumulatorSignedLiteralDescriptorWord sign
    (flatIndexedGadgetAccumulatorPairWord next state)

private noncomputable def flatIndexedGadgetAccumulatorDescriptorComputable
    (next sign : Bool) :
    BitTM
      (flatIndexedGadgetAccumulatorDescriptorWord next sign) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatIndexedGadgetAccumulatorPairComputable next)
    (pairedAccumulatorSignedLiteralDescriptorComputable sign)
  change BitTM
    (fun state : List Bool =>
      pairedAccumulatorSignedLiteralDescriptorWord sign
        (flatIndexedGadgetAccumulatorPairWord next state))
  simpa only [Function.comp_def] using physical

private def flatIndexedGadgetPaddingDescriptorWord
    (which : Bool) (sign : Bool) (state : List Bool) : List Bool :=
  paddingSignedLiteralDescriptorWord
    (if which then 3 else 2)
    sign state

private noncomputable def flatIndexedGadgetPaddingDescriptorComputable
    (which sign : Bool) :
    BitTM
      (flatIndexedGadgetPaddingDescriptorWord which sign) := by
  exact paddingSignedLiteralDescriptorComputable
    (if which then 3 else 2) sign

private def flatIndexedGadgetThreeDescriptorWord
    (first second third : List Bool → List Bool)
    (state : List Bool) : List Bool :=
  first state ++ second state ++ third state

private noncomputable def flatIndexedGadgetThreeDescriptorComputable
    {first second third : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second)
    (hthird : BitTM third) :
    BitTM
      (flatIndexedGadgetThreeDescriptorWord first second third) := by
  have tail := pointwiseAppendComputable hsecond hthird
  have physical := pointwiseAppendComputable hfirst tail
  change BitTM
    (fun state : List Bool =>
      first state ++ second state ++ third state)
  simpa only [List.append_assoc] using physical

private def flatIndexedSourceORGadgetDescriptorWord
    (state : List Bool) : List Bool :=
  flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetSourceDescriptorWord true)
      (flatIndexedGadgetAccumulatorDescriptorWord false true)
      (flatIndexedGadgetPaddingDescriptorWord false true) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetSourceDescriptorWord true)
      (flatIndexedGadgetAccumulatorDescriptorWord false true)
      (flatIndexedGadgetPaddingDescriptorWord false false) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetAccumulatorDescriptorWord true false)
      (flatIndexedGadgetAccumulatorDescriptorWord false true)
      (flatIndexedGadgetPaddingDescriptorWord false true) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetAccumulatorDescriptorWord true false)
      (flatIndexedGadgetAccumulatorDescriptorWord false true)
      (flatIndexedGadgetPaddingDescriptorWord false false) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetSourceDescriptorWord false)
      (flatIndexedGadgetAccumulatorDescriptorWord true true)
      (flatIndexedGadgetAccumulatorDescriptorWord false false) state

private noncomputable def flatIndexedSourceORGadgetDescriptorComputable :
    BitTM
      flatIndexedSourceORGadgetDescriptorWord := by
  have hsource := flatIndexedGadgetSourceDescriptorComputable false
  have hnegative := flatIndexedGadgetSourceDescriptorComputable true
  have hcurrent := flatIndexedGadgetAccumulatorDescriptorComputable
    false true
  have hcurrentNegative := flatIndexedGadgetAccumulatorDescriptorComputable
    false false
  have hnext := flatIndexedGadgetAccumulatorDescriptorComputable true true
  have hnextNegative :=
    flatIndexedGadgetAccumulatorDescriptorComputable true false
  have hpadTrue := flatIndexedGadgetPaddingDescriptorComputable
    false true
  have hpadFalse := flatIndexedGadgetPaddingDescriptorComputable
    false false
  have hfirst := flatIndexedGadgetThreeDescriptorComputable
    hnegative hcurrent hpadTrue
  have hsecond := flatIndexedGadgetThreeDescriptorComputable
    hnegative hcurrent hpadFalse
  have hthird := flatIndexedGadgetThreeDescriptorComputable
    hnextNegative hcurrent hpadTrue
  have hfourth := flatIndexedGadgetThreeDescriptorComputable
    hnextNegative hcurrent hpadFalse
  have hfifth := flatIndexedGadgetThreeDescriptorComputable
    hsource hnext hcurrentNegative
  have physical := pointwiseAppendComputable hfirst
    (pointwiseAppendComputable hsecond
      (pointwiseAppendComputable hthird
        (pointwiseAppendComputable hfourth hfifth)))
  change BitTM
    (fun state : List Bool =>
      flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetSourceDescriptorWord true)
          (flatIndexedGadgetAccumulatorDescriptorWord false true)
          (flatIndexedGadgetPaddingDescriptorWord false true) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetSourceDescriptorWord true)
          (flatIndexedGadgetAccumulatorDescriptorWord false true)
          (flatIndexedGadgetPaddingDescriptorWord false false) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetAccumulatorDescriptorWord true false)
          (flatIndexedGadgetAccumulatorDescriptorWord false true)
          (flatIndexedGadgetPaddingDescriptorWord false true) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetAccumulatorDescriptorWord true false)
          (flatIndexedGadgetAccumulatorDescriptorWord false true)
          (flatIndexedGadgetPaddingDescriptorWord false false) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetSourceDescriptorWord false)
          (flatIndexedGadgetAccumulatorDescriptorWord true true)
          (flatIndexedGadgetAccumulatorDescriptorWord false false) state)
  simpa only [List.append_assoc] using physical

private def flatIndexedSourceORPaddingDescriptorWord
    (sign : Bool) (state : List Bool) : List Bool :=
  flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetAccumulatorDescriptorWord false sign)
      (flatIndexedGadgetPaddingDescriptorWord false false)
      (flatIndexedGadgetPaddingDescriptorWord true false) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetAccumulatorDescriptorWord false sign)
      (flatIndexedGadgetPaddingDescriptorWord false false)
      (flatIndexedGadgetPaddingDescriptorWord true true) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetAccumulatorDescriptorWord false sign)
      (flatIndexedGadgetPaddingDescriptorWord false true)
      (flatIndexedGadgetPaddingDescriptorWord true false) state ++
    flatIndexedGadgetThreeDescriptorWord
      (flatIndexedGadgetAccumulatorDescriptorWord false sign)
      (flatIndexedGadgetPaddingDescriptorWord false true)
      (flatIndexedGadgetPaddingDescriptorWord true true) state

private noncomputable def flatIndexedSourceORPaddingDescriptorComputable
    (sign : Bool) :
    BitTM
      (flatIndexedSourceORPaddingDescriptorWord sign) := by
  have haccumulator := flatIndexedGadgetAccumulatorDescriptorComputable
    false sign
  have hzeroFalse := flatIndexedGadgetPaddingDescriptorComputable
    false false
  have hzeroTrue := flatIndexedGadgetPaddingDescriptorComputable
    false true
  have honeFalse := flatIndexedGadgetPaddingDescriptorComputable
    true false
  have honeTrue := flatIndexedGadgetPaddingDescriptorComputable
    true true
  have hfirst := flatIndexedGadgetThreeDescriptorComputable
    haccumulator hzeroFalse honeFalse
  have hsecond := flatIndexedGadgetThreeDescriptorComputable
    haccumulator hzeroFalse honeTrue
  have hthird := flatIndexedGadgetThreeDescriptorComputable
    haccumulator hzeroTrue honeFalse
  have hfourth := flatIndexedGadgetThreeDescriptorComputable
    haccumulator hzeroTrue honeTrue
  have physical := pointwiseAppendComputable hfirst
    (pointwiseAppendComputable hsecond
      (pointwiseAppendComputable hthird hfourth))
  change BitTM
    (fun state : List Bool =>
      flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetAccumulatorDescriptorWord false sign)
          (flatIndexedGadgetPaddingDescriptorWord false false)
          (flatIndexedGadgetPaddingDescriptorWord true false) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetAccumulatorDescriptorWord false sign)
          (flatIndexedGadgetPaddingDescriptorWord false false)
          (flatIndexedGadgetPaddingDescriptorWord true true) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetAccumulatorDescriptorWord false sign)
          (flatIndexedGadgetPaddingDescriptorWord false true)
          (flatIndexedGadgetPaddingDescriptorWord true false) state ++
        flatIndexedGadgetThreeDescriptorWord
          (flatIndexedGadgetAccumulatorDescriptorWord false sign)
          (flatIndexedGadgetPaddingDescriptorWord false true)
          (flatIndexedGadgetPaddingDescriptorWord true true) state)
  simpa only [List.append_assoc] using physical

@[simp] private theorem flatIndexedGadgetAccumulatorDescriptorWord_valid
    (clauseIndex prefixIndex : ℕ)
    (pending active emitted count : List Bool)
    (next sign : Bool) :
    flatIndexedGadgetAccumulatorDescriptorWord next sign
        (flatAnnotatedIndexedORGadgetState
          (List.replicate clauseIndex true)
          (List.replicate (prefixIndex + 1) true)
          pending active emitted count) =
      flatSignedLiteralDescriptor
        (accumulatorVariable clauseIndex
          (if next then prefixIndex + 1 else prefixIndex), sign) := by
  cases next with
  | false =>
      simpa only [flatIndexedGadgetAccumulatorDescriptorWord, flatIndexedGadgetAccumulatorPairWord,
          flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
              flatAnnotatedIndexedORGadgetState, List.replicate_succ,
          List.append_assoc, Function.iterate_zero, id_eq, firstFieldContents_valid,
              Bool.false_eq_true, ↓reduceIte,
          Function.iterate_one, firstFieldSuffix_valid, List.tail_cons, List.cons_append,
              List.nil_append,
          unarySourcePairWord] using (pairedAccumulatorSignedLiteralDescriptorWord_pair clauseIndex
              prefixIndex sign)
  | true =>
      simpa only [flatIndexedGadgetAccumulatorDescriptorWord, flatIndexedGadgetAccumulatorPairWord,
          flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
              flatAnnotatedIndexedORGadgetState, List.replicate_succ,
          List.append_assoc, Function.iterate_zero, id_eq, firstFieldContents_valid, ↓reduceIte,
              Function.iterate_one,
          firstFieldSuffix_valid, List.cons_append, List.nil_append, unarySourcePairWord] using
          (pairedAccumulatorSignedLiteralDescriptorWord_pair clauseIndex (prefixIndex + 1) sign)

@[simp] private theorem flatIndexedGadgetAccumulatorDescriptorWord_valid_initial
    (clauseIndex : ℕ)
    (pending active emitted count : List Bool)
    (sign : Bool) :
    flatIndexedGadgetAccumulatorDescriptorWord false sign
        (flatAnnotatedIndexedORGadgetState
          (List.replicate clauseIndex true)
          [] pending active emitted count) =
      flatSignedLiteralDescriptor
        (accumulatorVariable clauseIndex 0, sign) := by
  simpa only [flatIndexedGadgetAccumulatorDescriptorWord, flatIndexedGadgetAccumulatorPairWord,
      flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail, flatAnnotatedIndexedORGadgetState,
          List.append_assoc,
      Function.iterate_zero, id_eq, firstFieldContents_valid, Bool.false_eq_true, ↓reduceIte,
          Function.iterate_one,
      firstFieldSuffix_valid, List.tail_nil, List.nil_append, List.cons_append,
          unarySourcePairWord,
      List.replicate_zero] using (pairedAccumulatorSignedLiteralDescriptorWord_pair clauseIndex 0
          sign)

@[simp] private theorem flatIndexedGadgetSourceDescriptorWord_valid
    (literal : Literal)
    (clauseIndex prefixWord pending remaining emitted count : List Bool)
    (negated : Bool) :
    flatIndexedGadgetSourceDescriptorWord negated
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending
          (flatSignedLiteralDescriptor literal ++ remaining)
          emitted count) =
      flatSignedLiteralDescriptor
        (if negated then negate literal else literal) := by
  rcases literal with ⟨index, sign⟩
  cases negated <;> cases sign <;>
    simp [flatIndexedGadgetSourceDescriptorWord,
      flatIndexedGadgetSourcePayloadWord,
      flatIndexedGadgetNegateLeadingBitWord,
      flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      flatAnnotatedIndexedORGadgetState,
      flatSignedLiteralDescriptor, negate,
      Function.iterate_succ_apply', List.append_assoc]

private theorem flatIndexedSourceORGadgetDescriptorWord_valid
    (clauseIndex prefixIndex : ℕ) (literal : Literal)
    (pending remaining emitted count : List Bool) :
    flatIndexedSourceORGadgetDescriptorWord
        (flatAnnotatedIndexedORGadgetState
          (List.replicate clauseIndex true)
          (List.replicate (prefixIndex + 1) true)
          pending (flatSignedLiteralDescriptor literal ++ remaining)
          emitted count) =
      flatSignedLiteralDescriptorStream
        (flatThreeClauseLiterals
          (orGate literal
            (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
            (accumulatorLiteral clauseIndex prefixIndex true))) := by
  simp only [flatIndexedSourceORGadgetDescriptorWord, flatIndexedGadgetThreeDescriptorWord,
      flatIndexedGadgetSourceDescriptorWord_valid, ↓reduceIte, negate,
          flatIndexedGadgetAccumulatorDescriptorWord_valid,
      Bool.false_eq_true, flatIndexedGadgetPaddingDescriptorWord,
          paddingSignedLiteralDescriptorWord_eq,
      List.append_assoc, flatSignedLiteralDescriptorStream, flatThreeClauseLiterals, Fin.isValue,
          orGate, paddedBinary,
      triple, accumulatorLiteral, Bool.not_true, List.cons_append, List.nil_append,
          List.flatMap_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, List.flatMap_nil,
          List.append_nil]

private theorem flatIndexedSourceORPaddingDescriptorWord_valid
    (clauseIndex prefixIndex : ℕ) (sign : Bool)
    (pending active emitted count : List Bool) :
    flatIndexedSourceORPaddingDescriptorWord sign
        (flatAnnotatedIndexedORGadgetState
          (List.replicate clauseIndex true)
          (List.replicate (prefixIndex + 1) true)
          pending active emitted count) =
      flatSignedLiteralDescriptorStream
        (flatThreeClauseLiterals
          (paddedUnary
            (accumulatorLiteral clauseIndex prefixIndex sign))) := by
  simp only [flatIndexedSourceORPaddingDescriptorWord, flatIndexedGadgetThreeDescriptorWord,
      flatIndexedGadgetAccumulatorDescriptorWord_valid, Bool.false_eq_true, ↓reduceIte,
      flatIndexedGadgetPaddingDescriptorWord, paddingSignedLiteralDescriptorWord_eq,
          List.append_assoc,
      flatSignedLiteralDescriptorStream, flatThreeClauseLiterals, Fin.isValue, paddedUnary, triple,
          accumulatorLiteral,
      List.flatMap_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append]

private theorem flatIndexedSourceORPaddingDescriptorWord_valid_initial
    (clauseIndex : ℕ) (sign : Bool)
    (pending active emitted count : List Bool) :
    flatIndexedSourceORPaddingDescriptorWord sign
        (flatAnnotatedIndexedORGadgetState
          (List.replicate clauseIndex true)
          [] pending active emitted count) =
      flatSignedLiteralDescriptorStream
        (flatThreeClauseLiterals
          (paddedUnary (accumulatorLiteral clauseIndex 0 sign))) := by
  simp only [flatIndexedSourceORPaddingDescriptorWord, flatIndexedGadgetThreeDescriptorWord,
      flatIndexedGadgetAccumulatorDescriptorWord_valid_initial,
          flatIndexedGadgetPaddingDescriptorWord,
      Bool.false_eq_true, ↓reduceIte, paddingSignedLiteralDescriptorWord_eq, List.append_assoc,
      flatSignedLiteralDescriptorStream, flatThreeClauseLiterals, Fin.isValue, paddedUnary, triple,
          accumulatorLiteral,
      List.flatMap_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append]

end CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM

namespace CNFGuardedSourceDescriptorCompositeFoldTM

open Computability Turing GapCVP.CLVerifier GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CNFFlatStructuralRecordWorkerTM

private theorem guardedSourcePair_le_quadratic
    (first second : ℕ) :
    Nat.pair first second ≤
      (first + second) * (first + second) + (first + second) := by
  unfold Nat.pair
  split <;> nlinarith

private theorem guardedSourcePair_quadratic_lt_two_pow
    (count : ℕ) :
    4 * (count * count + count) + 1 <
      2 ^ ((count + 12) / 2) := by
  induction count using Nat.strong_induction_on with
  | h count ih =>
      by_cases hsmall : count < 7
      · interval_cases count <;> norm_num
      · have hcount : 7 ≤ count := by omega
        let previous := count - 2
        have hprevious : 5 ≤ previous := by
          dsimp [previous]
          omega
        have hlt : previous < count := by
          dsimp [previous]
          omega
        have hinduction := ih previous hlt
        have hproduct : 5 * previous ≤ previous * previous := by
          have hmul := Nat.mul_le_mul_right previous hprevious
          simpa only [Nat.mul_comm, ge_iff_le] using hmul
        have hquadratic :
            4 * ((previous + 2) * (previous + 2) +
              (previous + 2)) + 1 ≤
              2 * (4 * (previous * previous + previous) + 1) := by
          linarith
        have hdiv :
            (previous + 2 + 12) / 2 =
              (previous + 12) / 2 + 1 := by
          omega
        have hexponent :
            2 ^ ((previous + 2 + 12) / 2) =
              2 * 2 ^ ((previous + 12) / 2) := by
          rw [hdiv, pow_succ]
          omega
        have hrecover : count = previous + 2 := by
          dsimp [previous]
          omega
        rw [hrecover, hexponent]
        omega

private theorem guardedSourcePair_size_le
    (first second : ℕ) :
    Nat.size (4 * Nat.pair first second + 1) ≤
      (first + second + 12) / 2 := by
  apply Nat.size_le.mpr
  have hpair := guardedSourcePair_le_quadratic first second
  have hexponent := guardedSourcePair_quadratic_lt_two_pow
    (first + second)
  omega

private theorem guardedSourceAccumulatorDescriptor_length_le
    (first second : ℕ) (sign : Bool) :
    (flatSignedLiteralDescriptor
      (accumulatorVariable first second, sign)).length ≤
      first + second + 15 := by
  have hsize := guardedSourcePair_size_le first second
  change (lengthPrefixedWord
    (sign :: Computability.encodeNat
      (4 * Nat.pair first second + 1))).length ≤ _
  simp only [lengthPrefixedWord_length,
    List.length_cons, encodeNat_length_eq_size]
  omega

end CNFGuardedSourceDescriptorCompositeFoldTM

namespace CNFFiveFamilySourceIndexedORGadgetFoldCoreTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM

/-- GapCVP reduction support. -/
def flatAnnotatedIndexedORGadgetState
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    List Bool :=
  lengthPrefixedWord clauseIndex ++
    lengthPrefixedWord prefixWord ++
      lengthPrefixedWord pending ++
        lengthPrefixedWord active ++
          lengthPrefixedWord emitted ++
            lengthPrefixedWord count

@[simp] private theorem flatAnnotatedIndexedORGadgetState_field_zero
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedSourceFieldAt 0
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      clauseIndex := by
  simp only [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      flatAnnotatedIndexedORGadgetState,
      List.append_assoc, Function.iterate_zero, id_eq, firstFieldContents_valid]

@[simp] private theorem flatAnnotatedIndexedORGadgetState_field_one
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedSourceFieldAt 1
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      prefixWord := by
  simp only [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      flatAnnotatedIndexedORGadgetState,
      List.append_assoc, Function.iterate_one, firstFieldSuffix_valid, firstFieldContents_valid]

@[simp] private theorem flatAnnotatedIndexedORGadgetState_field_two
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedSourceFieldAt 2
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      pending := by
  simp [flatAnnotatedIndexedORGadgetState,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] private theorem flatAnnotatedIndexedORGadgetState_field_three
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedSourceFieldAt 3
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      active := by
  simp [flatAnnotatedIndexedORGadgetState,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] private theorem flatAnnotatedIndexedORGadgetState_field_four
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedSourceFieldAt 4
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      emitted := by
  simp [flatAnnotatedIndexedORGadgetState,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] private theorem flatAnnotatedIndexedORGadgetState_field_five
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedSourceFieldAt 5
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      count := by
  simpa [flatAnnotatedIndexedORGadgetState,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', List.append_assoc] using
    (firstFieldContents_valid count [])

@[simp] private theorem flatAnnotatedIndexedORGadgetState_length
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    (flatAnnotatedIndexedORGadgetState
      clauseIndex prefixWord pending active emitted count).length =
      2 * (clauseIndex.length + prefixWord.length + pending.length +
        active.length + emitted.length + count.length) + 6 := by
  simp only [flatAnnotatedIndexedORGadgetState, List.append_assoc, List.length_append,
      lengthPrefixedWord_length]
  omega

private noncomputable def orGadgetPrefixedComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (fun input => lengthPrefixedWord (worker input)) :=
  GapCVP.TMComposition.computableInPolyTime
    computer structuralPrefixWriterComputable

private noncomputable def orGadgetStateComputable
    {clauseIndex prefixWord pending active emitted count : List Bool → List Bool}
    (hclause : BitTM clauseIndex)
    (hprefix : BitTM prefixWord)
    (hpending : BitTM pending)
    (hactive : BitTM active)
    (hemitted : BitTM emitted)
    (hcount : BitTM count) :
    BitTM
      (fun input => flatAnnotatedIndexedORGadgetState
        (clauseIndex input) (prefixWord input) (pending input)
        (active input) (emitted input) (count input)) := by
  have hlast := pointwiseAppendComputable
    (orGadgetPrefixedComputable hemitted)
    (orGadgetPrefixedComputable hcount)
  have hfour := pointwiseAppendComputable
    (orGadgetPrefixedComputable hactive) hlast
  have hthree := pointwiseAppendComputable
    (orGadgetPrefixedComputable hpending) hfour
  have htwo := pointwiseAppendComputable
    (orGadgetPrefixedComputable hprefix) hthree
  have physical := pointwiseAppendComputable
    (orGadgetPrefixedComputable hclause) htwo
  change BitTM
    (fun input =>
      lengthPrefixedWord (clauseIndex input) ++
        lengthPrefixedWord (prefixWord input) ++
          lengthPrefixedWord (pending input) ++
            lengthPrefixedWord (active input) ++
              lengthPrefixedWord (emitted input) ++
                lengthPrefixedWord (count input))
  simpa only [List.append_assoc] using physical

private def orGadgetInitialState
    (input : List Bool) : List Bool :=
  flatAnnotatedIndexedORGadgetState [] [] input [] [] []

private noncomputable def flatAnnotatedIndexedORGadgetInitialStateComputable :
    BitTM
      orGadgetInitialState := by
  exact orGadgetStateComputable
    (sourceFixedWordComputable [])
    (sourceFixedWordComputable [])
    (Turing.idComputableInPolyTime bitEncoding)
    (sourceFixedWordComputable [])
    (sourceFixedWordComputable [])
    (sourceFixedWordComputable [])

private def orGadgetFieldHeadMarker
    (offset : ℕ) (input : List Bool) : List Bool :=
  fiveFamilyOriginalHeadBitWord
    (flatAnnotatedSourceFieldAt offset input)

private noncomputable def orGadgetFieldHeadComputable
    (offset : ℕ) :
    BitTM
      (orGadgetFieldHeadMarker offset) := by
  exact GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    fiveFamilyOriginalHeadBitComputable

private def orGadgetBooleanOr
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput first second

private noncomputable def flatAnnotatedIndexedORGadgetBooleanOrComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (orGadgetBooleanOr first second) :=
  sourceFourFamilyBooleanOrComputable hfirst hsecond

private theorem flatAnnotatedIndexedORGadgetBooleanOr_bits
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (hfirst : first input = [firstBit])
    (hsecond : second input = [secondBit]) :
    orGadgetBooleanOr first second input =
      [firstBit || secondBit] :=
  fourFamilyBooleanOrOutput_bits first second input firstBit secondBit
    hfirst hsecond

private def flatAnnotatedIndexedORGadgetDispatchChoice : List Bool → List Bool :=
  orGadgetBooleanOr
    (sourceFourFamilyBooleanAndOutput
      (orGadgetFieldHeadMarker 1)
      (orGadgetFieldHeadMarker 3))
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput
        (orGadgetFieldHeadMarker 1))
      (orGadgetFieldHeadMarker 2))

private noncomputable def flatAnnotatedIndexedORGadgetDispatchChoiceComputable :
    BitTM
      flatAnnotatedIndexedORGadgetDispatchChoice := by
  have hprefix := orGadgetFieldHeadComputable 1
  exact flatAnnotatedIndexedORGadgetBooleanOrComputable
    (fourFamilyBooleanAndComputable hprefix
      (orGadgetFieldHeadComputable 3))
    (fourFamilyBooleanAndComputable
      (fourFamilyBooleanNotOutputComputable hprefix)
      (orGadgetFieldHeadComputable 2))

private def orGadgetDispatchTag
    (input : List Bool) : List Bool :=
  orGadgetFieldHeadMarker 1 input ++
    flatAnnotatedIndexedORGadgetDispatchChoice input

private noncomputable def flatAnnotatedIndexedORGadgetDispatchTagComputable :
    BitTM
      orGadgetDispatchTag := by
  exact pointwiseAppendComputable
    (orGadgetFieldHeadComputable 1)
    flatAnnotatedIndexedORGadgetDispatchChoiceComputable

private def flatAnnotatedIndexedORGadgetDispatchInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (orGadgetDispatchTag input) ++ input

private noncomputable def flatAnnotatedIndexedORGadgetDispatchInputComputable :
    BitTM
      flatAnnotatedIndexedORGadgetDispatchInput := by
  have htag := orGadgetPrefixedComputable
    flatAnnotatedIndexedORGadgetDispatchTagComputable
  exact pointwiseAppendComputable htag
    (Turing.idComputableInPolyTime bitEncoding)

private def orGadgetStartStep
    (input : List Bool) : List Bool :=
  flatAnnotatedIndexedORGadgetState
    (flatAnnotatedSourceFieldAt 0 input)
    [true]
    (firstFieldSuffix (flatAnnotatedSourceFieldAt 2 input))
    (firstFieldContents
      (firstFieldContents (flatAnnotatedSourceFieldAt 2 input)))
    (flatAnnotatedSourceFieldAt 4 input ++
      flatIndexedSourceORPaddingDescriptorWord true input)
    (List.replicate 4 true ++ flatAnnotatedSourceFieldAt 5 input)

private noncomputable def flatAnnotatedIndexedORGadgetStartStepComputable :
    BitTM
      orGadgetStartStep := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 2)
    firstFieldSuffixComputable
  have hbody := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 2)
    firstFieldContentsComputable
  have hactive := GapCVP.TMComposition.computableInPolyTime
    hbody firstFieldContentsComputable
  have hemitted := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable 4)
    (flatIndexedSourceORPaddingDescriptorComputable true)
  have hcount := pointwiseAppendComputable
    (sourceFixedWordComputable (List.replicate 4 true))
    (annotatedSourceFieldAtComputable 5)
  exact orGadgetStateComputable
    (annotatedSourceFieldAtComputable 0)
    (sourceFixedWordComputable [true]) hpending hactive hemitted hcount

private def orGadgetGateStep
    (input : List Bool) : List Bool :=
  flatAnnotatedIndexedORGadgetState
    (flatAnnotatedSourceFieldAt 0 input)
    (true :: flatAnnotatedSourceFieldAt 1 input)
    (flatAnnotatedSourceFieldAt 2 input)
    (firstFieldSuffix (flatAnnotatedSourceFieldAt 3 input))
    (flatAnnotatedSourceFieldAt 4 input ++
      flatIndexedSourceORGadgetDescriptorWord input)
    (List.replicate 5 true ++ flatAnnotatedSourceFieldAt 5 input)

private noncomputable def flatAnnotatedIndexedORGadgetGateStepComputable :
    BitTM
      orGadgetGateStep := by
  have hprefix := fiveForbiddenUnarySuccessorComputable
    (annotatedSourceFieldAtComputable 1)
  have hactive := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 3)
    firstFieldSuffixComputable
  have hemitted := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable 4)
    flatIndexedSourceORGadgetDescriptorComputable
  have hcount := pointwiseAppendComputable
    (sourceFixedWordComputable (List.replicate 5 true))
    (annotatedSourceFieldAtComputable 5)
  exact orGadgetStateComputable
    (annotatedSourceFieldAtComputable 0)
    hprefix (annotatedSourceFieldAtComputable 2)
    hactive hemitted hcount

private def orGadgetFinishStep
    (input : List Bool) : List Bool :=
  flatAnnotatedIndexedORGadgetState
    (true :: flatAnnotatedSourceFieldAt 0 input)
    []
    (flatAnnotatedSourceFieldAt 2 input)
    []
    (flatAnnotatedSourceFieldAt 4 input ++
      flatIndexedSourceORPaddingDescriptorWord false input)
    (List.replicate 4 true ++ flatAnnotatedSourceFieldAt 5 input)

private noncomputable def flatAnnotatedIndexedORGadgetFinishStepComputable :
    BitTM
      orGadgetFinishStep := by
  have hclause := fiveForbiddenUnarySuccessorComputable
    (annotatedSourceFieldAtComputable 0)
  have hemitted := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable 4)
    (flatIndexedSourceORPaddingDescriptorComputable false)
  have hcount := pointwiseAppendComputable
    (sourceFixedWordComputable (List.replicate 4 true))
    (annotatedSourceFieldAtComputable 5)
  exact orGadgetStateComputable
    hclause (sourceFixedWordComputable [])
    (annotatedSourceFieldAtComputable 2)
    (sourceFixedWordComputable []) hemitted hcount

private def flatAnnotatedIndexedORGadgetStep : List Bool → List Bool :=
  fourFamilyTaggedPredicateMarker
      (fun input : List Bool => input)
      orGadgetStartStep
      orGadgetFinishStep
      orGadgetGateStep ∘
    flatAnnotatedIndexedORGadgetDispatchInput

private noncomputable def flatAnnotatedIndexedORGadgetStepComputable :
    BitTM
      flatAnnotatedIndexedORGadgetStep := by
  have hdispatch := fourFamilyTaggedPredicateMarkerComputable
    (Turing.idComputableInPolyTime bitEncoding)
    flatAnnotatedIndexedORGadgetStartStepComputable
    flatAnnotatedIndexedORGadgetFinishStepComputable
    flatAnnotatedIndexedORGadgetGateStepComputable
  exact GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedIndexedORGadgetDispatchInputComputable hdispatch

private theorem flatAnnotatedIndexedORGadgetDispatchTag_state
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    orGadgetDispatchTag
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      [prefixWord.headD false,
        (prefixWord.headD false && active.headD false) ||
          (!(prefixWord.headD false) && pending.headD false)] := by
  let state := flatAnnotatedIndexedORGadgetState
    clauseIndex prefixWord pending active emitted count
  have hprefix :
      orGadgetFieldHeadMarker 1 state =
        [prefixWord.headD false] := by
    simp only [orGadgetFieldHeadMarker, flatAnnotatedIndexedORGadgetState_field_one,
        fiveFamilyOriginalHeadBitWord_eq, List.headD_eq_head?_getD, state]
  have hactive :
      orGadgetFieldHeadMarker 3 state =
        [active.headD false] := by
    simp only [orGadgetFieldHeadMarker, flatAnnotatedIndexedORGadgetState_field_three,
        fiveFamilyOriginalHeadBitWord_eq, List.headD_eq_head?_getD, state]
  have hpending :
      orGadgetFieldHeadMarker 2 state =
        [pending.headD false] := by
    simp only [orGadgetFieldHeadMarker, flatAnnotatedIndexedORGadgetState_field_two,
        fiveFamilyOriginalHeadBitWord_eq, List.headD_eq_head?_getD, state]
  have hnotprefix := fourFamilyBooleanNotOutput_bit
    (orGadgetFieldHeadMarker 1)
    state (prefixWord.headD false) hprefix
  have hleft := fourFamilyBooleanAndOutput_bits
    (orGadgetFieldHeadMarker 1)
    (orGadgetFieldHeadMarker 3)
    state (prefixWord.headD false) (active.headD false)
    hprefix hactive
  have hright := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      (orGadgetFieldHeadMarker 1))
    (orGadgetFieldHeadMarker 2)
    state (!(prefixWord.headD false)) (pending.headD false)
    hnotprefix hpending
  have hchoice := flatAnnotatedIndexedORGadgetBooleanOr_bits
    (sourceFourFamilyBooleanAndOutput
      (orGadgetFieldHeadMarker 1)
      (orGadgetFieldHeadMarker 3))
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput
        (orGadgetFieldHeadMarker 1))
      (orGadgetFieldHeadMarker 2))
    state
    (prefixWord.headD false && active.headD false)
    (!(prefixWord.headD false) && pending.headD false)
    hleft hright
  change orGadgetDispatchTag state = _
  unfold orGadgetDispatchTag
  rw [hprefix]
  change [prefixWord.headD false] ++
    orGadgetBooleanOr _ _ state = _
  rw [hchoice]
  rfl

private theorem orGadgetStep_state
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    flatAnnotatedIndexedORGadgetStep
        (flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) =
      if prefixWord.headD false then
        if active.headD false then
          orGadgetGateStep
            (flatAnnotatedIndexedORGadgetState
              clauseIndex prefixWord pending active emitted count)
        else
          orGadgetFinishStep
            (flatAnnotatedIndexedORGadgetState
              clauseIndex prefixWord pending active emitted count)
      else if pending.headD false then
        orGadgetStartStep
          (flatAnnotatedIndexedORGadgetState
            clauseIndex prefixWord pending active emitted count)
      else
        flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count := by
  unfold flatAnnotatedIndexedORGadgetStep
  rw [Function.comp_apply]
  change fourFamilyTaggedPredicateMarker
      (fun input : List Bool => input)
      orGadgetStartStep
      orGadgetFinishStep
      orGadgetGateStep
      (lengthPrefixedWord
        (orGadgetDispatchTag
          (flatAnnotatedIndexedORGadgetState
            clauseIndex prefixWord pending active emitted count)) ++
        flatAnnotatedIndexedORGadgetState
          clauseIndex prefixWord pending active emitted count) = _
  rw [flatAnnotatedIndexedORGadgetDispatchTag_state]
  cases hp : prefixWord.headD false with
  | false =>
      cases hn : pending.headD false with
      | false =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.false_or, Bool.not_false]
          exact sourceFourFamilyTaggedPredicateMarker_interpolation
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _
      | true =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.false_or, Bool.not_false, ↓reduceIte]
          exact sourceFourFamilyTaggedPredicateMarker_normalization
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _
  | true =>
      cases ha : active.headD false with
      | false =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.false_or, Bool.not_true, ↓reduceIte]
          exact sourceFourFamilyTaggedPredicateMarker_diagonal
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _
      | true =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.true_or, Bool.not_true, ↓reduceIte]
          exact sourceFourFamilyTaggedPredicateMarker_clause
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _

end CNFFiveFamilySourceIndexedORGadgetFoldCoreTM

namespace CNFFiveFamilySourceIndexedORGadgetRecordWorkerBoundCert

open Computability Turing GapCVP.CLVerifier GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceTotalStructuralDecoder GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFPairedSourceGridDescriptorTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFGuardedSourceDescriptorCompositeFoldTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM

private theorem flatIndexedGadgetFirstFieldContents_length_le
    (input : List Bool) :
    (firstFieldContents input).length ≤ input.length := by
  have accounting := annotatedStructuralFieldAccounting input
  omega

@[simp] private theorem flatIndexedGadgetNegateLeadingBitWord_length
    (input : List Bool) :
    (flatIndexedGadgetNegateLeadingBitWord input).length =
      input.length := by
  cases input with
  | nil => rfl
  | cons bit remaining =>
      simp only [flatIndexedGadgetNegateLeadingBitWord, List.length_cons]

private theorem flatIndexedGadgetSourceDescriptorWord_length_le
    (negated : Bool) (state : List Bool) :
    (flatIndexedGadgetSourceDescriptorWord negated state).length ≤
      2 * (flatAnnotatedSourceFieldAt 3 state).length + 1 := by
  have payload := flatIndexedGadgetFirstFieldContents_length_le
    (flatAnnotatedSourceFieldAt 3 state)
  cases negated <;>
    simp only [flatIndexedGadgetSourceDescriptorWord,
      Bool.false_eq_true, ↓reduceIte, lengthPrefixedWord_length,
      flatIndexedGadgetSourcePayloadWord,
      flatIndexedGadgetNegateLeadingBitWord_length] <;>
    omega

private theorem flatIndexedGadgetAccumulatorPairWord_length_le
    (next : Bool) (state : List Bool) :
    (flatIndexedGadgetAccumulatorPairWord next state).length ≤
      (flatAnnotatedSourceFieldAt 0 state).length +
        (flatAnnotatedSourceFieldAt 1 state).length + 2 := by
  have tail :
      (flatAnnotatedSourceFieldAt 1 state).tail.length ≤
        (flatAnnotatedSourceFieldAt 1 state).length := by
    simp only [List.length_tail, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  cases next <;>
    simp only [flatIndexedGadgetAccumulatorPairWord,
      Bool.false_eq_true, ↓reduceIte,
      List.length_append, List.length_cons,
      List.length_nil] <;>
    omega

private theorem flatIndexedPairedAccumulatorDescriptorWord_length_le
    (sign : Bool) (input : List Bool) :
    (pairedAccumulatorSignedLiteralDescriptorWord sign input).length ≤
      input.length + 15 := by
  cases unaryInputSplit input with
  | inl missing =>
      obtain ⟨count, hinput⟩ := missing
      subst input
      simp only [pairedAccumulatorSignedLiteralDescriptorWord,
          accumulatorSignedLiteralDescriptorWord,
          polynomialSignedLiteralDescriptorWord, unarySourcePairOutput, readUnaryPrefix_missing,
              List.length_nil,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
              mul_zero, Polynomial.eval_one,
          zero_add, lengthPrefixedWord_length, List.length_cons, encodeNat_length_eq_size,
              Nat.size_one, Nat.reduceAdd,
          Nat.reduceMul, List.length_replicate, le_add_iff_nonneg_left, zero_le]
  | inr delimited =>
      obtain ⟨first, tail, hinput⟩ := delimited
      subst input
      cases unaryInputSplit tail with
      | inl missing =>
          obtain ⟨second, htail⟩ := missing
          subst tail
          simp only [pairedAccumulatorSignedLiteralDescriptorWord,
              accumulatorSignedLiteralDescriptorWord,
              polynomialSignedLiteralDescriptorWord, unarySourcePairOutput,
                  readUnaryPrefix_replicate, readUnaryPrefix_missing,
              List.length_nil, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
                  Polynomial.eval_X, mul_zero,
              Polynomial.eval_one, zero_add, lengthPrefixedWord_length, List.length_cons,
                  encodeNat_length_eq_size, Nat.size_one,
              Nat.reduceAdd, Nat.reduceMul, List.length_append, List.length_replicate,
                  le_add_iff_nonneg_left, zero_le]
      | inr delimited =>
          obtain ⟨second, remaining, htail⟩ := delimited
          subst tail
          cases remaining with
          | nil =>
              have bound := guardedSourceAccumulatorDescriptor_length_le
                first second sign
              have pair :
                  pairedAccumulatorSignedLiteralDescriptorWord sign
                      (List.replicate first true ++
                        false :: (List.replicate second true ++ [false])) =
                    flatSignedLiteralDescriptor
                      (accumulatorVariable first second, sign) := by
                simpa only [unarySourcePairWord]
                    using (pairedAccumulatorSignedLiteralDescriptorWord_pair first second sign)
              rw [pair]
              simp only [List.length_append, List.length_replicate,
                List.length_cons, List.length_nil]
              omega
          | cons bit remaining =>
              simp only [pairedAccumulatorSignedLiteralDescriptorWord,
                  accumulatorSignedLiteralDescriptorWord,
                  polynomialSignedLiteralDescriptorWord, unarySourcePairOutput,
                      readUnaryPrefix_replicate, List.length_nil,
                  Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
                      Polynomial.eval_X, mul_zero, Polynomial.eval_one,
                  zero_add, lengthPrefixedWord_length, List.length_cons, encodeNat_length_eq_size,
                      Nat.size_one, Nat.reduceAdd,
                  Nat.reduceMul, List.length_append, List.length_replicate, le_add_iff_nonneg_left,
                      zero_le]

private theorem flatIndexedGadgetAccumulatorDescriptorWord_length_le
    (next sign : Bool) (state : List Bool) :
    (flatIndexedGadgetAccumulatorDescriptorWord next sign state).length ≤
      (flatAnnotatedSourceFieldAt 0 state).length +
        (flatAnnotatedSourceFieldAt 1 state).length + 17 := by
  have pair := flatIndexedGadgetAccumulatorPairWord_length_le
    next state
  have descriptor := flatIndexedPairedAccumulatorDescriptorWord_length_le
    sign (flatIndexedGadgetAccumulatorPairWord next state)
  change
    (pairedAccumulatorSignedLiteralDescriptorWord sign
      (flatIndexedGadgetAccumulatorPairWord next state)).length ≤ _
  omega

private theorem flatIndexedGadgetPaddingDescriptorWord_length_le
    (which sign : Bool) (state : List Bool) :
    (flatIndexedGadgetPaddingDescriptorWord which sign state).length ≤
      7 := by
  cases which <;> cases sign <;>
    simp only [flatIndexedGadgetPaddingDescriptorWord,
      paddingSignedLiteralDescriptorWord_eq,
      flatSignedLiteralDescriptor,
      lengthPrefixedWord_length] <;>
    decide

private theorem flatIndexedSourceORGadgetDescriptorWord_length_le
    (state : List Bool) :
    (flatIndexedSourceORGadgetDescriptorWord state).length ≤
      200 *
        ((flatAnnotatedSourceFieldAt 0 state).length +
          (flatAnnotatedSourceFieldAt 1 state).length +
          (flatAnnotatedSourceFieldAt 3 state).length + 1) := by
  have source := flatIndexedGadgetSourceDescriptorWord_length_le
    false state
  have negative := flatIndexedGadgetSourceDescriptorWord_length_le
    true state
  have current := flatIndexedGadgetAccumulatorDescriptorWord_length_le
    false true state
  have currentNegative :=
    flatIndexedGadgetAccumulatorDescriptorWord_length_le
      false false state
  have next := flatIndexedGadgetAccumulatorDescriptorWord_length_le
    true true state
  have nextNegative :=
    flatIndexedGadgetAccumulatorDescriptorWord_length_le
      true false state
  have padTrue := flatIndexedGadgetPaddingDescriptorWord_length_le
    false true state
  have padFalse := flatIndexedGadgetPaddingDescriptorWord_length_le
    false false state
  simp only [flatIndexedSourceORGadgetDescriptorWord,
    flatIndexedGadgetThreeDescriptorWord, List.length_append]
  omega

private theorem flatIndexedSourceORPaddingDescriptorWord_length_le
    (sign : Bool) (state : List Bool) :
    (flatIndexedSourceORPaddingDescriptorWord sign state).length ≤
      200 *
        ((flatAnnotatedSourceFieldAt 0 state).length +
          (flatAnnotatedSourceFieldAt 1 state).length +
          (flatAnnotatedSourceFieldAt 3 state).length + 1) := by
  have accumulator :=
    flatIndexedGadgetAccumulatorDescriptorWord_length_le
      false sign state
  have zeroFalse := flatIndexedGadgetPaddingDescriptorWord_length_le
    false false state
  have zeroTrue := flatIndexedGadgetPaddingDescriptorWord_length_le
    false true state
  have oneFalse := flatIndexedGadgetPaddingDescriptorWord_length_le
    true false state
  have oneTrue := flatIndexedGadgetPaddingDescriptorWord_length_le
    true true state
  simp only [flatIndexedSourceORPaddingDescriptorWord,
    flatIndexedGadgetThreeDescriptorWord, List.length_append]
  omega

end CNFFiveFamilySourceIndexedORGadgetRecordWorkerBoundCert

namespace CNFFiveFamilySourceIndexedORGadgetFoldBoundCert

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerBoundCert
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM

private def orGadgetSourceWeight
    (input : List Bool) : ℕ :=
  (flatAnnotatedSourceFieldAt 0 input).length +
    (flatAnnotatedSourceFieldAt 1 input).length +
      (flatAnnotatedSourceFieldAt 2 input).length +
        (flatAnnotatedSourceFieldAt 3 input).length

private theorem flatAnnotatedIndexedORGadgetSixFieldAccounting
    (input : List Bool) :
    2 *
      ((flatAnnotatedSourceFieldAt 0 input).length +
        (flatAnnotatedSourceFieldAt 1 input).length +
          (flatAnnotatedSourceFieldAt 2 input).length +
            (flatAnnotatedSourceFieldAt 3 input).length +
              (flatAnnotatedSourceFieldAt 4 input).length +
                (flatAnnotatedSourceFieldAt 5 input).length) ≤
      input.length := by
  have hzero := annotatedStructuralFieldAccounting input
  have hone := annotatedStructuralFieldAccounting
    (firstFieldSuffix input)
  have htwo := annotatedStructuralFieldAccounting
    (firstFieldSuffix (firstFieldSuffix input))
  have hthree := annotatedStructuralFieldAccounting
    (firstFieldSuffix
      (firstFieldSuffix (firstFieldSuffix input)))
  have hfour := annotatedStructuralFieldAccounting
    (firstFieldSuffix
      (firstFieldSuffix
        (firstFieldSuffix (firstFieldSuffix input))))
  have hfive := annotatedStructuralFieldAccounting
    (firstFieldSuffix
      (firstFieldSuffix
        (firstFieldSuffix
          (firstFieldSuffix (firstFieldSuffix input)))))
  simp only [flatAnnotatedSourceFieldAt,
    flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', Function.iterate_zero,
    id_eq] at *
  omega

private theorem flatAnnotatedIndexedORGadgetDispatchTag_all
    (input : List Bool) :
    orGadgetDispatchTag input =
      [(flatAnnotatedSourceFieldAt 1 input).headD false,
        ((flatAnnotatedSourceFieldAt 1 input).headD false &&
          (flatAnnotatedSourceFieldAt 3 input).headD false) ||
          (!(flatAnnotatedSourceFieldAt 1 input).headD false &&
            (flatAnnotatedSourceFieldAt 2 input).headD false)] := by
  have hprefix :
      orGadgetFieldHeadMarker 1 input =
        [(flatAnnotatedSourceFieldAt 1 input).headD false] := by
    simp only [orGadgetFieldHeadMarker,
        CNFFiveFamilyOriginalIndexedBitTM.fiveFamilyOriginalHeadBitWord_eq,
        List.headD_eq_head?_getD]
  have hactive :
      orGadgetFieldHeadMarker 3 input =
        [(flatAnnotatedSourceFieldAt 3 input).headD false] := by
    simp only [orGadgetFieldHeadMarker,
        CNFFiveFamilyOriginalIndexedBitTM.fiveFamilyOriginalHeadBitWord_eq,
        List.headD_eq_head?_getD]
  have hpending :
      orGadgetFieldHeadMarker 2 input =
        [(flatAnnotatedSourceFieldAt 2 input).headD false] := by
    simp only [orGadgetFieldHeadMarker,
        CNFFiveFamilyOriginalIndexedBitTM.fiveFamilyOriginalHeadBitWord_eq,
        List.headD_eq_head?_getD]
  have hnotprefix := fourFamilyBooleanNotOutput_bit
    (orGadgetFieldHeadMarker 1)
    input ((flatAnnotatedSourceFieldAt 1 input).headD false) hprefix
  have hleft := fourFamilyBooleanAndOutput_bits
    (orGadgetFieldHeadMarker 1)
    (orGadgetFieldHeadMarker 3)
    input ((flatAnnotatedSourceFieldAt 1 input).headD false)
      ((flatAnnotatedSourceFieldAt 3 input).headD false)
    hprefix hactive
  have hright := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      (orGadgetFieldHeadMarker 1))
    (orGadgetFieldHeadMarker 2)
    input (!(flatAnnotatedSourceFieldAt 1 input).headD false)
      ((flatAnnotatedSourceFieldAt 2 input).headD false)
    hnotprefix hpending
  have hchoice := flatAnnotatedIndexedORGadgetBooleanOr_bits
    (sourceFourFamilyBooleanAndOutput
      (orGadgetFieldHeadMarker 1)
      (orGadgetFieldHeadMarker 3))
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput
        (orGadgetFieldHeadMarker 1))
      (orGadgetFieldHeadMarker 2))
    input
    ((flatAnnotatedSourceFieldAt 1 input).headD false &&
      (flatAnnotatedSourceFieldAt 3 input).headD false)
    (!(flatAnnotatedSourceFieldAt 1 input).headD false &&
      (flatAnnotatedSourceFieldAt 2 input).headD false)
    hleft hright
  unfold orGadgetDispatchTag
  rw [hprefix]
  change
    [(flatAnnotatedSourceFieldAt 1 input).headD false] ++
      orGadgetBooleanOr _ _ input = _
  rw [hchoice]
  rfl

private theorem flatAnnotatedIndexedORGadgetStep_all
    (input : List Bool) :
    flatAnnotatedIndexedORGadgetStep input =
      if (flatAnnotatedSourceFieldAt 1 input).headD false then
        if (flatAnnotatedSourceFieldAt 3 input).headD false then
          orGadgetGateStep input
        else
          orGadgetFinishStep input
      else if (flatAnnotatedSourceFieldAt 2 input).headD false then
        orGadgetStartStep input
      else input := by
  unfold flatAnnotatedIndexedORGadgetStep
  rw [Function.comp_apply]
  change fourFamilyTaggedPredicateMarker
      (fun input : List Bool => input)
      orGadgetStartStep
      orGadgetFinishStep
      orGadgetGateStep
      (lengthPrefixedWord
        (orGadgetDispatchTag input) ++ input) = _
  rw [flatAnnotatedIndexedORGadgetDispatchTag_all]
  cases hp : (flatAnnotatedSourceFieldAt 1 input).headD false with
  | false =>
      cases hn : (flatAnnotatedSourceFieldAt 2 input).headD false with
      | false =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.false_or, Bool.not_false]
          exact sourceFourFamilyTaggedPredicateMarker_interpolation
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _
      | true =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.false_or, Bool.not_false, ↓reduceIte]
          exact sourceFourFamilyTaggedPredicateMarker_normalization
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _
  | true =>
      cases ha : (flatAnnotatedSourceFieldAt 3 input).headD false with
      | false =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.false_or, Bool.not_true, ↓reduceIte]
          exact sourceFourFamilyTaggedPredicateMarker_diagonal
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _
      | true =>
          simp only [Bool.false_and, Bool.true_and,
            Bool.true_or, Bool.not_true, ↓reduceIte]
          exact sourceFourFamilyTaggedPredicateMarker_clause
            (fun input : List Bool => input)
            orGadgetStartStep
            orGadgetFinishStep
            orGadgetGateStep _

private theorem flatAnnotatedIndexedORGadgetStep_sourceWeight_le
    (input : List Bool) :
    orGadgetSourceWeight
        (flatAnnotatedIndexedORGadgetStep input) ≤
      orGadgetSourceWeight input + 1 := by
  rw [flatAnnotatedIndexedORGadgetStep_all]
  split
  · split
    · have active := annotatedStructuralFieldAccounting
        (flatAnnotatedSourceFieldAt 3 input)
      simp only [orGadgetGateStep,
        orGadgetSourceWeight,
        flatAnnotatedIndexedORGadgetState_field_zero,
        flatAnnotatedIndexedORGadgetState_field_one,
        flatAnnotatedIndexedORGadgetState_field_two,
        flatAnnotatedIndexedORGadgetState_field_three,
        List.length_cons]
      omega
    · simp only [orGadgetFinishStep,
        orGadgetSourceWeight,
        flatAnnotatedIndexedORGadgetState_field_zero,
        flatAnnotatedIndexedORGadgetState_field_one,
        flatAnnotatedIndexedORGadgetState_field_two,
        flatAnnotatedIndexedORGadgetState_field_three,
        List.length_cons, List.length_nil]
      omega
  · split
    · have pending := annotatedStructuralFieldAccounting
        (flatAnnotatedSourceFieldAt 2 input)
      have active := annotatedStructuralFieldAccounting
        (firstFieldContents (flatAnnotatedSourceFieldAt 2 input))
      simp only [orGadgetStartStep,
        orGadgetSourceWeight,
        flatAnnotatedIndexedORGadgetState_field_zero,
        flatAnnotatedIndexedORGadgetState_field_one,
        flatAnnotatedIndexedORGadgetState_field_two,
        flatAnnotatedIndexedORGadgetState_field_three,
        List.length_cons, List.length_nil]
      omega
    · omega

private theorem flatAnnotatedIndexedORGadgetStep_length_le
    (input : List Bool) :
    (flatAnnotatedIndexedORGadgetStep input).length ≤
      input.length +
        800 * (orGadgetSourceWeight input + 1) + 100 := by
  have accounting := flatAnnotatedIndexedORGadgetSixFieldAccounting input
  rw [flatAnnotatedIndexedORGadgetStep_all]
  split
  · split
    · have descriptor :=
        flatIndexedSourceORGadgetDescriptorWord_length_le input
      have active := annotatedStructuralFieldAccounting
        (flatAnnotatedSourceFieldAt 3 input)
      simp only [orGadgetGateStep,
        flatAnnotatedIndexedORGadgetState_length,
        orGadgetSourceWeight,
        List.length_append, List.length_cons,
        List.length_replicate] at *
      omega
    · have descriptor :=
        flatIndexedSourceORPaddingDescriptorWord_length_le false input
      simp only [orGadgetFinishStep,
        flatAnnotatedIndexedORGadgetState_length,
        orGadgetSourceWeight,
        List.length_append, List.length_cons,
        List.length_nil, List.length_replicate] at *
      omega
  · split
    · have descriptor :=
        flatIndexedSourceORPaddingDescriptorWord_length_le true input
      have pending := annotatedStructuralFieldAccounting
        (flatAnnotatedSourceFieldAt 2 input)
      have active := annotatedStructuralFieldAccounting
        (firstFieldContents (flatAnnotatedSourceFieldAt 2 input))
      simp only [orGadgetStartStep,
        flatAnnotatedIndexedORGadgetState_length,
        orGadgetSourceWeight,
        List.length_append, List.length_cons,
        List.length_nil, List.length_replicate] at *
      omega
    · omega

private theorem flatAnnotatedIndexedORGadgetStep_iterate_sourceWeight_le
    (input : List Bool) (stage : ℕ) :
    orGadgetSourceWeight
        ((flatAnnotatedIndexedORGadgetStep^[stage]) input) ≤
      orGadgetSourceWeight input + stage := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have transition := flatAnnotatedIndexedORGadgetStep_sourceWeight_le
        ((flatAnnotatedIndexedORGadgetStep^[stage]) input)
      omega

private theorem flatAnnotatedIndexedORGadgetStep_iterate_length_le
    (input : List Bool) (stage : ℕ) :
    ((flatAnnotatedIndexedORGadgetStep^[stage]) input).length ≤
      input.length +
        stage *
          (800 *
            (orGadgetSourceWeight input + stage + 1) +
            100) := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, add_zero, zero_mul, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have transition := flatAnnotatedIndexedORGadgetStep_length_le
        ((flatAnnotatedIndexedORGadgetStep^[stage]) input)
      have potential :=
        flatAnnotatedIndexedORGadgetStep_iterate_sourceWeight_le
          input stage
      linarith

private def flatAnnotatedIndexedORGadgetFoldStatePolynomial : Polynomial ℕ :=
  2000 * Polynomial.X ^ 2 + 2000 * Polynomial.X + 100

private theorem flatAnnotatedIndexedORGadgetStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatAnnotatedIndexedORGadgetStep
      flatAnnotatedIndexedORGadgetFoldStatePolynomial := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have seedLength := parsedUnaryFold_seed_length_le
    input count seed hparse
  have countLength := parsedUnaryFold_count_le_length
    input count seed hparse
  have seedAccounting := flatAnnotatedIndexedORGadgetSixFieldAccounting seed
  have iterate := flatAnnotatedIndexedORGadgetStep_iterate_length_le
    seed stage
  have stageLength : stage ≤ input.length := hstage.trans countLength
  have weightLength :
      orGadgetSourceWeight seed ≤ input.length := by
    unfold orGadgetSourceWeight
    omega
  have product := Nat.mul_le_mul stageLength (show
    orGadgetSourceWeight seed + stage + 1 ≤
      2 * input.length + 1 by omega)
  simp only [flatAnnotatedIndexedORGadgetFoldStatePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  linarith

end CNFFiveFamilySourceIndexedORGadgetFoldBoundCert

namespace CNFFiveFamilySourceIndexedORGadgetSourceIterationBudgetCert

open Computability Turing GapCVP.CL GapCVP.BinaryEncoding
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM

private def orGadgetBundledSourceStepCount
    {T S : ℕ} (clauses : List (Clause T S)) : ℕ :=
  (clauses.map (fun clause => clause.card + 2)).sum

private theorem flatAnnotatedIndexedORGadgetBundledSourceRecordStepCount_le
    {T S : ℕ} (clause : Clause T S) :
    clause.card + 2 ≤
      (flatAnnotatedBundledClauseRecord clause).length := by
  simp only [flatAnnotatedBundledClauseRecord, flatSourceClauseAnnotatedRecord,
      flatSourceClauseUnaryCountPayload, List.append_assoc, lengthPrefixedWord_length,
          List.length_append,
      List.length_replicate, Nat.reduceLeDiff, Order.add_one_le_iff]
  omega

private theorem flatAnnotatedIndexedORGadgetBundledSourceStepCount_le
    {T S : ℕ} (clauses : List (Clause T S)) :
    orGadgetBundledSourceStepCount clauses ≤
      (flatAnnotatedBundledClauseStream clauses).length := by
  induction clauses with
  | nil =>
      simp only [orGadgetBundledSourceStepCount, List.map_nil, List.sum_nil,
          flatAnnotatedBundledClauseStream,
          List.flatMap_nil, List.length_nil, Std.le_refl]
  | cons clause remaining ih =>
      have head :=
        flatAnnotatedIndexedORGadgetBundledSourceRecordStepCount_le clause
      have together := Nat.add_le_add head ih
      simpa only [orGadgetBundledSourceStepCount, List.map_cons, List.sum_cons, List.sum_map_add,
          List.map_const',
          List.sum_replicate, smul_eq_mul, flatAnnotatedBundledClauseStream, List.flatMap_cons,
              List.length_append,
          List.length_flatMap, ge_iff_le] using together

@[simp] private theorem flatAnnotatedIndexedORGadgetIdleEmptyStep
    (clauseIndex emitted count : List Bool) :
    flatAnnotatedIndexedORGadgetStep
        (flatAnnotatedIndexedORGadgetState
          clauseIndex [] [] [] emitted count) =
      flatAnnotatedIndexedORGadgetState
        clauseIndex [] [] [] emitted count := by
  rw [orGadgetStep_state]
  simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none, Bool.false_eq_true,
      ↓reduceIte]

private theorem flatAnnotatedIndexedORGadgetIdleEmptyIterate
    (clauseIndex emitted count : List Bool)
    (extra : ℕ) :
    ((flatAnnotatedIndexedORGadgetStep^[extra])
      (flatAnnotatedIndexedORGadgetState
        clauseIndex [] [] [] emitted count)) =
      flatAnnotatedIndexedORGadgetState
        clauseIndex [] [] [] emitted count := by
  induction extra with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ extra ih =>
      rw [Function.iterate_succ_apply']
      rw [ih, flatAnnotatedIndexedORGadgetIdleEmptyStep]

end CNFFiveFamilySourceIndexedORGadgetSourceIterationBudgetCert

namespace CNFFiveFamilySourceIndexedGadgetDescriptorExpansionTM

open Computability Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatWholeWordFoldTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.CNFAnnotatedSourceCompleteSortedDedupTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldBoundCert
open GapCVP.CNFFiveFamilySourceIndexedORGadgetSourceIterationBudgetCert

private def orGadgetBoundedInput
    (input : List Bool) : List Bool :=
  unaryBoundedFoldWord input.length
    (orGadgetInitialState input)

private noncomputable def flatAnnotatedIndexedORGadgetBoundedInputComputable :
    BitTM
      orGadgetBoundedInput := by
  have hcounter := polynomialValueUnaryComputable Polynomial.X
  have hdelimiter := pointwiseAppendComputable
    (sourceFixedWordComputable [false])
    flatAnnotatedIndexedORGadgetInitialStateComputable
  have physical := pointwiseAppendComputable hcounter hdelimiter
  unfold orGadgetBoundedInput
  simpa only [unaryBoundedFoldWord, Polynomial.eval_X, List.cons_append, List.nil_append]
      using physical

private noncomputable def flatAnnotatedIndexedORGadgetBoundedFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatAnnotatedIndexedORGadgetStep) :=
  boundedDependentRecordFoldComputable
    flatAnnotatedIndexedORGadgetStepComputable
    flatAnnotatedIndexedORGadgetFoldStatePolynomial
    flatAnnotatedIndexedORGadgetStep_polynomiallyBoundedFoldStates

private def flatAnnotatedIndexedORGadgetFinalWord
    (state : List Bool) : List Bool :=
  let count := flatAnnotatedSourceFieldAt 5 state
  let emitted := flatAnnotatedSourceFieldAt 4 state
  count ++ count ++ count ++
    [false] ++ emitted ++
      lengthPrefixedWord (Computability.encodeNat count.length)

private noncomputable def flatAnnotatedIndexedORGadgetFinalWordComputable :
    BitTM
      flatAnnotatedIndexedORGadgetFinalWord := by
  have hcount := annotatedSourceFieldAtComputable 5
  have hemitted := annotatedSourceFieldAtComputable 4
  have hbinary := GapCVP.TMComposition.computableInPolyTime
    hcount structuralNaturalBinaryWriterComputable
  have hheader := GapCVP.TMComposition.computableInPolyTime
    hbinary structuralPrefixWriterComputable
  have hbody := pointwiseAppendComputable hemitted hheader
  have hdelimiter := pointwiseAppendComputable
    (sourceFixedWordComputable [false]) hbody
  have hthree := pointwiseAppendComputable hcount hdelimiter
  have htwo := pointwiseAppendComputable hcount hthree
  have physical := pointwiseAppendComputable hcount htwo
  change BitTM
    (fun state : List Bool =>
      flatAnnotatedSourceFieldAt 5 state ++
        flatAnnotatedSourceFieldAt 5 state ++
          flatAnnotatedSourceFieldAt 5 state ++
            [false] ++ flatAnnotatedSourceFieldAt 4 state ++
              lengthPrefixedWord
                (Computability.encodeNat
                  (flatAnnotatedSourceFieldAt 5 state).length))
  simpa only [Function.comp_apply, List.append_assoc] using physical

private def orGadgetFoldOutput
    (input : List Bool) : List Bool :=
  flatAnnotatedIndexedORGadgetFinalWord
    (boundedRecordFoldOutput flatAnnotatedIndexedORGadgetStep
      (orGadgetBoundedInput input))

private noncomputable def flatAnnotatedIndexedORGadgetFoldComputable :
    BitTM
      orGadgetFoldOutput := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedIndexedORGadgetBoundedInputComputable
    flatAnnotatedIndexedORGadgetBoundedFoldComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hfold flatAnnotatedIndexedORGadgetFinalWordComputable

private abbrev orGadgetPhysicalState :=
  GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM.flatAnnotatedIndexedORGadgetState

private def orGadgetIdleState
    {T S : ℕ}
    (clauseIndex : ℕ)
    (pending : List (Clause T S))
    (emitted : ThreeCNF) : List Bool :=
  orGadgetPhysicalState
    (List.replicate clauseIndex true)
    []
    (flatAnnotatedBundledClauseStream pending)
    []
    (flatSignedLiteralDescriptorStream
      (flatThreeClauseLiterals emitted))
    (List.replicate emitted.length true)

private def orGadgetActiveState
    {T S : ℕ}
    (clauseIndex prefixIndex : ℕ)
    (pending : List (Clause T S))
    (active : List (SignedLiteral T S))
    (emitted : ThreeCNF) : List Bool :=
  orGadgetPhysicalState
    (List.replicate clauseIndex true)
    (List.replicate (prefixIndex + 1) true)
    (flatAnnotatedBundledClauseStream pending)
    (flatSignedLiteralDescriptorStream
      (active.map sourceLiteral))
    (flatSignedLiteralDescriptorStream
      (flatThreeClauseLiterals emitted))
    (List.replicate emitted.length true)

@[simp] private theorem flatAnnotatedIndexedORGadgetClauseDescriptors_append
    (first second : ThreeCNF) :
    flatSignedLiteralDescriptorStream
        (flatThreeClauseLiterals (first ++ second)) =
      flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals first) ++
        flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals second) := by
  simp only [flatSignedLiteralDescriptorStream, flatThreeClauseLiterals, Fin.isValue,
      List.flatMap_append]

private theorem flatAnnotatedIndexedORGadgetBundledSourceHead
    {T S : ℕ} (clause : Clause T S)
    (remaining : List (Clause T S)) :
    (flatAnnotatedBundledClauseStream
      (clause :: remaining)).headD false = true := by
  have hrecord := flatAnnotatedSortedDedupSourceClauseRecord_ne_nil clause
  have hhead := flatAnnotatedSortedDedupHeadBit_nonemptyPrefix
    (flatSourceClauseAnnotatedRecord clause)
    (flatAnnotatedBundledClauseStream remaining) hrecord
  simpa only [flatAnnotatedBundledClauseStream, List.flatMap_cons,
      flatAnnotatedBundledClauseRecord,
      List.headD_eq_head?_getD, List.head?_append, Option.getD_or,
          fiveFamilyOriginalHeadBitWord_eq, List.cons.injEq,
      and_true] using hhead

private theorem flatAnnotatedIndexedORGadgetStartState_valid
    {T S : ℕ}
    (clauseIndex : ℕ)
    (clause : Clause T S)
    (remaining : List (Clause T S))
    (emitted : ThreeCNF) :
    flatAnnotatedIndexedORGadgetStep
        (orGadgetIdleState
          clauseIndex (clause :: remaining) emitted) =
      orGadgetActiveState
        clauseIndex 0 remaining (sortedElements clause)
        (emitted ++
          paddedUnary (accumulatorLiteral clauseIndex 0 true)) := by
  have hpending := flatAnnotatedIndexedORGadgetBundledSourceHead
    clause remaining
  have hpadding :
      flatIndexedSourceORPaddingDescriptorWord true
        (orGadgetIdleState
          clauseIndex (clause :: remaining) emitted) =
        flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals
            (paddedUnary
              (accumulatorLiteral clauseIndex 0 true))) := by
    simpa only [orGadgetIdleState, orGadgetPhysicalState,
        CNFFiveFamilySourceIndexedORGadgetFoldCoreTM.flatAnnotatedIndexedORGadgetState,
            List.append_assoc,
        CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM.flatAnnotatedIndexedORGadgetState] using
        flatIndexedSourceORPaddingDescriptorWord_valid_initial clauseIndex true
          (flatAnnotatedBundledClauseStream (clause :: remaining)) []
          (flatSignedLiteralDescriptorStream (flatThreeClauseLiterals emitted)) (List.replicate
              emitted.length true)
  unfold orGadgetIdleState
    orGadgetActiveState
  rw [orGadgetStep_state]
  simp only [List.headD_nil, Bool.false_eq_true,
    ↓reduceIte, hpending]
  unfold orGadgetStartStep
  simp only [flatAnnotatedIndexedORGadgetState_field_zero,
    flatAnnotatedIndexedORGadgetState_field_two,
    flatAnnotatedIndexedORGadgetState_field_four,
    flatAnnotatedIndexedORGadgetState_field_five]
  rw [show
    flatIndexedSourceORPaddingDescriptorWord true
      (orGadgetPhysicalState
        (List.replicate clauseIndex true) []
        (flatAnnotatedBundledClauseStream (clause :: remaining))
        [] (flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals emitted))
        (List.replicate emitted.length true)) = _
      from hpadding]
  simp only [flatAnnotatedBundledClauseStream, List.flatMap_cons, flatAnnotatedBundledClauseRecord,
      flatSourceClauseAnnotatedRecord, flatSourceClauseDescriptorPayload, List.append_assoc,
          firstFieldSuffix_valid,
      firstFieldContents_valid, List.reduceReplicate, List.cons_append, List.nil_append,
          orGadgetPhysicalState, zero_add,
      List.replicate_one, flatAnnotatedIndexedORGadgetClauseDescriptors_append, List.length_append,
          paddedUnary_length,
      Nat.add_comm, List.replicate_add]

private theorem flatAnnotatedIndexedORGadgetGateState_valid
    {T S : ℕ}
    (clauseIndex prefixIndex : ℕ)
    (pending : List (Clause T S))
    (literal : SignedLiteral T S)
    (remaining : List (SignedLiteral T S))
    (emitted : ThreeCNF) :
    flatAnnotatedIndexedORGadgetStep
        (orGadgetActiveState
          clauseIndex prefixIndex pending (literal :: remaining) emitted) =
      orGadgetActiveState
        clauseIndex (prefixIndex + 1) pending remaining
        (emitted ++ orGate (sourceLiteral literal)
          (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
          (accumulatorLiteral clauseIndex prefixIndex true)) := by
  have hgate :
      flatIndexedSourceORGadgetDescriptorWord
        (orGadgetActiveState
          clauseIndex prefixIndex pending (literal :: remaining) emitted) =
        flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals
            (orGate (sourceLiteral literal)
              (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
              (accumulatorLiteral clauseIndex prefixIndex true))) := by
    simpa only [orGadgetActiveState, orGadgetPhysicalState,
        CNFFiveFamilySourceIndexedORGadgetFoldCoreTM.flatAnnotatedIndexedORGadgetState,
            List.append_assoc,
        flatSignedLiteralDescriptorStream, List.map_cons, List.flatMap_cons,
        CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM.flatAnnotatedIndexedORGadgetState] using
        flatIndexedSourceORGadgetDescriptorWord_valid clauseIndex prefixIndex (sourceLiteral
            literal)
          (flatAnnotatedBundledClauseStream pending) (flatSignedLiteralDescriptorStream
              (remaining.map sourceLiteral))
          (flatSignedLiteralDescriptorStream (flatThreeClauseLiterals emitted)) (List.replicate
              emitted.length true)
  unfold orGadgetActiveState
  rw [orGadgetStep_state]
  have hprefix :
      (List.replicate (prefixIndex + 1) true).headD false = true := by
    simp only [List.replicate_succ, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]
  have hactive :
      (flatSignedLiteralDescriptorStream
        ((literal :: remaining).map sourceLiteral)).headD false =
        true := by
    simp only [flatSignedLiteralDescriptorStream, List.map_cons, List.flatMap_cons,
        flatSignedLiteralDescriptor,
        lengthPrefixedWord, List.length_cons, List.replicate_succ, List.cons_append,
            List.append_assoc,
        List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]
  rw [hprefix, hactive]
  simp only [↓reduceIte]
  unfold orGadgetGateStep
  simp only [flatAnnotatedIndexedORGadgetState_field_zero,
    flatAnnotatedIndexedORGadgetState_field_one,
    flatAnnotatedIndexedORGadgetState_field_two,
    flatAnnotatedIndexedORGadgetState_field_three,
    flatAnnotatedIndexedORGadgetState_field_four,
    flatAnnotatedIndexedORGadgetState_field_five]
  rw [show flatIndexedSourceORGadgetDescriptorWord
      (orGadgetPhysicalState
        (List.replicate clauseIndex true)
        (List.replicate (prefixIndex + 1) true)
        (flatAnnotatedBundledClauseStream pending)
        (flatSignedLiteralDescriptorStream
          ((literal :: remaining).map sourceLiteral))
        (flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals emitted))
        (List.replicate emitted.length true)) = _ from hgate]
  simp only [List.replicate_succ, flatSignedLiteralDescriptorStream, List.map_cons,
      List.flatMap_cons,
      flatSignedLiteralDescriptor, firstFieldSuffix_valid, flatThreeClauseLiterals, Fin.isValue,
          List.replicate_zero,
      List.cons_append, List.nil_append, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd,
          List.flatMap_append,
      List.length_append, orGate_length, List.replicate_add]

private theorem flatAnnotatedIndexedORGadgetFinishState_valid
    {T S : ℕ}
    (clauseIndex prefixIndex : ℕ)
    (pending : List (Clause T S))
    (emitted : ThreeCNF) :
    flatAnnotatedIndexedORGadgetStep
        (orGadgetActiveState
          clauseIndex prefixIndex pending [] emitted) =
      orGadgetIdleState
        (clauseIndex + 1) pending
        (emitted ++
          paddedUnary
            (accumulatorLiteral clauseIndex prefixIndex false)) := by
  have hpadding :
      flatIndexedSourceORPaddingDescriptorWord false
        (orGadgetActiveState
          clauseIndex prefixIndex pending [] emitted) =
        flatSignedLiteralDescriptorStream
          (flatThreeClauseLiterals
            (paddedUnary
              (accumulatorLiteral clauseIndex prefixIndex false))) := by
    simpa only [orGadgetActiveState, orGadgetPhysicalState,
        CNFFiveFamilySourceIndexedORGadgetFoldCoreTM.flatAnnotatedIndexedORGadgetState,
            List.append_assoc,
        flatSignedLiteralDescriptorStream, List.map_nil, List.flatMap_nil,
        CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM.flatAnnotatedIndexedORGadgetState] using
        flatIndexedSourceORPaddingDescriptorWord_valid clauseIndex prefixIndex false
          (flatAnnotatedBundledClauseStream pending) []
          (flatSignedLiteralDescriptorStream (flatThreeClauseLiterals emitted)) (List.replicate
              emitted.length true)
  have hpadding' := hpadding
  simp only [orGadgetActiveState,
    orGadgetPhysicalState,
    List.replicate_succ, List.map_nil,
    flatSignedLiteralDescriptorStream, List.flatMap_nil] at hpadding'
  unfold orGadgetActiveState
    orGadgetIdleState
  rw [orGadgetStep_state]
  simp only [List.replicate_succ, List.headD_cons,
    List.map_nil, flatSignedLiteralDescriptorStream,
    List.flatMap_nil, List.headD_nil, ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold orGadgetFinishStep
  simp only [flatAnnotatedIndexedORGadgetState_field_zero,
    flatAnnotatedIndexedORGadgetState_field_two,
    flatAnnotatedIndexedORGadgetState_field_four,
    flatAnnotatedIndexedORGadgetState_field_five]
  rw [hpadding']
  simp only [flatThreeClauseLiterals, Fin.isValue, List.replicate_succ, List.replicate_zero,
      List.cons_append,
      List.nil_append, List.flatMap_append, List.length_append, paddedUnary_length, Nat.add_comm,
          List.replicate_add]

private theorem flatAnnotatedIndexedORGadgetActiveIterate_valid
    {T S : ℕ}
    (clauseIndex prefixIndex : ℕ)
    (pending : List (Clause T S))
    (active : List (SignedLiteral T S))
    (emitted : ThreeCNF) :
    ((flatAnnotatedIndexedORGadgetStep^[active.length + 1])
      (orGadgetActiveState
        clauseIndex prefixIndex pending active emitted)) =
      orGadgetIdleState
        (clauseIndex + 1) pending
        (emitted ++ gateList clauseIndex prefixIndex active ++
          paddedUnary
            (accumulatorLiteral clauseIndex
              (prefixIndex + active.length) false)) := by
  induction active generalizing prefixIndex emitted with
  | nil =>
      simpa only [List.length_nil, zero_add, Function.iterate_one, gateList, List.append_nil,
          add_zero] using
          flatAnnotatedIndexedORGadgetFinishState_valid clauseIndex prefixIndex pending emitted
  | cons literal remaining ih =>
      have hcount :
          (literal :: remaining).length + 1 =
            (remaining.length + 1) + 1 := by
        simp only [List.length_cons]
      rw [hcount, Function.iterate_succ_apply,
        flatAnnotatedIndexedORGadgetGateState_valid]
      rw [ih (prefixIndex + 1)
        (emitted ++ orGate (sourceLiteral literal)
          (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
          (accumulatorLiteral clauseIndex prefixIndex true))]
      simp only [List.append_assoc, Nat.add_assoc, gateList, List.length_cons, Nat.add_comm]

private theorem flatAnnotatedIndexedORGadgetSingleClauseIterate_valid
    {T S : ℕ}
    (clauseIndex : ℕ)
    (clause : Clause T S)
    (remaining : List (Clause T S))
    (emitted : ThreeCNF) :
    ((flatAnnotatedIndexedORGadgetStep^[clause.card + 2])
      (orGadgetIdleState
        clauseIndex (clause :: remaining) emitted)) =
      orGadgetIdleState
        (clauseIndex + 1) remaining
        (emitted ++ encodeClause clauseIndex clause) := by
  have hcount :
      clause.card + 2 =
        ((sortedElements clause).length + 1) + 1 := by
    simp only [sortedElements_length]
  rw [hcount, Function.iterate_add_apply,
    Function.iterate_one,
    flatAnnotatedIndexedORGadgetStartState_valid,
    flatAnnotatedIndexedORGadgetActiveIterate_valid]
  simp only [List.append_assoc, sortedElements_length, zero_add, encodeClause]

private theorem flatAnnotatedIndexedORGadgetSourceIterate_valid
    {T S : ℕ}
    (clauses : List (Clause T S))
    (clauseIndex : ℕ)
    (emitted : ThreeCNF) :
    ((flatAnnotatedIndexedORGadgetStep^[
      orGadgetBundledSourceStepCount clauses])
      (orGadgetIdleState
        clauseIndex clauses emitted)) =
      orGadgetIdleState
        (clauseIndex + clauses.length) ([] : List (Clause T S))
        (emitted ++ encodeFormulaFrom clauseIndex clauses) := by
  induction clauses generalizing clauseIndex emitted with
  | nil =>
      simp only [orGadgetBundledSourceStepCount, List.map_nil, List.sum_nil, Function.iterate_zero,
          id_eq,
          List.length_nil, add_zero, encodeFormulaFrom, List.append_nil]
  | cons clause remaining ih =>
      have hcount :
          orGadgetBundledSourceStepCount
              (clause :: remaining) =
            (clause.card + 2) +
              orGadgetBundledSourceStepCount
                remaining := by
        rfl
      rw [hcount, Nat.add_comm, Function.iterate_add_apply,
        flatAnnotatedIndexedORGadgetSingleClauseIterate_valid]
      rw [ih (clauseIndex + 1)
        (emitted ++ encodeClause clauseIndex clause)]
      simp only [Nat.add_assoc, List.append_assoc, List.length_cons, Nat.add_comm,
          encodeFormulaFrom]

private theorem flatAnnotatedIndexedORGadgetBoundedFoldOutput_valid
    {T S : ℕ}
    (clauses : List (Clause T S)) :
    boundedRecordFoldOutput flatAnnotatedIndexedORGadgetStep
        (orGadgetBoundedInput
          (flatAnnotatedBundledClauseStream clauses)) =
      orGadgetIdleState
        clauses.length ([] : List (Clause T S))
        (encodeFormulaFrom 0 clauses) := by
  have hbudget :=
    flatAnnotatedIndexedORGadgetBundledSourceStepCount_le clauses
  let steps := orGadgetBundledSourceStepCount clauses
  let source := flatAnnotatedBundledClauseStream clauses
  have hsplit : source.length = (source.length - steps) + steps := by
    dsimp [source, steps]
    omega
  have hinitial :
      orGadgetInitialState source =
        orGadgetIdleState 0 clauses [] := by
    simp only [orGadgetInitialState, orGadgetIdleState, orGadgetPhysicalState, List.replicate_zero,
        flatSignedLiteralDescriptorStream, flatThreeClauseLiterals, Fin.isValue, List.flatMap_nil,
            List.length_nil, source]
  unfold orGadgetBoundedInput
  rw [show flatAnnotatedBundledClauseStream clauses = source from rfl]
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  rw [hinitial, hsplit, Function.iterate_add_apply]
  change
    ((flatAnnotatedIndexedORGadgetStep^[source.length - steps])
      (((flatAnnotatedIndexedORGadgetStep^[steps])
        (orGadgetIdleState 0 clauses [])))) = _
  rw [show
    ((flatAnnotatedIndexedORGadgetStep^[steps])
      (orGadgetIdleState 0 clauses [])) =
      orGadgetIdleState
        clauses.length [] (encodeFormulaFrom 0 clauses) by
        simpa only [zero_add, List.nil_append, steps] using
            flatAnnotatedIndexedORGadgetSourceIterate_valid clauses 0 []]
  simpa only [orGadgetIdleState, orGadgetPhysicalState, flatAnnotatedBundledClauseStream,
      List.flatMap_nil] using
      flatAnnotatedIndexedORGadgetIdleEmptyIterate (List.replicate clauses.length true)
        (flatSignedLiteralDescriptorStream (flatThreeClauseLiterals (encodeFormulaFrom 0 clauses)))
        (List.replicate (encodeFormulaFrom 0 clauses).length true) (source.length - steps)

private theorem flatAnnotatedIndexedORGadgetFoldOutput_valid
    {T S : ℕ}
    (clauses : List (Clause T S)) :
    orGadgetFoldOutput
        (flatAnnotatedBundledClauseStream clauses) =
      structuralThreeCNFFlatFoldInput
        (encodeFormulaFrom 0 clauses) := by
  unfold orGadgetFoldOutput
  rw [flatAnnotatedIndexedORGadgetBoundedFoldOutput_valid clauses]
  simp only [flatAnnotatedIndexedORGadgetFinalWord,
    orGadgetIdleState,
    orGadgetPhysicalState,
    flatAnnotatedIndexedORGadgetState_field_four,
    flatAnnotatedIndexedORGadgetState_field_five,
    List.length_replicate,
    structuralThreeCNFFlatFoldInput,
    unaryBoundedFoldWord]
  rw [show 3 * (encodeFormulaFrom 0 clauses).length =
    (encodeFormulaFrom 0 clauses).length +
      (encodeFormulaFrom 0 clauses).length +
      (encodeFormulaFrom 0 clauses).length by omega,
    List.replicate_add, List.replicate_add]
  simp only [List.append_assoc, List.cons_append,
    List.nil_append]

end CNFFiveFamilySourceIndexedGadgetDescriptorExpansionTM

namespace CNFFiveFamilySourceIndexedORGadgetFinalCert

open Computability Turing GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatWholeWordFoldTM
open GapCVP.CNFFiveFamilyIndependentFiveFamilyPhysicalBundledSourceCert
open GapCVP.CNFFiveFamilySourceIndexedGadgetDescriptorExpansionTM

private def fiveActualSourceSortedIndexedORGadgetPreparationWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  orGadgetFoldOutput
    (fiveIndependentActualSortedDistinctBundledSourceWord
      bound machine original)

private noncomputable def fiveFamilyActualSourceSortedIndexedORGadgetPreparationComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveActualSourceSortedIndexedORGadgetPreparationWord
        bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentActualSortedDistinctBundledSourceComputable
      bound machine)
    flatAnnotatedIndexedORGadgetFoldComputable
  change BitTM
    (fun original : List Bool =>
      orGadgetFoldOutput
        (fiveIndependentActualSortedDistinctBundledSourceWord
          bound machine original))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyActualSourceSortedIndexedORGadgetPreparationWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveActualSourceSortedIndexedORGadgetPreparationWord
        bound machine original =
      totalVerifierSortedFiveFamilyFlatFoldInput
        bound machine original := by
  unfold fiveActualSourceSortedIndexedORGadgetPreparationWord
  rw [fiveFamilyIndependentActualSortedDistinctBundledSourceWord_valid
    bound machine original]
  rw [flatAnnotatedIndexedORGadgetFoldOutput_valid]
  unfold totalVerifierSortedFiveFamilyFlatFoldInput
  rw [totalVerifierFiveFamilySourceClauseCandidates_sorted]
  rfl

private noncomputable def actualSortedFiveFamilyFlatPreparationComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (totalVerifierSortedFiveFamilyFlatFoldInput bound machine) := by
  have physical :=
    fiveFamilyActualSourceSortedIndexedORGadgetPreparationComputable
      bound machine
  have equality :
      fiveActualSourceSortedIndexedORGadgetPreparationWord
          bound machine =
        totalVerifierSortedFiveFamilyFlatFoldInput bound machine := by
    funext original
    exact fiveFamilyActualSourceSortedIndexedORGadgetPreparationWord_valid
      bound machine original
  rwa [equality] at physical

/-- GapCVP reduction support. -/
noncomputable def actualWholeStructuralCNFOutputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (structuralWholeCNFWord bound machine) :=
  actualWholeStructuralCNFOutputComputableOfFlatPreparation
    bound machine
    (actualSortedFiveFamilyFlatPreparationComputable bound machine)

end CNFFiveFamilySourceIndexedORGadgetFinalCert

section

/-- GapCVP reduction support. -/
noncomputable def gapFactor400 (I : GapCVPInstance) : ℝ :=
  (I.dimension : ℝ) ^ ((1 : ℝ) / 400)

/-- GapCVP reduction support. -/
noncomputable def gapYES400 (I : GapCVPInstance) : Bool :=
  @decide (
  gapCVPWellFormed I ∧
    ∃ z : Fin I.dimension → ℤ,
      distanceSquared I z ≤ (I.radius : ℝ) ^ 2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def gapNO400 (I : GapCVPInstance) : Bool :=
  @decide (
  gapCVPWellFormed I ∧
    ∀ z : Fin I.dimension → ℤ,
      (gapFactor400 I * (I.radius : ℝ)) ^ 2 < distanceSquared I z
  ) (Classical.propDecidable _)
private theorem gapFactor400_one_le {I : GapCVPInstance}
    (hdimension : 0 < I.dimension) :
    1 ≤ gapFactor400 I := by
  unfold gapFactor400
  apply Real.one_le_rpow
  · exact_mod_cast hdimension
  · norm_num

theorem gapYES400_not_gapNO400 (I : GapCVPInstance)
    (hyes : gapYES400 I) (hno : gapNO400 I) : False := by
  unfold gapYES400 at hyes
  unfold gapNO400 at hno
  have hyesProposition := ofClassicalDecide08 hyes
  have hnoProposition := ofClassicalDecide08 hno
  rcases hyesProposition with ⟨hwellFormed, z, hz⟩
  unfold gapCVPWellFormed at hwellFormed
  have hwellFormedProposition := ofClassicalDecide08 hwellFormed
  rcases hwellFormedProposition with ⟨hdimension, _, hradius⟩
  have hfactor := gapFactor400_one_le hdimension
  have hradius_real : 0 < (I.radius : ℝ) := by
    exact_mod_cast hradius
  have hscaled :
      (I.radius : ℝ) ≤ gapFactor400 I * (I.radius : ℝ) := by
    nlinarith
  have hsquare :
      (I.radius : ℝ) ^ 2 ≤
        (gapFactor400 I * (I.radius : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (gapFactor400 I * (I.radius : ℝ)),
      sq_nonneg (I.radius : ℝ)]
  have hfar := hnoProposition.2 z
  linarith

/-- GapCVP reduction support. -/
noncomputable def gapCVP400Promise : PromiseProblem where
  yes bits :=
    @decide (
 ∃ I : GapCVPInstance,
    (binaryFinEncoding GapCVPInstance).encode I = bits ∧ gapYES400 I
    ) (Classical.propDecidable _)
  no bits :=
    @decide (
 ∃ I : GapCVPInstance,
    (binaryFinEncoding GapCVPInstance).encode I = bits ∧ gapNO400 I
    ) (Classical.propDecidable _)
  disjoint bits hyes hno := by
    simp only [decide_eq_true_eq] at hyes hno
    rcases hyes with ⟨I, hI, hy⟩
    rcases hno with ⟨J, hJ, hn⟩
    have hsame : I = J :=
      (binaryFinEncoding GapCVPInstance).encode_injective
        (hI.trans hJ.symm)
    subst J
    exact gapYES400_not_gapNO400 I hy hn

theorem gapYES400_iff_gapYES (I : GapCVPInstance) :
    gapYES400 I ↔ gapYES I := Iff.rfl

end

namespace Factor400BinaryCanonicalNo

private theorem canonicalNoInstance_squaredNo400 :
    GapCVP.Core.SquaredNoAt ((1 : ℝ) / 400)
      GapCVP.Core.canonicalNoInstance := by
  simp only [GapCVP.Core.SquaredNoAt, decide_eq_true_eq] at *
  intro z
  have hodd := GapCVP.Core.odd_integer_distance_gt_half (z 0)
  have hnonnegative :
      (0 : ℝ) ≤ |(1 : ℝ) - 2 * (z 0 : ℝ)| := abs_nonneg _
  have hsquare :
      ((1 : ℝ) / 2) ^ 2 <
        ((1 : ℝ) - 2 * (z 0 : ℝ)) ^ 2 := by
    nlinarith [sq_abs ((1 : ℝ) - 2 * (z 0 : ℝ))]
  simpa only [Core.canonicalNoInstance, one_div, Nat.cast_one,
      Real.one_rpow, Rat.cast_inv, Rat.cast_ofNat, one_mul, inv_pow,
      Core.squaredDistance, Matrix.of_apply, Fin.sum_univ_one,
      Rat.cast_one, Int.cast_ofNat, gt_iff_lt] using hsquare

/-- GapCVP reduction support. -/
abbrev adaptedCanonicalNoInstance : GapCVP.GapCVPInstance where
  dimension := GapCVP.Core.canonicalNoInstance.dimension
  basis := GapCVP.Core.canonicalNoInstance.basis
  target := GapCVP.Core.canonicalNoInstance.target
  radius := GapCVP.Core.canonicalNoInstance.radius

private theorem adaptedCanonicalNoInstance_wellFormed :
    gapCVPWellFormed adaptedCanonicalNoInstance := by
  simp only [GapCVP.gapCVPWellFormed, decide_eq_true_eq] at *
  exact ⟨GapCVP.Core.canonicalNoInstance.dimension_pos,
    GapCVP.Core.canonicalNoInstance.basis_nonsingular,
    GapCVP.Core.canonicalNoInstance.radius_pos⟩

private theorem adaptedCanonicalNoInstance_distanceSquared
    (z : Fin 1 → ℤ) :
    distanceSquared adaptedCanonicalNoInstance z =
      GapCVP.Core.squaredDistance GapCVP.Core.canonicalNoInstance z := by
  simp only [distanceSquared, adaptedCanonicalNoInstance,
      Core.canonicalNoInstance, Matrix.of_apply, Fin.sum_univ_one,
      Int.cast_ofNat, Rat.cast_one, Core.squaredDistance]
  ring

private theorem adaptedCanonicalNoInstance_gapNO400 :
    gapNO400 adaptedCanonicalNoInstance := by
  simp only [GapCVP.gapNO400, decide_eq_true_eq]
  refine ⟨adaptedCanonicalNoInstance_wellFormed, ?_⟩
  intro z
  rw [adaptedCanonicalNoInstance_distanceSquared]
  have noProof := canonicalNoInstance_squaredNo400
  simp only [GapCVP.Core.SquaredNoAt, decide_eq_true_eq] at noProof
  have h := noProof z
  simpa only [gapFactor400, adaptedCanonicalNoInstance, Core.canonicalNoInstance, one_div,
      Nat.cast_one,
      Real.one_rpow, Rat.cast_inv, Rat.cast_ofNat, one_mul, inv_pow, gt_iff_lt] using h

/-- GapCVP reduction support. -/
def adaptedCanonicalNoWord : List Bool :=
  (binaryFinEncoding GapCVPInstance).encode adaptedCanonicalNoInstance

theorem adaptedCanonicalNoWord_mem_no :
    gapCVP400Promise.no adaptedCanonicalNoWord := by
  simp only [GapCVP.gapCVP400Promise, decide_eq_true_eq]
  exact ⟨adaptedCanonicalNoInstance, rfl,
    adaptedCanonicalNoInstance_gapNO400⟩

end Factor400BinaryCanonicalNo

namespace Core

/-- GapCVP reduction support. -/
structure Literal (variableCount : ℕ) where
  /-- GapCVP reduction support. -/
  variableIndex : Fin variableCount
  /-- GapCVP reduction support. -/
  satisfyingValue : Bool
deriving DecidableEq

/-- GapCVP reduction support. -/
structure Clause (variableCount : ℕ) where
  /-- GapCVP reduction support. -/
  literals : Finset (Literal variableCount)
  nonempty : literals.Nonempty
  size_le_three : literals.card ≤ 3

/-- GapCVP reduction support. -/
structure Formula where
  /-- GapCVP reduction support. -/
  variableCount : ℕ
  /-- GapCVP reduction support. -/
  clauses : List (Clause variableCount)

/-- GapCVP reduction support. -/
noncomputable def Clause.Satisfied {variableCount : ℕ} (clause : Clause variableCount)
    (assignment : Fin variableCount → Bool) : Bool :=
  @decide (
  ∃ literal ∈ clause.literals,
    assignment literal.variableIndex = literal.satisfyingValue
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def Formula.Satisfied (formula : Formula)
    (assignment : Fin formula.variableCount → Bool) : Bool :=
  @decide (
  ∀ i : Fin formula.clauses.length,
    (formula.clauses.get i).Satisfied assignment
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def Formula.Satisfiable (formula : Formula) : Bool :=
  @decide (
  ∃ assignment : Fin formula.variableCount → Bool,
    formula.Satisfied assignment
  ) (Classical.propDecidable _)
end Core

namespace Factor400FormulaBridge

open GapCVP.SourceMachineCert

theorem formula_satisfied_iff_forall_mem
    (formula : GapCVP.Core.Formula)
    (assignment : Fin formula.variableCount → Bool) :
    formula.Satisfied assignment ↔
      ∀ clause ∈ formula.clauses, clause.Satisfied assignment := by
  simp only [GapCVP.Core.Formula.Satisfied, decide_eq_true_eq]
  constructor
  · intro hsatisfied clause hclause
    obtain ⟨index, hindex⟩ := List.mem_iff_get.mp hclause
    rw [← hindex]
    exact hsatisfied index
  · intro hsatisfied index
    exact hsatisfied _ (List.get_mem formula.clauses index)

end Factor400FormulaBridge

namespace BinarySourceVariableCompaction

open GapCVP.SourceMachineCert

/-- GapCVP reduction support. -/
def occurringVariables (formula : ThreeCNF) : List ℕ :=
  (formulaVariables formula).eraseDups

/-- GapCVP reduction support. -/
def occurringVariableCount (formula : ThreeCNF) : ℕ :=
  (occurringVariables formula).length

theorem mem_occurringVariables_iff
    (formula : ThreeCNF) (name : ℕ) :
    name ∈ occurringVariables formula ↔
      name ∈ formulaVariables formula := by
  simp only [occurringVariables, List.mem_eraseDups]

theorem eraseDups_nodup (names : List ℕ) :
    names.eraseDups.Nodup := by
  induction names using
      (measure fun values : List ℕ => values.length).wf.induction with
  | h names induction =>
      cases names with
      | nil => simp only [List.eraseDups_nil, List.nodup_nil]
      | cons name remaining =>
          rw [List.eraseDups_cons, List.nodup_cons]
          constructor
          · simp only [List.mem_eraseDups, List.mem_filter, BEq.rfl, Bool.not_true,
              Bool.false_eq_true, and_false,
                not_false_eq_true]
          · exact induction
              (remaining.filter fun candidate => !(candidate == name))
              (Nat.lt_succ_of_le (List.length_filter_le _ _))

theorem occurringVariables_nodup (formula : ThreeCNF) :
    (occurringVariables formula).Nodup :=
  eraseDups_nodup (formulaVariables formula)

/-- GapCVP reduction support. -/
def compactVariableRank (formula : ThreeCNF) (name : ℕ) : ℕ :=
  (occurringVariables formula).idxOf name

theorem mem_formulaVariables_iff_exists_literal
    (formula : ThreeCNF) (name : ℕ) :
    name ∈ formulaVariables formula ↔
      ∃ clause ∈ formula, ∃ index : Fin 3,
        (clause index).1 = name := by
  constructor
  · intro hvariable
    unfold formulaVariables at hvariable
    obtain ⟨clause, hclause, hposition⟩ :=
      List.mem_flatMap.mp hvariable
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hposition
    rcases hposition with hzero | hone | htwo
    · exact ⟨clause, hclause, 0, hzero.symm⟩
    · exact ⟨clause, hclause, 1, hone.symm⟩
    · exact ⟨clause, hclause, 2, htwo.symm⟩
  · rintro ⟨clause, hclause, index, rfl⟩
    exact mem_formulaVariables formula clause hclause index

end BinarySourceVariableCompaction

namespace Core.EffectiveBinaryGaussian

open scoped BigOperators
open Matrix

/-- GapCVP reduction support. -/
structure System (m n : ℕ) where
  /-- GapCVP reduction support. -/
  check : Matrix (Fin m) (Fin n) (ZMod 2)
  /-- GapCVP reduction support. -/
  rhs : Fin m → ZMod 2

/-- GapCVP reduction support. -/
noncomputable def System.Satisfies {m n : ℕ} (system : System m n)
    (assignment : Fin n → ZMod 2) : Bool :=
  @decide (
  system.check.mulVec assignment = system.rhs
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def swapRows {m n : ℕ} (system : System m n)
    (left right : Fin m) : System m n where
  check row column := system.check (Equiv.swap left right row) column
  rhs row := system.rhs (Equiv.swap left right row)

theorem swapRows_satisfies_iff {m n : ℕ} (system : System m n)
    (left right : Fin m) (assignment : Fin n → ZMod 2) :
    (swapRows system left right).Satisfies assignment ↔
      system.Satisfies assignment := by
  simp only [GapCVP.Core.EffectiveBinaryGaussian.System.Satisfies, decide_eq_true_eq] at *
  constructor
  · intro h
    funext row
    have hr := congrFun h (Equiv.swap left right row)
    simpa only [mulVec, dotProduct, swapRows, Equiv.swap_apply_self] using hr
  · intro h
    funext row
    have hr := congrFun h (Equiv.swap left right row)
    simpa only [mulVec, dotProduct, swapRows] using hr

/-- GapCVP reduction support. -/
def addRow {m n : ℕ} (system : System m n)
    (source target : Fin m) : System m n where
  check row column :=
    if row = target then
      system.check row column + system.check source column
    else system.check row column
  rhs row :=
    if row = target then system.rhs row + system.rhs source
    else system.rhs row

theorem binary_add_self (value : ZMod 2) : value + value = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, htwo, zero_mul]

theorem binary_eq_zero_of_ne_one (value : ZMod 2)
    (hne : value ≠ 1) : value = 0 := by
  have hval : value.val < 2 := ZMod.val_lt value
  have hnotone : value.val ≠ 1 := by
    intro h
    apply hne
    apply ZMod.val_injective 2
    rw [ZMod.val_one]
    exact h
  apply ZMod.val_injective 2
  simp only [ZMod.val_zero]
  omega

@[simp] private theorem addRow_twice {m n : ℕ} (system : System m n)
    (source target : Fin m) (hne : source ≠ target) :
    addRow (addRow system source target) source target = system := by
  cases system with
  | mk check rhs =>
    refine congrArg₂ (@System.mk m n) ?_ ?_
    · funext row column
      by_cases hr : row = target
      · subst row
        simp only [↓reduceIte, addRow, hne, add_assoc, binary_add_self, add_zero]
      · simp only [hr, ↓reduceIte, addRow]
    · funext row
      by_cases hr : row = target
      · subst row
        simp only [↓reduceIte, addRow, hne, add_assoc, binary_add_self, add_zero]
      · simp only [hr, ↓reduceIte, addRow]

private theorem satisfies_addRow {m n : ℕ} (system : System m n)
    (source target : Fin m) (assignment : Fin n → ZMod 2)
    (h : system.Satisfies assignment) :
    (addRow system source target).Satisfies assignment := by
  simp only [GapCVP.Core.EffectiveBinaryGaussian.System.Satisfies, decide_eq_true_eq] at *
  funext row
  by_cases hr : row = target
  · subst row
    have htarget := congrFun h target
    have hsource := congrFun h source
    simp only [addRow, ↓reduceIte, Matrix.mulVec, dotProduct] at htarget hsource ⊢
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, htarget, hsource]
  · have hrow := congrFun h row
    simpa only [mulVec, dotProduct, addRow, hr, ↓reduceIte] using hrow

theorem addRow_satisfies_iff {m n : ℕ} (system : System m n)
    (source target : Fin m) (hne : source ≠ target)
    (assignment : Fin n → ZMod 2) :
    (addRow system source target).Satisfies assignment ↔
      system.Satisfies assignment := by
  constructor
  · intro h
    have h' := satisfies_addRow
      (addRow system source target) source target assignment h
    simpa only [addRow_twice system source target hne] using h'
  · exact satisfies_addRow system source target assignment

/-- GapCVP reduction support. -/
inductive RowOperation (m : ℕ) where
  | swap (left right : Fin m)
  | add (source target : Fin m) (distinct : source ≠ target)

/-- GapCVP reduction support. -/
def RowOperation.apply {m n : ℕ} (operation : RowOperation m)
    (system : System m n) : System m n :=
  match operation with
  | .swap left right => swapRows system left right
  | .add source target _ => addRow system source target

theorem RowOperation.satisfies_iff {m n : ℕ}
    (operation : RowOperation m) (system : System m n)
    (assignment : Fin n → ZMod 2) :
    (operation.apply system).Satisfies assignment ↔
      system.Satisfies assignment := by
  cases operation with
  | swap left right =>
      exact swapRows_satisfies_iff system left right assignment
  | add source target distinct =>
      exact addRow_satisfies_iff system source target distinct assignment

/-- GapCVP reduction support. -/
structure State (m n : ℕ) where
  /-- GapCVP reduction support. -/
  system : System m n
  /-- GapCVP reduction support. -/
  nextPivot : ℕ
  /-- GapCVP reduction support. -/
  pivots : List (Fin m × Fin n)
  /-- GapCVP reduction support. -/
  operations : List (RowOperation m)

/-- GapCVP reduction support. -/
def initialState {m n : ℕ} (system : System m n) : State m n where
  system := system
  nextPivot := 0
  pivots := []
  operations := []

/-- GapCVP reduction support. -/
def applyOperation {m n : ℕ} (state : State m n)
    (operation : RowOperation m) : State m n where
  system := operation.apply state.system
  nextPivot := state.nextPivot
  pivots := state.pivots
  operations := operation :: state.operations

private theorem applyOperation_satisfies_iff {m n : ℕ}
    (state : State m n) (operation : RowOperation m)
    (assignment : Fin n → ZMod 2) :
    (applyOperation state operation).system.Satisfies assignment ↔
      state.system.Satisfies assignment :=
  operation.satisfies_iff state.system assignment

/-- GapCVP reduction support. -/
def findPivotOption {m n : ℕ} (state : State m n)
    (column : Fin n) : Option (Fin m) :=
  (List.finRange m).find? fun row =>
    decide (state.nextPivot ≤ row.val ∧
      state.system.check row column = (1 : ZMod 2))

theorem findPivotOption_some {m n : ℕ} (state : State m n)
    (column : Fin n) (row : Fin m)
    (h : findPivotOption state column = some row) :
    state.nextPivot ≤ row.val ∧
      state.system.check row column = (1 : ZMod 2) := by
  have hp := List.find?_some h
  simpa only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] using hp

/-- GapCVP reduction support. -/
def clearTarget {m n : ℕ} (pivot : Fin m) (column : Fin n)
    (state : State m n) (target : Fin m) : State m n :=
  if htarget : target = pivot then
    state
  else if state.system.check target column = (1 : ZMod 2) then
    applyOperation state (.add pivot target (Ne.symm htarget))
  else
    state

private theorem clearTarget_satisfies_iff {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (state : State m n) (target : Fin m)
    (assignment : Fin n → ZMod 2) :
    (clearTarget pivot column state target).system.Satisfies assignment ↔
      state.system.Satisfies assignment := by
  unfold clearTarget
  split
  · rfl
  · split
    · exact applyOperation_satisfies_iff _ _ _
    · rfl

theorem clearTarget_check_pivot {m n : ℕ}
    (pivot : Fin m) (column otherColumn : Fin n)
    (state : State m n) (target : Fin m) :
    (clearTarget pivot column state target).system.check pivot otherColumn =
      state.system.check pivot otherColumn := by
  unfold clearTarget
  split
  · rfl
  · rename_i hne
    split
    · simp only [applyOperation, RowOperation.apply, addRow, Ne.symm hne, ↓reduceIte]
    · rfl

theorem clearTarget_rhs_pivot {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (state : State m n) (target : Fin m) :
    (clearTarget pivot column state target).system.rhs pivot =
      state.system.rhs pivot := by
  unfold clearTarget
  split
  · rfl
  · rename_i hne
    split
    · simp only [applyOperation, RowOperation.apply, addRow, Ne.symm hne, ↓reduceIte]
    · rfl

private theorem clearTarget_check_zero {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (state : State m n) (target row : Fin m)
    (hzero : state.system.check row column = 0) :
    (clearTarget pivot column state target).system.check row column = 0 := by
  unfold clearTarget
  split
  · exact hzero
  · split
    · rename_i hne hone
      by_cases hrow : row = target
      · subst row
        simp only [hzero, zero_ne_one] at hone
      · simpa only [applyOperation, RowOperation.apply, addRow, hrow, ↓reduceIte] using hzero
    · exact hzero

private theorem clearTarget_check_target_zero {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (state : State m n) (target : Fin m)
    (hne : target ≠ pivot)
    (hpivot : state.system.check pivot column = 1) :
    (clearTarget pivot column state target).system.check target column = 0 := by
  unfold clearTarget
  simp only [hne, ↓reduceDIte]
  by_cases hone : state.system.check target column = (1 : ZMod 2)
  · simp only [hone, ↓reduceIte, applyOperation, RowOperation.apply,
      addRow, ↓reduceIte]
    rw [hpivot, binary_add_self]
  · simp only [hone, ↓reduceIte]
    exact binary_eq_zero_of_ne_one _ hone

/-- GapCVP reduction support. -/
def clearTargets {m n : ℕ} (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m)) (state : State m n) : State m n :=
  targets.foldl (clearTarget pivot column) state

private theorem clearTargets_satisfies_iff {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m)) (state : State m n)
    (assignment : Fin n → ZMod 2) :
    (clearTargets pivot column targets state).system.Satisfies assignment ↔
      state.system.Satisfies assignment := by
  induction targets generalizing state with
  | nil => rfl
  | cons target rest ih =>
      change
        (clearTargets pivot column rest
          (clearTarget pivot column state target)).system.Satisfies assignment ↔
          state.system.Satisfies assignment
      exact (ih (clearTarget pivot column state target)).trans
        (clearTarget_satisfies_iff pivot column state target assignment)

private theorem clearTargets_check_pivot {m n : ℕ}
    (pivot : Fin m) (column otherColumn : Fin n)
    (targets : List (Fin m)) (state : State m n) :
    (clearTargets pivot column targets state).system.check
        pivot otherColumn = state.system.check pivot otherColumn := by
  induction targets generalizing state with
  | nil => rfl
  | cons target rest ih =>
      change
        (clearTargets pivot column rest
          (clearTarget pivot column state target)).system.check
            pivot otherColumn = state.system.check pivot otherColumn
      exact (ih (clearTarget pivot column state target)).trans
        (clearTarget_check_pivot pivot column otherColumn state target)

private theorem clearTargets_check_zero {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m)) (state : State m n) (row : Fin m)
    (hzero : state.system.check row column = 0) :
    (clearTargets pivot column targets state).system.check row column = 0 := by
  induction targets generalizing state with
  | nil => exact hzero
  | cons target rest ih =>
      change
        (clearTargets pivot column rest
          (clearTarget pivot column state target)).system.check
            row column = 0
      exact ih (clearTarget pivot column state target)
        (clearTarget_check_zero pivot column state target row hzero)

private theorem clearTargets_check_zero_of_mem {m n : ℕ}
    (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m)) (state : State m n) (row : Fin m)
    (hpivot : state.system.check pivot column = 1)
    (hne : row ≠ pivot) (hmem : row ∈ targets) :
    (clearTargets pivot column targets state).system.check row column = 0 := by
  induction targets generalizing state with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons target rest ih =>
      change
        (clearTargets pivot column rest
          (clearTarget pivot column state target)).system.check
            row column = 0
      rcases List.mem_cons.mp hmem with hrow | hrest
      · subst target
        exact clearTargets_check_zero pivot column rest
          (clearTarget pivot column state row) row
          (clearTarget_check_target_zero pivot column state row hne hpivot)
      · apply ih (clearTarget pivot column state target)
        · rw [clearTarget_check_pivot]
          exact hpivot
        · exact hrest

/-- GapCVP reduction support. -/
def columnStep {m n : ℕ} (state : State m n)
    (column : Fin n) : State m n :=
  if hrow : state.nextPivot < m then
    match findPivotOption state column with
    | none => state
    | some candidate =>
      let pivot : Fin m := ⟨state.nextPivot, hrow⟩
      let swapped := applyOperation state (.swap candidate pivot)
      let cleared := clearTargets pivot column (List.finRange m) swapped
      { cleared with
        nextPivot := state.nextPivot + 1
        pivots := (pivot, column) :: cleared.pivots }
  else
    state

private theorem columnStep_satisfies_iff {m n : ℕ}
    (state : State m n) (column : Fin n)
    (assignment : Fin n → ZMod 2) :
    (columnStep state column).system.Satisfies assignment ↔
      state.system.Satisfies assignment := by
  by_cases hrow : state.nextPivot < m
  · cases hpivot : findPivotOption state column with
    | none =>
        simp only [columnStep, hrow, ↓reduceDIte, hpivot]
    | some candidate =>
        simp only [columnStep, hrow, ↓reduceDIte, hpivot]
        exact (clearTargets_satisfies_iff
          ⟨state.nextPivot, hrow⟩ column (List.finRange m)
          (applyOperation state
            (.swap candidate ⟨state.nextPivot, hrow⟩)) assignment).trans
          (applyOperation_satisfies_iff state
            (.swap candidate ⟨state.nextPivot, hrow⟩) assignment)
  · simp only [columnStep, hrow, ↓reduceDIte]

theorem columnStep_pivot_column {m n : ℕ}
    (state : State m n) (column : Fin n)
    (hrow : state.nextPivot < m) (candidate : Fin m)
    (hfound : findPivotOption state column = some candidate)
    (row : Fin m) :
    (columnStep state column).system.check row column =
      if row = (⟨state.nextPivot, hrow⟩ : Fin m)
      then (1 : ZMod 2) else 0 := by
  let pivot : Fin m := ⟨state.nextPivot, hrow⟩
  let swapped : State m n :=
    applyOperation state (.swap candidate pivot)
  have hcandidate := (findPivotOption_some state column candidate hfound).2
  have hpivot : swapped.system.check pivot column = 1 := by
    simp [swapped, applyOperation, RowOperation.apply,
      swapRows, Equiv.swap_apply_right, hcandidate]
  simp only [columnStep, hrow, ↓reduceDIte, hfound]
  by_cases hsame : row = pivot
  · subst row
    change
      (clearTargets pivot column (List.finRange m) swapped).system.check
        pivot column = if pivot = ⟨state.nextPivot, hrow⟩ then 1 else 0
    rw [clearTargets_check_pivot]
    simpa [pivot] using hpivot
  · change
      (clearTargets pivot column (List.finRange m) swapped).system.check
        row column = if row = ⟨state.nextPivot, hrow⟩ then 1 else 0
    have hzero := clearTargets_check_zero_of_mem
      pivot column (List.finRange m) swapped row hpivot hsame
      (List.mem_finRange row)
    simpa [pivot, hsame] using hzero

private theorem addRow_check_of_source_zero {m n : ℕ}
    (system : System m n) (source target : Fin m)
    (column : Fin n)
    (hzero : system.check source column = 0) (row : Fin m) :
    (addRow system source target).check row column =
      system.check row column := by
  by_cases hrow : row = target
  · subst row
    simp only [addRow, ↓reduceIte, hzero, add_zero]
  · simp only [addRow, hrow, ↓reduceIte]

private theorem clearTarget_check_of_pivot_zero {m n : ℕ}
    (pivot : Fin m) (pivotColumn oldColumn : Fin n)
    (state : State m n) (target row : Fin m)
    (hzero : state.system.check pivot oldColumn = 0) :
    (clearTarget pivot pivotColumn state target).system.check
        row oldColumn = state.system.check row oldColumn := by
  unfold clearTarget
  split
  · rfl
  · split
    · exact addRow_check_of_source_zero
        state.system pivot target oldColumn hzero row
    · rfl

theorem clearTargets_check_of_pivot_zero {m n : ℕ}
    (pivot : Fin m) (pivotColumn oldColumn : Fin n)
    (targets : List (Fin m)) (state : State m n)
    (hzero : state.system.check pivot oldColumn = 0) (row : Fin m) :
    (clearTargets pivot pivotColumn targets state).system.check
        row oldColumn = state.system.check row oldColumn := by
  induction targets generalizing state with
  | nil => rfl
  | cons target rest ih =>
      change
        (clearTargets pivot pivotColumn rest
          (clearTarget pivot pivotColumn state target)).system.check
            row oldColumn = state.system.check row oldColumn
      have hpivot :
          (clearTarget pivot pivotColumn state target).system.check
              pivot oldColumn = 0 := by
        rw [clearTarget_check_pivot]
        exact hzero
      calc
        (clearTargets pivot pivotColumn rest
          (clearTarget pivot pivotColumn state target)).system.check
            row oldColumn =
          (clearTarget pivot pivotColumn state target).system.check
            row oldColumn := ih _ hpivot
        _ = state.system.check row oldColumn :=
          clearTarget_check_of_pivot_zero
            pivot pivotColumn oldColumn state target row hzero

/-- GapCVP reduction support. -/
def runColumns {m n : ℕ}
    (columns : List (Fin n)) (state : State m n) : State m n :=
  columns.foldl columnStep state

private theorem runColumns_satisfies_iff {m n : ℕ}
    (columns : List (Fin n)) (state : State m n)
    (assignment : Fin n → ZMod 2) :
    (runColumns columns state).system.Satisfies assignment ↔
      state.system.Satisfies assignment := by
  induction columns generalizing state with
  | nil => rfl
  | cons column rest ih =>
      change
        (runColumns rest (columnStep state column)).system.Satisfies assignment ↔
          state.system.Satisfies assignment
      exact (ih (columnStep state column)).trans
        (columnStep_satisfies_iff state column assignment)

/-- GapCVP reduction support. -/
def eliminate {m n : ℕ} (system : System m n) : State m n :=
  runColumns (List.finRange n) (initialState system)

theorem eliminate_satisfies_iff {m n : ℕ}
    (system : System m n) (assignment : Fin n → ZMod 2) :
    (eliminate system).system.Satisfies assignment ↔
      system.Satisfies assignment := by
  exact runColumns_satisfies_iff
    (List.finRange n) (initialState system) assignment

end Core.EffectiveBinaryGaussian

namespace Core.EffectiveBinaryField

open scoped BigOperators
open Polynomial

/-- GapCVP reduction support. -/
abbrev Word (e : ℕ) := Fin e → Bool

/-- GapCVP reduction support. -/
def allWords : (e : ℕ) → List (Word e)
  | 0 => [fun i => Fin.elim0 i]
  | e + 1 =>
      (allWords e).flatMap fun tail =>
        [Fin.cases false tail, Fin.cases true tail]

private theorem word_head_tail {e : ℕ} (word : Word (e + 1)) :
    Fin.cases (word 0) (fun i : Fin e => word i.succ) = word := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem mem_allWords {e : ℕ} (word : Word e) : word ∈ allWords e := by
  induction e with
  | zero =>
      have heq : word = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      simp only [allWords, heq, List.mem_cons, List.not_mem_nil, or_false]
  | succ e ih =>
      let tail : Word e := fun i => word i.succ
      have htail : tail ∈ allWords e := ih tail
      have hword : Fin.cases (word 0) tail = word :=
        word_head_tail word
      rw [← hword, allWords]
      apply List.mem_flatMap.mpr
      refine ⟨tail, htail, ?_⟩
      cases hbit : word 0 <;> simp

/-- GapCVP reduction support. -/
def bitValue (bit : Bool) : ZMod 2 :=
  if bit then 1 else 0

theorem bitValue_xor (left right : Bool) :
    bitValue (Bool.xor left right) =
      bitValue left + bitValue right := by
  cases left <;> cases right <;> decide

private theorem bitValue_and (left right : Bool) :
    bitValue (left && right) =
      bitValue left * bitValue right := by
  cases left <;> cases right <;> decide

private theorem bitValue_decide (value : ZMod 2) :
    bitValue (decide (value = 1)) = value := by
  by_cases h : value = 1
  · subst value
    decide
  · have hz := EffectiveBinaryGaussian.binary_eq_zero_of_ne_one value h
    simp only [bitValue, hz, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- GapCVP reduction support. -/
noncomputable def wordPolynomial {e : ℕ}
    (word : Word e) : (ZMod 2)[X] :=
  ∑ i : Fin e, Polynomial.monomial i.val (bitValue (word i))

@[simp] theorem wordPolynomial_coeff_fin {e : ℕ}
    (word : Word e) (i : Fin e) :
    (wordPolynomial word).coeff i.val = bitValue (word i) := by
  classical
  unfold wordPolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp only [coeff_monomial_same]
  · intro j _ hji
    have hval : j.val ≠ i.val := by
      intro heq
      exact hji (Fin.ext heq)
    simp only [coeff_monomial, hval, ↓reduceIte]
  · simp only [Finset.mem_univ, not_true_eq_false, coeff_monomial_same, IsEmpty.forall_iff]

theorem wordPolynomial_coeff_eq_zero {e : ℕ}
    (word : Word e) (k : ℕ) (hk : e ≤ k) :
    (wordPolynomial word).coeff k = 0 := by
  classical
  simp only [wordPolynomial, finsetSum_coeff, coeff_monomial,
      show ∀ i : Fin e, i.val ≠ k by
          intro i h
          have := i.isLt
          omega,
      ↓reduceIte, Finset.sum_const_zero]

theorem wordPolynomial_degree_lt {e : ℕ}
    (word : Word e) :
    (wordPolynomial word).degree < (e : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ e).mpr
  intro k hk
  exact wordPolynomial_coeff_eq_zero word k hk

/-- GapCVP reduction support. -/
noncomputable def monicPolynomial {e : ℕ}
    (word : Word e) : (ZMod 2)[X] :=
  Polynomial.X ^ e + wordPolynomial word

/-- GapCVP reduction support. -/
noncomputable def coefficientWord (e : ℕ) (p : (ZMod 2)[X]) : Word e :=
  fun i => decide (p.coeff i.val = 1)

private theorem wordPolynomial_coefficientWord
    (e : ℕ) (p : (ZMod 2)[X])
    (hdegree : p.degree < (e : WithBot ℕ)) :
    wordPolynomial (coefficientWord e p) = p := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < e
  · let i : Fin e := ⟨k, hk⟩
    change
      (wordPolynomial (coefficientWord e p)).coeff i.val =
        p.coeff i.val
    rw [wordPolynomial_coeff_fin]
    exact bitValue_decide (p.coeff i.val)
  · have hke : e ≤ k := Nat.le_of_not_gt hk
    rw [wordPolynomial_coeff_eq_zero _ k hke]
    symm
    exact ((Polynomial.degree_lt_iff_coeff_zero p e).mp hdegree) k hke

private theorem exists_monicPolynomial_word
    {e : ℕ} (p : (ZMod 2)[X])
    (hmonic : p.Monic) (hdegree : p.natDegree = e) :
    ∃ word : Word e, monicPolynomial word = p := by
  let lower := p.eraseLead
  have hlow : lower.degree < (e : WithBot ℕ) := by
    have hp : p ≠ 0 := hmonic.ne_zero
    have h := Polynomial.degree_eraseLead_lt hp
    rw [Polynomial.degree_eq_natDegree hp, hdegree] at h
    exact h
  refine ⟨coefficientWord e lower, ?_⟩
  unfold monicPolynomial
  rw [wordPolynomial_coefficientWord e lower hlow]
  have hlead := Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff p
  rw [hdegree, hmonic.leadingCoeff, ← Polynomial.X_pow_eq_monomial] at hlead
  simpa only [add_comm] using hlead

private theorem exists_monic_irreducible_polynomial
    (e : ℕ) (he : 0 < e) :
    ∃ p : (ZMod 2)[X],
      p.Monic ∧ p.natDegree = e ∧ Irreducible p := by
  obtain ⟨root, hroot⟩ :=
    Field.exists_primitive_element_of_finite_top
      (ZMod 2) (GaloisField 2 e)
  have hintegral : IsIntegral (ZMod 2) root :=
    IsIntegral.of_finite (ZMod 2) root
  refine ⟨minpoly (ZMod 2) root,
    minpoly.monic hintegral, ?_, minpoly.irreducible hintegral⟩
  calc
    (minpoly (ZMod 2) root).natDegree =
        Module.finrank (ZMod 2) (GaloisField 2 e) :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        (ZMod 2) root).mp hroot
    _ = e := GaloisField.finrank 2 (Nat.ne_of_gt he)

private theorem exists_monic_irreducible_word
    (e : ℕ) (he : 0 < e) :
    ∃ word : Word e, Irreducible (monicPolynomial word) := by
  obtain ⟨p, hmonic, hdegree, hirr⟩ :=
    exists_monic_irreducible_polynomial e he
  obtain ⟨word, hword⟩ :=
    exists_monicPolynomial_word p hmonic hdegree
  exact ⟨word, hword.symm ▸ hirr⟩

private theorem monicPolynomial_monic {e : ℕ}
    (word : Word e) :
    (monicPolynomial word).Monic := by
  exact Polynomial.monic_X_pow_add (wordPolynomial_degree_lt word)

private theorem monicPolynomial_natDegree {e : ℕ}
    (word : Word e) :
    (monicPolynomial word).natDegree = e := by
  have hdegree :
      (monicPolynomial word).degree = (e : WithBot ℕ) := by
    unfold monicPolynomial
    have hlt :
        (wordPolynomial word).degree <
          (Polynomial.X ^ e : (ZMod 2)[X]).degree := by
      simpa only [degree_pow, degree_X, nsmul_eq_mul, mul_one] using wordPolynomial_degree_lt word
    simpa only [degree_pow, degree_X, nsmul_eq_mul, mul_one]
        using Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hne : monicPolynomial word ≠ 0 :=
    (monicPolynomial_monic word).ne_zero
  rw [Polynomial.degree_eq_natDegree hne] at hdegree
  exact_mod_cast hdegree

private theorem bitValue_foldl {α : Type}
    (items : List α) (step : Bool → α → Bool)
    (weight : α → ZMod 2)
    (hstep : ∀ accumulator item,
      bitValue (step accumulator item) =
        bitValue accumulator + weight item)
    (initial : Bool) :
    bitValue (items.foldl step initial) =
      bitValue initial + (items.map weight).sum := by
  induction items generalizing initial with
  | nil =>
      simp only [bitValue, List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
      rfl
  | cons item rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (step initial item), hstep]
      ac_rfl

private theorem finRange_list_sum {e : ℕ} (f : Fin e → ZMod 2) :
    ((List.finRange e).map f).sum = ∑ i : Fin e, f i := by
  rfl

/-- GapCVP reduction support. -/
def multiplyWords {e : ℕ} (left right : Word e) : Word (2 * e) :=
  fun k =>
    (List.finRange e).foldl
      (fun acc i =>
        (List.finRange e).foldl
          (fun inner j =>
            if i.val + j.val = k.val then
              Bool.xor inner (left i && right j)
            else inner)
          acc)
      false

private theorem bitValue_multiplyWords {e : ℕ}
    (left right : Word e) (k : Fin (2 * e)) :
    bitValue (multiplyWords left right k) =
      ∑ i : Fin e, ∑ j : Fin e,
        if i.val + j.val = k.val then
          bitValue (left i) * bitValue (right j)
        else 0 := by
  have hinner (i : Fin e) (initial : Bool) :
      bitValue
        ((List.finRange e).foldl
          (fun inner j =>
            if i.val + j.val = k.val then
              Bool.xor inner (left i && right j)
            else inner)
          initial) =
        bitValue initial +
          ∑ j : Fin e,
            if i.val + j.val = k.val then
              bitValue (left i) * bitValue (right j)
            else 0 := by
    calc
      bitValue
        ((List.finRange e).foldl
          (fun inner j =>
            if i.val + j.val = k.val then
              Bool.xor inner (left i && right j)
            else inner)
          initial) =
        bitValue initial +
          ((List.finRange e).map fun j =>
            if i.val + j.val = k.val then
              bitValue (left i) * bitValue (right j)
            else 0).sum := by
          apply bitValue_foldl
          intro accumulator j
          by_cases hij : i.val + j.val = k.val
          · simp only [hij, ↓reduceIte, bitValue_xor, bitValue_and]
          · simp only [hij, ↓reduceIte, add_zero]
      _ = bitValue initial +
          ∑ j : Fin e,
            if i.val + j.val = k.val then
              bitValue (left i) * bitValue (right j)
            else 0 := by
          rw [finRange_list_sum]
  unfold multiplyWords
  calc
    bitValue
      ((List.finRange e).foldl
        (fun acc i =>
          (List.finRange e).foldl
            (fun inner j =>
              if i.val + j.val = k.val then
                Bool.xor inner (left i && right j)
              else inner)
            acc)
        false) =
      bitValue false +
        ((List.finRange e).map fun i =>
          ∑ j : Fin e,
            if i.val + j.val = k.val then
              bitValue (left i) * bitValue (right j)
            else 0).sum := by
        apply bitValue_foldl
        intro accumulator i
        exact hinner i accumulator
    _ = ∑ i : Fin e, ∑ j : Fin e,
          if i.val + j.val = k.val then
            bitValue (left i) * bitValue (right j)
          else 0 := by
        rw [finRange_list_sum]
        simp only [bitValue, Bool.false_eq_true, ↓reduceIte, mul_ite, mul_one, mul_zero, zero_add]

private theorem wordPolynomial_mul_coeff {e : ℕ}
    (left right : Word e) (k : ℕ) :
    (wordPolynomial left * wordPolynomial right).coeff k =
      ∑ i : Fin e, ∑ j : Fin e,
        if i.val + j.val = k then
          bitValue (left i) * bitValue (right j)
        else 0 := by
  classical
  simp only [wordPolynomial, Finset.mul_sum, Finset.sum_mul, monomial_mul_monomial,
      finsetSum_coeff,
      coeff_monomial]
  rw [Finset.sum_comm]

theorem wordPolynomial_multiplyWords {e : ℕ}
    (left right : Word e) :
    wordPolynomial (multiplyWords left right) =
      wordPolynomial left * wordPolynomial right := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 * e
  · let i : Fin (2 * e) := ⟨k, hk⟩
    change
      (wordPolynomial (multiplyWords left right)).coeff i.val =
        (wordPolynomial left * wordPolynomial right).coeff i.val
    rw [wordPolynomial_coeff_fin, bitValue_multiplyWords,
      wordPolynomial_mul_coeff]
  · have hlarge : 2 * e ≤ k := Nat.le_of_not_gt hk
    rw [wordPolynomial_coeff_eq_zero _ k hlarge,
      wordPolynomial_mul_coeff]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : i.val + j.val ≠ k := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp only [hne, ↓reduceIte]

/-- GapCVP reduction support. -/
def monicWord {e : ℕ} (lower : Word e) : Word (2 * e) :=
  fun i =>
    if h : i.val < e then lower ⟨i.val, h⟩
    else decide (i.val = e)

theorem bitValue_injective : Function.Injective bitValue := by
  intro left right h
  cases left <;> cases right <;> simp [bitValue] at h ⊢

private theorem wordPolynomial_injective {e : ℕ} :
    Function.Injective (@wordPolynomial e) := by
  intro left right h
  funext i
  apply bitValue_injective
  have hcoeff := congrArg (fun p : (ZMod 2)[X] => p.coeff i.val) h
  simpa only [wordPolynomial_coeff_fin] using hcoeff

private theorem wordPolynomial_monicWord {e : ℕ} (he : 0 < e)
    (lower : Word e) :
    wordPolynomial (monicWord lower) = monicPolynomial lower := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 * e
  · let i : Fin (2 * e) := ⟨k, hk⟩
    change
      (wordPolynomial (monicWord lower)).coeff i.val =
        (monicPolynomial lower).coeff i.val
    rw [wordPolynomial_coeff_fin]
    unfold monicPolynomial
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow]
    by_cases hlow : i.val < e
    · have hne : i.val ≠ e := Nat.ne_of_lt hlow
      rw [ite_eq_right hne]
      simp only [zero_add]
      change
        bitValue (if h : i.val < e then lower ⟨i.val, h⟩
          else decide (i.val = e)) =
          (wordPolynomial lower).coeff i.val
      simp only [hlow, ↓reduceDIte]
      exact (wordPolynomial_coeff_fin lower ⟨i.val, hlow⟩).symm
    · have hlarge : e ≤ i.val := Nat.le_of_not_gt hlow
      rw [wordPolynomial_coeff_eq_zero lower i.val hlarge, add_zero]
      change
        bitValue (if h : i.val < e then lower ⟨i.val, h⟩
          else decide (i.val = e)) =
          if i.val = e then 1 else 0
      simp only [bitValue, hlow, ↓reduceDIte, decide_eq_true_eq]
  · have hlarge : 2 * e ≤ k := Nat.le_of_not_gt hk
    rw [wordPolynomial_coeff_eq_zero _ k hlarge]
    unfold monicPolynomial
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow]
    have hke : e ≤ k := by omega
    rw [wordPolynomial_coeff_eq_zero lower k hke]
    have hne : k ≠ e := by omega
    simp only [hne, ↓reduceIte, add_zero]

private theorem multiplyWords_eq_monicWord_iff {e : ℕ} (he : 0 < e)
    (left right lower : Word e) :
    multiplyWords left right = monicWord lower ↔
      wordPolynomial left * wordPolynomial right =
        monicPolynomial lower := by
  constructor
  · intro h
    calc
      wordPolynomial left * wordPolynomial right =
          wordPolynomial (multiplyWords left right) :=
        (wordPolynomial_multiplyWords left right).symm
      _ = wordPolynomial (monicWord lower) := congrArg wordPolynomial h
      _ = monicPolynomial lower := wordPolynomial_monicWord he lower
  · intro h
    apply wordPolynomial_injective
    rw [wordPolynomial_multiplyWords,
      wordPolynomial_monicWord he lower]
    exact h

/-- GapCVP reduction support. -/
def noProperFactors (e : ℕ) (lower : Word e) : Bool :=
  (allWords e).all fun left =>
    (allWords e).all fun right =>
      decide (multiplyWords left right ≠ monicWord lower)

theorem noProperFactors_eq_true_iff {e : ℕ} (lower : Word e) :
    noProperFactors e lower = true ↔
      ∀ left right : Word e,
        multiplyWords left right ≠ monicWord lower := by
  constructor
  · intro h left right
    have hleft := (List.all_eq_true.mp h) left (mem_allWords left)
    have hright := (List.all_eq_true.mp hleft) right (mem_allWords right)
    exact of_decide_eq_true hright
  · intro h
    apply List.all_eq_true.mpr
    intro left _
    apply List.all_eq_true.mpr
    intro right _
    exact decide_eq_true (h left right)

private theorem monicPolynomial_irreducible_iff {e : ℕ} (he : 0 < e)
    (lower : Word e) :
    Irreducible (monicPolynomial lower) ↔
      ∀ left right : Word e,
        multiplyWords left right ≠ monicWord lower := by
  constructor
  · intro hirr left right hbits
    have hfactor :
        monicPolynomial lower =
          wordPolynomial left * wordPolynomial right :=
      ((multiplyWords_eq_monicWord_iff he left right lower).mp hbits).symm
    have hnonzero : monicPolynomial lower ≠ 0 :=
      (monicPolynomial_monic lower).ne_zero
    have hleft : wordPolynomial left ≠ 0 := by
      intro h
      apply hnonzero
      rw [hfactor, h, zero_mul]
    have hright : wordPolynomial right ≠ 0 := by
      intro h
      apply hnonzero
      rw [hfactor, h, mul_zero]
    have hleftdegree : (wordPolynomial left).natDegree < e :=
      (Polynomial.natDegree_lt_iff_degree_lt hleft).mpr
        (wordPolynomial_degree_lt left)
    have hrightdegree : (wordPolynomial right).natDegree < e :=
      (Polynomial.natDegree_lt_iff_degree_lt hright).mpr
        (wordPolynomial_degree_lt right)
    have hdegree :
        e = (wordPolynomial left).natDegree +
          (wordPolynomial right).natDegree := by
      have h := congrArg Polynomial.natDegree hfactor
      rw [monicPolynomial_natDegree,
        Polynomial.natDegree_mul hleft hright] at h
      exact h
    rcases (irreducible_iff.mp hirr).2 hfactor with hunit | hunit
    · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hunit
      omega
    · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hunit
      omega
  · intro hno
    apply irreducible_iff.mpr
    constructor
    · apply Polynomial.not_isUnit_of_natDegree_pos
      rw [monicPolynomial_natDegree]
      exact he
    · intro left right hfactor
      by_cases hleftunit : IsUnit left
      · exact Or.inl hleftunit
      by_cases hrightunit : IsUnit right
      · exact Or.inr hrightunit
      exfalso
      have hnonzero : monicPolynomial lower ≠ 0 :=
        (monicPolynomial_monic lower).ne_zero
      have hleft : left ≠ 0 := by
        intro h
        apply hnonzero
        rw [hfactor, h, zero_mul]
      have hright : right ≠ 0 := by
        intro h
        apply hnonzero
        rw [hfactor, h, mul_zero]
      have hdegree : e = left.natDegree + right.natDegree := by
        have h := congrArg Polynomial.natDegree hfactor
        rw [monicPolynomial_natDegree,
          Polynomial.natDegree_mul hleft hright] at h
        exact h
      have hleftpositive : 0 < left.natDegree :=
        Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
          (monicPolynomial_monic lower) hleftunit
          ⟨right, hfactor⟩
      have hrightpositive : 0 < right.natDegree :=
        Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
          (monicPolynomial_monic lower) hrightunit
          ⟨left, by simpa only [mul_comm] using hfactor⟩
      have hleftdegree : left.natDegree < e := by omega
      have hrightdegree : right.natDegree < e := by omega
      have hleftdegree' : left.degree < (e : WithBot ℕ) :=
        (Polynomial.natDegree_lt_iff_degree_lt hleft).mp hleftdegree
      have hrightdegree' : right.degree < (e : WithBot ℕ) :=
        (Polynomial.natDegree_lt_iff_degree_lt hright).mp hrightdegree
      let leftWord := coefficientWord e left
      let rightWord := coefficientWord e right
      have hleftWord : wordPolynomial leftWord = left :=
        wordPolynomial_coefficientWord e left hleftdegree'
      have hrightWord : wordPolynomial rightWord = right :=
        wordPolynomial_coefficientWord e right hrightdegree'
      apply hno leftWord rightWord
      apply (multiplyWords_eq_monicWord_iff
        he leftWord rightWord lower).mpr
      rw [hleftWord, hrightWord]
      exact hfactor.symm

private theorem noProperFactors_eq_true_iff_irreducible {e : ℕ}
    (he : 0 < e) (lower : Word e) :
    noProperFactors e lower = true ↔
      Irreducible (monicPolynomial lower) := by
  rw [noProperFactors_eq_true_iff]
  exact (monicPolynomial_irreducible_iff he lower).symm

/-- GapCVP reduction support. -/
def findIrreducibleWordOption (e : ℕ) : Option (Word e) :=
  (allWords e).find? (noProperFactors e)

private theorem findIrreducibleWordOption_some {e : ℕ} (word : Word e)
    (h : findIrreducibleWordOption e = some word) :
    noProperFactors e word = true :=
  List.find?_some h

theorem findIrreducibleWordOption_exists
    (e : ℕ) (he : 0 < e) :
    ∃ word : Word e,
      findIrreducibleWordOption e = some word ∧
        Irreducible (monicPolynomial word) := by
  obtain ⟨candidate, hirr⟩ := exists_monic_irreducible_word e he
  have hcandidate : noProperFactors e candidate = true :=
    (noProperFactors_eq_true_iff_irreducible he candidate).mpr hirr
  cases hfind : findIrreducibleWordOption e with
  | none =>
      exfalso
      have hnone :
          ∀ word ∈ allWords e,
            ¬ noProperFactors e word = true := by
        exact List.find?_eq_none.mp hfind
      exact hnone candidate (mem_allWords candidate) hcandidate
  | some word =>
      refine ⟨word, rfl, ?_⟩
      apply (noProperFactors_eq_true_iff_irreducible he word).mp
      exact findIrreducibleWordOption_some word hfind

/-- GapCVP reduction support. -/
def irreducibleWord (e : ℕ) : Word e :=
  (findIrreducibleWordOption e).getD fun _ => false

private theorem irreducibleWord_irreducible (e : ℕ) (he : 0 < e) :
    Irreducible (monicPolynomial (irreducibleWord e)) := by
  obtain ⟨word, hword, hirr⟩ := findIrreducibleWordOption_exists e he
  simpa only [irreducibleWord, hword, Option.getD_some] using hirr

/-- GapCVP reduction support. -/
def xorAt {d : ℕ} (word : Word d) (index : Fin d) (bit : Bool) : Word d :=
  fun i => if i = index then Bool.xor (word i) bit else word i

theorem wordPolynomial_xorAt {d : ℕ}
    (word : Word d) (index : Fin d) (bit : Bool) :
    wordPolynomial (xorAt word index bit) =
      wordPolynomial word +
        Polynomial.monomial index.val (bitValue bit) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · let i : Fin d := ⟨k, hk⟩
    change
      (wordPolynomial (xorAt word index bit)).coeff i.val =
        (wordPolynomial word +
          Polynomial.monomial index.val (bitValue bit)).coeff i.val
    rw [Polynomial.coeff_add, wordPolynomial_coeff_fin,
      wordPolynomial_coeff_fin, Polynomial.coeff_monomial]
    by_cases hi : i = index
    · subst index
      simp only [xorAt, ↓reduceIte, bitValue_xor]
    · have hval : index.val ≠ i.val := by
        intro h
        exact hi (Fin.ext h.symm)
      simp only [xorAt, hi, ↓reduceIte, hval, add_zero]
  · have hlarge : d ≤ k := Nat.le_of_not_gt hk
    have hindex : index.val ≠ k := by
      have hlt := index.isLt
      omega
    rw [wordPolynomial_coeff_eq_zero _ k hlarge,
      Polynomial.coeff_add,
      wordPolynomial_coeff_eq_zero _ k hlarge,
      Polynomial.coeff_monomial]
    simp only [hindex, ↓reduceIte, add_zero]

/-- GapCVP reduction support. -/
def shiftXor {e : ℕ} (lower : Word e) (degree : ℕ)
    (word : Word (2 * e)) : Word (2 * e) :=
  (List.finRange e).foldl
    (fun accumulator i =>
      if h : degree - e + i.val < 2 * e then
        xorAt accumulator ⟨degree - e + i.val, h⟩ (lower i)
      else
        accumulator)
    word

/-- GapCVP reduction support. -/
def reduceAt {e : ℕ} (lower : Word e) (degree : ℕ)
    (word : Word (2 * e)) : Word (2 * e) :=
  if hd : e ≤ degree ∧ degree < 2 * e then
    let leading : Fin (2 * e) := ⟨degree, hd.2⟩
    if word leading then
      shiftXor lower degree (xorAt word leading true)
    else
      word
  else
    word

/-- GapCVP reduction support. -/
def reduceProduct {e : ℕ} (lower : Word e)
    (word : Word (2 * e)) : Word (2 * e) :=
  (List.range e).foldl
    (fun accumulator offset =>
      reduceAt lower (2 * e - 1 - offset) accumulator)
    word

/-- GapCVP reduction support. -/
def multiplyMod {e : ℕ}
    (lower left right : Word e) : Word e :=
  fun i =>
    (reduceProduct lower (multiplyWords left right))
      ⟨i.val, by
        have hi := i.isLt
        omega⟩

/-- GapCVP reduction support. -/
noncomputable def selectedPolynomial (e : ℕ) : (ZMod 2)[X] :=
  monicPolynomial (irreducibleWord e)

theorem selectedPolynomial_monic (e : ℕ) :
    (selectedPolynomial e).Monic :=
  monicPolynomial_monic (irreducibleWord e)

theorem selectedPolynomial_natDegree (e : ℕ) :
    (selectedPolynomial e).natDegree = e :=
  monicPolynomial_natDegree (irreducibleWord e)

private theorem selectedPolynomial_irreducible (e : ℕ) (he : 0 < e) :
    Irreducible (selectedPolynomial e) :=
  irreducibleWord_irreducible e he

/-- GapCVP reduction support. -/
abbrev Extension (e : ℕ) :=
  AdjoinRoot (selectedPolynomial e)

private noncomputable def extensionBasis (e : ℕ) :
    Module.Basis (Fin e) (ZMod 2) (Extension e) :=
  (AdjoinRoot.powerBasisAux' (selectedPolynomial_monic e)).reindex
    (finCongr (selectedPolynomial_natDegree e))

noncomputable instance extensionFintype (e : ℕ) :
    Fintype (Extension e) :=
  Fintype.ofEquiv (Fin e → ZMod 2)
    (extensionBasis e).equivFun.toEquiv.symm

private theorem extension_card (e : ℕ) :
    Fintype.card (Extension e) = 2 ^ e := by
  simpa only [ZMod.card, Fintype.card_fin] using Module.card_fintype (extensionBasis e)

/-- GapCVP reduction support. -/
noncomputable def extensionAlgEquivGaloisField (e : ℕ) (he : 0 < e) :
    Extension e ≃ₐ[ZMod 2] GaloisField 2 e := by
  letI : Fact (Irreducible (selectedPolynomial e)) :=
    ⟨selectedPolynomial_irreducible e he⟩
  exact GaloisField.algEquivGaloisFieldOfFintype 2 e
    (extension_card e)

end Core.EffectiveBinaryField

namespace BinaryFieldBasis

open Polynomial GapCVP.Core GapCVP.Core.EffectiveBinaryField

/-- GapCVP reduction support. -/
def indexedWord (degree : ℕ) (index : Fin (2 ^ degree)) :
    EffectiveBinaryField.Word degree :=
  fun bit => index.val.testBit bit.val

theorem indexedWord_injective (degree : ℕ) :
    Function.Injective (indexedWord degree) := by
  intro left right hwords
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hin : bit < degree
  · exact congrFun hwords ⟨bit, hin⟩
  · have hge : degree ≤ bit := Nat.le_of_not_gt hin
    have hpower : 2 ^ degree ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by norm_num) hge
    have hleft : left.val < 2 ^ bit :=
      lt_of_lt_of_le left.isLt hpower
    have hright : right.val < 2 ^ bit :=
      lt_of_lt_of_le right.isLt hpower
    rw [Nat.testBit_eq_false_of_lt hleft,
      Nat.testBit_eq_false_of_lt hright]

/-- GapCVP reduction support. -/
def boundedWordIndex {degree count : ℕ}
    (hcount : count ≤ 2 ^ degree) :
    Fin count ↪ Fin (2 ^ degree) :=
  Fin.castLEEmb hcount

/-- GapCVP reduction support. -/
def evaluationWordIndex {degree count : ℕ}
    (hcount : count ≤ 2 ^ degree) :
    Fin (2 ^ degree - count) ↪ Fin (2 ^ degree) :=
  (Fin.natAddEmb count).trans
    (finCongr (Nat.add_sub_of_le hcount)).toEmbedding

attribute [local instance] Classical.propDecidable

noncomputable instance (priority := 100)
    factor400GaloisFieldFintype (degree : ℕ) :
    Fintype (GaloisField 2 degree) :=
  Fintype.ofFinite (GaloisField 2 degree)

/-- GapCVP reduction support. -/
def wordElement {degree : ℕ}
    (word : EffectiveBinaryField.Word degree) :
    EffectiveBinaryField.Extension degree :=
  AdjoinRoot.mk (EffectiveBinaryField.selectedPolynomial degree)
    (EffectiveBinaryField.wordPolynomial word)

theorem wordElement_injective (degree : ℕ) :
    Function.Injective (@wordElement degree) := by
  intro left right helements
  have hdivides :
      EffectiveBinaryField.selectedPolynomial degree ∣
        EffectiveBinaryField.wordPolynomial left -
          EffectiveBinaryField.wordPolynomial right :=
    AdjoinRoot.mk_eq_mk.mp helements
  have hdegree :
      (EffectiveBinaryField.wordPolynomial left -
        EffectiveBinaryField.wordPolynomial right).degree <
          (degree : WithBot ℕ) :=
    (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt (EffectiveBinaryField.wordPolynomial_degree_lt left)
        (EffectiveBinaryField.wordPolynomial_degree_lt right))
  have hmodulus :
      (EffectiveBinaryField.selectedPolynomial degree).degree =
        (degree : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree
      (EffectiveBinaryField.selectedPolynomial_monic degree).ne_zero,
      EffectiveBinaryField.selectedPolynomial_natDegree]
  have hzero :
      EffectiveBinaryField.wordPolynomial left -
        EffectiveBinaryField.wordPolynomial right = 0 := by
    by_contra hnonzero
    have hmonic := EffectiveBinaryField.selectedPolynomial_monic degree
    have hnot := hmonic.not_dvd_of_degree_lt hnonzero (by
      rw [hmodulus]
      exact hdegree)
    exact hnot hdivides
  exact EffectiveBinaryField.wordPolynomial_injective
    (sub_eq_zero.mp hzero)

/-- GapCVP reduction support. -/
def effectiveExtensionBasis (degree : ℕ) :
    Module.Basis (Fin degree) (ZMod 2)
      (EffectiveBinaryField.Extension degree) :=
  EffectiveBinaryField.extensionBasis degree

/-- GapCVP reduction support. -/
def effectiveFieldBasis (degree : ℕ) (hdegree : 0 < degree) :
    Module.Basis (Fin degree) (ZMod 2) (GaloisField 2 degree) :=
  (effectiveExtensionBasis degree).map
    (EffectiveBinaryField.extensionAlgEquivGaloisField
      degree hdegree).toLinearEquiv

theorem effectiveFieldBasis_coordinates_transport
    (degree : ℕ) (hdegree : 0 < degree)
    (value : EffectiveBinaryField.Extension degree) :
    (effectiveFieldBasis degree hdegree).equivFun
        (EffectiveBinaryField.extensionAlgEquivGaloisField
          degree hdegree value) =
      (effectiveExtensionBasis degree).equivFun value := by
  simp only [effectiveFieldBasis, Module.Basis.map_equivFun, LinearEquiv.trans_apply,
      AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.symm_apply_apply, Module.Basis.equivFun_apply]

private def indexedFieldElement (degree : ℕ) (hdegree : 0 < degree)
    (index : Fin (2 ^ degree)) : GaloisField 2 degree :=
  EffectiveBinaryField.extensionAlgEquivGaloisField degree hdegree
    (wordElement (indexedWord degree index))

private theorem indexedFieldElement_injective
    (degree : ℕ) (hdegree : 0 < degree) :
    Function.Injective (indexedFieldElement degree hdegree) := by
  exact (EffectiveBinaryField.extensionAlgEquivGaloisField
    degree hdegree).injective.comp
      ((wordElement_injective degree).comp
        (indexedWord_injective degree))

private theorem field_card (degree : ℕ) (hdegree : 0 < degree) :
    Fintype.card (GaloisField 2 degree) = 2 ^ degree := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 degree hdegree.ne'

private theorem indexedFieldElement_bijective
    (degree : ℕ) (hdegree : 0 < degree) :
    Function.Bijective (indexedFieldElement degree hdegree) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨indexedFieldElement_injective degree hdegree, ?_⟩
  simp only [Fintype.card_fin, field_card degree hdegree]

/-- GapCVP reduction support. -/
def indexedFieldEquiv (degree : ℕ) (hdegree : 0 < degree) :
    Fin (2 ^ degree) ≃ GaloisField 2 degree :=
  Equiv.ofBijective (indexedFieldElement degree hdegree)
    (indexedFieldElement_bijective degree hdegree)

/-- GapCVP reduction support. -/
def effectiveAnchor (degree : ℕ) (hdegree : 0 < degree)
    {count : ℕ} (hcount : count ≤ 2 ^ degree) :
    Fin count ↪ GaloisField 2 degree where
  toFun index := indexedFieldElement degree hdegree
    (boundedWordIndex hcount index)
  inj' := (indexedFieldElement_injective degree hdegree).comp
    (boundedWordIndex hcount).injective

/-- GapCVP reduction support. -/
def effectiveEvaluationEmbedding (degree : ℕ) (hdegree : 0 < degree)
    {count : ℕ} (hcount : count ≤ 2 ^ degree) :
    Fin (2 ^ degree - count) ↪ GaloisField 2 degree where
  toFun index := indexedFieldElement degree hdegree
    (evaluationWordIndex hcount index)
  inj' := (indexedFieldElement_injective degree hdegree).comp
    (evaluationWordIndex hcount).injective

theorem effectiveEvaluationEmbedding_ne_anchor
    (degree : ℕ) (hdegree : 0 < degree)
    {count : ℕ} (hcount : count ≤ 2 ^ degree)
    (point : Fin (2 ^ degree - count))
    (anchor : Fin count) :
    effectiveEvaluationEmbedding degree hdegree hcount point ≠
      effectiveAnchor degree hdegree hcount anchor := by
  intro hequal
  have hindex :=
    indexedFieldElement_injective degree hdegree hequal
  have hvalue := congrArg Fin.val hindex
  change count + point.val = anchor.val at hvalue
  have hanchor := anchor.isLt
  omega

end BinaryFieldBasis

namespace Core

section

open Matrix

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]
variable {e m n : ℕ}

/-- GapCVP reduction support. -/
def binaryFieldVectorEquiv
    (basis : Module.Basis (Fin e) (ZMod 2) K) (dimension : ℕ) :
    (Fin dimension → K) ≃ₗ[ZMod 2]
      ((Fin dimension × Fin e) → ZMod 2) :=
  (LinearEquiv.piCongrRight fun _ : Fin dimension => basis.equivFun).trans
    (LinearEquiv.curry (ZMod 2) (ZMod 2) (Fin dimension) (Fin e)).symm

/-- GapCVP reduction support. -/
def binaryFieldBitEmbedding (dimension : ℕ) :
    (Fin dimension → ZMod 2) →ₗ[ZMod 2] (Fin dimension → K) :=
  LinearMap.pi fun i =>
    (Algebra.linearMap (ZMod 2) K).comp (LinearMap.proj i)

/-- GapCVP reduction support. -/
def binaryFieldParityLinearMap
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (checks : Matrix (Fin m) (Fin n) K) :
    (Fin n → ZMod 2) →ₗ[ZMod 2]
      ((Fin m × Fin e) → ZMod 2) :=
  (binaryFieldVectorEquiv basis m).toLinearMap.comp
    ((checks.mulVecLin.restrictScalars (ZMod 2)).comp
      (binaryFieldBitEmbedding n))

/-- GapCVP reduction support. -/
def binaryFieldParityMatrix
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (checks : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin m × Fin e) (Fin n) (ZMod 2) :=
  LinearMap.toMatrix' (binaryFieldParityLinearMap basis checks)

private def binaryFieldRightHandSide
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (target : Fin m → K) : (Fin m × Fin e) → ZMod 2 :=
  binaryFieldVectorEquiv basis m target

private theorem binaryFieldParityMatrix_mulVec
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (checks : Matrix (Fin m) (Fin n) K)
    (bits : Fin n → ZMod 2) :
    (binaryFieldParityMatrix basis checks).mulVec bits =
      binaryFieldVectorEquiv basis m
        (checks.mulVec
          (fun position => algebraMap (ZMod 2) K (bits position))) := by
  rw [binaryFieldParityMatrix, LinearMap.toMatrix'_mulVec]
  rfl

private theorem binaryFieldParityMatrix_mulVec_eq_iff
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (checks : Matrix (Fin m) (Fin n) K)
    (bits : Fin n → ZMod 2) (target : Fin m → K) :
    (binaryFieldParityMatrix basis checks).mulVec bits =
        binaryFieldRightHandSide basis target ↔
      checks.mulVec
          (fun position => algebraMap (ZMod 2) K (bits position)) =
        target := by
  rw [binaryFieldParityMatrix_mulVec]
  change binaryFieldVectorEquiv basis m _ =
    binaryFieldVectorEquiv basis m target ↔ _
  constructor
  · intro h
    exact (binaryFieldVectorEquiv basis m).injective h
  · intro h
    rw [h]

end

section

/-- GapCVP reduction support. -/
def binaryResidue {n : ℕ} (z : Fin n → ℤ) : Fin n → ZMod 2 :=
  fun i => (z i : ZMod 2)

theorem binaryResidue_sub {n : ℕ} (x y : Fin n → ℤ) :
    binaryResidue (x - y) = binaryResidue x - binaryResidue y := by
  ext i
  simp only [binaryResidue, Pi.sub_apply, Int.cast_sub]

/-- GapCVP reduction support. -/
structure BinaryAffineSystem where
  /-- GapCVP reduction support. -/
  rowCount : ℕ
  /-- GapCVP reduction support. -/
  dimension : ℕ
  /-- GapCVP reduction support. -/
  check : Matrix (Fin rowCount) (Fin dimension) (ZMod 2)
  /-- GapCVP reduction support. -/
  rightHandSide : Fin rowCount → ZMod 2

/-- GapCVP reduction support. -/
noncomputable def BinaryAffineSystem.Solves (system : BinaryAffineSystem)
    (z : Fin system.dimension → ℤ) : Bool :=
  @decide (
  system.check.mulVec (binaryResidue z) = system.rightHandSide
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def BinaryAffineSystem.InLattice (system : BinaryAffineSystem)
    (z : Fin system.dimension → ℤ) : Bool :=
  @decide (
  system.check.mulVec (binaryResidue z) = 0
  ) (Classical.propDecidable _)
theorem BinaryAffineSystem.solves_sub_iff_inLattice
    (system : BinaryAffineSystem) {u : Fin system.dimension → ℤ}
    (hu : system.Solves u) (z : Fin system.dimension → ℤ) :
    system.Solves (u - z) ↔ system.InLattice z := by
  simp only [BinaryAffineSystem.Solves, BinaryAffineSystem.InLattice,
    decide_eq_true_eq] at hu ⊢
  rw [binaryResidue_sub, Matrix.mulVec_sub, hu]
  simp only [sub_eq_self]

open Matrix

variable {ι K : Type*} [Field K] [Algebra (ZMod 2) K]
variable {e n : ℕ}

/-- GapCVP reduction support. -/
abbrev assembledBinaryRow (rowCounts : ι → ℕ) (e : ℕ) :=
  Σ family : ι, Fin (rowCounts family) × Fin e

/-- GapCVP reduction support. -/
def assembledBinaryParityMatrix
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K) :
    Matrix (assembledBinaryRow rowCounts e) (Fin n) (ZMod 2) :=
  fun row column =>
    binaryFieldParityMatrix basis (checks row.1) row.2 column

/-- GapCVP reduction support. -/
def assembledBinaryRightHandSide
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (targets : (family : ι) → Fin (rowCounts family) → K) :
    assembledBinaryRow rowCounts e → ZMod 2 :=
  fun row => binaryFieldRightHandSide basis (targets row.1) row.2

@[simp] theorem assembledBinaryParityMatrix_mulVec_apply
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (bits : Fin n → ZMod 2)
    (row : assembledBinaryRow rowCounts e) :
    (assembledBinaryParityMatrix basis rowCounts checks).mulVec bits row =
      (binaryFieldParityMatrix basis (checks row.1)).mulVec bits row.2 := by
  rfl

theorem assembledBinaryParityMatrix_mulVec_eq_iff
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (bits : Fin n → ZMod 2)
    (targets : (family : ι) → Fin (rowCounts family) → K) :
    (assembledBinaryParityMatrix basis rowCounts checks).mulVec bits =
        assembledBinaryRightHandSide basis rowCounts targets ↔
      ∀ family : ι,
        (checks family).mulVec
            (fun position => algebraMap (ZMod 2) K (bits position)) =
          targets family := by
  constructor
  · intro h family
    apply (binaryFieldParityMatrix_mulVec_eq_iff
      basis (checks family) bits (targets family)).mp
    funext coordinate
    exact congrFun h ⟨family, coordinate⟩
  · intro h
    funext row
    obtain ⟨family, coordinate⟩ := row
    change
      (binaryFieldParityMatrix basis (checks family)).mulVec bits coordinate =
        binaryFieldRightHandSide basis (targets family) coordinate
    exact congrFun
      ((binaryFieldParityMatrix_mulVec_eq_iff
        basis (checks family) bits (targets family)).mpr (h family))
      coordinate

/-- GapCVP reduction support. -/
abbrev assembledBinaryAffineSystem [Fintype ι]
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (targets : (family : ι) → Fin (rowCounts family) → K) :
    BinaryAffineSystem where
  rowCount := Fintype.card (assembledBinaryRow rowCounts e)
  dimension := n
  check := fun row column =>
    assembledBinaryParityMatrix basis rowCounts checks
      ((Fintype.equivFin (assembledBinaryRow rowCounts e)).symm row)
      column
  rightHandSide := fun row =>
    assembledBinaryRightHandSide basis rowCounts targets
      ((Fintype.equivFin (assembledBinaryRow rowCounts e)).symm row)

@[simp] private theorem assembledBinaryAffineSystem_check_mulVec_apply
    [Fintype ι]
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (bits : Fin n → ZMod 2)
    (row : Fin (Fintype.card (assembledBinaryRow rowCounts e))) :
    (assembledBinaryAffineSystem basis rowCounts checks targets).check.mulVec
        bits row =
      (assembledBinaryParityMatrix basis rowCounts checks).mulVec bits
        ((Fintype.equivFin (assembledBinaryRow rowCounts e)).symm row) := by
  rfl

@[simp] private theorem assembledBinaryAffineSystem_rightHandSide_apply
    [Fintype ι]
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (row : Fin (Fintype.card (assembledBinaryRow rowCounts e))) :
    (assembledBinaryAffineSystem basis rowCounts checks targets).rightHandSide
        row =
      assembledBinaryRightHandSide basis rowCounts targets
        ((Fintype.equivFin (assembledBinaryRow rowCounts e)).symm row) := by
  rfl

private theorem assembledBinaryAffineSystem_check_mulVec_eq_iff
    [Fintype ι]
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (bits : Fin n → ZMod 2)
    (targets : (family : ι) → Fin (rowCounts family) → K) :
    (assembledBinaryAffineSystem basis rowCounts checks targets).check.mulVec
        bits =
      (assembledBinaryAffineSystem basis rowCounts checks targets).rightHandSide ↔
      ∀ family : ι,
        (checks family).mulVec
          (fun position => algebraMap (ZMod 2) K (bits position)) =
            targets family := by
  let rowEquiv := Fintype.equivFin (assembledBinaryRow rowCounts e)
  constructor
  · intro h
    apply (assembledBinaryParityMatrix_mulVec_eq_iff
      basis rowCounts checks bits targets).mp
    funext row
    have hrow := congrFun h (rowEquiv row)
    rw [assembledBinaryAffineSystem_check_mulVec_apply,
      assembledBinaryAffineSystem_rightHandSide_apply] at hrow
    simpa [rowEquiv] using hrow
  · intro h
    have hstack := (assembledBinaryParityMatrix_mulVec_eq_iff
      basis rowCounts checks bits targets).mpr h
    funext row
    have hrow := congrFun hstack (rowEquiv.symm row)
    rw [assembledBinaryAffineSystem_check_mulVec_apply,
      assembledBinaryAffineSystem_rightHandSide_apply]
    exact hrow

theorem assembledBinaryAffineSystem_solves_iff
    [Fintype ι]
    (basis : Module.Basis (Fin e) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) → Matrix (Fin (rowCounts family)) (Fin n) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (z : Fin n → ℤ) :
    (assembledBinaryAffineSystem basis rowCounts checks targets).Solves z ↔
      ∀ family : ι,
        (checks family).mulVec
          (fun position => algebraMap (ZMod 2) K
            (z position : ZMod 2)) = targets family := by
  simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq]
  exact assembledBinaryAffineSystem_check_mulVec_eq_iff
    basis rowCounts checks (binaryResidue z) targets

end

section

theorem source_moment_degree_le {N d : ℕ}
    (hd : d ≤ N) : d * N ^ 30 ≤ N ^ 31 := by
  calc
    d * N ^ 30 ≤ N * N ^ 30 := Nat.mul_le_mul_right _ hd
    _ = N ^ 31 :=
      (mul_comm N (N ^ 30)).trans (pow_succ N 30).symm

private theorem source_moment_degree_lt_punctured_grid {N q m : ℕ}
    (hN : 100 ≤ N) (hq : N ^ 200 ≤ q) (hm : m ≤ N) :
    N ^ 31 < q - m := by
  have hbase : 1 < N := by omega
  have hNpow : N ≤ N ^ 31 := by
    calc
      N = N ^ 1 := by simp only [pow_one]
      _ ≤ N ^ 31 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hdouble : N ^ 31 + N ^ 31 ≤ N * N ^ 31 := by
    have h := Nat.mul_le_mul_right (N ^ 31) (show 2 ≤ N by omega)
    simpa only [ge_iff_le, two_mul] using h
  have hsum : N ^ 31 + N ≤ N ^ 32 := by
    calc
      N ^ 31 + N ≤ N ^ 31 + N ^ 31 := Nat.add_le_add_left hNpow _
      _ ≤ N * N ^ 31 := hdouble
      _ = N ^ 32 :=
        (mul_comm N (N ^ 31)).trans (pow_succ N 31).symm
  have hpow : N ^ 32 < N ^ 200 :=
    Nat.pow_lt_pow_right hbase (by norm_num)
  have htotal : N ^ 31 + m < q := by
    have hsmall : N ^ 31 + m ≤ N ^ 31 + N := Nat.add_le_add_left hm _
    exact (hsmall.trans hsum).trans_lt (hpow.trans_le hq)
  omega

/-- GapCVP reduction support. -/
def sourcePuncturedGrid {k : Type*} [Fintype k] [DecidableEq k]
    (variablePlaces : Finset k) : Finset k :=
  Finset.univ \ variablePlaces

private theorem sourcePuncturedGrid_card {k : Type*}
    [Fintype k] [DecidableEq k] (variablePlaces : Finset k) :
    (sourcePuncturedGrid variablePlaces).card =
      Fintype.card k - variablePlaces.card := by
  unfold sourcePuncturedGrid
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ]

theorem source_moment_degree_lt_actual_grid
    {k : Type*} [Fintype k] [DecidableEq k]
    {N : ℕ} (variablePlaces : Finset k)
    (hN : 100 ≤ N)
    (hq : N ^ 200 ≤ Fintype.card k)
    (hplaces : variablePlaces.card ≤ N) :
    N ^ 31 < (sourcePuncturedGrid variablePlaces).card := by
  rw [sourcePuncturedGrid_card]
  exact source_moment_degree_lt_punctured_grid hN hq hplaces

theorem source_cleared_moment_degree_lt_half_field_size {N q : ℕ}
    (hN : 100 ≤ N) (hq : N ^ 200 ≤ q) :
    2 * N ^ 39 < q / 2 := by
  have hpositive : 1 ≤ N ^ 39 := by
    have hpos : 0 < N ^ 39 := pow_pos (by omega) _
    omega
  have hscale : 6 * N ^ 39 ≤ N * N ^ 39 :=
    Nat.mul_le_mul_right (N ^ 39) (show 6 ≤ N by omega)
  have hneeded : (2 * N ^ 39 + 1) * 2 ≤ q := by
    calc
      (2 * N ^ 39 + 1) * 2 ≤ 6 * N ^ 39 := by omega
      _ ≤ N * N ^ 39 := hscale
      _ = N ^ 40 :=
        (mul_comm N (N ^ 39)).trans (pow_succ N 39).symm
      _ ≤ N ^ 200 :=
        Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ q := hq
  have hhalf : 2 * N ^ 39 + 1 ≤ q / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr hneeded
  omega

theorem source_clause_support_lt_moment_budget {N : ℕ}
    (hN : 100 ≤ N) : 9 * N ^ 4 < N ^ 30 := by
  calc
    9 * N ^ 4 ≤ N * N ^ 4 :=
      Nat.mul_le_mul_right (N ^ 4) (by omega)
    _ = N ^ 5 := (mul_comm N (N ^ 4)).trans (pow_succ N 4).symm
    _ < N ^ 30 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem source_valuation_moment_degree_lt_budget {N : ℕ}
    (hN : 100 ≤ N) : 5 * N ^ 21 < N ^ 30 := by
  calc
    5 * N ^ 21 ≤ N * N ^ 21 :=
      Nat.mul_le_mul_right (N ^ 21) (by omega)
    _ = N ^ 22 := (mul_comm N (N ^ 21)).trans (pow_succ N 21).symm
    _ < N ^ 30 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem source_valuation_index_le {N h U : ℕ}
    (hN : 100 ≤ N) (hh : h ≤ N ^ 4) (hU : U ≤ 4 * N ^ 17) :
    h * U + h ≤ 5 * N ^ 21 := by
  have hproduct : N ^ 4 * (4 * N ^ 17) = 4 * N ^ 21 := by
    rw [show (21 : ℕ) = 4 + 17 by norm_num, pow_add]
    ring
  have hpower : N ^ 4 ≤ N ^ 21 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  calc
    h * U + h ≤ N ^ 4 * (4 * N ^ 17) + N ^ 4 := by
      gcongr
    _ = 4 * N ^ 21 + N ^ 4 := by rw [hproduct]
    _ ≤ 5 * N ^ 21 := by omega

theorem source_valuation_index_lt_moment_budget {N h U : ℕ}
    (hN : 100 ≤ N) (hh : h ≤ N ^ 4) (hU : U ≤ 4 * N ^ 17) :
    h * U + h < N ^ 30 := by
  exact (source_valuation_index_le hN hh hU).trans_lt
    (source_valuation_moment_degree_lt_budget hN)

theorem source_cleared_moment_degree_le {N d h j : ℕ}
    (hd : d ≤ N) (hh : h ≤ N ^ 4) (hj : j ≤ N ^ 30) :
    2 * d * h ^ 2 * j ≤ 2 * N ^ 39 := by
  calc
    2 * d * h ^ 2 * j ≤ 2 * N * (N ^ 4) ^ 2 * N ^ 30 := by
      gcongr
    _ = 2 * N ^ (1 + 4 * 2 + 30) := by
      rw [pow_add, pow_add, pow_one, pow_mul]
      ring
    _ = 2 * N ^ 39 := by norm_num

private theorem source_output_dimension_le {N ell theta p q : ℕ}
    (hN : 100 ≤ N)
    (hell : ell ≤ N)
    (htheta : theta ≤ 1 + 8 * ell)
    (hp : p ≤ q)
    (hq : q < 2 * N ^ 200) :
    theta * p * q ≤ 40 * N ^ 401 := by
  have hthetaNine : theta ≤ 9 * N := by omega
  have hqTwo : q ≤ 2 * N ^ 200 := Nat.le_of_lt hq
  have hpTwo : p ≤ 2 * N ^ 200 := hp.trans hqTwo
  calc
    theta * p * q ≤
        (9 * N) * (2 * N ^ 200) * (2 * N ^ 200) := by
      gcongr
    _ = 36 * N ^ 401 := by
      rw [show (401 : ℕ) = 1 + 200 + 200 by norm_num,
        pow_add, pow_add, pow_one]
      ring
    _ ≤ 40 * N ^ 401 := Nat.mul_le_mul_right _ (by norm_num)

/-- GapCVP reduction support. -/
@[irreducible] def sourceFieldExponent (N : ℕ) : ℕ :=
  Nat.clog 2 (N ^ 200)

theorem sourceFieldExponent_eq (N : ℕ) :
    sourceFieldExponent N = Nat.clog 2 (N ^ 200) := by
  rw [sourceFieldExponent]

/-- GapCVP reduction support. -/
abbrev SourceFiniteField (N : ℕ) :=
  GaloisField 2 (sourceFieldExponent N)

noncomputable instance sourceFiniteFieldFintype (N : ℕ) :
    Fintype (SourceFiniteField N) :=
  Fintype.ofFinite (SourceFiniteField N)

theorem sourceFieldExponent_pos {N : ℕ} (hN : 100 ≤ N) :
    0 < sourceFieldExponent N := by
  unfold sourceFieldExponent
  apply Nat.clog_pos (by norm_num)
  simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.one_lt_pow_iff, pow_zero] using
      (Nat.pow_lt_pow_right (show 1 < N by omega) (show (0 : ℕ) < 200 by norm_num))

theorem sourceFiniteField_card {N : ℕ} (hN : 100 ≤ N) :
    Fintype.card (SourceFiniteField N) =
      2 ^ sourceFieldExponent N := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 (sourceFieldExponent N)
    (Nat.ne_of_gt (sourceFieldExponent_pos hN))

theorem sourceFiniteField_card_lower {N : ℕ} (hN : 100 ≤ N) :
    N ^ 200 ≤ Fintype.card (SourceFiniteField N) := by
  rw [sourceFiniteField_card hN, sourceFieldExponent_eq]
  exact Nat.le_pow_clog (by norm_num) (N ^ 200)

theorem sourceFiniteField_card_upper {N : ℕ} (hN : 100 ≤ N) :
    Fintype.card (SourceFiniteField N) < 2 * N ^ 200 := by
  rw [sourceFiniteField_card hN]
  have hpow : 1 < N ^ 200 := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.one_lt_pow_iff, pow_zero] using
        (Nat.pow_lt_pow_right (show 1 < N by omega) (show (0 : ℕ) < 200 by norm_num))
  have hpred :
      2 ^ (sourceFieldExponent N).pred < N ^ 200 := by
    rw [sourceFieldExponent_eq]
    exact Nat.pow_pred_clog_lt_self (by norm_num) hpow
  have hexp : (sourceFieldExponent N).pred + 1 =
      sourceFieldExponent N :=
    Nat.succ_pred_eq_of_pos (sourceFieldExponent_pos hN)
  calc
    2 ^ sourceFieldExponent N =
        2 ^ ((sourceFieldExponent N).pred + 1) := by rw [hexp]
    _ = 2 * 2 ^ (sourceFieldExponent N).pred := by
      rw [pow_succ]
      ac_rfl
    _ < 2 * N ^ 200 := Nat.mul_lt_mul_of_pos_left hpred (by norm_num)

open Matrix Finset

private theorem hankel_eq_vandermonde_transpose_mul {R : Type*} [CommRing R]
    {n : ℕ} (v : Fin n → R) :
    (Matrix.of fun i j : Fin n => ∑ k : Fin n, v k ^ (i.val + j.val)) =
      (Matrix.vandermonde v)ᵀ * Matrix.vandermonde v := by
  ext i j
  simpa only [of_apply] using (Matrix.vandermonde_transpose_mul_vandermonde v i j).symm

theorem hankel_det_eq_vandermonde_det_sq {R : Type*} [CommRing R]
    {n : ℕ} (v : Fin n → R) :
    (Matrix.of fun i j : Fin n => ∑ k : Fin n, v k ^ (i.val + j.val)).det =
      (Matrix.vandermonde v).det ^ 2 := by
  rw [hankel_eq_vandermonde_transpose_mul, Matrix.det_mul,
    Matrix.det_transpose, pow_two]

theorem hankel_det_ne_zero_of_injective {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {v : Fin n → R} (hv : Function.Injective v) :
    (Matrix.of fun i j : Fin n => ∑ k : Fin n, v k ^ (i.val + j.val)).det ≠ 0 := by
  rw [hankel_det_eq_vandermonde_det_sq]
  exact pow_ne_zero 2 (Matrix.det_vandermonde_ne_zero_iff.mpr hv)

private theorem exists_nonzero_power_sum {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) {v : Fin n → K} (hv : Function.Injective v) :
    ∃ j : Fin n, (∑ i : Fin n, v i ^ j.val) ≠ 0 := by
  by_contra h
  push Not at h
  have hmul : (Matrix.vandermonde v)ᵀ.mulVec (fun _ : Fin n => (1 : K)) = 0 := by
    ext j
    simpa only [mulVec, dotProduct, transpose_apply, vandermonde_apply, mul_one, Pi.zero_apply]
        using h j
  have hdet : ((Matrix.vandermonde v)ᵀ).det ≠ 0 := by
    simpa only [det_transpose, ne_eq] using (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  have hz : (fun _ : Fin n => (1 : K)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have hone : (1 : K) = 0 := congrFun hz ⟨0, hn⟩
  exact one_ne_zero hone

end

section

open Finset Polynomial
open scoped symmDiff

theorem polynomial_eq_of_agree_on_points {K : Type*} [Field K]
    (points : Finset K) (f g : K[X])
    (hdeg : max f.natDegree g.natDegree < points.card)
    (hagree : ∀ x ∈ points, f.eval x = g.eval x) : f = g := by
  exact Polynomial.eq_of_natDegree_lt_card_of_eval_eq' f g points hagree hdeg

private theorem exists_assignment_interpolant {K : Type*} [Field K] {m : ℕ}
    (variablePoint : Fin m → K)
    (hinj : Function.Injective variablePoint)
    (assignment : Fin m → K) :
    ∃ polynomial : K[X],
      polynomial.degree < (m : WithBot ℕ) ∧
      ∀ i : Fin m, polynomial.eval (variablePoint i) = assignment i := by
  classical
  let points : Finset (Fin m) := Finset.univ
  let polynomial : K[X] :=
    Lagrange.interpolate points variablePoint assignment
  refine ⟨polynomial, ?_, ?_⟩
  · simpa [points, polynomial] using
      (Lagrange.degree_interpolate_lt assignment
        (s := points) hinj.injOn)
  · intro i
    simpa [points, polynomial] using
      (Lagrange.eval_interpolate_at_node assignment
        (s := points) hinj.injOn (Finset.mem_univ i))

/-- GapCVP reduction support. -/
noncomputable def supportMoment {K : Type*} [Field K]
    (support : Finset K) (j : ℕ) : K :=
  ∑ a ∈ support, a ^ j

private theorem exists_nonzero_supportMoment {K : Type*} [Field K]
    (support : Finset K) (hsupport : support.Nonempty) :
    ∃ j : ℕ, j < support.card ∧ supportMoment support j ≠ 0 := by
  classical
  let e := Finset.equivFin support
  let v : Fin support.card → K := fun i => (e.symm i : K)
  have hinj : Function.Injective v := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  obtain ⟨j, hj⟩ := exists_nonzero_power_sum
    (Finset.card_pos.mpr hsupport) hinj
  refine ⟨j.val, j.isLt, ?_⟩
  intro hzero
  apply hj
  calc
    (∑ i : Fin support.card, v i ^ j.val) =
        ∑ a : support, (a : K) ^ j.val := by
      exact Equiv.sum_comp e.symm (fun a : support => (a : K) ^ j.val)
    _ = supportMoment support j.val := by
      exact (Finset.sum_subtype support (fun _ => Iff.rfl)
        (fun a : K => a ^ j.val)).symm
    _ = 0 := hzero

private theorem support_eq_empty_of_low_moments_eq_zero {K : Type*} [Field K]
    (support : Finset K)
    (hmoments : ∀ j : ℕ, j < support.card → supportMoment support j = 0) :
    support = ∅ := by
  classical
  by_contra hnonempty
  obtain ⟨j, hj, hne⟩ := exists_nonzero_supportMoment support
    (Finset.nonempty_iff_ne_empty.mpr hnonempty)
  exact hne (hmoments j hj)

private theorem supportMoment_symmDiff {K : Type*} [Field K] [CharP K 2]
    [DecidableEq K]
    (s t : Finset K) (j : ℕ) :
    supportMoment (s ∆ t) j = supportMoment s j + supportMoment t j := by
  classical
  have hdisjoint : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hs :
      (∑ a ∈ s ∩ t, a ^ j) + (∑ a ∈ s \ t, a ^ j) =
        ∑ a ∈ s, a ^ j :=
    Finset.sum_inter_add_sum_sdiff s t (fun a : K => a ^ j)
  have ht :
      (∑ a ∈ s ∩ t, a ^ j) + (∑ a ∈ t \ s, a ^ j) =
        ∑ a ∈ t, a ^ j := by
    simpa only [inter_comm] using (Finset.sum_inter_add_sum_sdiff t s (fun a : K => a ^ j))
  rw [supportMoment, Finset.symmDiff_def, Finset.sum_union hdisjoint]
  calc
    (∑ a ∈ s \ t, a ^ j) + (∑ a ∈ t \ s, a ^ j) =
        ((∑ a ∈ s ∩ t, a ^ j) + (∑ a ∈ s ∩ t, a ^ j)) +
          ((∑ a ∈ s \ t, a ^ j) + (∑ a ∈ t \ s, a ^ j)) := by
            rw [CharTwo.add_self_eq_zero, zero_add]
    _ = ((∑ a ∈ s ∩ t, a ^ j) + (∑ a ∈ s \ t, a ^ j)) +
          ((∑ a ∈ s ∩ t, a ^ j) + (∑ a ∈ t \ s, a ^ j)) := by
            ac_rfl
    _ = (∑ a ∈ s, a ^ j) + (∑ a ∈ t, a ^ j) := by
          rw [hs, ht]

private theorem support_eq_of_low_supportMoments_eq
    {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
    (s t : Finset K)
    (hmoments : ∀ j : ℕ, j < (s ∆ t).card →
      supportMoment s j = supportMoment t j) : s = t := by
  apply Finset.symmDiff_eq_empty.mp
  apply support_eq_empty_of_low_moments_eq_zero
  intro j hj
  rw [supportMoment_symmDiff, hmoments j hj,
    CharTwo.add_self_eq_zero]

private theorem support_eq_of_supportMoments_eq_below_card_sum
    {K : Type*} [Field K] [CharP K 2]
    (s t : Finset K)
    (hmoments : ∀ j : ℕ, j < s.card + t.card →
      supportMoment s j = supportMoment t j) : s = t := by
  classical
  apply support_eq_of_low_supportMoments_eq s t
  intro j hj
  apply hmoments j
  exact lt_of_lt_of_le hj
    ((Finset.card_le_card (Finset.symmDiff_subset_union (s := s) (t := t))).trans
      (Finset.card_union_le s t))

/-- GapCVP reduction support. -/
def paritySupport {K : Type*} [DecidableEq K] :
    List (Finset K) → Finset K
  | [] => ∅
  | s :: supports => s ∆ paritySupport supports

private theorem supportMoment_paritySupport
    {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
    (supports : List (Finset K)) (j : ℕ) :
    supportMoment (paritySupport supports) j =
      (supports.map (fun s => supportMoment s j)).sum := by
  induction supports with
  | nil => simp only [supportMoment, paritySupport, sum_empty, List.map_nil, List.sum_nil]
  | cons s supports ih =>
      simp only [paritySupport, supportMoment_symmDiff, ih, List.map_cons, List.sum_cons]

private theorem exists_mem_of_mem_paritySupport
    {K : Type*} [DecidableEq K]
    (supports : List (Finset K)) {a : K}
    (ha : a ∈ paritySupport supports) :
    ∃ s ∈ supports, a ∈ s := by
  induction supports generalizing a with
  | nil => simp only [paritySupport, notMem_empty] at ha
  | cons s supports ih =>
      have hcases :
          a ∈ s ∧ a ∉ paritySupport supports ∨
          a ∈ paritySupport supports ∧ a ∉ s := by
        apply Finset.mem_symmDiff.mp
        simpa only [paritySupport] using ha
      rcases hcases with ⟨has, _⟩ | ⟨haparity, _⟩
      · exact ⟨s, by simp only [List.mem_cons, true_or], has⟩
      · obtain ⟨t, ht, hat⟩ := ih haparity
        exact ⟨t, by simp only [List.mem_cons, ht, or_true], hat⟩

private theorem global_support_eq_paritySupport_of_moment_refinement
    {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
    (global : Finset K) (subtypes : List (Finset K))
    (hmoments : ∀ j : ℕ,
      j < global.card + (paritySupport subtypes).card →
      supportMoment global j =
        (subtypes.map (fun s => supportMoment s j)).sum) :
    global = paritySupport subtypes := by
  apply support_eq_of_supportMoments_eq_below_card_sum
  intro j hj
  calc
    supportMoment global j =
        (subtypes.map (fun s => supportMoment s j)).sum := hmoments j hj
    _ = supportMoment (paritySupport subtypes) j :=
      (supportMoment_paritySupport subtypes j).symm

theorem global_root_mem_subtype_of_moment_refinement
    {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
    (global : Finset K) (subtypes : List (Finset K))
    (hmoments : ∀ j : ℕ,
      j < global.card + (paritySupport subtypes).card →
      supportMoment global j =
        (subtypes.map (fun s => supportMoment s j)).sum)
    {a : K} (ha : a ∈ global) :
    ∃ s ∈ subtypes, a ∈ s := by
  apply exists_mem_of_mem_paritySupport subtypes
  rw [← global_support_eq_paritySupport_of_moment_refinement
    global subtypes hmoments]
  exact ha

private theorem shifted_supportMoment_binomial {K : Type*} [Field K]
    (support : Finset K) (β : K) (j : ℕ) :
    (∑ w ∈ support, (w - β) ^ j) =
      ∑ l ∈ Finset.range (j + 1),
        (j.choose l : K) * (-β) ^ (j - l) * supportMoment support l := by
  classical
  simp_rw [sub_eq_add_neg, add_pow, supportMoment]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem scaled_shifted_supportMoment {K : Type*} [Field K]
    (support : Finset K) (β π : K) (j : ℕ) (hπ : π ≠ 0) :
    π ^ j * (∑ w ∈ support, ((w - β) / π) ^ j) =
      ∑ l ∈ Finset.range (j + 1),
        (j.choose l : K) * (-β) ^ (j - l) * supportMoment support l := by
  classical
  calc
    π ^ j * (∑ w ∈ support, ((w - β) / π) ^ j) =
        ∑ w ∈ support, (w - β) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [div_pow]
      exact mul_div_cancel₀ ((w - β) ^ j) (pow_ne_zero j hπ)
    _ = _ := shifted_supportMoment_binomial support β j

/-- GapCVP reduction support. -/
noncomputable def shiftedMomentCombination {K : Type*} [Field K]
    (moments : ℕ → K[X]) (β : K) (j : ℕ) : K[X] :=
  ∑ l ∈ Finset.range (j + 1),
    Polynomial.C ((j.choose l : K) * (-β) ^ (j - l)) * moments l

end

section

/-- GapCVP reduction support. -/
def sourceSizeParameter (encodingLength : ℕ) (formula : Formula) : ℕ :=
  100 + encodingLength + formula.variableCount + formula.clauses.length

theorem sourceSizeParameter_ge_one_hundred
    (encodingLength : ℕ) (formula : Formula) :
    100 ≤ sourceSizeParameter encodingLength formula := by
  simp only [sourceSizeParameter]
  omega

theorem source_variableCount_le_size
    (encodingLength : ℕ) (formula : Formula) :
    formula.variableCount ≤ sourceSizeParameter encodingLength formula := by
  simp only [sourceSizeParameter]
  omega

theorem source_clauseCount_le_size
    (encodingLength : ℕ) (formula : Formula) :
    formula.clauses.length ≤ sourceSizeParameter encodingLength formula := by
  simp only [sourceSizeParameter]
  omega

open scoped BigOperators
open Finset Matrix Polynomial

/-- GapCVP reduction support. -/
def Clause.variableSet {m : ℕ} (C : Clause m) : Finset (Fin m) :=
  C.literals.image (fun literal => literal.variableIndex)

theorem Clause.variableSet_card_le_three {m : ℕ} (C : Clause m) :
    C.variableSet.card ≤ 3 :=
  (Finset.card_image_le).trans C.size_le_three

/-- GapCVP reduction support. -/
abbrev Clause.LocalVariable {m : ℕ} (C : Clause m) :=
  {i : Fin m // i ∈ C.variableSet}

/-- GapCVP reduction support. -/
abbrev Clause.LocalAssignment {m : ℕ} (C : Clause m) :=
  C.LocalVariable → Bool

/-- GapCVP reduction support. -/
noncomputable def Clause.LocalSatisfied {m : ℕ} (C : Clause m)
    (assignment : C.LocalAssignment) : Bool :=
  @decide (
  ∃ (literal : Literal m) (hliteral : literal ∈ C.literals),
    assignment
      ⟨literal.variableIndex,
        Finset.mem_image_of_mem (fun l : Literal m => l.variableIndex)
          hliteral⟩ = literal.satisfyingValue
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
abbrev Clause.SatisfyingLocalTuple {m : ℕ} (C : Clause m) :=
  {assignment : C.LocalAssignment // C.LocalSatisfied assignment}

noncomputable instance Clause.instFintypeSatisfyingLocalTuple
    {m : ℕ} (C : Clause m) : Fintype C.SatisfyingLocalTuple :=
  Fintype.ofFinite _

theorem Clause.satisfyingLocalTuple_card_le_eight
    {m : ℕ} (C : Clause m) :
    Fintype.card C.SatisfyingLocalTuple ≤ 8 := by
  calc
    Fintype.card C.SatisfyingLocalTuple ≤
        Fintype.card C.LocalAssignment :=
      Fintype.card_subtype_le (fun assignment => C.LocalSatisfied assignment)
    _ = 2 ^ C.variableSet.card := by
      rw [Fintype.card_fun]
      simp only [Fintype.card_bool, Fintype.card_coe]
    _ ≤ 2 ^ (3 : ℕ) :=
      Nat.pow_le_pow_right (by norm_num) C.variableSet_card_le_three
    _ = 8 := by norm_num

/-- GapCVP reduction support. -/
def Clause.restrictAssignment {m : ℕ} (C : Clause m)
    (assignment : Fin m → Bool) : C.LocalAssignment :=
  fun i => assignment i.val

theorem Clause.localSatisfied_restrict_iff {m : ℕ} (C : Clause m)
    (assignment : Fin m → Bool) :
    C.LocalSatisfied (C.restrictAssignment assignment) ↔
      C.Satisfied assignment := by
  simp only [GapCVP.Core.Clause.LocalSatisfied, GapCVP.Core.Clause.Satisfied, decide_eq_true_eq]
  constructor
  · rintro ⟨literal, hliteral, hvalue⟩
    exact ⟨literal, hliteral, hvalue⟩
  · rintro ⟨literal, hliteral, hvalue⟩
    exact ⟨literal, hliteral, hvalue⟩

/-- GapCVP reduction support. -/
def Clause.satisfyingLocalTupleOfAssignment {m : ℕ}
    (C : Clause m) (assignment : Fin m → Bool)
    (h : C.Satisfied assignment) : C.SatisfyingLocalTuple :=
  ⟨C.restrictAssignment assignment,
    (C.localSatisfied_restrict_iff assignment).mpr h⟩

/-- GapCVP reduction support. -/
abbrev sourceSATTableType (F : Formula) :=
  Unit ⊕
    (Σ C : Fin F.clauses.length,
      (F.clauses.get C).SatisfyingLocalTuple)

private theorem sourceSATTableType_card_le (F : Formula) :
    Fintype.card (sourceSATTableType F) ≤ 1 + 8 * F.clauses.length := by
  classical
  simp only [Fintype.card_sum, Fintype.card_unique,
    Fintype.card_sigma]
  have hsum :
      (∑ C : Fin F.clauses.length,
        Fintype.card (F.clauses.get C).SatisfyingLocalTuple) ≤
          ∑ _C : Fin F.clauses.length, (8 : ℕ) := by
    exact Finset.sum_le_sum
      (fun C _ => (F.clauses.get C).satisfyingLocalTuple_card_le_eight)
  simpa only [List.get_eq_getElem, add_le_add_iff_left, ge_iff_le, sum_const, card_univ,
      Fintype.card_fin,
      smul_eq_mul, Nat.mul_comm] using Nat.add_le_add_left hsum 1

/-- GapCVP reduction support. -/
abbrev sourceSATGridPoint {K : Type*} (points : Finset K) :=
  {p : K // p ∈ points}

/-- GapCVP reduction support. -/
abbrev sourceSATTableCoordinate
    (F : Formula) (K : Type*) (points : Finset K) :=
  sourceSATTableType F × sourceSATGridPoint points × K

/-- GapCVP reduction support. -/
def sourceSATTableDimension
    (F : Formula) (K : Type*) [Fintype K]
    (points : Finset K) : ℕ :=
  Fintype.card (sourceSATTableCoordinate F K points)

theorem sourceSATTableDimension_eq
    (F : Formula) (K : Type*) [Fintype K]
    (points : Finset K) :
    sourceSATTableDimension F K points =
      Fintype.card (sourceSATTableType F) * points.card * Fintype.card K := by
  classical
  simp only [sourceSATTableDimension, Fintype.card_prod, Fintype.card_sum, Fintype.card_unique,
      List.get_eq_getElem, Fintype.card_sigma, Fintype.card_coe, mul_assoc]

theorem sourceSATTableDimension_le
    (F : Formula) (K : Type*) [Fintype K]
    (points : Finset K) (N : ℕ)
    (hN : 100 ≤ N) (hclauses : F.clauses.length ≤ N)
    (hgrid : points.card ≤ Fintype.card K)
    (hfield : Fintype.card K < 2 * N ^ 200) :
    sourceSATTableDimension F K points ≤ 40 * N ^ 401 := by
  rw [sourceSATTableDimension_eq]
  exact source_output_dimension_le hN hclauses
    (sourceSATTableType_card_le F) hgrid hfield

variable {K : Type*} [Field K]

private def sourceGridEvaluationLinearMap (points : Finset K) :
    K[X] →ₗ[K] (sourceSATGridPoint points → K) :=
  LinearMap.pi fun p : sourceSATGridPoint points =>
    (Polynomial.aeval (p : K)).toLinearMap

/-- GapCVP reduction support. -/
def sourceReedSolomonCode (points : Finset K) (degreeBound : ℕ) :
    Submodule K (sourceSATGridPoint points → K) :=
  LinearMap.range
    ((sourceGridEvaluationLinearMap points).comp
      (Polynomial.degreeLE K (degreeBound : WithBot ℕ)).subtype)

theorem sourceReedSolomonCode_mem_iff
    (points : Finset K) (degreeBound : ℕ)
    (values : sourceSATGridPoint points → K) :
    values ∈ sourceReedSolomonCode points degreeBound ↔
      ∃ polynomial : K[X], polynomial.natDegree ≤ degreeBound ∧
        ∀ point : sourceSATGridPoint points,
          polynomial.eval point.val = values point := by
  constructor
  · rintro ⟨⟨polynomial, hdegree⟩, hvalues⟩
    refine ⟨polynomial, ?_, ?_⟩
    · exact Polynomial.natDegree_le_iff_degree_le.mpr
        (Polynomial.mem_degreeLE.mp hdegree)
    · intro point
      exact congrFun hvalues point
  · rintro ⟨polynomial, hdegree, hvalues⟩
    refine ⟨⟨polynomial, ?_⟩, ?_⟩
    · exact Polynomial.mem_degreeLE.mpr
        (Polynomial.natDegree_le_iff_degree_le.mp hdegree)
    · funext point
      exact hvalues point

private def sourceReedSolomonCodimension
    (points : Finset K) (degreeBound : ℕ) : ℕ :=
  Module.finrank K
    ((sourceSATGridPoint points → K) ⧸
      sourceReedSolomonCode points degreeBound)

private def sourceReedSolomonParityMap
    (points : Finset K) (degreeBound : ℕ) :
    (sourceSATGridPoint points → K) →ₗ[K]
      (Fin (sourceReedSolomonCodimension points degreeBound) → K) :=
  (Module.finBasis K
      ((sourceSATGridPoint points → K) ⧸
        sourceReedSolomonCode points degreeBound)).equivFun.toLinearMap.comp
    (sourceReedSolomonCode points degreeBound).mkQ

private theorem sourceReedSolomonParityMap_eq_zero_iff
    (points : Finset K) (degreeBound : ℕ)
    (values : sourceSATGridPoint points → K) :
    sourceReedSolomonParityMap points degreeBound values = 0 ↔
      values ∈ sourceReedSolomonCode points degreeBound := by
  change
    (Module.finBasis K
      ((sourceSATGridPoint points → K) ⧸
        sourceReedSolomonCode points degreeBound)).equivFun
        ((sourceReedSolomonCode points degreeBound).mkQ values) = 0 ↔
      values ∈ sourceReedSolomonCode points degreeBound
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- GapCVP reduction support. -/
def sourceFiniteReindexLinearEquiv
    (α : Type*) [Fintype α] :
    (α → K) ≃ₗ[K] (Fin (Fintype.card α) → K) :=
  LinearEquiv.funCongrLeft K K (Fintype.equivFin α).symm

/-- GapCVP reduction support. -/
def sourceSATColumnIndex
    (F : Formula) [Fintype K] (points : Finset K)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points) (value : K) :
    Fin (sourceSATTableDimension F K points) :=
  Fintype.equivFin (sourceSATTableCoordinate F K points)
    (tableType, point, value)

/-- GapCVP reduction support. -/
def sourceGlobalNormalizationMap
    (F : Formula) [Fintype K] (points : Finset K) :
    (Fin (sourceSATTableDimension F K points) → K) →ₗ[K]
      (sourceSATGridPoint points → K) where
  toFun table point :=
    ∑ value : K,
      table (sourceSATColumnIndex F points (.inl ()) point value)
  map_add' left right := by
    funext point
    simp only [List.get_eq_getElem, Pi.add_apply, sum_add_distrib]
  map_smul' scalar table := by
    funext point
    simp only [List.get_eq_getElem, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]

/-- GapCVP reduction support. -/
def sourceClauseRefinementMap
    (F : Formula) [Fintype K] (points : Finset K)
    (clause : Fin F.clauses.length) :
    (Fin (sourceSATTableDimension F K points) → K) →ₗ[K]
      (sourceSATGridPoint points × K → K) where
  toFun table position :=
    table (sourceSATColumnIndex F points (.inl ())
      position.1 position.2) -
      ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
        table (sourceSATColumnIndex F points
          (.inr ⟨clause, tuple⟩) position.1 position.2)
  map_add' left right := by
    funext position
    simp only [List.get_eq_getElem, Pi.add_apply, sum_add_distrib]
    ring
  map_smul' scalar table := by
    funext position
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, RingHom.id_apply]
    rw [Finset.mul_sum]

/-- GapCVP reduction support. -/
def sourceOrdinaryMomentMap
    (F : Formula) [Fintype K] (points : Finset K)
    (tableType : sourceSATTableType F) (j : ℕ) :
    (Fin (sourceSATTableDimension F K points) → K) →ₗ[K]
      (sourceSATGridPoint points → K) where
  toFun table point :=
    ∑ value : K,
      table (sourceSATColumnIndex F points tableType point value) *
        value ^ j
  map_add' left right := by
    funext point
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' scalar table := by
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, mul_sum]

/-- GapCVP reduction support. -/
def sourceSATFieldBit (bit : Bool) : K :=
  if bit then 1 else 0

/-- GapCVP reduction support. -/
def sourceShiftedMomentMap
    (F : Formula) [Fintype K] (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) :
    (Fin (sourceSATTableDimension F K points) → K) →ₗ[K]
      (sourceSATGridPoint points → K) where
  toFun table point :=
    ∑ value : K,
      table (sourceSATColumnIndex F points
        (.inr ⟨clause, tuple⟩) point value) *
          ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
            (point.val - variablePlace localVar.val)) ^ j
  map_add' left right := by
    funext point
    simp only [List.get_eq_getElem, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' scalar table := by
    funext point
    simp only [List.get_eq_getElem, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply,
        mul_sum]

/-- GapCVP reduction support. -/
abbrev sourceSATConstraintFamily (F : Formula) (momentBudget : ℕ) :=
  Unit ⊕
    (Fin F.clauses.length ⊕
      ((sourceSATTableType F × Fin (momentBudget + 1)) ⊕
        (Σ clause : Fin F.clauses.length,
          Σ _tuple : (F.clauses.get clause).SatisfyingLocalTuple,
            (F.clauses.get clause).LocalVariable ×
              Fin (momentBudget + 1))))

private def sourceSATFamilyRowCount
    (F : Formula) [Fintype K]
    (points : Finset K) (momentBudget : ℕ)
    (family : sourceSATConstraintFamily F momentBudget) : ℕ :=
  match family with
  | .inl _ => Fintype.card (sourceSATGridPoint points)
  | .inr (.inl _) =>
      Fintype.card (sourceSATGridPoint points × K)
  | .inr (.inr (.inl ⟨_, j⟩)) =>
      sourceReedSolomonCodimension points
        (F.variableCount * j.val)
  | .inr (.inr (.inr ⟨_, _, _, j⟩)) =>
      sourceReedSolomonCodimension points
        ((F.variableCount - 1) * j.val)

private def sourceSATFamilyLinearMap
    (F : Formula) [Fintype K]
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (family : sourceSATConstraintFamily F momentBudget) :
    (Fin (sourceSATTableDimension F K points) → K) →ₗ[K]
      (Fin (sourceSATFamilyRowCount F points momentBudget family) → K) := by
  classical
  rcases family with _ | family
  · exact
      (sourceFiniteReindexLinearEquiv
        (K := K) (sourceSATGridPoint points)).toLinearMap.comp
        (sourceGlobalNormalizationMap F points)
  · rcases family with clause | family
    · exact
        (sourceFiniteReindexLinearEquiv
          (K := K) (sourceSATGridPoint points × K)).toLinearMap.comp
          (sourceClauseRefinementMap F points clause)
    · rcases family with ordinary | shifted
      · obtain ⟨tableType, j⟩ := ordinary
        exact
          (sourceReedSolomonParityMap points
            (F.variableCount * j.val)).comp
              (sourceOrdinaryMomentMap F points tableType j.val)
      · obtain ⟨clause, tuple, localVar, j⟩ := shifted
        exact
          (sourceReedSolomonParityMap points
            ((F.variableCount - 1) * j.val)).comp
              (sourceShiftedMomentMap F points variablePlace
                clause tuple localVar j.val)

private def sourceSATFamilyTarget
    (F : Formula) [Fintype K]
    (points : Finset K) (momentBudget : ℕ)
    (family : sourceSATConstraintFamily F momentBudget) :
    Fin (sourceSATFamilyRowCount F points momentBudget family) → K :=
  fun _ => match family with
    | .inl _ => 1
    | .inr _ => 0

private def sourceSATFamilyFieldMatrix
    (F : Formula) [Fintype K]
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (family : sourceSATConstraintFamily F momentBudget) :
    Matrix
      (Fin (sourceSATFamilyRowCount F points momentBudget family))
      (Fin (sourceSATTableDimension F K points)) K :=
  LinearMap.toMatrix'
    (sourceSATFamilyLinearMap F points variablePlace momentBudget family)

/-- GapCVP reduction support. -/
def concreteSATBinaryAffineSystem
    [Algebra (ZMod 2) K] [Fintype K]
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ) : BinaryAffineSystem :=
  assembledBinaryAffineSystem fieldBasis
    (sourceSATFamilyRowCount F points momentBudget)
    (sourceSATFamilyFieldMatrix F points variablePlace momentBudget)
    (sourceSATFamilyTarget F points momentBudget)

private theorem concreteSATBinaryAffineSystem_solves_iff_family
    [Algebra (ZMod 2) K] [Fintype K]
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ) :
    (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z ↔
        ∀ family : sourceSATConstraintFamily F momentBudget,
          sourceSATFamilyLinearMap F points variablePlace
              momentBudget family
            (fun position =>
              algebraMap (ZMod 2) K (z position : ZMod 2)) =
              sourceSATFamilyTarget F points momentBudget family := by
  unfold concreteSATBinaryAffineSystem
  rw [assembledBinaryAffineSystem_solves_iff]
  simp only [sourceSATFamilyFieldMatrix, LinearMap.toMatrix'_mulVec]

/-- GapCVP reduction support. -/
noncomputable def concreteSATFieldChecks
    (F : Formula) [Fintype K]
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (values : Fin (sourceSATTableDimension F K points) → K) : Bool :=
  @decide (
  sourceGlobalNormalizationMap F points values =
      (fun _ : sourceSATGridPoint points => (1 : K)) ∧
    (∀ clause : Fin F.clauses.length,
      sourceClauseRefinementMap F points clause values = 0) ∧
    (∀ (tableType : sourceSATTableType F)
      (j : Fin (momentBudget + 1)),
      sourceOrdinaryMomentMap F points tableType j.val values ∈
        sourceReedSolomonCode points (F.variableCount * j.val)) ∧
    (∀ (clause : Fin F.clauses.length)
      (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
      (localVar : (F.clauses.get clause).LocalVariable)
      (j : Fin (momentBudget + 1)),
      sourceShiftedMomentMap F points variablePlace
          clause tuple localVar j.val values ∈
        sourceReedSolomonCode points
          ((F.variableCount - 1) * j.val))
  ) (Classical.propDecidable _)
private theorem sourceSATFamilyChecks_iff_concrete
    (F : Formula) [Fintype K]
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (values : Fin (sourceSATTableDimension F K points) → K) :
    (∀ family : sourceSATConstraintFamily F momentBudget,
      sourceSATFamilyLinearMap F points variablePlace
        momentBudget family values =
          sourceSATFamilyTarget F points momentBudget family) ↔
      concreteSATFieldChecks F points variablePlace momentBudget values := by
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq]
  classical
  constructor
  · intro hfamilies
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext point
      have hpoint := congrFun
        (hfamilies (.inl ()))
        (Fintype.equivFin (sourceSATGridPoint points) point)
      change
        sourceGlobalNormalizationMap F points values
          ((Fintype.equivFin (sourceSATGridPoint points)).symm
            (Fintype.equivFin (sourceSATGridPoint points) point)) = 1
        at hpoint
      simpa only [Equiv.symm_apply_apply] using hpoint
    · intro clause
      funext position
      have hposition := congrFun
        (hfamilies (.inr (.inl clause)))
        (Fintype.equivFin (sourceSATGridPoint points × K) position)
      change
        sourceClauseRefinementMap F points clause values
          ((Fintype.equivFin (sourceSATGridPoint points × K)).symm
            (Fintype.equivFin (sourceSATGridPoint points × K) position)) = 0
        at hposition
      simpa only [Pi.zero_apply, Equiv.symm_apply_apply] using hposition
    · intro tableType j
      apply (sourceReedSolomonParityMap_eq_zero_iff points
        (F.variableCount * j.val)
        (sourceOrdinaryMomentMap F points tableType j.val values)).mp
      have hmoment := hfamilies
        (.inr (.inr (.inl (tableType, j))))
      change
        sourceReedSolomonParityMap points (F.variableCount * j.val)
          (sourceOrdinaryMomentMap F points tableType j.val values) = 0
        at hmoment
      exact hmoment
    · intro clause tuple localVar j
      apply (sourceReedSolomonParityMap_eq_zero_iff points
        ((F.variableCount - 1) * j.val)
        (sourceShiftedMomentMap F points variablePlace
          clause tuple localVar j.val values)).mp
      have hmoment := hfamilies
        (.inr (.inr (.inr ⟨clause, tuple, localVar, j⟩)))
      change
        sourceReedSolomonParityMap points
          ((F.variableCount - 1) * j.val)
            (sourceShiftedMomentMap F points variablePlace
              clause tuple localVar j.val values) = 0
        at hmoment
      exact hmoment
  · rintro ⟨hnormalization, hrefinement, hordinary, hshifted⟩
    intro family
    rcases family with _ | family
    · change
        (sourceFiniteReindexLinearEquiv (K := K)
          (sourceSATGridPoint points))
            (sourceGlobalNormalizationMap F points values) =
          fun _ => (1 : K)
      rw [hnormalization]
      rfl
    · rcases family with clause | family
      · change
          (sourceFiniteReindexLinearEquiv (K := K)
            (sourceSATGridPoint points × K))
              (sourceClauseRefinementMap F points clause values) = 0
        rw [hrefinement clause]
        exact map_zero _
      · rcases family with ordinary | shifted
        · obtain ⟨tableType, j⟩ := ordinary
          change
            sourceReedSolomonParityMap points
              (F.variableCount * j.val)
                (sourceOrdinaryMomentMap F points tableType j.val values) = 0
          exact (sourceReedSolomonParityMap_eq_zero_iff points
            (F.variableCount * j.val)
            (sourceOrdinaryMomentMap F points tableType j.val values)).mpr
              (hordinary tableType j)
        · obtain ⟨clause, tuple, localVar, j⟩ := shifted
          change
            sourceReedSolomonParityMap points
              ((F.variableCount - 1) * j.val)
                (sourceShiftedMomentMap F points variablePlace
                  clause tuple localVar j.val values) = 0
          exact (sourceReedSolomonParityMap_eq_zero_iff points
            ((F.variableCount - 1) * j.val)
            (sourceShiftedMomentMap F points variablePlace
              clause tuple localVar j.val values)).mpr
                (hshifted clause tuple localVar j)

theorem concreteSATBinaryAffineSystem_solves_iff
    [Algebra (ZMod 2) K] [Fintype K]
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ) :
    (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z ↔
      concreteSATFieldChecks F points variablePlace momentBudget
        (fun position =>
          algebraMap (ZMod 2) K (z position : ZMod 2)) := by
  exact
    (concreteSATBinaryAffineSystem_solves_iff_family
      F fieldBasis points variablePlace momentBudget z).trans
      (sourceSATFamilyChecks_iff_concrete F points variablePlace
        momentBudget _)

/-- GapCVP reduction support. -/
def sourceSATPuncturedGrid
    (F : Formula) [Fintype K]
    (variablePlace : Fin F.variableCount → K) : Finset K := by
  classical
  exact sourcePuncturedGrid
    ((Finset.univ : Finset (Fin F.variableCount)).image variablePlace)

omit [Field K] in
theorem sourceSATPuncturedGrid_card
    (F : Formula) [Fintype K]
    (variablePlace : Fin F.variableCount → K)
    (hinjective : Function.Injective variablePlace) :
    (sourceSATPuncturedGrid F variablePlace).card =
      Fintype.card K - F.variableCount := by
  classical
  unfold sourceSATPuncturedGrid
  rw [sourcePuncturedGrid_card,
    Finset.card_image_of_injective _ hinjective]
  simp only [card_univ, Fintype.card_fin]

theorem sourceSATPuncturedGrid_sub_ne_zero
    (F : Formula) [Fintype K]
    (variablePlace : Fin F.variableCount → K)
    (point : sourceSATGridPoint
      (sourceSATPuncturedGrid F variablePlace))
    (i : Fin F.variableCount) :
    point.val - variablePlace i ≠ 0 := by
  classical
  have hpoint : point.val ∈
      (Finset.univ : Finset K) \
        ((Finset.univ : Finset (Fin F.variableCount)).image variablePlace) := by
    exact point.property
  have hnot := (Finset.mem_sdiff.mp hpoint).2
  apply sub_ne_zero.mpr
  intro heq
  apply hnot
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, heq.symm⟩

end

section

open scoped BigOperators

/-- GapCVP reduction support. -/
abbrev sourceFormulaField (encodingLength : ℕ) (F : Formula) :=
  SourceFiniteField (sourceSizeParameter encodingLength F)

end

section

open scoped BigOperators
open Finset Matrix Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- GapCVP reduction support. -/
def sourceActiveLocalTuple
    (F : Formula) (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (clause : Fin F.clauses.length) :
    (F.clauses.get clause).SatisfyingLocalTuple := by
  have satisfaction := hsatisfies
  simp only [GapCVP.Core.Formula.Satisfied, decide_eq_true_eq] at satisfaction
  exact (F.clauses.get clause).satisfyingLocalTupleOfAssignment
    assignment (satisfaction clause)

@[simp] private theorem sourceActiveLocalTuple_apply
    (F : Formula) (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (clause : Fin F.clauses.length)
    (localVar : (F.clauses.get clause).LocalVariable) :
    (sourceActiveLocalTuple F assignment hsatisfies clause).val localVar =
      assignment localVar.val := by
  rfl

omit [Fintype K] [DecidableEq K] in
theorem exists_sourceSAT_assignment_interpolant_of_injective
    (F : Formula)
    (variablePlace : Fin F.variableCount → K)
    (hinjective : Function.Injective variablePlace)
    (assignment : Fin F.variableCount → Bool) :
    ∃ interpolant : K[X],
      interpolant.natDegree ≤ F.variableCount - 1 ∧
        ∀ i : Fin F.variableCount,
          interpolant.eval (variablePlace i) =
            sourceSATFieldBit (K := K) (assignment i) := by
  classical
  obtain ⟨interpolant, hdegree, hvalues⟩ :=
    exists_assignment_interpolant variablePlace hinjective
      (fun i => sourceSATFieldBit (K := K) (assignment i))
  refine ⟨interpolant, ?_, hvalues⟩
  by_cases hzero : interpolant = 0
  · simp only [hzero, natDegree_zero, zero_le]
  · have hlt : interpolant.natDegree < F.variableCount :=
      (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdegree
    omega

/-- GapCVP reduction support. -/
def sourceOneHotSignedTable
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X]) :
    Fin (sourceSATTableDimension F K points) → ℤ := by
  classical
  intro position
  let coordinate :=
    (Fintype.equivFin (sourceSATTableCoordinate F K points)).symm position
  exact match coordinate.1 with
    | .inl _ =>
        if coordinate.2.2 = interpolant.eval coordinate.2.1.val
          then 1 else 0
    | .inr ⟨clause, tuple⟩ =>
        if tuple = sourceActiveLocalTuple F assignment hsatisfies clause ∧
          coordinate.2.2 = interpolant.eval coordinate.2.1.val
          then 1 else 0

private def sourceOneHotFieldTable [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X]) :
    Fin (sourceSATTableDimension F K points) → K :=
  fun position => algebraMap (ZMod 2) K
    (sourceOneHotSignedTable F points assignment hsatisfies
      interpolant position : ZMod 2)

@[simp] private theorem sourceOneHotSignedTable_global
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (point : sourceSATGridPoint points) (value : K) :
    sourceOneHotSignedTable F points assignment hsatisfies interpolant
      (sourceSATColumnIndex F points (.inl ()) point value) =
        if value = interpolant.eval point.val then 1 else 0 := by
  classical
  simp only [sourceOneHotSignedTable, sourceSATColumnIndex, List.get_eq_getElem,
      Equiv.symm_apply_apply]

@[simp] private theorem sourceOneHotSignedTable_subtype
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (point : sourceSATGridPoint points) (value : K) :
    sourceOneHotSignedTable F points assignment hsatisfies interpolant
      (sourceSATColumnIndex F points (.inr ⟨clause, tuple⟩) point value) =
        if tuple = sourceActiveLocalTuple F assignment hsatisfies clause ∧
          value = interpolant.eval point.val then 1 else 0 := by
  classical
  simp only [sourceOneHotSignedTable, sourceSATColumnIndex, List.get_eq_getElem,
      Equiv.symm_apply_apply]

@[simp] private theorem sourceOneHotFieldTable_global [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (point : sourceSATGridPoint points) (value : K) :
    sourceOneHotFieldTable F points assignment hsatisfies interpolant
      (sourceSATColumnIndex F points (.inl ()) point value) =
        if value = interpolant.eval point.val then 1 else 0 := by
  classical
  simp only [sourceOneHotFieldTable, List.get_eq_getElem, sourceOneHotSignedTable_global,
      Int.cast_ite,
      Int.cast_one, Int.cast_zero, MonoidWithZeroHom.map_ite_one_zero]

@[simp] private theorem sourceOneHotFieldTable_subtype [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (point : sourceSATGridPoint points) (value : K) :
    sourceOneHotFieldTable F points assignment hsatisfies interpolant
      (sourceSATColumnIndex F points (.inr ⟨clause, tuple⟩) point value) =
        if tuple = sourceActiveLocalTuple F assignment hsatisfies clause ∧
          value = interpolant.eval point.val then 1 else 0 := by
  classical
  simp only [sourceOneHotFieldTable, List.get_eq_getElem, sourceOneHotSignedTable_subtype,
      Int.cast_ite,
      Int.cast_one, Int.cast_zero, MonoidWithZeroHom.map_ite_one_zero]

private theorem sourceOneHot_global_normalization [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X]) :
    sourceGlobalNormalizationMap F points
      (sourceOneHotFieldTable F points assignment hsatisfies interpolant) =
        (fun _ : sourceSATGridPoint points => (1 : K)) := by
  classical
  funext point
  change
    (∑ value : K,
      sourceOneHotFieldTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points (.inl ()) point value)) = 1
  simp only [List.get_eq_getElem, sourceOneHotFieldTable_global, sum_ite_eq', mem_univ, ↓reduceIte]

private theorem sourceOneHot_clause_refinement [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (clause : Fin F.clauses.length) :
    sourceClauseRefinementMap F points clause
      (sourceOneHotFieldTable F points assignment hsatisfies interpolant) = 0 := by
  classical
  funext position
  change
    sourceOneHotFieldTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points (.inl ()) position.1 position.2) -
      (∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
        sourceOneHotFieldTable F points assignment hsatisfies interpolant
          (sourceSATColumnIndex F points
            (.inr ⟨clause, tuple⟩) position.1 position.2)) = 0
  by_cases hvalue : position.2 = interpolant.eval position.1.val
  · simp only [List.get_eq_getElem, hvalue, sourceOneHotFieldTable_global, ↓reduceIte,
        sourceOneHotFieldTable_subtype, and_true, sum_ite_eq', mem_univ, sub_self]
  · simp only [List.get_eq_getElem, sourceOneHotFieldTable_global, hvalue, ↓reduceIte,
        sourceOneHotFieldTable_subtype, and_false, sum_const_zero, sub_self]

@[simp] private theorem sourceOneHot_global_moment [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X]) (j : ℕ)
    (point : sourceSATGridPoint points) :
    sourceOrdinaryMomentMap F points (.inl ()) j
        (sourceOneHotFieldTable F points assignment hsatisfies interpolant)
      point = interpolant.eval point.val ^ j := by
  classical
  change
    (∑ value : K,
      sourceOneHotFieldTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points (.inl ()) point value) * value ^ j) = _
  simp only [List.get_eq_getElem, sourceOneHotFieldTable_global, ite_mul, one_mul, zero_mul,
      sum_ite_eq',
      mem_univ, ↓reduceIte]

@[simp] private theorem sourceOneHot_subtype_moment [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (j : ℕ) (point : sourceSATGridPoint points) :
    sourceOrdinaryMomentMap F points (.inr ⟨clause, tuple⟩) j
        (sourceOneHotFieldTable F points assignment hsatisfies interpolant)
      point =
        if tuple = sourceActiveLocalTuple F assignment hsatisfies clause
          then interpolant.eval point.val ^ j else 0 := by
  classical
  change
    (∑ value : K,
      sourceOneHotFieldTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points
          (.inr ⟨clause, tuple⟩) point value) * value ^ j) = _
  by_cases hactive :
      tuple = sourceActiveLocalTuple F assignment hsatisfies clause
  · simp only [List.get_eq_getElem, hactive, sourceOneHotFieldTable_subtype, true_and, ite_mul,
      one_mul, zero_mul,
        sum_ite_eq', mem_univ, ↓reduceIte]
  · simp only [List.get_eq_getElem, sourceOneHotFieldTable_subtype, hactive, false_and, ↓reduceIte,
      zero_mul,
        sum_const_zero]

@[simp] private theorem sourceOneHot_shifted_moment [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) (point : sourceSATGridPoint points) :
    sourceShiftedMomentMap F points variablePlace clause tuple localVar j
        (sourceOneHotFieldTable F points assignment hsatisfies interpolant)
      point =
        if tuple = sourceActiveLocalTuple F assignment hsatisfies clause
          then
            ((interpolant.eval point.val -
                sourceSATFieldBit (K := K) (tuple.val localVar)) /
              (point.val - variablePlace localVar.val)) ^ j
          else 0 := by
  classical
  change
    (∑ value : K,
      sourceOneHotFieldTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points
          (.inr ⟨clause, tuple⟩) point value) *
        ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
          (point.val - variablePlace localVar.val)) ^ j) = _
  by_cases hactive :
      tuple = sourceActiveLocalTuple F assignment hsatisfies clause
  · simp only [List.get_eq_getElem, hactive, sourceOneHotFieldTable_subtype, true_and,
        sourceActiveLocalTuple_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
            ↓reduceIte]
  · simp only [List.get_eq_getElem, sourceOneHotFieldTable_subtype, hactive, false_and, ↓reduceIte,
      zero_mul,
        sum_const_zero]

private theorem sourceOneHot_ordinary_reedSolomon [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (hdegree : interpolant.natDegree ≤ F.variableCount)
    (tableType : sourceSATTableType F) (j : ℕ) :
    sourceOrdinaryMomentMap F points tableType j
        (sourceOneHotFieldTable F points assignment hsatisfies interpolant)
      ∈ sourceReedSolomonCode points (F.variableCount * j) := by
  classical
  cases tableType with
  | inl global =>
      cases global
      apply (sourceReedSolomonCode_mem_iff points
        (F.variableCount * j) _).mpr
      refine ⟨interpolant ^ j, ?_, ?_⟩
      · rw [Polynomial.natDegree_pow]
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_left j hdegree
      · intro point
        simp only [eval_pow, List.get_eq_getElem, sourceOneHot_global_moment]
  | inr subtype =>
      obtain ⟨clause, tuple⟩ := subtype
      by_cases hactive :
          tuple = sourceActiveLocalTuple F assignment hsatisfies clause
      · apply (sourceReedSolomonCode_mem_iff points
          (F.variableCount * j) _).mpr
        refine ⟨interpolant ^ j, ?_, ?_⟩
        · rw [Polynomial.natDegree_pow]
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_left j hdegree
        · intro point
          simp only [eval_pow, List.get_eq_getElem, hactive, sourceOneHot_subtype_moment,
              ↓reduceIte]
      · have hzero :
            sourceOrdinaryMomentMap F points (.inr ⟨clause, tuple⟩) j
              (sourceOneHotFieldTable F points assignment hsatisfies
                interpolant) = 0 := by
            funext point
            simp only [List.get_eq_getElem, sourceOneHot_subtype_moment, hactive, ↓reduceIte,
                Pi.zero_apply]
        rw [hzero]
        exact (sourceReedSolomonCode points
          (F.variableCount * j)).zero_mem

omit [Fintype K] [DecidableEq K] in
private theorem exists_sourceShiftedMomentQuotient
    (interpolant : K[X]) (place bit : K) (bound : ℕ)
    (hdegree : interpolant.natDegree ≤ bound)
    (hroot : interpolant.eval place = bit) :
    ∃ quotient : K[X],
      quotient.natDegree ≤ bound ∧
        interpolant - Polynomial.C bit =
          (Polynomial.X - Polynomial.C place) * quotient := by
  classical
  have hdivides :
      Polynomial.X - Polynomial.C place ∣
        interpolant - Polynomial.C bit := by
    simpa only [hroot] using (Polynomial.X_sub_C_dvd_sub_C_eval (a := place) (p := interpolant))
  by_cases hzero : interpolant - Polynomial.C bit = 0
  · refine ⟨0, by simp only [natDegree_zero, zero_le], ?_⟩
    simpa only [mul_zero] using hzero
  · obtain ⟨quotient, hquotient⟩ := hdivides
    refine ⟨quotient, ?_, hquotient⟩
    have hquotientDivides :
        quotient ∣ interpolant - Polynomial.C bit := by
      refine ⟨Polynomial.X - Polynomial.C place, ?_⟩
      simpa only [mul_comm] using hquotient
    calc
      quotient.natDegree ≤
          (interpolant - Polynomial.C bit).natDegree :=
        Polynomial.natDegree_le_of_dvd hquotientDivides hzero
      _ ≤ max interpolant.natDegree (Polynomial.C bit).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ = interpolant.natDegree := by simp only [natDegree_C, zero_le, sup_of_le_left]
      _ ≤ bound := hdegree

omit [Fintype K] [DecidableEq K] in
private theorem sourceShiftedMomentQuotient_eval
    (interpolant quotient : K[X]) (place bit point : K)
    (hfactor : interpolant - Polynomial.C bit =
      (Polynomial.X - Polynomial.C place) * quotient)
    (hpoint : point - place ≠ 0) :
    quotient.eval point =
      (interpolant.eval point - bit) / (point - place) := by
  apply (eq_div_iff hpoint).mpr
  have heval := congrArg
    (fun polynomial : K[X] => polynomial.eval point) hfactor
  simpa only [mul_comm, eval_mul, eval_sub, eval_X, eval_C] using heval.symm

private theorem sourceOneHot_shifted_reedSolomon [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (hdegree : interpolant.natDegree ≤ F.variableCount - 1)
    (hinterpolant : ∀ i : Fin F.variableCount,
      interpolant.eval (variablePlace i) =
        sourceSATFieldBit (K := K) (assignment i))
    (hplaces : ∀ point : sourceSATGridPoint points,
      ∀ i : Fin F.variableCount, point.val - variablePlace i ≠ 0)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) :
    sourceShiftedMomentMap F points variablePlace
        clause tuple localVar j
          (sourceOneHotFieldTable F points assignment hsatisfies
            interpolant) ∈
      sourceReedSolomonCode points ((F.variableCount - 1) * j) := by
  classical
  by_cases hactive :
      tuple = sourceActiveLocalTuple F assignment hsatisfies clause
  · have hroot :
        interpolant.eval (variablePlace localVar.val) =
          sourceSATFieldBit (K := K) (tuple.val localVar) := by
      subst tuple
      simpa only [List.get_eq_getElem, sourceActiveLocalTuple_apply] using hinterpolant
          localVar.val
    obtain ⟨quotient, hquotientDegree, hquotient⟩ :=
      exists_sourceShiftedMomentQuotient interpolant
        (variablePlace localVar.val)
        (sourceSATFieldBit (K := K) (tuple.val localVar))
        (F.variableCount - 1) hdegree hroot
    apply (sourceReedSolomonCode_mem_iff points
      ((F.variableCount - 1) * j) _).mpr
    refine ⟨quotient ^ j, ?_, ?_⟩
    · rw [Polynomial.natDegree_pow]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left j hquotientDegree
    · intro point
      rw [Polynomial.eval_pow, sourceOneHot_shifted_moment]
      simp only [hactive, ite_true]
      simpa only [List.get_eq_getElem, sourceActiveLocalTuple_apply, hactive] using
          congrArg (fun value : K => value ^ j)
            (sourceShiftedMomentQuotient_eval interpolant quotient (variablePlace localVar.val)
              (sourceSATFieldBit (K := K) (tuple.val localVar)) point.val hquotient (hplaces point
                  localVar.val))
  · have hzero :
        sourceShiftedMomentMap F points variablePlace
          clause tuple localVar j
            (sourceOneHotFieldTable F points assignment hsatisfies
              interpolant) = 0 := by
        funext point
        simp only [sourceOneHot_shifted_moment, List.get_eq_getElem, hactive, ↓reduceIte,
            Pi.zero_apply]
    rw [hzero]
    exact (sourceReedSolomonCode points
      ((F.variableCount - 1) * j)).zero_mem

private theorem sourceOneHot_satisfies_concreteFieldChecks
    [Algebra (ZMod 2) K]
    (F : Formula) (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (hdegree : interpolant.natDegree ≤ F.variableCount - 1)
    (hinterpolant : ∀ i : Fin F.variableCount,
      interpolant.eval (variablePlace i) =
        sourceSATFieldBit (K := K) (assignment i))
    (hplaces : ∀ point : sourceSATGridPoint points,
      ∀ i : Fin F.variableCount, point.val - variablePlace i ≠ 0)
    (momentBudget : ℕ) :
    concreteSATFieldChecks F points variablePlace momentBudget
      (sourceOneHotFieldTable F points assignment hsatisfies interpolant) := by
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq]
  refine ⟨sourceOneHot_global_normalization
    F points assignment hsatisfies interpolant, ?_, ?_, ?_⟩
  · intro clause
    exact sourceOneHot_clause_refinement
      F points assignment hsatisfies interpolant clause
  · intro tableType j
    apply sourceOneHot_ordinary_reedSolomon
      F points assignment hsatisfies interpolant _ tableType j.val
    exact hdegree.trans (Nat.sub_le _ _)
  · intro clause tuple localVar j
    exact sourceOneHot_shifted_reedSolomon
      F points variablePlace assignment hsatisfies interpolant
      hdegree hinterpolant hplaces clause tuple localVar j.val

theorem sourceOneHot_solves_concreteSATBinaryAffineSystem
    [Algebra (ZMod 2) K]
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (hdegree : interpolant.natDegree ≤ F.variableCount - 1)
    (hinterpolant : ∀ i : Fin F.variableCount,
      interpolant.eval (variablePlace i) =
        sourceSATFieldBit (K := K) (assignment i))
    (hplaces : ∀ point : sourceSATGridPoint points,
      ∀ i : Fin F.variableCount, point.val - variablePlace i ≠ 0)
    (momentBudget : ℕ) :
    (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves
        (sourceOneHotSignedTable F points assignment hsatisfies
          interpolant) := by
  apply (concreteSATBinaryAffineSystem_solves_iff
    F fieldBasis points variablePlace momentBudget
      (sourceOneHotSignedTable F points assignment hsatisfies
        interpolant)).mpr
  change concreteSATFieldChecks F points variablePlace momentBudget
    (sourceOneHotFieldTable F points assignment hsatisfies interpolant)
  exact sourceOneHot_satisfies_concreteFieldChecks
    F points variablePlace assignment hsatisfies interpolant
    hdegree hinterpolant hplaces momentBudget

private theorem sourceOneHotSignedTable_global_row_weight
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (point : sourceSATGridPoint points) :
    (∑ value : K,
      (sourceOneHotSignedTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points (.inl ()) point value)).natAbs ^ 2) =
      1 := by
  classical
  calc
    (∑ value : K,
      (sourceOneHotSignedTable F points assignment hsatisfies interpolant
        (sourceSATColumnIndex F points (.inl ()) point value)).natAbs ^ 2) =
        (sourceOneHotSignedTable F points assignment hsatisfies interpolant
          (sourceSATColumnIndex F points (.inl ()) point
            (interpolant.eval point.val))).natAbs ^ 2 := by
          apply Fintype.sum_eq_single (interpolant.eval point.val)
          intro value hvalue
          simp only [List.get_eq_getElem, sourceOneHotSignedTable_global, hvalue, ↓reduceIte,
              Int.natAbs_zero, ne_eq,
              OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    _ = 1 := by simp only [List.get_eq_getElem, sourceOneHotSignedTable_global, ↓reduceIte,
        isUnit_one, Int.natAbs_of_isUnit,
                    one_pow]

private theorem sourceOneHotSignedTable_clause_row_weight
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X])
    (clause : Fin F.clauses.length)
    (point : sourceSATGridPoint points) :
    (∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
      ∑ value : K,
        (sourceOneHotSignedTable F points assignment hsatisfies interpolant
          (sourceSATColumnIndex F points
            (.inr ⟨clause, tuple⟩) point value)).natAbs ^ 2) = 1 := by
  classical
  calc
    (∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
      ∑ value : K,
        (sourceOneHotSignedTable F points assignment hsatisfies interpolant
          (sourceSATColumnIndex F points
            (.inr ⟨clause, tuple⟩) point value)).natAbs ^ 2) =
      ∑ value : K,
        (sourceOneHotSignedTable F points assignment hsatisfies interpolant
          (sourceSATColumnIndex F points
            (.inr ⟨clause,
              sourceActiveLocalTuple F assignment hsatisfies clause⟩)
              point value)).natAbs ^ 2 := by
        apply Fintype.sum_eq_single
          (sourceActiveLocalTuple F assignment hsatisfies clause)
        intro tuple htuple
        simp only [List.get_eq_getElem, sourceOneHotSignedTable_subtype, htuple, false_and,
            ↓reduceIte,
            Int.natAbs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
                sum_const_zero]
    _ = (sourceOneHotSignedTable F points assignment hsatisfies interpolant
          (sourceSATColumnIndex F points
            (.inr ⟨clause,
              sourceActiveLocalTuple F assignment hsatisfies clause⟩)
              point (interpolant.eval point.val))).natAbs ^ 2 := by
        apply Fintype.sum_eq_single (interpolant.eval point.val)
        intro value hvalue
        simp only [List.get_eq_getElem, sourceOneHotSignedTable_subtype, hvalue, and_false,
            ↓reduceIte,
            Int.natAbs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    _ = 1 := by simp only [List.get_eq_getElem, sourceOneHotSignedTable_subtype, and_self,
        ↓reduceIte, isUnit_one,
                    Int.natAbs_of_isUnit, one_pow]

theorem sourceOneHotSignedTable_squaredNorm
    (F : Formula) (points : Finset K)
    (assignment : Fin F.variableCount → Bool)
    (hsatisfies : F.Satisfied assignment)
    (interpolant : K[X]) :
    (∑ position : Fin (sourceSATTableDimension F K points),
      (sourceOneHotSignedTable F points assignment hsatisfies interpolant
        position).natAbs ^ 2) =
      (F.clauses.length + 1) * points.card := by
  classical
  calc
    (∑ position : Fin (sourceSATTableDimension F K points),
      (sourceOneHotSignedTable F points assignment hsatisfies interpolant
        position).natAbs ^ 2) =
      ∑ coordinate : sourceSATTableCoordinate F K points,
        (sourceOneHotSignedTable F points assignment hsatisfies interpolant
          (Fintype.equivFin
            (sourceSATTableCoordinate F K points) coordinate)).natAbs ^ 2 := by
      exact (Equiv.sum_comp
        (Fintype.equivFin (sourceSATTableCoordinate F K points))
        (fun position : Fin (sourceSATTableDimension F K points) =>
          (sourceOneHotSignedTable F points assignment hsatisfies interpolant
            position).natAbs ^ 2)).symm
    _ = (F.clauses.length + 1) * points.card := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      change
        (∑ tableType : sourceSATTableType F,
          ∑ point : sourceSATGridPoint points,
            ∑ value : K,
              (sourceOneHotSignedTable F points assignment hsatisfies
                interpolant
                (sourceSATColumnIndex F points tableType point value)).natAbs ^
                  2) =
          (F.clauses.length + 1) * points.card
      rw [Fintype.sum_sum_type, Fintype.sum_sigma]
      have hclause :
          ∀ clause : Fin F.clauses.length,
            (∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
              ∑ point : sourceSATGridPoint points,
                ∑ value : K,
                  (sourceOneHotSignedTable F points assignment hsatisfies
                    interpolant (sourceSATColumnIndex F points
                      (.inr ⟨clause, tuple⟩) point value)).natAbs ^ 2) =
                points.card := by
        intro clause
        rw [Finset.sum_comm]
        simp_rw [sourceOneHotSignedTable_clause_row_weight]
        simp only [univ_eq_attach, sum_const, card_attach, smul_eq_mul, mul_one]
      simp_rw [sourceOneHotSignedTable_global_row_weight, hclause]
      simp only [univ_unique, PUnit.default_eq_unit, univ_eq_attach, sum_const, card_attach,
          smul_eq_mul, mul_one,
          card_singleton, one_mul, card_univ, Fintype.card_fin]
      rw [Nat.add_mul]
      simp only [one_mul, Nat.add_comm]

/-- GapCVP reduction support. -/
def integerSquaredNorm {n : ℕ} (z : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, (z i).natAbs ^ 2

/-- GapCVP reduction support. -/
def sourceOneHotCompletenessRadius
    (F : Formula) {α : Type*} (points : Finset α) : ℚ :=
  (Nat.ceil
    (Real.sqrt (((F.clauses.length + 1) * points.card : ℕ) : ℝ)) : ℚ)

theorem sourceOneHotCompletenessRadius_pos
    (F : Formula) {α : Type*} (points : Finset α)
    (hpoints : 0 < points.card) :
    0 < sourceOneHotCompletenessRadius F points := by
  have hweight :
      0 < (F.clauses.length + 1) * points.card :=
    Nat.mul_pos (Nat.zero_lt_succ F.clauses.length) hpoints
  have hreal :
      (0 : ℝ) <
        (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := by
    exact_mod_cast hweight
  have hceil :
      0 < Nat.ceil
        (Real.sqrt (((F.clauses.length + 1) * points.card : ℕ) : ℝ)) :=
    Nat.ceil_pos.mpr (Real.sqrt_pos.mpr hreal)
  unfold sourceOneHotCompletenessRadius
  exact_mod_cast hceil

theorem sourceOneHotCompletenessRadius_squared_bound
    (F : Formula) {α : Type*} (points : Finset α) :
    ((((F.clauses.length + 1) * points.card : ℕ) : ℝ)) ≤
      ((sourceOneHotCompletenessRadius F points : ℚ) : ℝ) ^ 2 := by
  have hroot := Nat.le_ceil
    (Real.sqrt (((F.clauses.length + 1) * points.card : ℕ) : ℝ))
  have hsquare := Real.sq_sqrt
    (by positivity :
      (0 : ℝ) ≤ (((F.clauses.length + 1) * points.card : ℕ) : ℝ))
  unfold sourceOneHotCompletenessRadius
  norm_num only [Rat.cast_natCast]
  nlinarith [Real.sqrt_nonneg
    (((F.clauses.length + 1) * points.card : ℕ) : ℝ)]

end

end Core


end GapCVP

end

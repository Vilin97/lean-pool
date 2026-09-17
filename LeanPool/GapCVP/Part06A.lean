/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part05

/-! # GapCVP proof, part 06 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFCappedFlatSourceListFoldTotalCert

open Computability Turing GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFUnaryPairIndexTM GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFFlatSourceOrder GapCVP.CNFCappedFlatSourceListFoldTM
open GapCVP.CNFGuardedSourceDescriptorRotationBoundedFoldTM

private theorem flatCappedUnarySourceListStep_iterate
    (cap accumulator : ℕ) (records : List ℕ) :
    ((flatCappedUnarySourceListStep^[records.length])
      (flatCappedUnarySourceListState cap accumulator records)) =
      flatCappedUnarySourceListState cap
        (records.foldl
          (fun value head =>
            min cap (Nat.succ (Nat.pair head value)))
          accumulator)
        [] := by
  induction records generalizing accumulator with
  | nil =>
      simp only [List.length_nil, Function.iterate_zero, id_eq, Nat.succ_eq_add_one,
          List.foldl_nil]
  | cons head remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flatCappedUnarySourceListStep_state]
      simpa only [Nat.succ_eq_add_one, List.foldl_cons] using ih (min cap (Nat.succ (Nat.pair head
          accumulator)))

private theorem flatCappedUnaryReverseFold_eq_source
    (cap : ℕ) (records : List ℕ) :
    records.reverse.foldl
        (fun value head =>
          min cap (Nat.succ (Nat.pair head value))) 0 =
      cappedFlatSourceListValue cap records := by
  induction records with
  | nil =>
      rfl
  | cons head remaining ih =>
      simp only [Nat.succ_eq_add_one, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
          List.foldl_nil,
          cappedFlatSourceListValue]

private theorem boundedRecordFoldOutput_flatCappedUnarySourceList
    (cap : ℕ) (records : List ℕ) :
    boundedRecordFoldOutput flatCappedUnarySourceListStep
      (unaryBoundedFoldWord records.length
        (flatCappedUnarySourceListState cap 0 records.reverse)) =
      flatCappedUnarySourceListState cap
        (cappedFlatSourceListValue cap records) [] := by
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  have hphysical := flatCappedUnarySourceListStep_iterate
    cap 0 records.reverse
  rw [flatCappedUnaryReverseFold_eq_source cap records] at hphysical
  simpa only [List.length_reverse] using hphysical

private def flatCappedUnaryCurrentCap (input : List Bool) : ℕ :=
  (cappedUnaryMinimumOutput input).length

private theorem cappedUnaryMinimumOutput_eq_replicate_length
    (input : List Bool) :
    cappedUnaryMinimumOutput input =
      List.replicate (cappedUnaryMinimumOutput input).length true := by
  cases hfirst : readUnaryPrefix input with
  | none =>
      simp only [cappedUnaryMinimumOutput, hfirst, List.length_nil, List.replicate_zero]
  | some firstParsed =>
      obtain ⟨first, remaining⟩ := firstParsed
      cases hsecond : readUnaryPrefix remaining with
      | none =>
          simp only [cappedUnaryMinimumOutput, hfirst, hsecond, List.length_nil,
              List.replicate_zero]
      | some secondParsed =>
          obtain ⟨second, suffix⟩ := secondParsed
          simp only [cappedUnaryMinimumOutput, hfirst, hsecond, List.length_replicate]

private theorem flatDuplicatedUnaryFieldAt_eq_replicate
    (offset : ℕ) (input : List Bool) :
    flatDuplicatedUnaryFieldAt offset input =
      List.replicate
        (cappedUnaryMinimumOutput
          (flatUnaryDropFields offset input)).length true ++
        [false] := by
  unfold flatDuplicatedUnaryFieldAt
    flatDuplicatedUnaryFieldWord flatDuplicatedUnaryValueWord
  exact congrArg
    (fun output : List Bool => output ++ [false])
    (cappedUnaryMinimumOutput_eq_replicate_length
      (flatUnaryDropFields offset input))

private theorem flatCappedUnarySourceListNextField_eq
    (input : List Bool) :
    flatCappedUnarySourceListNextField input =
      List.replicate
        (min (flatCappedUnaryCurrentCap input)
          (Nat.succ (Nat.pair
            (cappedUnaryMinimumOutput
              (flatUnaryDropFields 2 input)).length
            (cappedUnaryMinimumOutput
              (flatUnaryDropFields 4 input)).length))) true ++
        [false] := by
  unfold flatCappedUnarySourceListNextField
    flatCappedUnarySourceListQuery
  rw [flatDuplicatedUnaryFieldAt_eq_replicate,
    flatDuplicatedUnaryFieldAt_eq_replicate,
    flatDuplicatedUnaryFieldAt_eq_replicate]
  have hquery :
      (List.replicate
          (cappedUnaryMinimumOutput
            (flatUnaryDropFields 0 input)).length true ++
        [false]) ++
        (List.replicate
          (cappedUnaryMinimumOutput
            (flatUnaryDropFields 2 input)).length true ++
          [false]) ++
        (List.replicate
          (cappedUnaryMinimumOutput
            (flatUnaryDropFields 4 input)).length true ++
          [false]) =
        List.replicate (flatCappedUnaryCurrentCap input) true ++
          false ::
            (unarySourcePairWord
              (cappedUnaryMinimumOutput
                (flatUnaryDropFields 2 input)).length
              (cappedUnaryMinimumOutput
                (flatUnaryDropFields 4 input)).length ++ []) := by
    simp only [flatUnaryDropFields, Function.iterate_zero, id_eq, Function.iterate_succ,
        Function.comp_apply,
      List.append_assoc, List.cons_append, List.nil_append, flatCappedUnaryCurrentCap,
      unarySourcePairWord, List.append_nil]
  rw [hquery]
  rw [cappedUnarySourcePairRecurrenceWord_valid]

private def flatCappedUnaryNextValue (input : List Bool) : ℕ :=
  min (flatCappedUnaryCurrentCap input)
    (Nat.succ (Nat.pair
      (cappedUnaryMinimumOutput
        (flatUnaryDropFields 2 input)).length
      (cappedUnaryMinimumOutput
        (flatUnaryDropFields 4 input)).length))

private theorem flatCappedUnarySourceListStep_normalized
    (input : List Bool) :
    flatCappedUnarySourceListStep input =
      unarySourcePairWord
        (flatCappedUnaryCurrentCap input)
        (flatCappedUnaryCurrentCap input) ++
      sourcePairPrefixOutput (flatUnaryDropFields 6 input) ++
      unarySourcePairWord
        (flatCappedUnaryNextValue input)
        (flatCappedUnaryNextValue input) ++
      flatUnaryDropFields 2 (flatUnaryDropFields 6 input) := by
  unfold flatCappedUnarySourceListStep
    flatCappedUnaryPendingPair flatCappedUnaryPendingRemainder
  simp only [flatDuplicatedUnaryFieldAt_eq_replicate,
    flatCappedUnarySourceListNextField_eq]
  simp only [flatUnaryDropFields, Function.iterate_zero, id_eq, List.append_assoc,
      List.cons_append,
    List.nil_append, Function.iterate_succ, Function.comp_apply, flatCappedUnaryCurrentCap,
    Nat.succ_eq_add_one, unarySourcePairWord, flatCappedUnaryNextValue]

@[simp] private theorem flatCappedUnaryCurrentCap_step
    (input : List Bool) :
    flatCappedUnaryCurrentCap
      (flatCappedUnarySourceListStep input) =
      flatCappedUnaryCurrentCap input := by
  rw [flatCappedUnarySourceListStep_normalized]
  unfold flatCappedUnaryCurrentCap
  simp only [List.append_assoc, cappedUnaryMinimumOutput_pair, min_self, List.length_replicate]

private theorem flatUnaryPrefix_reconstruct
    (input : List Bool) (count : ℕ) (suffix : List Bool)
    (hread : readUnaryPrefix input = some (count, suffix)) :
    input = List.replicate count true ++ false :: suffix :=
  guardedRotation_readUnaryPrefix_some_reconstruct
    input count suffix hread

private theorem unaryPrefixSuffixOutput_length_le
    (input : List Bool) :
    (unaryPrefixSuffixOutput input).length ≤ input.length := by
  cases hread : readUnaryPrefix input with
  | none =>
      simp only [unaryPrefixSuffixOutput, hread, List.length_nil, zero_le]
  | some parsed =>
      obtain ⟨count, suffix⟩ := parsed
      have hshape := flatUnaryPrefix_reconstruct
        input count suffix hread
      simp only [unaryPrefixSuffixOutput, hread]
      rw [hshape]
      simp only [List.length_append, List.length_replicate, List.length_cons, ge_iff_le]
      omega

theorem flatUnaryDropFields_length_le
    (count : ℕ) (input : List Bool) :
    (flatUnaryDropFields count input).length ≤ input.length := by
  induction count with
  | zero =>
      simp only [flatUnaryDropFields, Function.iterate_zero, id_eq, Std.le_refl]
  | succ count ih =>
      unfold flatUnaryDropFields at ih ⊢
      rw [Function.iterate_succ_apply']
      exact (unaryPrefixSuffixOutput_length_le
        ((unaryPrefixSuffixOutput^[count]) input)).trans ih

private theorem cappedUnaryMinimumOutput_length_le
    (input : List Bool) :
    (cappedUnaryMinimumOutput input).length ≤ input.length := by
  cases hfirst : readUnaryPrefix input with
  | none =>
      simp only [cappedUnaryMinimumOutput, hfirst, List.length_nil, zero_le]
  | some firstParsed =>
      obtain ⟨first, remaining⟩ := firstParsed
      cases hsecond : readUnaryPrefix remaining with
      | none =>
          simp only [cappedUnaryMinimumOutput, hfirst, hsecond, List.length_nil, zero_le]
      | some secondParsed =>
          obtain ⟨second, suffix⟩ := secondParsed
          have hfirstShape := flatUnaryPrefix_reconstruct
            input first remaining hfirst
          have hsecondShape := flatUnaryPrefix_reconstruct
            remaining second suffix hsecond
          simp only [cappedUnaryMinimumOutput,
            hfirst, hsecond, List.length_replicate]
          rw [hfirstShape, hsecondShape]
          simp only [List.length_append,
            List.length_replicate, List.length_cons]
          omega

theorem sourcePairPrefixOutput_drop_length_le
    (pending : List Bool) :
    (sourcePairPrefixOutput pending).length +
      (flatUnaryDropFields 2 pending).length ≤ pending.length := by
  cases hfirst : readUnaryPrefix pending with
  | none =>
      simp [sourcePairPrefixOutput, hfirst,
        flatUnaryDropFields, Function.iterate_succ_apply',
        unaryPrefixSuffixOutput, readUnaryPrefix]
  | some firstParsed =>
      obtain ⟨first, remaining⟩ := firstParsed
      cases hsecond : readUnaryPrefix remaining with
      | none =>
          simp [sourcePairPrefixOutput, hfirst, hsecond,
            flatUnaryDropFields, Function.iterate_succ_apply',
            unaryPrefixSuffixOutput]
      | some secondParsed =>
          obtain ⟨second, suffix⟩ := secondParsed
          have hfirstShape := flatUnaryPrefix_reconstruct
            pending first remaining hfirst
          have hsecondShape := flatUnaryPrefix_reconstruct
            remaining second suffix hsecond
          have hshape :
              pending = unarySourcePairWord first second ++ suffix := by
            rw [hfirstShape, hsecondShape]
            simp [unarySourcePairWord, List.append_assoc]
          rw [hshape]
          simp [sourcePairPrefixOutput_pair,
            flatUnaryDropFields_two_unaryPair,
            List.length_append]

private theorem flatCappedUnarySourceListStep_length_le_cap_pending
    (input : List Bool) :
    (flatCappedUnarySourceListStep input).length ≤
      4 * flatCappedUnaryCurrentCap input +
        (flatUnaryDropFields 6 input).length + 4 := by
  rw [flatCappedUnarySourceListStep_normalized]
  have hpending := sourcePairPrefixOutput_drop_length_le
    (flatUnaryDropFields 6 input)
  have hnext : flatCappedUnaryNextValue input ≤
      flatCappedUnaryCurrentCap input :=
    Nat.min_le_left _ _
  simp only [List.length_append, unarySourcePairWord,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem flatCappedUnarySourceListStep_pending
    (input : List Bool) :
    flatUnaryDropFields 6
      (flatCappedUnarySourceListStep input) =
      flatUnaryDropFields 2 (flatUnaryDropFields 6 input) := by
  rw [flatCappedUnarySourceListStep_normalized]
  generalize hpending : flatUnaryDropFields 6 input = pending
  generalize hcap : flatCappedUnaryCurrentCap input = cap
  generalize hnext : flatCappedUnaryNextValue input = next
  cases hfirst : readUnaryPrefix pending with
  | none =>
      have hdrop : flatUnaryDropFields 2 pending = [] := by
        simp [flatUnaryDropFields,
          Function.iterate_succ_apply',
          unaryPrefixSuffixOutput, hfirst, readUnaryPrefix]
      have hprefix : sourcePairPrefixOutput pending = [] := by
        simp [sourcePairPrefixOutput, hfirst]
      rw [hdrop, hprefix]
      simp [flatUnaryDropFields,
        Function.iterate_succ_apply',
        unarySourcePairWord,
        unaryPrefixSuffixOutput,
        readUnaryPrefix, List.append_assoc]
  | some firstParsed =>
      obtain ⟨first, remaining⟩ := firstParsed
      cases hsecond : readUnaryPrefix remaining with
      | none =>
          have hdrop : flatUnaryDropFields 2 pending = [] := by
            simp [flatUnaryDropFields,
              Function.iterate_succ_apply',
              unaryPrefixSuffixOutput, hfirst, hsecond]
          have hprefix : sourcePairPrefixOutput pending = [] := by
            simp [sourcePairPrefixOutput, hfirst, hsecond]
          rw [hdrop, hprefix]
          simp [flatUnaryDropFields,
            Function.iterate_succ_apply',
            unarySourcePairWord,
            unaryPrefixSuffixOutput,
            readUnaryPrefix, List.append_assoc]
      | some secondParsed =>
          obtain ⟨second, suffix⟩ := secondParsed
          have hfirstShape := flatUnaryPrefix_reconstruct
            pending first remaining hfirst
          have hsecondShape := flatUnaryPrefix_reconstruct
            remaining second suffix hsecond
          have hshape :
              pending = unarySourcePairWord first second ++ suffix := by
            rw [hfirstShape, hsecondShape]
            simp [unarySourcePairWord, List.append_assoc]
          rw [hshape]
          simp only [sourcePairPrefixOutput_pair,
            flatUnaryDropFields_two_unaryPair]
          simpa [List.append_assoc] using
            flatUnaryDropFields_six_unaryPairs
              cap cap first second next next suffix

private theorem flatCappedUnaryCurrentCap_iterate
    (input : List Bool) (stage : ℕ) :
    flatCappedUnaryCurrentCap
      ((flatCappedUnarySourceListStep^[stage]) input) =
      flatCappedUnaryCurrentCap input := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        flatCappedUnaryCurrentCap_step, ih]

private theorem flatCappedUnaryPending_iterate_length_le
    (input : List Bool) (stage : ℕ) :
    (flatUnaryDropFields 6
      ((flatCappedUnarySourceListStep^[stage]) input)).length ≤
      (flatUnaryDropFields 6 input).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        flatCappedUnarySourceListStep_pending]
      exact (flatUnaryDropFields_length_le 2
        (flatUnaryDropFields 6
          ((flatCappedUnarySourceListStep^[stage]) input))).trans ih

private theorem flatCappedUnarySourceListStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatCappedUnarySourceListStep
      (5 * Polynomial.X + 4) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hseed := parsedUnaryFold_seed_length_le
    input count seed hparse
  cases stage with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_ofNat,
          Polynomial.eval_X, ge_iff_le]
      omega
  | succ stage =>
      rw [Function.iterate_succ_apply']
      have hstep := flatCappedUnarySourceListStep_length_le_cap_pending
        ((flatCappedUnarySourceListStep^[stage]) seed)
      rw [flatCappedUnaryCurrentCap_iterate] at hstep
      have hpending := flatCappedUnaryPending_iterate_length_le
        seed stage
      have htail := flatUnaryDropFields_length_le 6 seed
      have hcap := cappedUnaryMinimumOutput_length_le seed
      unfold flatCappedUnaryCurrentCap at hstep
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X, ge_iff_le]
      omega

private noncomputable def actualCappedFlatSourceListFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatCappedUnarySourceListStep) :=
  boundedDependentRecordFoldComputable
    flatCappedUnarySourceListStepComputable
    (5 * Polynomial.X + 4)
    flatCappedUnarySourceListStep_polynomiallyBoundedFoldStates

end CNFCappedFlatSourceListFoldTotalCert

namespace CNFFiveFamilyFlatCandidateGenerationTM

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds GapCVP.BinaryEncoding
open GapCVP.ThreeCNFReduction GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralCNFVariableBounds GapCVP.CLStructuralWholeCNFOutputTM
open GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatSourceOrderPolynomialBounds
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert
open GapCVP.CNFCappedFlatSourceListFoldTM

private def unarySignedLiteralCodePairInput (sign : Bool)
    (input : List Bool) : List Bool :=
  input ++ [false] ++
    List.replicate (Encodable.encode sign) true ++ [false]

private noncomputable def unarySignedLiteralCodePairInputComputable
    (sign : Bool) :
    BitTM
      (unarySignedLiteralCodePairInput sign) := by
  have hidentity := prependWordComputable []
  have hsuffix := constantWordComputable
    ([false] ++ List.replicate (Encodable.encode sign) true ++ [false])
  have hphysical := pointwiseAppendComputable hidentity hsuffix
  change BitTM
    (fun input : List Bool =>
      input ++ [false] ++
        List.replicate (Encodable.encode sign) true ++ [false])
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hphysical

private def unarySignedLiteralCodeWord (sign : Bool)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput (unarySignedLiteralCodePairInput sign input)

private noncomputable def unarySignedLiteralCodeComputable (sign : Bool) :
    BitTM
      (unarySignedLiteralCodeWord sign) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (unarySignedLiteralCodePairInputComputable sign)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input : List Bool =>
      unarySourcePairOutput (unarySignedLiteralCodePairInput sign input))
  simpa only [Function.comp_def] using hphysical

@[simp] private theorem unarySignedLiteralCodeWord_sourceVariable
    {T S : ℕ} (atom : Variable T S) (sign : Bool) :
    unarySignedLiteralCodeWord sign
        (List.replicate (Encodable.encode atom) true) =
      List.replicate
        (Encodable.encode ((atom, sign) : SignedLiteral T S)) true := by
  unfold unarySignedLiteralCodeWord unarySignedLiteralCodePairInput
  have hinput :
      List.replicate (Encodable.encode atom) true ++ [false] ++
          List.replicate (Encodable.encode sign) true ++ [false] =
        unarySourcePairWord
          (Encodable.encode atom) (Encodable.encode sign) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append, unarySourcePairWord]
  rw [hinput, unarySourcePairOutput_word]
  rfl

private def duplicateUnarySourceCodeWord (input : List Bool) : List Bool :=
  input ++ [false] ++ input ++ [false]

private noncomputable def duplicateUnarySourceCodeComputable :
    BitTM
      duplicateUnarySourceCodeWord := by
  have hidentity := prependWordComputable []
  have hone := pointwiseAppendComputable
    hidentity (constantWordComputable [false])
  have hphysical := pointwiseAppendComputable hone hone
  change BitTM
    (fun input : List Bool => input ++ [false] ++ input ++ [false])
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hphysical

/-- GapCVP reduction support. -/
def duplicatedUnarySignedLiteralCodeWord (sign : Bool)
    (input : List Bool) : List Bool :=
  duplicateUnarySourceCodeWord (unarySignedLiteralCodeWord sign input)

/-- GapCVP reduction support. -/
noncomputable def duplicatedUnarySignedLiteralCodeComputable
    (sign : Bool) :
    BitTM
      (duplicatedUnarySignedLiteralCodeWord sign) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (unarySignedLiteralCodeComputable sign)
    duplicateUnarySourceCodeComputable
  change BitTM
    (fun input : List Bool =>
      duplicateUnarySourceCodeWord (unarySignedLiteralCodeWord sign input))
  simpa only [Function.comp_def] using hphysical

@[simp] theorem duplicatedUnarySignedLiteralCodeWord_sourceVariable
    {T S : ℕ} (atom : Variable T S) (sign : Bool) :
    duplicatedUnarySignedLiteralCodeWord sign
        (List.replicate (Encodable.encode atom) true) =
      flatDuplicatedUnaryField
        (Encodable.encode ((atom, sign) : SignedLiteral T S)) := by
  simp only [duplicatedUnarySignedLiteralCodeWord, duplicateUnarySourceCodeWord,
      unarySignedLiteralCodeWord_sourceVariable, Encodable.encode_prod_val, List.append_assoc,
          List.cons_append,
      List.nil_append, flatDuplicatedUnaryField, unarySourcePairWord]

/-- GapCVP reduction support. -/
def flatSourceClauseDescriptorPayload {T S : ℕ}
    (clause : Clause T S) : List Bool :=
  flatSignedLiteralDescriptorStream
    ((sortedElements clause).map sourceLiteral)

/-- GapCVP reduction support. -/
def flatSourceClauseDuplicatedCodePayload {T S : ℕ}
    (clause : Clause T S) : List Bool :=
  flatDuplicatedUnarySourceStream (flatSourceFinsetCodes clause)

/-- GapCVP reduction support. -/
def flatSourceClauseUnaryCountPayload {T S : ℕ}
    (clause : Clause T S) : List Bool :=
  List.replicate clause.card true

/-- GapCVP reduction support. -/
def flatSourceClauseAnnotatedRecord {T S : ℕ}
    (clause : Clause T S) : List Bool :=
  lengthPrefixedWord (flatSourceClauseDescriptorPayload clause) ++
    lengthPrefixedWord (flatSourceClauseDuplicatedCodePayload clause) ++
      lengthPrefixedWord (flatSourceClauseUnaryCountPayload clause)

@[simp] theorem flatSourceClauseUnaryCountPayload_length
    {T S : ℕ} (clause : Clause T S) :
    (flatSourceClauseUnaryCountPayload clause).length =
      (flatSourceFinsetCodes clause).length := by
  simp only [flatSourceClauseUnaryCountPayload, List.length_replicate, flatSourceFinsetCodes,
      List.length_map,
      sortedElements_length]

@[simp] private theorem flatDuplicatedUnaryField_length (value : ℕ) :
    (flatDuplicatedUnaryField value).length = 2 * value + 2 := by
  simp only [flatDuplicatedUnaryField, unarySourcePairWord, List.length_append,
      List.length_replicate,
      List.length_cons, List.length_nil, zero_add]
  omega

private theorem flatDuplicatedUnarySourceStream_length_le
    (records : List ℕ) (bound : ℕ)
    (hbound : ∀ code ∈ records, code < bound) :
    (flatDuplicatedUnarySourceStream records).length ≤
      records.length * (2 * bound + 2) := by
  induction records with
  | nil => simp only [flatDuplicatedUnarySourceStream, List.flatMap_nil, List.length_nil, zero_mul,
      Std.le_refl]
  | cons code remaining ih =>
      have hcode : code < bound := hbound code (by simp only [List.mem_cons, true_or])
      have hrest := ih (fun next hnext =>
        hbound next (by simp only [List.mem_cons, hnext, or_true]))
      simp only [flatDuplicatedUnarySourceStream,
        List.flatMap_cons, List.length_append,
        flatDuplicatedUnaryField_length, List.length_cons,
        Nat.succ_mul] at hrest ⊢
      omega

private theorem flatSourceSignedLiteralDescriptor_length_le
    {T S : ℕ} (literal : SignedLiteral T S) :
    (flatSignedLiteralDescriptor (sourceLiteral literal)).length ≤
      8 * tableauFiniteVariableCodeBound T S + 3 := by
  have hvariable := sourceVariable_lt_tableauFiniteBound literal.1
  have hsize := structuralNatSize_le_self
    (sourceVariable literal.1)
  simp only [flatSignedLiteralDescriptor, sourceLiteral,
    lengthPrefixedWord_length, List.length_cons,
    encodeNat_length_eq_size]
  omega

private theorem flatSourceClauseDescriptorPayload_length_le
    {T S : ℕ} (clause : Clause T S) :
    (flatSourceClauseDescriptorPayload clause).length ≤
      clause.card * (8 * tableauFiniteVariableCodeBound T S + 3) := by
  have hgeneral : ∀ (literals : List (SignedLiteral T S)),
      (flatSignedLiteralDescriptorStream
        (literals.map sourceLiteral)).length ≤
          literals.length *
            (8 * tableauFiniteVariableCodeBound T S + 3) := by
    intro literals
    induction literals with
    | nil => simp only [flatSignedLiteralDescriptorStream, List.map_nil, List.flatMap_nil,
        List.length_nil, zero_mul,
                 Std.le_refl]
    | cons literal remaining ih =>
        have hhead := flatSourceSignedLiteralDescriptor_length_le literal
        simp only [List.map_cons, flatSignedLiteralDescriptorStream,
          List.flatMap_cons, List.length_append,
          List.length_cons, Nat.succ_mul] at ih ⊢
        omega
  simpa only [flatSourceClauseDescriptorPayload, ge_iff_le, sortedElements_length] using
      hgeneral (sortedElements clause)

private theorem flatSourceClauseDuplicatedCodePayload_length_le
    {T S : ℕ} (clause : Clause T S) :
    (flatSourceClauseDuplicatedCodePayload clause).length ≤
      clause.card * (2 * tableauSignedLiteralCodeBound T S + 2) := by
  have hbound := flatDuplicatedUnarySourceStream_length_le
    (flatSourceFinsetCodes clause)
    (tableauSignedLiteralCodeBound T S)
    (fun code hcode => flatSourceClauseLiteralCode_lt clause code hcode)
  simpa only [flatSourceClauseDuplicatedCodePayload, flatSourceFinsetCodes, ge_iff_le,
      List.length_map,
      sortedElements_length] using hbound

/-- GapCVP reduction support. -/
def flatSourceAnnotatedClauseLengthBound (T S : ℕ) : ℕ :=
  (2 * ((T + 1) ^ 2 * (S + 1))) *
    (16 * tableauFiniteVariableCodeBound T S +
      4 * tableauSignedLiteralCodeBound T S + 12) + 3

theorem flatSourceClauseAnnotatedRecord_length_le
    {T S : ℕ} (clause : Clause T S) :
    (flatSourceClauseAnnotatedRecord clause).length ≤
      flatSourceAnnotatedClauseLengthBound T S := by
  have hdescriptors := flatSourceClauseDescriptorPayload_length_le clause
  have hcodes := flatSourceClauseDuplicatedCodePayload_length_le clause
  have hcard : clause.card ≤ 2 * ((T + 1) ^ 2 * (S + 1)) := by
    calc
      clause.card ≤ Fintype.card (SignedLiteral T S) :=
        Finset.card_le_univ clause
      _ = 2 * ((T + 1) ^ 2 * (S + 1)) := signedLiteral_card T S
  have hproduct := Nat.mul_le_mul_right
    (16 * tableauFiniteVariableCodeBound T S +
      4 * tableauSignedLiteralCodeBound T S + 12) hcard
  have hexpand :
      clause.card *
          (16 * tableauFiniteVariableCodeBound T S +
            4 * tableauSignedLiteralCodeBound T S + 12) =
        2 * (clause.card *
          (8 * tableauFiniteVariableCodeBound T S + 3)) +
          2 * (clause.card *
            (2 * tableauSignedLiteralCodeBound T S + 2)) +
            2 * clause.card := by
    ring
  rw [hexpand] at hproduct
  simp only [flatSourceClauseAnnotatedRecord,
    flatSourceClauseUnaryCountPayload,
    List.length_append, lengthPrefixedWord_length,
    List.length_replicate,
    flatSourceAnnotatedClauseLengthBound] at hproduct ⊢
  omega

/-- GapCVP reduction support. -/
def flatSourceAnnotatedClauseLengthPolynomial
    (time : Polynomial ℕ) (symbols : ℕ) : Polynomial ℕ :=
  let finite := ((time + Polynomial.C (symbols + 2)) ^ 2 + 1) ^ 2
  let signed := (finite + 2) ^ 2
  let literalCount :=
    2 * ((time + 1) ^ 2 * Polynomial.C (symbols + 1))
  literalCount * (16 * finite + 4 * signed + 12) + 3

theorem flatSourceAnnotatedClauseLengthBound_eq_polynomial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    flatSourceAnnotatedClauseLengthBound
        (rowWidth bound machine input)
        (completePhaseSymbolCount machine.tm) =
      (flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)).eval input.length := by
  simp only [flatSourceAnnotatedClauseLengthBound,
    flatSourceAnnotatedClauseLengthPolynomial,
    tableauSignedLiteralCodeBound, tableauFiniteVariableCodeBound,
    rowWidth, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  ring

end CNFFiveFamilyFlatCandidateGenerationTM

namespace CNFCappedFlatSourceListComparatorTM

open Computability Turing GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryMinimumTotalCert GapCVP.CNFFlatSourceOrder
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert

private def fullCappedFlatSourceListUnaryWord
    (input : List Bool) : List Bool :=
  cappedUnaryMinimumOutput
    (flatUnaryDropFields 2
      (boundedRecordFoldOutput flatCappedUnarySourceListStep input))

private noncomputable def fullCappedFlatSourceListUnaryComputable :
    BitTM
      fullCappedFlatSourceListUnaryWord := by
  have hdrop := GapCVP.TMComposition.computableInPolyTime
    actualCappedFlatSourceListFoldComputable
    (flatUnaryDropFieldsComputable 2)
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hdrop actualCappedUnaryMinimumComputable
  change BitTM
    (fun input : List Bool =>
      cappedUnaryMinimumOutput
        (flatUnaryDropFields 2
          (boundedRecordFoldOutput flatCappedUnarySourceListStep input)))
  simpa only [Function.comp_def] using hphysical

@[simp] private theorem fullCappedFlatSourceListUnaryWord_valid
    (cap : ℕ) (records : List ℕ) :
    fullCappedFlatSourceListUnaryWord
      (unaryBoundedFoldWord records.length
        (flatCappedUnarySourceListState cap 0 records.reverse)) =
      List.replicate (cappedFlatSourceListValue cap records) true := by
  unfold fullCappedFlatSourceListUnaryWord
  rw [boundedRecordFoldOutput_flatCappedUnarySourceList]
  simp only [flatCappedUnarySourceListState,
    flatDuplicatedUnaryField,
    flatUnaryDropFields_two_unaryPair]
  simpa only [List.append_nil, min_self] using
      cappedUnaryMinimumOutput_pair (cappedFlatSourceListValue cap records)
          (cappedFlatSourceListValue cap records) []

/-- GapCVP reduction support. -/
def fullCappedFlatSourceListBinaryWord
    (input : List Bool) : List Bool :=
  Computability.encodeNat
    (fullCappedFlatSourceListUnaryWord input).length

/-- GapCVP reduction support. -/
noncomputable def fullCappedFlatSourceListBinaryComputable :
    BitTM
      fullCappedFlatSourceListBinaryWord := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    fullCappedFlatSourceListUnaryComputable
    structuralNaturalBinaryWriterComputable
  change BitTM
    (fun input : List Bool =>
      Computability.encodeNat
        (fullCappedFlatSourceListUnaryWord input).length)
  simpa only [Function.comp_def] using hphysical

@[simp] theorem fullCappedFlatSourceListBinaryWord_valid
    (cap : ℕ) (records : List ℕ) :
    fullCappedFlatSourceListBinaryWord
      (unaryBoundedFoldWord records.length
        (flatCappedUnarySourceListState cap 0 records.reverse)) =
      Computability.encodeNat (cappedFlatSourceListValue cap records) := by
  simp only [fullCappedFlatSourceListBinaryWord, fullCappedFlatSourceListUnaryWord_valid,
      List.length_replicate]

end CNFCappedFlatSourceListComparatorTM

namespace SourceCanonicalFixedWordTuringTM

open Turing GapCVP.SourceMachineCert

private abbrev sourceInputEraseMachine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    .peek () (fun _ symbol => symbol)
      (.branch (fun symbol => symbol.isSome)
        (.pop () (fun _ _ => none)
          (.goto (fun _ => ())))
        (.load (fun _ => none) .halt))

private def sourceInputEraseConfiguration (input : List Bool) :
    sourceInputEraseMachine.Cfg where
  l := some ()
  var := none
  stk := fun _ => input

private theorem sourceInputEraseMachine_init (input : List Bool) :
    Turing.initList sourceInputEraseMachine input =
      sourceInputEraseConfiguration input := by
  simp only [sourceInputEraseMachine, initList, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
      sourceInputEraseConfiguration]
  rfl

private theorem sourceInputErase_scan_step
    (bit : Bool) (input : List Bool) :
    sourceInputEraseMachine.step
      (sourceInputEraseConfiguration (bit :: input)) =
        some (sourceInputEraseConfiguration input) := by
  cases bit <;> compactMachineStepTac [sourceInputEraseMachine, sourceInputEraseConfiguration]

private theorem sourceInputErase_finish :
    sourceInputEraseMachine.step
      (sourceInputEraseConfiguration []) =
        some (Turing.haltList sourceInputEraseMachine []) := by
  compactMachineStepTac [sourceInputEraseMachine, sourceInputEraseConfiguration]

private def sourceInputErase_totalTrace (input : List Bool) :
    EvalsToInTime sourceInputEraseMachine.step (sourceInputEraseConfiguration input)
      (some (Turing.haltList sourceInputEraseMachine []))
      (input.length + 1) := by
  induction input with
  | nil =>
      simpa only [FinTM2.step, List.length_nil, zero_add] using oneStep _ _ sourceInputErase_finish
  | cons bit input ih =>
      have first := oneStep _ _ (sourceInputErase_scan_step bit input)
      have full := EvalsToInTime.trans sourceInputEraseMachine.step _ _ _ _ _ first ih
      simpa only [FinTM2.step, List.length_cons, Nat.add_assoc, Nat.reduceAdd] using full

private noncomputable def sourceInputEraseComputable :
    BitTM
      (fun _ : List Bool => []) where
  tm := sourceInputEraseMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := {
    steps := (sourceInputErase_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Equiv.invFun_as_coe, Equiv.refl_symm,
          Equiv.coe_refl,
          bitEncoding, id_eq, List.map_id_fun, sourceInputEraseMachine_init, List.map_nil,
              Option.map_some] using
          (sourceInputErase_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (sourceInputErase_totalTrace input).steps_le_m
      simpa only [FinTM2.step, bitEncoding, id_eq, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one,
          ge_iff_le] using hsteps
  }

/-- GapCVP reduction support. -/
noncomputable def sourceFixedWordComputable (word : List Bool) :
    BitTM
      (fun _ : List Bool => word) := by
  have machine := GapCVP.TMComposition.computableInPolyTime
    sourceInputEraseComputable (prependWordComputable word)
  simpa only [Function.comp_def, List.append_nil] using machine

end SourceCanonicalFixedWordTuringTM

namespace CNFAnnotatedSourceClausePairPreparationTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryMinimumTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
def flatAnnotatedSourceFieldTail
    (offset : ℕ) (input : List Bool) : List Bool :=
  (firstFieldSuffix^[offset]) input

/-- GapCVP reduction support. -/
noncomputable def annotatedSourceFieldTailComputable :
    (offset : ℕ) →
      BitTM
        (flatAnnotatedSourceFieldTail offset)
  | 0 => by
      change BitTM
        (fun input : List Bool => input)
      exact Turing.idComputableInPolyTime bitEncoding
  | offset + 1 => by
      have physical := GapCVP.TMComposition.computableInPolyTime
        (annotatedSourceFieldTailComputable offset)
        firstFieldSuffixComputable
      change BitTM
        (fun input : List Bool =>
          (firstFieldSuffix^[offset + 1]) input)
      simpa only [Function.iterate_succ_apply', Function.comp_def, flatAnnotatedSourceFieldTail]
          using physical

/-- GapCVP reduction support. -/
def flatAnnotatedSourceFieldAt
    (offset : ℕ) (input : List Bool) : List Bool :=
  firstFieldContents (flatAnnotatedSourceFieldTail offset input)

/-- GapCVP reduction support. -/
noncomputable def annotatedSourceFieldAtComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSourceFieldAt offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldTailComputable offset)
    firstFieldContentsComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldContents (flatAnnotatedSourceFieldTail offset input))
  exact physical

/-- GapCVP reduction support. -/
def annotatedSourceAdjacentClauseWord
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) : List Bool :=
  lengthPrefixedWord firstClause ++
    lengthPrefixedWord firstCodes ++
      lengthPrefixedWord (List.replicate firstCount true) ++
        lengthPrefixedWord secondClause ++
          lengthPrefixedWord secondCodes ++
            lengthPrefixedWord (List.replicate secondCount true) ++
              suffix

@[simp] theorem flatAnnotatedSourceFieldAt_firstCodes
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedSourceFieldAt 1
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      firstCodes := by
  simp only [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      annotatedSourceAdjacentClauseWord,
      List.append_assoc, Function.iterate_one, firstFieldSuffix_valid, firstFieldContents_valid]

@[simp] theorem flatAnnotatedSourceFieldAt_firstCount
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedSourceFieldAt 2
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      List.replicate firstCount true := by
  simp [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    annotatedSourceAdjacentClauseWord,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] theorem flatAnnotatedSourceFieldAt_secondCodes
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedSourceFieldAt 4
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      secondCodes := by
  simp [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    annotatedSourceAdjacentClauseWord,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] theorem flatAnnotatedSourceFieldAt_secondCount
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedSourceFieldAt 5
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      List.replicate secondCount true := by
  simp [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    annotatedSourceAdjacentClauseWord,
    Function.iterate_succ_apply', List.append_assoc]

private def flatAnnotatedSourceUnaryCountField
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatAnnotatedSourceFieldAt offset input ++ [false]

private noncomputable def flatAnnotatedSourceUnaryCountFieldComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSourceUnaryCountField offset) := by
  have physical := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable offset)
    (sourceFixedWordComputable [false])
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceFieldAt offset input ++ [false])
  exact physical

private def flatAnnotatedSourcePairCountQuery
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceUnaryCountField 2 input ++
    flatAnnotatedSourceUnaryCountField 5 input

private noncomputable def flatAnnotatedSourcePairCountQueryComputable :
    BitTM
      flatAnnotatedSourcePairCountQuery := by
  have physical := pointwiseAppendComputable
    (flatAnnotatedSourceUnaryCountFieldComputable 2)
    (flatAnnotatedSourceUnaryCountFieldComputable 5)
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceUnaryCountField 2 input ++
        flatAnnotatedSourceUnaryCountField 5 input)
  exact physical

private def flatAnnotatedSourceMinimumCountWord
    (input : List Bool) : List Bool :=
  cappedUnaryMinimumOutput (flatAnnotatedSourcePairCountQuery input)

private noncomputable def flatAnnotatedSourceMinimumCountComputable :
    BitTM
      flatAnnotatedSourceMinimumCountWord := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSourcePairCountQueryComputable
    actualCappedUnaryMinimumComputable
  change BitTM
    (fun input : List Bool =>
      cappedUnaryMinimumOutput (flatAnnotatedSourcePairCountQuery input))
  exact physical

@[simp] private theorem flatAnnotatedSourceMinimumCountWord_valid
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedSourceMinimumCountWord
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      List.replicate (min firstCount secondCount) true := by
  simp only [flatAnnotatedSourceMinimumCountWord, cappedUnaryMinimumOutput,
      flatAnnotatedSourcePairCountQuery,
      flatAnnotatedSourceUnaryCountField, flatAnnotatedSourceFieldAt_firstCount,
          flatAnnotatedSourceFieldAt_secondCount,
      List.append_assoc, List.cons_append, List.nil_append, readUnaryPrefix_replicate]

/-- GapCVP reduction support. -/
def flatAnnotatedSourceZipCountWord
    (input : List Bool) : List Bool :=
  List.tail (flatAnnotatedSourceMinimumCountWord input)

/-- GapCVP reduction support. -/
noncomputable def flatAnnotatedSourceZipCountComputable :
    BitTM
      flatAnnotatedSourceZipCountWord := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSourceMinimumCountComputable dropHeadComputable
  change BitTM
    (fun input : List Bool =>
      List.tail (flatAnnotatedSourceMinimumCountWord input))
  exact physical

@[simp] theorem flatAnnotatedSourceZipCountWord_valid
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedSourceZipCountWord
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      List.replicate (min firstCount secondCount - 1) true := by
  unfold flatAnnotatedSourceZipCountWord
  rw [flatAnnotatedSourceMinimumCountWord_valid]
  cases hminimum : min firstCount secondCount with
  | zero => simp only [List.replicate_zero, List.tail_nil, zero_tsub]
  | succ minimum =>
      simp only [List.replicate_succ, List.tail_cons, add_tsub_cancel_right]

/-- GapCVP reduction support. -/
def flatAnnotatedSourcePrefixedField
    (offset : ℕ) (input : List Bool) : List Bool :=
  lengthPrefixedWord (flatAnnotatedSourceFieldAt offset input)

/-- GapCVP reduction support. -/
noncomputable def annotatedSourcePrefixedFieldComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSourcePrefixedField offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    structuralPrefixWriterComputable
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord (flatAnnotatedSourceFieldAt offset input))
  exact physical

end CNFAnnotatedSourceClausePairPreparationTM

namespace CNFFlatAdjacentConditionalSwapTM

open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatAdjacentRecordSwapTotalCert

/-- GapCVP reduction support. -/
def flatAdjacentConditionalSwapOutput : List Bool → List Bool
  | true :: input => flatAdjacentRecordSwapOutput input
  | false :: input => input
  | [] => []

private abbrev actualFlatAdjacentConditionalSwapMachine : Turing.FinTM2 where
  K := actualFlatAdjacentRecordSwapMachine.K
  k₀ := actualFlatAdjacentRecordSwapMachine.k₀
  k₁ := actualFlatAdjacentRecordSwapMachine.k₀
  Γ := actualFlatAdjacentRecordSwapMachine.Γ
  Λ := ConditionalLabel actualFlatAdjacentRecordSwapMachine
  main := .inr false
  σ := ConditionalState actualFlatAdjacentRecordSwapMachine
  initialState := (none, none)
  m
    | .inl phase =>
        liftValidStatement actualFlatAdjacentRecordSwapMachine
          (actualFlatAdjacentRecordSwapMachine.m phase)
    | .inr false =>
        .pop 0 (fun state symbol => (symbol, state.2))
          (.branch (fun state => state.1.getD false)
            (.goto (fun _ => .inl (0 : Fin 7)))
            (.load (fun _ => (none, none)) .halt))
    | .inr true =>
        .load (fun _ => (none, none)) .halt

private def flatAdjacentConditionalSwapEmbedded
    (configuration : actualFlatAdjacentRecordSwapMachine.Cfg) :
    actualFlatAdjacentConditionalSwapMachine.Cfg where
  l := configuration.l.map Sum.inl
  var :=
    (if configuration.l.isSome then some true else none,
      configuration.var)
  stk := configuration.stk

private theorem flatAdjacentConditionalSwapEmbedded_step
    (configuration next : actualFlatAdjacentRecordSwapMachine.Cfg)
    (hstep : actualFlatAdjacentRecordSwapMachine.step configuration =
      some next) :
    actualFlatAdjacentConditionalSwapMachine.step
      (flatAdjacentConditionalSwapEmbedded configuration) =
      some (flatAdjacentConditionalSwapEmbedded next) := by
  rcases configuration with ⟨label, state, sourceStacks⟩
  cases label with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at hstep
  | some label =>
      change some
        (Turing.TM2.stepAux
          (actualFlatAdjacentRecordSwapMachine.m label)
          state sourceStacks) = some next at hstep
      have hnext := Option.some.inj hstep
      subst next
      change some
        (Turing.TM2.stepAux
          (liftValidStatement flatAdjacentRecordSwapComputable.tm
            (flatAdjacentRecordSwapComputable.tm.m label))
          (some true, state) sourceStacks) =
        some (validConfiguration flatAdjacentRecordSwapComputable []
          (Turing.TM2.stepAux
            (flatAdjacentRecordSwapComputable.tm.m label)
            state sourceStacks))
      rw [liftValidStatement_stepAux
        flatAdjacentRecordSwapComputable []]
      rfl

private theorem flatAdjacentConditionalSwap_start_true
    (input : List Bool) :
    actualFlatAdjacentConditionalSwapMachine.step
      (Turing.initList actualFlatAdjacentConditionalSwapMachine
        (true :: input)) =
      some (flatAdjacentConditionalSwapEmbedded
        (Turing.initList actualFlatAdjacentRecordSwapMachine input)) := by
  compactMachineStepTac [actualFlatAdjacentConditionalSwapMachine,
    flatAdjacentConditionalSwapEmbedded, actualFlatAdjacentRecordSwapMachine, Turing.initList]

private theorem flatAdjacentConditionalSwap_start_false
    (input : List Bool) :
    actualFlatAdjacentConditionalSwapMachine.step
      (Turing.initList actualFlatAdjacentConditionalSwapMachine
        (false :: input)) =
      some (Turing.haltList
        actualFlatAdjacentConditionalSwapMachine input) := by
  compactMachineStepTac [actualFlatAdjacentConditionalSwapMachine, Turing.initList]

private theorem flatAdjacentConditionalSwap_start_missing :
    actualFlatAdjacentConditionalSwapMachine.step
      (Turing.initList actualFlatAdjacentConditionalSwapMachine []) =
      some (Turing.haltList
        actualFlatAdjacentConditionalSwapMachine []) := by
  compactMachineStepTac [actualFlatAdjacentConditionalSwapMachine, Turing.initList]

private theorem flatAdjacentConditionalSwapEmbedded_halt
    (output : List Bool) :
    flatAdjacentConditionalSwapEmbedded
      (Turing.haltList actualFlatAdjacentRecordSwapMachine output) =
      Turing.haltList actualFlatAdjacentConditionalSwapMachine output := by
  rfl

private def flatAdjacentConditionalSwapTimePolynomial : Polynomial ℕ :=
  flatAdjacentRecordSwapTimePolynomial + 1

private noncomputable def flatAdjacentConditionalSwap_totalTrace
    (input : List Bool) :
    EvalsToInTime actualFlatAdjacentConditionalSwapMachine.step
      (Turing.initList actualFlatAdjacentConditionalSwapMachine input)
      (some (Turing.haltList actualFlatAdjacentConditionalSwapMachine
        (flatAdjacentConditionalSwapOutput input)))
      (flatAdjacentConditionalSwapTimePolynomial.eval input.length) := by
  cases input with
  | nil =>
      have hphysical := oneStep _ _ flatAdjacentConditionalSwap_start_missing
      refine {
        steps := hphysical.steps
        evals_in_steps := ?_
        steps_le_m := ?_
      }
      · simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue,
          flatAdjacentConditionalSwapOutput] using
            hphysical.evals_in_steps
      · simp [flatAdjacentConditionalSwapTimePolynomial,
          flatAdjacentRecordSwapTimePolynomial,
          Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_ofNat]
          at hphysical ⊢
        have hsteps := hphysical.steps_le_m
        omega
  | cons marker remaining =>
      cases marker with
      | false =>
          have hphysical := oneStep _ _ (flatAdjacentConditionalSwap_start_false remaining)
          refine {
            steps := hphysical.steps
            evals_in_steps := ?_
            steps_le_m := ?_
          }
          · simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue,
              flatAdjacentConditionalSwapOutput] using
                hphysical.evals_in_steps
          · simp [flatAdjacentConditionalSwapTimePolynomial,
              flatAdjacentRecordSwapTimePolynomial,
              Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_X, Polynomial.eval_ofNat]
              at hphysical ⊢
            have hsteps := hphysical.steps_le_m
            omega
      | true =>
          have hstart := oneStep _ _ (flatAdjacentConditionalSwap_start_true remaining)
          have horiginal := flatAdjacentRecordTotalTrace remaining
          rw [← actualFlatAdjacentRecordSwapMachine_init] at horiginal
          have hvalid :=
            GapCVP.TMComposition.evalsToInTimeMapOfStep
              actualFlatAdjacentRecordSwapMachine.step
              actualFlatAdjacentConditionalSwapMachine.step
              flatAdjacentConditionalSwapEmbedded
              flatAdjacentConditionalSwapEmbedded_step horiginal
          rw [flatAdjacentConditionalSwapEmbedded_halt] at hvalid
          have hfull := EvalsToInTime.trans actualFlatAdjacentConditionalSwapMachine.step
            _ _ _ _ _ hstart hvalid
          refine {
            steps := hfull.steps
            evals_in_steps := ?_
            steps_le_m := ?_
          }
          · simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue,
              flatAdjacentConditionalSwapOutput] using
                hfull.evals_in_steps
          · have hsteps := hfull.steps_le_m
            simp [flatAdjacentConditionalSwapTimePolynomial,
              flatAdjacentRecordSwapTimePolynomial,
              Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_X, Polynomial.eval_ofNat]
              at hsteps ⊢
            omega

/-- GapCVP reduction support. -/
noncomputable def flatAdjacentConditionalSwapComputable :
    BitTM
      flatAdjacentConditionalSwapOutput where
  tm := actualFlatAdjacentConditionalSwapMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := flatAdjacentConditionalSwapTimePolynomial
  outputsFun input := {
    steps := (flatAdjacentConditionalSwap_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, Option.map_some] using
          (flatAdjacentConditionalSwap_totalTrace input).evals_in_steps
    steps_le_m := by
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq] using
          (flatAdjacentConditionalSwap_totalTrace input).steps_le_m
  }

end CNFFlatAdjacentConditionalSwapTM

namespace CNFGuardedFiveFamilyTagDispatchTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CNFEncodedClauseSort

/-- GapCVP reduction support. -/
def keepFirstDropSecondWord : List Bool → List Bool
  | [] => []
  | bit :: remaining => bit :: remaining.tail

private abbrev keepFirstDropSecondMachine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    .peek () (fun _ inspected => inspected)
      (.pop () (fun state _ => state)
        (.pop () (fun state _ => state)
          (.branch (fun state => state.isSome)
            (.push () (fun state => state.getD false)
              (.load (fun _ => none) .halt))
            (.load (fun _ => none) .halt))))

private theorem keepFirstDropSecondMachine_step
    (input : List Bool) :
    keepFirstDropSecondMachine.step
      (Turing.initList keepFirstDropSecondMachine input) =
      some (Turing.haltList keepFirstDropSecondMachine
        (keepFirstDropSecondWord input)) := by
  cases input with
  | nil =>
      simp only [keepFirstDropSecondMachine, FinTM2.step, TM2.step, initList, ↓reduceDIte,
          eq_mpr_eq_cast, cast_eq,
          TM2.stepAux, List.head?_nil, Option.isSome_none, List.tail_nil, Function.update_eq_self,
              Function.update_self,
          Option.getD_none, Bool.cond_false, haltList, keepFirstDropSecondWord]
      rfl
  | cons bit remaining =>
      cases remaining with
      | nil =>
          simp only [keepFirstDropSecondMachine, FinTM2.step, TM2.step, initList, ↓reduceDIte,
              eq_mpr_eq_cast, cast_eq,
              TM2.stepAux, List.head?_cons, Option.isSome_some, List.tail_cons,
                  Function.update_self, List.tail_nil,
              Function.update_idem, Option.getD_some, Function.update_eq_self, Bool.cond_true,
                  haltList,
                  keepFirstDropSecondWord]
          rfl
      | cons next remaining =>
          simp only [keepFirstDropSecondMachine, FinTM2.step, TM2.step, initList, ↓reduceDIte,
              eq_mpr_eq_cast, cast_eq,
              TM2.stepAux, List.head?_cons, Option.isSome_some, List.tail_cons,
                  Function.update_self, Function.update_idem,
              Option.getD_some, Bool.cond_true, haltList, keepFirstDropSecondWord]
          congr 2

/-- GapCVP reduction support. -/
noncomputable def keepFirstDropSecondComputable :
    BitTM
      keepFirstDropSecondWord where
  tm := keepFirstDropSecondMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun input := {
    steps := 1
    evals_in_steps := by
      rw [Function.iterate_one]
      rw [Option.bind_eq_bind]
      simp only [flip]
      rw [Option.bind_some]
      simpa only [FinTM2.step,
          Equiv.invFun_as_coe, Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun,
          Option.map_some] using keepFirstDropSecondMachine_step input
    steps_le_m := by simp only [id_eq, Polynomial.eval_one, Std.le_refl]
  }

/-- GapCVP reduction support. -/
def encodedOrderingEqualityBitWord : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput (fun bits => false :: bits) [true])
    [false]

/-- GapCVP reduction support. -/
noncomputable def encodedOrderingEqualityBitComputable :
    BitTM
      encodedOrderingEqualityBitWord :=
  markerConditionalComputable
    (markerConditionalComputable
      (prependBitComputable false) [true]) [false]

@[simp] theorem encodedOrderingEqualityBitWord_ordering
    (outcome : EncodedWordOrdering) :
    encodedOrderingEqualityBitWord
      (encodedWordOrderingWord outcome) =
      [decide (outcome = .equal)] := by
  cases outcome <;>
    rfl

private def fixedDelimitedWordOrderingWord
    (expected : List Bool) (input : List Bool) : List Bool :=
  firstFieldSuffix
    (sourcePreservingDelimitedPairComparisonWord
      (lengthPrefixedWord expected ++ input))

private noncomputable def fixedDelimitedWordOrderingComputable
    (expected : List Bool) :
    BitTM
      (fixedDelimitedWordOrderingWord expected) := by
  have hcompare := GapCVP.TMComposition.computableInPolyTime
    (prependWordComputable (lengthPrefixedWord expected))
    sourcePreservingDelimitedPairComparisonComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hcompare firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix
        (sourcePreservingDelimitedPairComparisonWord
          (lengthPrefixedWord expected ++ input)))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def fixedDelimitedWordEqualityBitWord
    (expected : List Bool) (input : List Bool) : List Bool :=
  encodedOrderingEqualityBitWord
    (fixedDelimitedWordOrderingWord expected input)

/-- GapCVP reduction support. -/
noncomputable def fixedDelimitedWordEqualityBitComputable
    (expected : List Bool) :
    BitTM
      (fixedDelimitedWordEqualityBitWord expected) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (fixedDelimitedWordOrderingComputable expected)
    encodedOrderingEqualityBitComputable
  change BitTM
    (fun input : List Bool =>
      encodedOrderingEqualityBitWord
        (fixedDelimitedWordOrderingWord expected input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def fixedDelimitedWordEqualitySelector
    (expected : List Bool) (input : List Bool) : Bool :=
  decide
    (delimitedPairWordOrdering
      (lengthPrefixedWord expected ++ input) = .equal)

@[simp] theorem fixedDelimitedWordEqualityBitWord_eq
    (expected input : List Bool) :
    fixedDelimitedWordEqualityBitWord expected input =
      [fixedDelimitedWordEqualitySelector expected input] := by
  unfold fixedDelimitedWordEqualityBitWord
    fixedDelimitedWordOrderingWord
    fixedDelimitedWordEqualitySelector
  simp only [sourcePreservingDelimitedPairComparisonWord,
    firstFieldSuffix_valid]
  exact encodedOrderingEqualityBitWord_ordering _

@[simp] theorem fixedDelimitedWordEqualitySelector_valid
    (expected actual suffix : List Bool) :
    fixedDelimitedWordEqualitySelector expected
      (lengthPrefixedWord actual ++ suffix) =
      decide (expected = actual) := by
  unfold fixedDelimitedWordEqualitySelector
  simp only [delimitedPairWordOrdering,
    readLengthPrefixedWord_append]
  simp only [lexicographicEncodedWordOrdering_eq_equal_iff]

private def fixedDelimitedWordEqualitySelectionWord
    (expected : List Bool) (input : List Bool) : List Bool :=
  fixedDelimitedWordEqualitySelector expected input :: input

private noncomputable def fixedDelimitedWordEqualitySelectionComputable
    (expected : List Bool) :
    BitTM
      (fixedDelimitedWordEqualitySelectionWord expected) := by
  have hpreserved := originalSourcePreservingComputable
    (fixedDelimitedWordEqualityBitComputable expected)
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved keepFirstDropSecondComputable
  have hequality :
      (fun input : List Bool =>
        keepFirstDropSecondWord
          (originalSourcePreservingOutput
            (fixedDelimitedWordEqualityBitWord expected) input)) =
        fixedDelimitedWordEqualitySelectionWord expected := by
    funext input
    simp only [keepFirstDropSecondWord, originalSourcePreservingOutput,
        fixedDelimitedWordEqualityBitWord_eq,
        List.cons_append, List.nil_append, List.tail_cons, fixedDelimitedWordEqualitySelectionWord]
  rw [← hequality]
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def fixedDelimitedGuardedWorkerWord
    (expected : List Bool) (worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  if fixedDelimitedWordEqualitySelector expected input
    then worker input
    else []

/-- GapCVP reduction support. -/
noncomputable def fixedDelimitedGuardedWorkerComputable
    (expected : List Bool)
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (fixedDelimitedGuardedWorkerWord expected worker) := by
  exact sourcePreservingConditionalComputable
    (fixedDelimitedWordEqualitySelectionComputable expected)
    computer []

end CNFGuardedFiveFamilyTagDispatchTM

namespace CNFFlatCappedComparisonControlledSwapTM

open Turing GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatAdjacentConditionalSwapTM

private def flatEncodedOrderingGreaterBitWord : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput (fun _ => [true]) [false])
    [false]

private noncomputable def flatEncodedOrderingGreaterBitComputable :
    BitTM
      flatEncodedOrderingGreaterBitWord :=
  markerConditionalComputable
    (markerConditionalComputable
      (sourceFixedWordComputable [true]) [false])
    [false]

@[simp] private theorem flatEncodedOrderingGreaterBitWord_eq
    (input : List Bool) :
    flatEncodedOrderingGreaterBitWord input =
      [input.headD false && input.tail.headD false] := by
  cases input with
  | nil => rfl
  | cons first remaining =>
      cases first with
      | false => rfl
      | true =>
          cases remaining with
          | nil => rfl
          | cons second suffix =>
              cases second <;> rfl

/-- GapCVP reduction support. -/
def flatComparisonGreaterMarker
    (comparison : List Bool → List Bool)
    (input : List Bool) : Bool :=
  let outcome := firstFieldSuffix (comparison input)
  outcome.headD false && outcome.tail.headD false

private def flatComparisonGreaterSelectionWord
    (comparison : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  flatComparisonGreaterMarker comparison input :: input

private noncomputable def flatComparisonGreaterSelectionComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatComparisonGreaterSelectionWord comparison) := by
  have houtcome := GapCVP.TMComposition.computableInPolyTime
    computer firstFieldSuffixComputable
  have hmarker := GapCVP.TMComposition.computableInPolyTime
    houtcome flatEncodedOrderingGreaterBitComputable
  have hpreserved := originalSourcePreservingComputable hmarker
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved keepFirstDropSecondComputable
  change BitTM
    (fun input => flatComparisonGreaterMarker comparison input :: input)
  have hequality :
      (fun input : List Bool =>
        keepFirstDropSecondWord
          (originalSourcePreservingOutput
            (fun source => flatEncodedOrderingGreaterBitWord
              (firstFieldSuffix (comparison source))) input)) =
        (fun input =>
          flatComparisonGreaterMarker comparison input :: input) := by
    funext input
    simp only [keepFirstDropSecondWord, originalSourcePreservingOutput,
        flatEncodedOrderingGreaterBitWord_eq,
        List.headD_eq_head?_getD, List.head?_tail, List.cons_append, List.nil_append,
            List.tail_cons,
        flatComparisonGreaterMarker]
  rw [← hequality]
  simpa only [flatEncodedOrderingGreaterBitWord_eq, List.headD_eq_head?_getD, List.head?_tail,
      Function.comp_def] using hphysical

private def flatAdjacentComparisonControlledSwapWord
    (comparison : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  flatAdjacentConditionalSwapOutput
    (flatComparisonGreaterSelectionWord comparison input)

private noncomputable def flatAdjacentComparisonControlledSwapComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatAdjacentComparisonControlledSwapWord comparison) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (flatComparisonGreaterSelectionComputable computer)
    flatAdjacentConditionalSwapComputable
  change BitTM
    (fun input => flatAdjacentConditionalSwapOutput
      (flatComparisonGreaterSelectionWord comparison input))
  simpa only [Function.comp_def] using hphysical

private theorem flatAdjacentComparisonControlledSwapWord_eq
    (comparison : List Bool → List Bool) (input : List Bool) :
    flatAdjacentComparisonControlledSwapWord comparison input =
      if flatComparisonGreaterMarker comparison input then
        flatAdjacentRecordSwapOutput input
      else input := by
  unfold flatAdjacentComparisonControlledSwapWord
    flatComparisonGreaterSelectionWord
  cases flatComparisonGreaterMarker comparison input <;> rfl

private theorem flatAdjacentComparisonControlledSwapWord_length_le
    (comparison : List Bool → List Bool) (input : List Bool) :
    (flatAdjacentComparisonControlledSwapWord
      comparison input).length ≤ input.length := by
  rw [flatAdjacentComparisonControlledSwapWord_eq]
  split
  · exact flatAdjacentRecordSwapOutput_length_le input
  · exact Nat.le_refl _

end CNFFlatCappedComparisonControlledSwapTM

namespace CNFAnnotatedSourceClauseBubblePassTM

open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFGuardedSourceDescriptorRotationBoundedFoldTM
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatCappedComparisonControlledSwapTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

/-- GapCVP reduction support. -/
def flatAnnotatedBundledClauseRecord {T S : ℕ}
    (clause : Clause T S) : List Bool :=
  lengthPrefixedWord (flatSourceClauseAnnotatedRecord clause)

/-- GapCVP reduction support. -/
def flatAnnotatedBundledClauseStream {T S : ℕ}
    (clauses : List (Clause T S)) : List Bool :=
  clauses.flatMap flatAnnotatedBundledClauseRecord

/-- GapCVP reduction support. -/
def annotatedBundledPairComparisonInput
    (input : List Bool) : List Bool :=
  firstFieldContents input ++
    firstFieldContents (firstFieldSuffix input)

private noncomputable def flatAnnotatedBundledPairComparisonInputComputable :
    BitTM
      annotatedBundledPairComparisonInput := by
  have hsecond := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  have physical := pointwiseAppendComputable
    firstFieldContentsComputable hsecond
  change BitTM
    (fun input : List Bool =>
      firstFieldContents input ++
        firstFieldContents (firstFieldSuffix input))
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def annotatedBundledPairComparisonWord
    (comparison : List Bool → List Bool) (input : List Bool) : List Bool :=
  comparison (annotatedBundledPairComparisonInput input)

/-- GapCVP reduction support. -/
noncomputable def flatAnnotatedBundledPairComparisonComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (annotatedBundledPairComparisonWord comparison) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedBundledPairComparisonInputComputable computer
  change BitTM
    (fun input : List Bool =>
      comparison (annotatedBundledPairComparisonInput input))
  simpa only [Function.comp_def] using physical

theorem flatAnnotatedBundledPairComparisonInput_records
    {T S : ℕ} (first second : Clause T S) (suffix : List Bool) :
    annotatedBundledPairComparisonInput
      (flatAnnotatedBundledClauseRecord first ++
        flatAnnotatedBundledClauseRecord second ++ suffix) =
      flatSourceClauseAnnotatedRecord first ++
        flatSourceClauseAnnotatedRecord second := by
  simp only [annotatedBundledPairComparisonInput, flatAnnotatedBundledClauseRecord,
      List.append_assoc,
      firstFieldContents_valid, firstFieldSuffix_valid]

/-- GapCVP reduction support. -/
def flatAnnotatedBubblePassState
    (active emitted : List Bool) : List Bool :=
  lengthPrefixedWord active ++ lengthPrefixedWord emitted

private def flatAnnotatedBubbleActiveSwap
    (comparison : List Bool → List Bool) (input : List Bool) : List Bool :=
  flatAdjacentComparisonControlledSwapWord
    (annotatedBundledPairComparisonWord comparison)
    (firstFieldContents input)

private noncomputable def flatAnnotatedBubbleActiveSwapComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatAnnotatedBubbleActiveSwap comparison) := by
  have hswap := flatAdjacentComparisonControlledSwapComputable
    (flatAnnotatedBundledPairComparisonComputable computer)
  have physical := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable hswap
  change BitTM
    (fun input : List Bool =>
      flatAdjacentComparisonControlledSwapWord
        (annotatedBundledPairComparisonWord comparison)
        (firstFieldContents input))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedBubbleRemaining
    (comparison : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldSuffix (flatAnnotatedBubbleActiveSwap comparison input)

private noncomputable def flatAnnotatedBubbleRemainingComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatAnnotatedBubbleRemaining comparison) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedBubbleActiveSwapComputable computer)
    firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix (flatAnnotatedBubbleActiveSwap comparison input))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedBubbleSelected
    (comparison : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (firstFieldContents (flatAnnotatedBubbleActiveSwap comparison input))

private noncomputable def flatAnnotatedBubbleSelectedComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatAnnotatedBubbleSelected comparison) := by
  have hcontents := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedBubbleActiveSwapComputable computer)
    firstFieldContentsComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hcontents structuralPrefixWriterComputable
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord
        (firstFieldContents
          (flatAnnotatedBubbleActiveSwap comparison input)))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedBubbleNextArchive
    (comparison : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix input) ++
    flatAnnotatedBubbleSelected comparison input

private noncomputable def flatAnnotatedBubbleNextArchiveComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatAnnotatedBubbleNextArchive comparison) := by
  have harchive := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  have physical := pointwiseAppendComputable harchive
    (flatAnnotatedBubbleSelectedComputable computer)
  change BitTM
    (fun input : List Bool =>
      firstFieldContents (firstFieldSuffix input) ++
        flatAnnotatedBubbleSelected comparison input)
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def flatAnnotatedBubblePassStep
    (comparison : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (flatAnnotatedBubbleRemaining comparison input) ++
    lengthPrefixedWord (flatAnnotatedBubbleNextArchive comparison input)

private noncomputable def flatAnnotatedBubblePassStepComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (flatAnnotatedBubblePassStep comparison) := by
  have hremaining := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedBubbleRemainingComputable computer)
    structuralPrefixWriterComputable
  have harchive := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedBubbleNextArchiveComputable computer)
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable hremaining harchive
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord
          (flatAnnotatedBubbleRemaining comparison input) ++
        lengthPrefixedWord
          (flatAnnotatedBubbleNextArchive comparison input))
  simpa only [Function.comp_def] using physical

theorem annotatedStructuralFieldAccounting
    (input : List Bool) :
    2 * (firstFieldContents input).length +
      (firstFieldSuffix input).length ≤ input.length := by
  cases hread : readLengthPrefixedWord input with
  | none =>
      simp only [firstFieldContents, payloadDecodeOutput, hread, List.tail_cons, List.length_nil,
          mul_zero,
          firstFieldSuffix, add_zero, zero_le]
  | some parsed =>
      obtain ⟨payload, suffix⟩ := parsed
      have hshape :=
        guardedRotation_readLengthPrefixedWord_some_reconstruct
          input payload suffix hread
      simp only [firstFieldContents, payloadDecodeOutput,
        firstFieldSuffix, hread, List.tail_cons]
      rw [hshape]
      simp only [List.length_append, lengthPrefixedWord_length, add_le_add_iff_right,
          le_add_iff_nonneg_right,
          zero_le]

theorem annotatedStructuralTwoFieldAccounting
    (input : List Bool) :
    2 * (firstFieldContents input).length +
      2 * (firstFieldContents (firstFieldSuffix input)).length ≤
        input.length := by
  have hfirst := annotatedStructuralFieldAccounting input
  have hsecond :=
    annotatedStructuralFieldAccounting (firstFieldSuffix input)
  omega

private theorem flatAnnotatedBubblePassStep_length_le
    (comparison : List Bool → List Bool)
    (input : List Bool) :
    (flatAnnotatedBubblePassStep comparison input).length ≤
      input.length + 4 := by
  have hswap := flatAdjacentComparisonControlledSwapWord_length_le
    (annotatedBundledPairComparisonWord comparison)
    (firstFieldContents input)
  have hswapFields := annotatedStructuralFieldAccounting
    (flatAnnotatedBubbleActiveSwap comparison input)
  have hsourceFields := annotatedStructuralTwoFieldAccounting input
  change
    (lengthPrefixedWord
        (firstFieldSuffix
          (flatAnnotatedBubbleActiveSwap comparison input)) ++
      lengthPrefixedWord
        (firstFieldContents (firstFieldSuffix input) ++
          lengthPrefixedWord
            (firstFieldContents
              (flatAnnotatedBubbleActiveSwap comparison input)))).length ≤
      input.length + 4
  simp only [List.length_append, lengthPrefixedWord_length]
  change
    (flatAnnotatedBubbleActiveSwap comparison input).length ≤
      (firstFieldContents input).length at hswap
  omega

theorem flatAnnotatedBubblePassStep_iterate_length_le
    (comparison : List Bool → List Bool)
    (input : List Bool) (count : ℕ) :
    (((flatAnnotatedBubblePassStep comparison)^[count]) input).length ≤
      input.length + 4 * count := by
  induction count with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      have hstep := flatAnnotatedBubblePassStep_length_le comparison
        (((flatAnnotatedBubblePassStep comparison)^[count]) input)
      simp only [Nat.mul_succ]
      omega

private theorem flatAnnotatedBubblePass_polynomiallyBoundedFoldStates
    (comparison : List Bool → List Bool) :
    PolynomiallyBoundedFoldStates
      (flatAnnotatedBubblePassStep comparison)
      (5 * Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := parsedUnaryFold_seed_length_le input count seed hparse
  have hcount := parsedUnaryFold_count_le_length input count seed hparse
  have hiterate := flatAnnotatedBubblePassStep_iterate_length_le
    comparison seed stage
  have hstage' : stage ≤ input.length := hstage.trans hcount
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

/-- GapCVP reduction support. -/
noncomputable def flatAnnotatedBubblePassFoldComputable
    {comparison : List Bool → List Bool}
    (computer : BitTM comparison) :
    BitTM
      (boundedRecordFoldOutput
        (flatAnnotatedBubblePassStep comparison)) :=
  boundedDependentRecordFoldComputable
    (flatAnnotatedBubblePassStepComputable computer)
    (5 * Polynomial.X)
    (flatAnnotatedBubblePass_polynomiallyBoundedFoldStates comparison)

/-- GapCVP reduction support. -/
def flatAnnotatedBubbleClauseState {T S : ℕ}
    (active emitted : List (Clause T S)) : List Bool :=
  flatAnnotatedBubblePassState
    (flatAnnotatedBundledClauseStream active)
    (flatAnnotatedBundledClauseStream emitted)

/-- GapCVP reduction support. -/
noncomputable def CorrectFlatAnnotatedBundledSourceComparison
    (comparison : List Bool → List Bool) : Bool :=
  @decide (
  ∀ {T S : ℕ} (first second : Clause T S) (suffix : List Bool),
    flatComparisonGreaterMarker
      (annotatedBundledPairComparisonWord comparison)
      (flatAnnotatedBundledClauseRecord first ++
        flatAnnotatedBundledClauseRecord second ++ suffix) =
      decide (Encodable.encode second < Encodable.encode first)
  ) (Classical.propDecidable _)
@[simp] theorem flatAnnotatedBubblePassStep_clauseState
    {comparison : List Bool → List Bool}
    (hcomparison : CorrectFlatAnnotatedBundledSourceComparison comparison)
    {T S : ℕ} (first second : Clause T S)
    (remaining emitted : List (Clause T S)) :
    flatAnnotatedBubblePassStep comparison
        (flatAnnotatedBubbleClauseState
          (first :: second :: remaining) emitted) =
      if Encodable.encode second < Encodable.encode first then
        flatAnnotatedBubbleClauseState
          (first :: remaining) (emitted ++ [second])
      else
        flatAnnotatedBubbleClauseState
          (second :: remaining) (emitted ++ [first]) := by
  have comparison := hcomparison
  simp only [CorrectFlatAnnotatedBundledSourceComparison,
    decide_eq_true_eq] at comparison
  have hmarker := comparison first second
    (flatAnnotatedBundledClauseStream remaining)
  have hemit :
      firstFieldContents
          (lengthPrefixedWord
            (emitted.flatMap flatAnnotatedBundledClauseRecord)) =
        emitted.flatMap flatAnnotatedBundledClauseRecord := by
    simpa only [List.append_nil] using
        firstFieldContents_valid (emitted.flatMap flatAnnotatedBundledClauseRecord) []
  simp only [flatAnnotatedBundledClauseStream,
    flatAnnotatedBundledClauseRecord, List.append_assoc]
    at hmarker
  unfold flatAnnotatedBubblePassStep
    flatAnnotatedBubbleRemaining flatAnnotatedBubbleNextArchive
    flatAnnotatedBubbleSelected flatAnnotatedBubbleActiveSwap
    flatAnnotatedBubbleClauseState flatAnnotatedBubblePassState
  simp only [flatAnnotatedBundledClauseStream, List.flatMap_cons,
    firstFieldContents_valid, firstFieldSuffix_valid,
    flatAdjacentComparisonControlledSwapWord_eq]
  by_cases horder : Encodable.encode second < Encodable.encode first
  · simp only [flatAnnotatedBundledClauseRecord, hmarker, horder, decide_true, ↓reduceIte,
        flatAdjacentRecordSwapOutput, readLengthPrefixedWord_append, List.append_assoc,
            firstFieldSuffix_valid, hemit,
        firstFieldContents_valid, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
  · simp only [flatAnnotatedBundledClauseRecord, hmarker, horder, decide_false, Bool.false_eq_true,
      ↓reduceIte,
        firstFieldSuffix_valid, hemit, firstFieldContents_valid, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil,
        List.append_nil]

end CNFAnnotatedSourceClauseBubblePassTM

namespace SourceUnaryIntegerMultiplicationTM

section

open Turing GapCVP.BinaryEncoding

/-- GapCVP reduction support. -/
def sourceUnaryIntegerMultiplicationQuery
    (left right : ℕ) : List Bool :=
  List.replicate left true ++ false :: List.replicate right true

/-- GapCVP reduction support. -/
def sourceUnaryIntegerMultiplicationOutput
    (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => []
  | some (left, right) =>
      if right.all (fun bit => bit) then
        List.replicate (left * right.length) true
      else []

@[simp] theorem sourceUnaryIntegerMultiplicationOutput_query
    (left right : ℕ) :
    sourceUnaryIntegerMultiplicationOutput
        (sourceUnaryIntegerMultiplicationQuery left right) =
      List.replicate (left * right) true := by
  simp only [sourceUnaryIntegerMultiplicationOutput, sourceUnaryIntegerMultiplicationQuery,
      readUnaryPrefix_replicate, List.all_replicate, ite_self, ↓reduceIte, List.length_replicate]

private def sourceIntegerMultiplicationPeek (stack : Fin 5)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def sourceIntegerMultiplicationPop (stack : Fin 5)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  .pop stack (fun current _ => current) next

private def sourceIntegerMultiplicationPush (stack : Fin 5)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  .push stack (fun _ => true) next

private def sourceIntegerMultiplicationGoto (phase : Fin 11) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationLeftStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 0
    (.branch (fun symbol => symbol.getD false)
      (sourceIntegerMultiplicationPop 0
        (sourceIntegerMultiplicationPush 1
          (sourceIntegerMultiplicationGoto 0)))
      (sourceIntegerMultiplicationPop 0
        (sourceIntegerMultiplicationGoto 1)))
    (sourceIntegerMultiplicationGoto 6)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationRightStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 0
    (.branch (fun symbol => symbol.getD false)
      (sourceIntegerMultiplicationPop 0
        (sourceIntegerMultiplicationPush 2
          (sourceIntegerMultiplicationGoto 1)))
      (sourceIntegerMultiplicationPop 0
        (sourceIntegerMultiplicationGoto 6)))
    (sourceIntegerMultiplicationGoto 2)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationOuterStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 1
    (sourceIntegerMultiplicationPop 1
      (sourceIntegerMultiplicationGoto 3))
    (sourceIntegerMultiplicationGoto 5)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationCopyStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 2
    (sourceIntegerMultiplicationPop 2
      (sourceIntegerMultiplicationPush 3
        (sourceIntegerMultiplicationPush 4
          (sourceIntegerMultiplicationGoto 3))))
    (sourceIntegerMultiplicationGoto 4)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 3
    (sourceIntegerMultiplicationPop 3
      (sourceIntegerMultiplicationPush 2
        (sourceIntegerMultiplicationGoto 4)))
    (sourceIntegerMultiplicationGoto 2)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationSuccessCleanupStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 2
    (sourceIntegerMultiplicationPop 2
      (sourceIntegerMultiplicationGoto 5))
    (.load (fun _ => none) .halt)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationFailureInputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 0
    (sourceIntegerMultiplicationPop 0
      (sourceIntegerMultiplicationGoto 6))
    (sourceIntegerMultiplicationGoto 7)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationFailureLeftStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 1
    (sourceIntegerMultiplicationPop 1
      (sourceIntegerMultiplicationGoto 7))
    (sourceIntegerMultiplicationGoto 8)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationFailureRightStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 2
    (sourceIntegerMultiplicationPop 2
      (sourceIntegerMultiplicationGoto 8))
    (sourceIntegerMultiplicationGoto 9)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationFailureRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 3
    (sourceIntegerMultiplicationPop 3
      (sourceIntegerMultiplicationGoto 9))
    (sourceIntegerMultiplicationGoto 10)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationFailureOutputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 11) (Option Bool) :=
  sourceIntegerMultiplicationPeek 4
    (sourceIntegerMultiplicationPop 4
      (sourceIntegerMultiplicationGoto 10))
    (.load (fun _ => none) .halt)

/-- Internal support shared across GapCVP continuation modules. -/
abbrev sourceUnaryIntegerMultiplicationMachine : Turing.FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Fin 11
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 11) then
      sourceIntegerMultiplicationLeftStatement
    else if phase = (1 : Fin 11) then
      sourceIntegerMultiplicationRightStatement
    else if phase = (2 : Fin 11) then
      sourceIntegerMultiplicationOuterStatement
    else if phase = (3 : Fin 11) then
      sourceIntegerMultiplicationCopyStatement
    else if phase = (4 : Fin 11) then
      sourceIntegerMultiplicationRestoreStatement
    else if phase = (5 : Fin 11) then
      sourceIntegerMultiplicationSuccessCleanupStatement
    else if phase = (6 : Fin 11) then
      sourceIntegerMultiplicationFailureInputStatement
    else if phase = (7 : Fin 11) then
      sourceIntegerMultiplicationFailureLeftStatement
    else if phase = (8 : Fin 11) then
      sourceIntegerMultiplicationFailureRightStatement
    else if phase = (9 : Fin 11) then
      sourceIntegerMultiplicationFailureRestoreStatement
    else
      sourceIntegerMultiplicationFailureOutputStatement

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIntegerMultiplicationConfiguration
    (phase : Fin 11)
    (input left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, left, right, restore, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryIntegerMultiplicationMachine_init
    (input : List Bool) :
    Turing.initList sourceUnaryIntegerMultiplicationMachine input =
      sourceIntegerMultiplicationConfiguration
        0 input [] [] [] [] := by
  simp only [sourceUnaryIntegerMultiplicationMachine, Fin.isValue, initList, eq_mpr_eq_cast,
      cast_eq,
      dite_eq_ite, sourceIntegerMultiplicationConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `sourceIntegerMultiplicationStepTac` machine-step simplifier. -/
macro "sourceIntegerMultiplicationStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [sourceUnaryIntegerMultiplicationMachine,
          sourceIntegerMultiplicationConfiguration,
          sourceIntegerMultiplicationPeek,
          sourceIntegerMultiplicationPop,
          sourceIntegerMultiplicationPush,
          sourceIntegerMultiplicationGoto,
          sourceIntegerMultiplicationLeftStatement,
          sourceIntegerMultiplicationRightStatement,
          sourceIntegerMultiplicationOuterStatement,
          sourceIntegerMultiplicationCopyStatement,
          sourceIntegerMultiplicationRestoreStatement,
          sourceIntegerMultiplicationSuccessCleanupStatement,
          sourceIntegerMultiplicationFailureInputStatement,
          sourceIntegerMultiplicationFailureLeftStatement,
          sourceIntegerMultiplicationFailureRightStatement,
          sourceIntegerMultiplicationFailureRestoreStatement,
          sourceIntegerMultiplicationFailureOutputStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
         try { congr 2; funext stack; fin_cases stack <;>
           (first | rfl | simp [Function.update]) } <;>
         try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_left_true
    (input left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 0
        (true :: input) left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 0
        input (true :: left) right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_left_delimiter
    (input left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 0
        (false :: input) left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 1
        input left right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_left_missing
    (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 0
        [] left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 6
        [] left right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_right_true
    (input left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 1
        (true :: input) left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 1
        input left (true :: right) restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_right_false
    (input left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 1
        (false :: input) left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 6
        input left right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_right_finish
    (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 1
        [] left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 2
        [] left right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_outer_step
    (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 2
        [] (true :: left) right restore output) =
      some (sourceIntegerMultiplicationConfiguration 3
        [] left right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_outer_finish
    (right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 2
        [] [] right restore output) =
      some (sourceIntegerMultiplicationConfiguration 5
        [] [] right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_copy_step
    (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 3
        [] left (true :: right) restore output) =
      some (sourceIntegerMultiplicationConfiguration 3
        [] left right (true :: restore) (true :: output)) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_copy_finish
    (left restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 3
        [] left [] restore output) =
      some (sourceIntegerMultiplicationConfiguration 4
        [] left [] restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_restore_step
    (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 4
        [] left right (true :: restore) output) =
      some (sourceIntegerMultiplicationConfiguration 4
        [] left (true :: right) restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_restore_finish
    (left right output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 4
        [] left right [] output) =
      some (sourceIntegerMultiplicationConfiguration 2
        [] left right [] output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_success_step
    (right output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 5
        [] [] (true :: right) [] output) =
      some (sourceIntegerMultiplicationConfiguration 5
        [] [] right [] output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_success_finish
    (output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 5
        [] [] [] [] output) =
      some (Turing.haltList
        sourceUnaryIntegerMultiplicationMachine output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_input_step
    (bit : Bool) (input left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 6
        (bit :: input) left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 6
        input left right restore output) := by
  cases bit <;> sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_input_finish
    (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 6
        [] left right restore output) =
      some (sourceIntegerMultiplicationConfiguration 7
        [] left right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_left_step
    (bit : Bool) (left right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 7
        [] (bit :: left) right restore output) =
      some (sourceIntegerMultiplicationConfiguration 7
        [] left right restore output) := by
  cases bit <;> sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_left_finish
    (right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 7
        [] [] right restore output) =
      some (sourceIntegerMultiplicationConfiguration 8
        [] [] right restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_right_step
    (bit : Bool) (right restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 8
        [] [] (bit :: right) restore output) =
      some (sourceIntegerMultiplicationConfiguration 8
        [] [] right restore output) := by
  cases bit <;> sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_right_finish
    (restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 8
        [] [] [] restore output) =
      some (sourceIntegerMultiplicationConfiguration 9
        [] [] [] restore output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_restore_step
    (bit : Bool) (restore output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 9
        [] [] [] (bit :: restore) output) =
      some (sourceIntegerMultiplicationConfiguration 9
        [] [] [] restore output) := by
  cases bit <;> sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_restore_finish
    (output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 9
        [] [] [] [] output) =
      some (sourceIntegerMultiplicationConfiguration 10
        [] [] [] [] output) := by
  sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_output_step
    (bit : Bool) (output : List Bool) :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 10
        [] [] [] [] (bit :: output)) =
      some (sourceIntegerMultiplicationConfiguration 10
        [] [] [] [] output) := by
  cases bit <;> sourceIntegerMultiplicationStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIntegerMultiplication_failure_finish :
    sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 10
        [] [] [] [] []) =
      some (Turing.haltList
        sourceUnaryIntegerMultiplicationMachine []) := by
  sourceIntegerMultiplicationStepTac

end

end SourceUnaryIntegerMultiplicationTM

end GapCVP

end

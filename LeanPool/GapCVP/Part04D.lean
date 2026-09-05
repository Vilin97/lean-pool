/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04C

/-! # GapCVP proof, part 04, continuation 04 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace OutputPolynomialCompositionClosure

open Turing

private noncomputable def markerConditional_trueTrace
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback input : List Bool) :
    EvalsToInTime (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback)
        (computer.inputAlphabet.invFun true ::
          List.map computer.inputAlphabet.invFun input))
      (some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun (valid input))))
      (computer.time.eval input.length + 1) := by
  have hstart := oneStep _ _ (markerConditional_start_true computer fallback
      (List.map computer.inputAlphabet.invFun input))
  have hvalid :
      EvalsToInTime (markerConditionalMachine computer fallback).step
        (validConfiguration computer fallback
          (Turing.initList computer.tm
            (List.map computer.inputAlphabet.invFun input)))
        (some (validConfiguration computer fallback
          (Turing.haltList computer.tm
            (List.map computer.outputAlphabet.invFun (valid input)))))
        (computer.time.eval input.length) := by
    simpa only [FinTM2.step, bitEncoding, Equiv.invFun_as_coe, id_eq] using
        (GapCVP.TMComposition.evalsToInTimeMapOfStep computer.tm.step (markerConditionalMachine
            computer fallback).step
          (validConfiguration computer fallback) (validConfiguration_step computer fallback)
              (computer.outputsFun input))
  rw [validConfiguration_halt computer fallback] at hvalid
  have hfull := EvalsToInTime.trans (markerConditionalMachine computer fallback).step
    1 (computer.time.eval input.length)
    _ _ _ hstart hvalid
  refine {
    steps := hfull.steps
    evals_in_steps := ?_
    steps_le_m := ?_
  }
  · exact hfull.evals_in_steps
  · have hbudget := hfull.steps_le_m
    omega

private noncomputable def markerConditional_falseTrace
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback input : List Bool) :
    EvalsToInTime (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback)
        (computer.inputAlphabet.invFun false ::
          List.map computer.inputAlphabet.invFun input))
      (some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun fallback)))
      (input.length + 2) := by
  have hstart := oneStep _ _ (markerConditional_start_false computer fallback
      (List.map computer.inputAlphabet.invFun input))
  have hrest := fallbackTrace computer fallback
    (List.map computer.inputAlphabet.invFun input)
  have hfull := EvalsToInTime.trans (markerConditionalMachine computer fallback).step
    1 ((List.map computer.inputAlphabet.invFun input).length + 1)
    _ _ _ hstart hrest
  refine {
    steps := hfull.steps
    evals_in_steps := ?_
    steps_le_m := ?_
  }
  · exact hfull.evals_in_steps
  · have hbudget := hfull.steps_le_m
    simp only [List.length_map] at hbudget
    omega

private noncomputable def markerConditional_missingTrace
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool) :
    EvalsToInTime (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback) [])
      (some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun fallback))) 2 := by
  have hstart := oneStep _ _ (markerConditional_start_missing computer fallback)
  have hrest := fallbackTrace computer fallback []
  exact EvalsToInTime.trans (markerConditionalMachine computer fallback).step
    1 1 _ _ _ hstart hrest

private noncomputable def markerConditional_totalTrace
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback input : List Bool) :
    EvalsToInTime (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback)
        (List.map computer.inputAlphabet.invFun input))
      (some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun
          (markerConditionalOutput valid fallback input))))
      ((computer.time + Polynomial.X + 3).eval input.length) := by
  cases input with
  | nil =>
      have hbudget :
          2 ≤ (computer.time + Polynomial.X + 3).eval 0 := by
        simp only [Polynomial.eval_add, Polynomial.eval_X, add_zero, Polynomial.eval_ofNat,
            Nat.reduceLeDiff]
      convert rebound (markerConditional_missingTrace computer fallback) hbudget using 1 <;>
        simp [markerConditionalOutput]
  | cons marker input =>
      cases marker with
      | false =>
          have hbudget :
              input.length + 2 ≤
                (computer.time + Polynomial.X + 3).eval
                  (input.length + 1) := by
            simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
                Nat.reduceLeDiff]
            omega
          convert rebound (markerConditional_falseTrace computer fallback input) hbudget using 1
              <;>
            simp [markerConditionalOutput]
      | true =>
          have hmonotone :
              computer.time.eval input.length ≤
                computer.time.eval (input.length + 1) :=
            GapCVP.TMComposition.natPolynomial_eval_monotone
              computer.time (by omega)
          have hbudget :
              computer.time.eval input.length + 1 ≤
                (computer.time + Polynomial.X + 3).eval
                  (input.length + 1) := by
            simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
                Order.add_one_le_iff]
            omega
          convert rebound (markerConditional_trueTrace computer fallback input) hbudget using 1 <;>
            simp [markerConditionalOutput]

/-- GapCVP reduction support. -/
noncomputable def markerConditionalComputable
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool) :
    BitTM
      (markerConditionalOutput valid fallback) where
  tm := markerConditionalMachine computer fallback
  inputAlphabet := computer.inputAlphabet
  outputAlphabet := computer.outputAlphabet
  time := computer.time + Polynomial.X + 3
  outputsFun input := by
    change EvalsToInTime
      (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback)
        (List.map computer.inputAlphabet.invFun input))
      (some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun
          (markerConditionalOutput valid fallback input))))
      ((computer.time + Polynomial.X + 3).eval input.length)
    exact markerConditional_totalTrace computer fallback input

/-- GapCVP reduction support. -/
noncomputable def sourcePreservingConditionalComputable
    {selector : List Bool → Bool}
    {valid : List Bool → List Bool}
    (selection : BitTM
      (fun input => selector input :: input))
    (computer : BitTM valid)
    (fallback : List Bool) :
    BitTM
      (fun input => if selector input then valid input else fallback) := by
  convert GapCVP.TMComposition.computableInPolyTime
    selection (markerConditionalComputable computer fallback) using 1
  funext input
  cases hselector : selector input <;>
    simp [Function.comp_apply, markerConditionalOutput, hselector]

end OutputPolynomialCompositionClosure

namespace CNFBoundedRecordFoldTM

open Computability Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFClauseLoop GapCVP.CNFFiniteRecordSort
open GapCVP.CNFPolynomialRowMarkerTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralCNFOutputMachinesUnconditional GapCVP.CNFDependentFiveFamilyRecordTM

/-- GapCVP reduction support. -/
def actualWindowIndexEquiv (T : ℕ) :
    Window T ≃ (Fin T × Position T) where
  toFun window :=
    (⟨window.1.1.val, by have h := window.2; omega⟩,
      window.1.2)
  invFun index := windowAt index.1 index.2
  left_inv window := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  right_inv index := by
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl

/-- GapCVP reduction support. -/
def totalAtMostOneFamilyClauses (T S : ℕ) : List (Clause T S) :=
  (clauseLoopFiniteElements
    ((Time T × Position T) × (Symbol S × Symbol S))).map
    (fun candidate =>
      if candidate.2.1 < candidate.2.2 then
        atMostOneClause candidate.1.1 candidate.1.2
          candidate.2.1 candidate.2.2
      else
        atLeastOneClause candidate.1.1 candidate.1.2)

/-- GapCVP reduction support. -/
def totalForbiddenTransitionFamilyClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  (clauseLoopFiniteElements (Window T × WindowSymbols S)).map
    (fun candidate =>
      if specification.allowed candidate.2 = false then
        transitionClause candidate.1 candidate.2
      else
        atLeastOneClause candidate.1.1.1 candidate.1.1.2)

/-- GapCVP reduction support. -/
def totalFiveFamilySourceClauseCandidates {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  executableAtLeastOneFamilyClauses T S ++
    totalAtMostOneFamilyClauses T S ++
    executableInitialFamilyClauses specification ++
    executableAcceptanceFamilyClauses specification ++
    totalForbiddenTransitionFamilyClauses specification

private theorem totalAtMostOneFamilyClauses_mem_tableauFormula
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S)
    (hclause : clause ∈ totalAtMostOneFamilyClauses T S) :
    clause ∈ tableauFormula specification := by
  obtain ⟨candidate, _, hvalue⟩ := List.mem_map.mp hclause
  by_cases hvalid : candidate.2.1 < candidate.2.2
  · simp only [hvalid, ↓reduceIte] at hvalue
    subst clause
    exact atMostOneClause_mem_tableauFormula specification
      candidate.1.1 candidate.1.2
      candidate.2.1 candidate.2.2 hvalid
  · simp only [hvalid, ↓reduceIte] at hvalue
    subst clause
    exact atLeastOneClause_mem_tableauFormula specification
      candidate.1.1 candidate.1.2

private theorem totalForbiddenTransitionFamilyClauses_mem_tableauFormula
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S)
    (hclause : clause ∈
      totalForbiddenTransitionFamilyClauses specification) :
    clause ∈ tableauFormula specification := by
  obtain ⟨candidate, _, hvalue⟩ := List.mem_map.mp hclause
  by_cases hvalid : specification.allowed candidate.2 = false
  · simp only [hvalid, ↓reduceIte] at hvalue
    subst clause
    exact transitionClause_mem_tableauFormula specification
      candidate.1 candidate.2 hvalid
  · simp only [hvalid, Bool.true_eq_false, ↓reduceIte] at hvalue
    subst clause
    exact atLeastOneClause_mem_tableauFormula specification
      candidate.1.1.1 candidate.1.1.2

private theorem executableAtMostOneFamilyClauses_subset_total
    (T S : ℕ) (clause : Clause T S)
    (hclause : clause ∈ executableAtMostOneFamilyClauses T S) :
    clause ∈ totalAtMostOneFamilyClauses T S := by
  unfold executableAtMostOneFamilyClauses at hclause
  obtain ⟨candidate, hcandidate, hvalue⟩ :=
    List.mem_filterMap.mp hclause
  by_cases hvalid : candidate.2.1 < candidate.2.2
  · simp only [hvalid, ↓reduceIte, Option.some.injEq] at hvalue
    apply List.mem_map.mpr
    refine ⟨candidate, hcandidate, ?_⟩
    simpa only [hvalid, ↓reduceIte] using hvalue
  · simp only [hvalid, ↓reduceIte, reduceCtorEq] at hvalue

private theorem executableForbiddenTransitionFamilyClauses_subset_total
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S)
    (hclause : clause ∈
      executableForbiddenTransitionFamilyClauses specification) :
    clause ∈ totalForbiddenTransitionFamilyClauses specification := by
  unfold executableForbiddenTransitionFamilyClauses at hclause
  obtain ⟨candidate, hcandidate, hvalue⟩ :=
    List.mem_filterMap.mp hclause
  by_cases hvalid : specification.allowed candidate.2 = false
  · simp only [hvalid, ↓reduceIte, Option.some.injEq] at hvalue
    apply List.mem_map.mpr
    refine ⟨candidate, hcandidate, ?_⟩
    simpa only [hvalid, ↓reduceIte] using hvalue
  · simp only [hvalid, Bool.true_eq_false, ↓reduceIte, reduceCtorEq] at hvalue

theorem totalFiveFamilySourceClauseCandidates_toFinset
    {T S : ℕ} (specification : Specification T S) :
    (totalFiveFamilySourceClauseCandidates specification).toFinset =
      tableauFormula specification := by
  ext clause
  simp only [List.mem_toFinset]
  constructor
  · intro hclause
    simp only [totalFiveFamilySourceClauseCandidates,
      List.mem_append] at hclause
    rcases hclause with hremaining | hforbidden
    · rcases hremaining with hremaining | haccept
      · rcases hremaining with hremaining | hinitial
        · rcases hremaining with hleast | hmost
          · obtain ⟨index, _, rfl⟩ := List.mem_map.mp hleast
            exact atLeastOneClause_mem_tableauFormula specification
              index.1 index.2
          · exact totalAtMostOneFamilyClauses_mem_tableauFormula
              specification clause hmost
        · obtain ⟨position, _, rfl⟩ := List.mem_map.mp hinitial
          exact initialClause_mem_tableauFormula specification position
      · have haccept' :
            clause = acceptanceClause specification.accept := by
          simpa only [executableAcceptanceFamilyClauses, List.mem_cons, List.not_mem_nil, or_false]
              using haccept
        subst clause
        exact acceptanceClause_mem_tableauFormula specification
    · exact totalForbiddenTransitionFamilyClauses_mem_tableauFormula
        specification clause hforbidden
  · intro hclause
    have hexecutable :
        clause ∈ executableFiveFamilySourceClauseCandidates
          specification := by
      have hfinset :
          clause ∈
            (executableFiveFamilySourceClauseCandidates
              specification).toFinset := by
        rw [executableFiveFamilySourceClauseCandidates_toFinset]
        exact hclause
      simpa only [List.mem_toFinset] using hfinset
    simp only [executableFiveFamilySourceClauseCandidates,
      List.mem_append] at hexecutable
    simp only [totalFiveFamilySourceClauseCandidates,
      List.mem_append]
    rcases hexecutable with hremaining | hforbidden
    · rcases hremaining with hremaining | haccept
      · rcases hremaining with hremaining | hinitial
        · rcases hremaining with hleast | hmost
          · exact Or.inl (Or.inl (Or.inl (Or.inl hleast)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr
              (executableAtMostOneFamilyClauses_subset_total
                T S clause hmost))))
        · exact Or.inl (Or.inl (Or.inr hinitial))
      · exact Or.inl (Or.inr haccept)
    · exact Or.inr
        (executableForbiddenTransitionFamilyClauses_subset_total
          specification clause hforbidden)

/-- GapCVP reduction support. -/
def totalVerifierFiveFamilySourceClauseCandidates
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :=
  totalFiveFamilySourceClauseCandidates
    ((paddedStructuralTableauSimulation bound machine).specification input)

theorem totalVerifierFiveFamilySourceClauseCandidates_sorted
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    sourceOrderedDistinctRecords
      (totalVerifierFiveFamilySourceClauseCandidates
        bound machine input) =
      structuralWholeSourceClauses bound machine input := by
  unfold sourceOrderedDistinctRecords
    totalVerifierFiveFamilySourceClauseCandidates
  rw [totalFiveFamilySourceClauseCandidates_toFinset]
  rfl

private theorem encodeFormulaFrom_totalVerifierFiveFamilies
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    encodeFormulaFrom 0
      (sourceOrderedDistinctRecords
        (totalVerifierFiveFamilySourceClauseCandidates
          bound machine input)) =
      structuralWholeThreeCNF bound machine input := by
  rw [totalVerifierFiveFamilySourceClauseCandidates_sorted]
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem encodeThreeCNF_totalVerifierFiveFamilies
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    encodeThreeCNF
      (encodeFormulaFrom 0
        (sourceOrderedDistinctRecords
          (totalVerifierFiveFamilySourceClauseCandidates
            bound machine input))) =
      structuralWholeCNFWord bound machine input := by
  rw [encodeFormulaFrom_totalVerifierFiveFamilies]
  rfl

/-- GapCVP reduction support. -/
noncomputable def polynomialValueUnaryComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (fun input : List Bool =>
        List.replicate (polynomial.eval input.length) true) := by
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    (sourcePreservingPolynomialMarkerComputable polynomial)
    firstFieldSuffixComputable
  have hcontents := GapCVP.TMComposition.computableInPolyTime
    hsuffix firstFieldContentsComputable
  have hfunction :
      (fun input : List Bool =>
        firstFieldContents
          (firstFieldSuffix
            (sourcePreservingPolynomialMarkerWord polynomial input))) =
        (fun input : List Bool =>
          List.replicate (polynomial.eval input.length) true) := by
    funext input
    rw [firstFieldSuffix_sourcePreservingPolynomialMarkerWord]
    simpa only [List.append_nil] using
        (firstFieldContents_valid (List.replicate (polynomial.eval input.length) true) [])
  rw [← hfunction]
  simpa only [Function.comp_def] using hcontents

end CNFBoundedRecordFoldTM

namespace OutputBoundedDependentRecordFold

open Turing

@[simp] private theorem boundedFold_cast_nil
    {α β : Type} (h : α = β) :
    cast (congrArg List h) ([] : List α) = ([] : List β) := by
  cases h
  rfl

/-- GapCVP reduction support. -/
def parseUnaryBoundedFold : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: remaining => some (0, remaining)
  | true :: remaining =>
      (parseUnaryBoundedFold remaining).map
        (fun parsed => (parsed.1 + 1, parsed.2))

/-- GapCVP reduction support. -/
def unaryBoundedFoldWord (count : ℕ) (seed : List Bool) : List Bool :=
  List.replicate count true ++ false :: seed

@[simp] theorem parseUnaryBoundedFold_word
    (count : ℕ) (seed : List Bool) :
    parseUnaryBoundedFold (unaryBoundedFoldWord count seed) =
      some (count, seed) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [unaryBoundedFoldWord, List.replicate_succ, List.cons_append,
          parseUnaryBoundedFold,
          Option.map_eq_some_iff, Prod.mk.injEq, Nat.add_right_cancel_iff, Prod.exists,
              exists_eq_right_right,
          exists_eq_right, Option.map_some] using
          congrArg (Option.map (fun parsed : ℕ × List Bool => (parsed.1 + 1, parsed.2))) ih

/-- GapCVP reduction support. -/
def boundedRecordFoldOutput
    (worker : List Bool → List Bool) (input : List Bool) : List Bool :=
  match parseUnaryBoundedFold input with
  | none => []
  | some (count, seed) => (worker^[count]) seed

theorem parsedUnaryFold_count_le_length
    (input : List Bool) (count : ℕ) (seed : List Bool)
    (hparse : parseUnaryBoundedFold input = some (count, seed)) :
    count ≤ input.length := by
  induction input generalizing count seed with
  | nil => simp only [parseUnaryBoundedFold, reduceCtorEq] at hparse
  | cons bit remaining ih =>
      cases bit with
      | false =>
          simp only [parseUnaryBoundedFold, Option.some.injEq, Prod.mk.injEq] at hparse
          omega
      | true =>
          cases hrest : parseUnaryBoundedFold remaining with
          | none => simp only [parseUnaryBoundedFold, hrest, Option.map_none, reduceCtorEq]
              at hparse
          | some parsed =>
              obtain ⟨parsedCount, parsedSeed⟩ := parsed
              simp only [parseUnaryBoundedFold, hrest, Option.map_some, Option.some.injEq,
                  Prod.mk.injEq] at hparse
              obtain ⟨hcount, hseed⟩ := hparse
              subst count
              have hbounded := ih parsedCount parsedSeed hrest
              simp only [List.length_cons]
              omega

/-- GapCVP reduction support. -/
noncomputable def PolynomiallyBoundedFoldStates
    (worker : List Bool → List Bool)
    (bound : Polynomial ℕ) : Bool :=
  @decide (
  ∀ (input : List Bool) (count : ℕ) (seed : List Bool),
    parseUnaryBoundedFold input = some (count, seed) →
      ∀ stage : ℕ, stage ≤ count →
        ((worker^[stage]) seed).length ≤ bound.eval input.length
  ) (Classical.propDecidable _)
private abbrev BoundedFoldStack (tm : Turing.FinTM2) := tm.K ⊕ Bool

private abbrev boundedFoldAlphabet (tm : Turing.FinTM2) :
    BoundedFoldStack tm → Type
  | .inl k => tm.Γ k
  | .inr _ => Bool

private abbrev BoundedFoldLabel (tm : Turing.FinTM2) := tm.Λ ⊕ Fin 5

private abbrev BoundedFoldState (tm : Turing.FinTM2) := Option Bool × tm.σ

private def liftBoundedFoldWorkerStatement (tm : Turing.FinTM2) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Turing.TM2.Stmt (boundedFoldAlphabet tm)
        (BoundedFoldLabel tm) (BoundedFoldState tm)
  | .push k f next =>
      .push (.inl k) (fun state => f state.2)
        (liftBoundedFoldWorkerStatement tm next)
  | .peek k f next =>
      .peek (.inl k)
        (fun state symbol => (state.1, f state.2 symbol))
        (liftBoundedFoldWorkerStatement tm next)
  | .pop k f next =>
      .pop (.inl k)
        (fun state symbol => (state.1, f state.2 symbol))
        (liftBoundedFoldWorkerStatement tm next)
  | .load f next =>
      .load (fun state => (state.1, f state.2))
        (liftBoundedFoldWorkerStatement tm next)
  | .branch test yes no =>
      .branch (fun state => test state.2)
        (liftBoundedFoldWorkerStatement tm yes)
        (liftBoundedFoldWorkerStatement tm no)
  | .goto next => .goto (fun state => .inl (next state.2))
  | .halt =>
      .load (fun state => (none, state.2))
        (.goto (fun _ => .inr (2 : Fin 5)))

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedDependentRecordFoldMachine
    {worker : List Bool → List Bool}
    (computer : BitTM worker) : Turing.FinTM2 := by
  classical
  letI : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  letI : Fintype computer.tm.K := computer.tm.kFin
  letI : Fintype computer.tm.Λ := computer.tm.ΛFin
  letI : Fintype computer.tm.σ := computer.tm.σFin
  letI : Fintype (computer.tm.Γ computer.tm.k₀) :=
    computer.tm.Γk₀Fin
  exact {
    K := BoundedFoldStack computer.tm
    k₀ := .inl computer.tm.k₀
    k₁ := .inl computer.tm.k₀
    Γ := boundedFoldAlphabet computer.tm
    Λ := BoundedFoldLabel computer.tm
    main := .inr (0 : Fin 5)
    σ := BoundedFoldState computer.tm
    initialState := (none, computer.tm.initialState)
    m := fun
      | .inl label =>
          liftBoundedFoldWorkerStatement computer.tm
            (computer.tm.m label)
      | .inr phase =>
          if phase = (0 : Fin 5) then
            .peek (.inl computer.tm.k₀)
              (fun state symbol =>
                (symbol.map computer.inputAlphabet, state.2))
              (.branch (fun state => state.1.isSome)
                (.branch (fun state => state.1.getD false)
                  (.pop (.inl computer.tm.k₀)
                    (fun state _ => (none, state.2))
                    (.push (.inr false) (fun _ => true)
                      (.goto (fun _ => .inr (0 : Fin 5)))))
                  (.pop (.inl computer.tm.k₀)
                    (fun state _ => (none, state.2))
                    (.goto (fun _ => .inr (1 : Fin 5)))))
                (.goto (fun _ => .inr (4 : Fin 5))))
          else if phase = (1 : Fin 5) then
            .peek (.inr false)
              (fun state symbol => (symbol, state.2))
              (.branch (fun state => state.1.isSome)
                (.pop (.inr false)
                  (fun state _ => (none, state.2))
                  (.goto (fun _ => .inl computer.tm.main)))
                (.load (fun state => (none, state.2)) .halt))
          else if phase = (2 : Fin 5) then
            .peek (.inl computer.tm.k₁)
              (fun state symbol =>
                (symbol.map computer.outputAlphabet, state.2))
              (.branch (fun state => state.1.isSome)
                (.pop (.inl computer.tm.k₁)
                  (fun state _ => state)
                  (.push (.inr true)
                    (fun state => state.1.getD false)
                    (.load (fun state => (none, state.2))
                      (.goto (fun _ => .inr (2 : Fin 5))))))
                (.load (fun state => (none, state.2))
                  (.goto (fun _ => .inr (3 : Fin 5)))))
          else if phase = (3 : Fin 5) then
            .peek (.inr true)
              (fun state symbol => (symbol, state.2))
              (.branch (fun state => state.1.isSome)
                (.pop (.inr true)
                  (fun state _ => state)
                  (.push (.inl computer.tm.k₀)
                    (fun state =>
                      computer.inputAlphabet.invFun
                        (state.1.getD false))
                    (.load (fun state => (none, state.2))
                      (.goto (fun _ => .inr (3 : Fin 5))))))
                (.load (fun state => (none, state.2))
                  (.goto (fun _ => .inr (1 : Fin 5)))))
          else
            .peek (.inr false)
              (fun state symbol => (symbol, state.2))
              (.branch (fun state => state.1.isSome)
                (.pop (.inr false)
                  (fun state _ => (none, state.2))
                  (.goto (fun _ => .inr (4 : Fin 5))))
                (.load (fun state => (none, state.2)) .halt))
  }

private def boundedFoldStacks
    (tm : Turing.FinTM2)
    (sourceStacks : ∀ k, List (tm.Γ k))
    (counter scratch : List Bool) :
    (k : BoundedFoldStack tm) → List (boundedFoldAlphabet tm k)
  | .inl k => sourceStacks k
  | .inr false => counter
  | .inr true => scratch

private noncomputable def boundedFoldPhaseConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (phase : Fin 5)
    (sourceStacks : ∀ k, List (computer.tm.Γ k))
    (counter scratch : List Bool) :
    (boundedDependentRecordFoldMachine computer).Cfg where
  l := some (.inr phase)
  var := (none, computer.tm.initialState)
  stk := boundedFoldStacks computer.tm sourceStacks counter scratch

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedFoldWorkerConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool)
    (configuration : computer.tm.Cfg) :
    (boundedDependentRecordFoldMachine computer).Cfg where
  l := match configuration.l with
    | some label => some (.inl label)
    | none => some (.inr (2 : Fin 5))
  var := (none, configuration.var)
  stk := boundedFoldStacks computer.tm configuration.stk counter []

private theorem boundedFoldStacks_update_worker
    (tm : Turing.FinTM2)
    (sourceStacks : ∀ k, List (tm.Γ k))
    (counter scratch : List Bool)
    (k : tm.K) (value : List (tm.Γ k)) :
    boundedFoldStacks tm (Function.update sourceStacks k value)
        counter scratch =
      Function.update
        (boundedFoldStacks tm sourceStacks counter scratch)
        (.inl k) value := by
  classical
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = k
      · subst stack
        simp only [boundedFoldStacks, Function.update_self]
      · simp only [boundedFoldStacks, Function.update, heq, ↓reduceDIte, Sum.inl.injEq]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks, Function.update]

private theorem liftBoundedFoldWorkerStatement_stepAux
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool)
    (statement : Turing.TM2.Stmt
      computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (state : computer.tm.σ)
    (sourceStacks : ∀ k, List (computer.tm.Γ k)) :
    Turing.TM2.stepAux
      (liftBoundedFoldWorkerStatement computer.tm statement)
      (none, state)
      (boundedFoldStacks computer.tm sourceStacks counter []) =
        boundedFoldWorkerConfiguration computer counter
          (Turing.TM2.stepAux statement state sourceStacks) := by
  classical
  induction statement generalizing state sourceStacks with
  | push k f next ih =>
      change Turing.TM2.stepAux
        (liftBoundedFoldWorkerStatement computer.tm next)
        (none, state)
        (Function.update
          (boundedFoldStacks computer.tm sourceStacks counter [])
          (.inl k) (f state :: sourceStacks k)) = _
      rw [← boundedFoldStacks_update_worker]
      exact ih (state := state)
        (sourceStacks :=
          Function.update sourceStacks k (f state :: sourceStacks k))
  | peek k f next ih =>
      exact ih (state := f state (sourceStacks k).head?)
        (sourceStacks := sourceStacks)
  | pop k f next ih =>
      change Turing.TM2.stepAux
        (liftBoundedFoldWorkerStatement computer.tm next)
        (none, f state (sourceStacks k).head?)
        (Function.update
          (boundedFoldStacks computer.tm sourceStacks counter [])
          (.inl k) (sourceStacks k).tail) = _
      rw [← boundedFoldStacks_update_worker]
      exact ih (state := f state (sourceStacks k).head?)
        (sourceStacks :=
          Function.update sourceStacks k (sourceStacks k).tail)
  | load f next ih =>
      exact ih (state := f state) (sourceStacks := sourceStacks)
  | branch test yes no ihYes ihNo =>
      cases htest : test state with
      | false =>
          simpa only [liftBoundedFoldWorkerStatement, TM2.stepAux, htest, Bool.cond_false] using
              ihNo (state := state) (sourceStacks := sourceStacks)
      | true =>
          simpa only [liftBoundedFoldWorkerStatement, TM2.stepAux, htest, Bool.cond_true] using
              ihYes (state := state) (sourceStacks := sourceStacks)
  | goto next => rfl
  | halt => rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFoldWorkerConfiguration_step
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool)
    (configuration next : computer.tm.Cfg)
    (hstep : computer.tm.step configuration = some next) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldWorkerConfiguration computer counter configuration) =
        some (boundedFoldWorkerConfiguration computer counter next) := by
  rcases configuration with ⟨label, state, sourceStacks⟩
  cases label with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at hstep
  | some label =>
      change some (Turing.TM2.stepAux (computer.tm.m label)
        state sourceStacks) = some next at hstep
      have hnext := Option.some.inj hstep
      subst next
      change some (Turing.TM2.stepAux
        (liftBoundedFoldWorkerStatement computer.tm
          (computer.tm.m label))
        (none, state)
        (boundedFoldStacks computer.tm sourceStacks counter [])) =
        some (boundedFoldWorkerConfiguration computer counter
          (Turing.TM2.stepAux (computer.tm.m label)
            state sourceStacks))
      rw [liftBoundedFoldWorkerStatement_stepAux computer counter]
      rfl

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedFoldScanConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (remaining : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).Cfg :=
  boundedFoldPhaseConfiguration computer 0
    (Turing.initList computer.tm remaining).stk counter []

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedFoldDispatchConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).Cfg :=
  boundedFoldPhaseConfiguration computer 1
    (Turing.initList computer.tm input).stk counter []

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedFoldDrainConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (output : List (computer.tm.Γ computer.tm.k₁))
    (counter scratch : List Bool) :
    (boundedDependentRecordFoldMachine computer).Cfg :=
  boundedFoldPhaseConfiguration computer 2
    (Turing.haltList computer.tm output).stk counter scratch

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedFoldRestoreConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀))
    (counter scratch : List Bool) :
    (boundedDependentRecordFoldMachine computer).Cfg :=
  boundedFoldPhaseConfiguration computer 3
    (Turing.initList computer.tm input).stk counter scratch

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def boundedFoldMalformedConfiguration
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).Cfg :=
  boundedFoldPhaseConfiguration computer 4
    (Turing.initList computer.tm []).stk counter []

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem boundedFoldWorkerConfiguration_halt
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool)
    (output : List (computer.tm.Γ computer.tm.k₁)) :
    boundedFoldWorkerConfiguration computer counter
      (Turing.haltList computer.tm output) =
        boundedFoldDrainConfiguration computer output counter [] := by
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedDependentRecordFoldMachine_init
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀)) :
    Turing.initList (boundedDependentRecordFoldMachine computer) input =
      boundedFoldScanConfiguration computer input [] := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, initList,
      eq_mpr_eq_cast,
      boundedFoldScanConfiguration, boundedFoldPhaseConfiguration]
  congr 1
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [↓reduceDIte, cast_eq, boundedFoldStacks]
        rfl
      · simp only [Sum.inl.injEq, heq, ↓reduceDIte, boundedFoldStacks]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_scan_true
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (remaining : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldScanConfiguration computer
        (computer.inputAlphabet.invFun true :: remaining) counter) =
      some (boundedFoldScanConfiguration computer remaining
        (true :: counter)) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldScanConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          ↓reduceIte, TM2.stepAux,
      boundedFoldStacks, ↓reduceDIte, cast_eq, List.head?_cons, Option.map_some,
          Equiv.apply_symm_apply,
      Option.isSome_some, Option.getD_some, List.tail_cons, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne,
      Bool.cond_true]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [Function.update, reduceCtorEq, ↓reduceDIte, boundedFoldStacks, cast_eq]
      · simp only [Function.update, reduceCtorEq, ↓reduceDIte, Sum.inl.injEq, heq,
          boundedFoldStacks]
  | inr stack =>
      cases stack <;> simp [Function.update, boundedFoldStacks]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_scan_delimiter
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (remaining : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldScanConfiguration computer
        (computer.inputAlphabet.invFun false :: remaining) counter) =
      some (boundedFoldDispatchConfiguration computer remaining
        counter) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldScanConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          ↓reduceIte, TM2.stepAux,
      boundedFoldStacks, ↓reduceDIte, cast_eq, List.head?_cons, Option.map_some,
          Equiv.apply_symm_apply,
      Option.isSome_some, Option.getD_some, List.tail_cons, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne,
      Bool.cond_false, Bool.cond_true, boundedFoldDispatchConfiguration]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [Function.update, ↓reduceDIte, boundedFoldStacks, cast_eq]
      · simp only [Function.update, Sum.inl.injEq, heq, ↓reduceDIte, boundedFoldStacks]
  | inr stack =>
      cases stack <;> simp [Function.update, boundedFoldStacks]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_scan_missing
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldScanConfiguration computer [] counter) =
      some (boundedFoldMalformedConfiguration computer counter) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldScanConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          ↓reduceIte, TM2.stepAux,
      boundedFoldStacks, ↓reduceDIte, cast_eq, List.head?_nil, Option.map_none, Option.isSome_none,
          Option.getD_none,
      List.tail_nil, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
          Bool.cond_false,
      boundedFoldMalformedConfiguration]
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_dispatch_step
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDispatchConfiguration computer input
        (true :: counter)) =
      some (boundedFoldWorkerConfiguration computer counter
        (Turing.initList computer.tm input)) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldDispatchConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          one_ne_zero, ↓reduceIte,
      TM2.stepAux, boundedFoldStacks, List.head?_cons, Option.isSome_some, List.tail_cons,
          Bool.cond_true,
      boundedFoldWorkerConfiguration]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [Function.update, reduceCtorEq, ↓reduceDIte, boundedFoldStacks, cast_eq]
      · simp only [Function.update, reduceCtorEq, ↓reduceDIte, boundedFoldStacks, heq]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks, Function.update]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_dispatch_finish
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀)) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDispatchConfiguration computer input []) =
      some (Turing.haltList
        (boundedDependentRecordFoldMachine computer) input) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldDispatchConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          one_ne_zero, ↓reduceIte,
      TM2.stepAux, boundedFoldStacks, List.head?_nil, Option.isSome_none, List.tail_nil,
          Bool.cond_false, haltList]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [boundedFoldStacks, ↓reduceDIte, cast_eq]
        rfl
      · simp only [boundedFoldStacks, heq, ↓reduceDIte, Sum.inl.injEq]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_drain_step
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (symbol : computer.tm.Γ computer.tm.k₁)
    (remaining : List (computer.tm.Γ computer.tm.k₁))
    (counter scratch : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDrainConfiguration computer
        (symbol :: remaining) counter scratch) =
      some (boundedFoldDrainConfiguration computer
        remaining counter
        (computer.outputAlphabet symbol :: scratch)) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldDrainConfiguration, boundedFoldPhaseConfiguration, haltList, eq_mpr_eq_cast,
          Fin.reduceEq, ↓reduceIte,
      TM2.stepAux, boundedFoldStacks, ↓reduceDIte, cast_eq, List.head?_cons, Option.map_some,
          Option.isSome_some,
      List.tail_cons, Option.getD_some, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne, Bool.cond_true]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₁
      · subst stack
        simp only [Function.update, reduceCtorEq, ↓reduceDIte, boundedFoldStacks, cast_eq]
      · simp only [Function.update, reduceCtorEq, ↓reduceDIte, Sum.inl.injEq, heq,
          boundedFoldStacks]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks, Function.update]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_drain_finish
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter scratch : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDrainConfiguration computer [] counter scratch) =
      some (boundedFoldRestoreConfiguration computer []
        counter scratch) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldDrainConfiguration, boundedFoldPhaseConfiguration, haltList, eq_mpr_eq_cast,
          Fin.reduceEq, ↓reduceIte,
      TM2.stepAux, boundedFoldStacks, ↓reduceDIte, cast_eq, List.head?_nil, Option.map_none,
          Option.isSome_none,
      List.tail_nil, Option.getD_none, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne, Bool.cond_false,
      boundedFoldRestoreConfiguration, initList]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases hin : stack = computer.tm.k₀
      · subst stack
        simp only [boundedFoldStacks, ↓reduceDIte, cast_eq, dite_eq_right_iff]
        intro h
        first
        | exact boundedFold_cast_nil (congrArg computer.tm.Γ h)
        | exact boundedFold_cast_nil (congrArg computer.tm.Γ h.symm)
      · by_cases hout : stack = computer.tm.k₁
        · subst stack
          simp only [boundedFoldStacks, ↓reduceDIte, cast_eq, hin]
        · simp only [boundedFoldStacks, hout, ↓reduceDIte, hin]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_restore_step
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool)
    (bit : Bool) (scratch : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldRestoreConfiguration computer input
        counter (bit :: scratch)) =
      some (boundedFoldRestoreConfiguration computer
        (computer.inputAlphabet.invFun bit :: input)
        counter scratch) := by
  classical
  cases bit <;>
    compactMachineStepTac [boundedDependentRecordFoldMachine,
      boundedFoldRestoreConfiguration, boundedFoldPhaseConfiguration,
      boundedFoldStacks, Turing.initList]
  all_goals
    congr 2
    funext stack
    cases stack with
    | inl stack =>
        by_cases heq : stack = computer.tm.k₀
        · subst stack
          simp only [Function.update, ↓reduceDIte, boundedFoldStacks, cast_eq,
            reduceCtorEq]
        · simp only [Function.update, Sum.inl.injEq, heq, ↓reduceDIte, reduceCtorEq,
            boundedFoldStacks]
    | inr stack =>
        cases stack <;> simp [boundedFoldStacks, Function.update]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_restore_finish
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldRestoreConfiguration computer input counter []) =
      some (boundedFoldDispatchConfiguration computer input counter) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldRestoreConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          Fin.reduceEq, ↓reduceIte,
      TM2.stepAux, boundedFoldStacks, List.head?_nil, Option.isSome_none, List.tail_nil,
          Option.getD_none,
          Bool.cond_false,
      boundedFoldDispatchConfiguration]
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_malformed_step
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (counter : List Bool) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldMalformedConfiguration computer
        (true :: counter)) =
      some (boundedFoldMalformedConfiguration computer counter) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldMalformedConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          Fin.reduceEq,
      ↓reduceIte, TM2.stepAux, boundedFoldStacks, List.head?_cons, Option.isSome_some,
          List.tail_cons, Bool.cond_true]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [Function.update, reduceCtorEq, ↓reduceDIte, boundedFoldStacks, cast_eq]
      · simp only [Function.update, reduceCtorEq, ↓reduceDIte, boundedFoldStacks, heq]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks, Function.update]

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedFold_malformed_finish
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    (boundedDependentRecordFoldMachine computer).step
      (boundedFoldMalformedConfiguration computer []) =
      some (Turing.haltList
        (boundedDependentRecordFoldMachine computer) []) := by
  classical
  simp only [boundedDependentRecordFoldMachine, Fin.isValue, Equiv.invFun_as_coe, FinTM2.step,
      TM2.step,
      boundedFoldMalformedConfiguration, boundedFoldPhaseConfiguration, initList, eq_mpr_eq_cast,
          Fin.reduceEq,
      ↓reduceIte, TM2.stepAux, boundedFoldStacks, List.head?_nil, Option.isSome_none,
          List.tail_nil, Bool.cond_false, haltList]
  congr 2
  funext stack
  cases stack with
  | inl stack =>
      by_cases heq : stack = computer.tm.k₀
      · subst stack
        simp only [boundedFoldStacks, ↓reduceDIte, cast_eq]
        rfl
      · simp only [boundedFoldStacks, heq, ↓reduceDIte, Sum.inl.injEq]
  | inr stack =>
      cases stack <;> simp [boundedFoldStacks]

end OutputBoundedDependentRecordFold

namespace CNFTypedRecordWorkerTM

open Turing GapCVP.CL GapCVP.OutputBoundedDependentRecordFold

theorem parsedUnaryFold_seed_length_le
    (raw : List Bool) (count : ℕ) (seed : List Bool)
    (hparse : parseUnaryBoundedFold raw = some (count, seed)) :
    seed.length ≤ raw.length := by
  induction raw generalizing count seed with
  | nil =>
      simp only [parseUnaryBoundedFold, reduceCtorEq] at hparse
  | cons bit remaining ih =>
      cases bit with
      | false =>
          simp only [parseUnaryBoundedFold, Option.some.injEq, Prod.mk.injEq] at hparse
          obtain ⟨hcount, hseed⟩ := hparse
          subst count
          subst seed
          simp only [List.length_cons, le_add_iff_nonneg_right, zero_le]
      | true =>
          cases hrest : parseUnaryBoundedFold remaining with
          | none =>
              simp only [parseUnaryBoundedFold, hrest, Option.map_none, reduceCtorEq] at hparse
          | some parsed =>
              obtain ⟨parsedCount, parsedSeed⟩ := parsed
              simp only [parseUnaryBoundedFold, hrest, Option.map_some, Option.some.injEq,
                  Prod.mk.injEq] at hparse
              obtain ⟨hcount, hseed⟩ := hparse
              subst count
              subst seed
              have hbounded := ih parsedCount parsedSeed hrest
              simp only [List.length_cons]
              omega

theorem acceptanceClause_exact_card
    {T S : ℕ} (accept : Symbol S) :
    (acceptanceClause (T := T) accept).card = T + 1 := by
  classical
  have hinjective : Function.Injective
      (fun position : Position T =>
        positive ((Fin.last T), position, accept)) := by
    intro first second heq
    exact congrArg
      (fun literal : SignedLiteral T S => literal.1.2.1) heq
  unfold acceptanceClause
  calc
    (Finset.univ.image
      (fun position : Position T =>
        positive ((Fin.last T), position, accept))).card =
      (Finset.univ : Finset (Position T)).card :=
        Finset.card_image_of_injective Finset.univ hinjective
    _ = T + 1 := by simp only [Finset.card_univ, Fintype.card_fin]

end CNFTypedRecordWorkerTM

end GapCVP

end

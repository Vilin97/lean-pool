/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineKuhnSemantics
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixDimension
import Mathlib.Tactic

/-!
# Reachable-state bounds for the encoded Kuhn evaluator

The finite-word transition clamps every dynamic field to one fixed word.  This
file proves that the clamp is inactive along the canonical execution.  We use
a deliberately generous octic envelope; its only purpose is to make the
polynomial-space estimate transparent.
-/

namespace BeyondBethe

open Complexity

/-! ## A semantic invariant -/

def KuhnFrameDataBound (n : ℕ) : KuhnFrame n → Prop
  | .search frame => frame.fuel ≤ n + 1 ∧ frame.remaining.length ≤ n
  | .build frame => frame.rows.length ≤ n

def KuhnStackDataBound {n : ℕ} (stack : List (KuhnFrame n)) : Prop :=
  ∀ frame ∈ stack, KuhnFrameDataBound n frame

def KuhnEvalReachableBound {n : ℕ} (steps : ℕ) :
    KuhnEvalState n → Prop
  | .call fuel remaining _row _seen _mate stack =>
      fuel ≤ n + 1 ∧ remaining.length ≤ n ∧
        KuhnStackDataBound stack ∧ stack.length ≤ steps + 1
  | .ret _result stack =>
      KuhnStackDataBound stack ∧ stack.length ≤ steps + 1
  | .done _mate => True

theorem kuhnStackDataBound_tail {n : ℕ} {frame : KuhnFrame n}
    {stack : List (KuhnFrame n)}
    (h : KuhnStackDataBound (frame :: stack)) :
    KuhnStackDataBound stack := by
  intro next hnext
  exact h next (by simp [hnext])

theorem kuhnEvalStep_reachableBound {n steps : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n)
    (hstate : KuhnEvalReachableBound steps state) :
    KuhnEvalReachableBound (steps + 1) (kuhnEvalStep A state) := by
  cases state with
  | done mate => trivial
  | call fuel remaining row seen mate stack =>
      rcases hstate with ⟨hfuel, hremaining, hstack, hlength⟩
      cases fuel with
      | zero =>
          exact ⟨hstack, by omega⟩
      | succ fuel =>
          cases remaining with
          | nil =>
              exact ⟨hstack, by omega⟩
          | cons col remaining =>
              simp only [List.length_cons] at hremaining
              by_cases hskip : col ∈ seen ∨ A row col = 0
              · simp only [kuhnEvalStep, hskip, ↓reduceIte]
                exact ⟨hfuel, by omega, hstack, by omega⟩
              · simp only [kuhnEvalStep, hskip, ↓reduceIte]
                cases hmate : mate col with
                | none =>
                    exact ⟨hstack, by omega⟩
                | some oldRow =>
                    refine ⟨by omega, by simp, ?_, by simp; omega⟩
                    intro frame hframe
                    simp only [List.mem_cons] at hframe
                    rcases hframe with rfl | hframe
                    · change fuel + 1 ≤ n + 1 ∧ remaining.length ≤ n
                      exact ⟨hfuel, by omega⟩
                    · exact hstack frame hframe
  | ret result stack =>
      rcases hstate with ⟨hstack, hlength⟩
      cases stack with
      | nil => exact ⟨by simp [KuhnStackDataBound], by omega⟩
      | cons frame stack =>
          have htail := kuhnStackDataBound_tail hstack
          have hframe := hstack frame (by simp)
          cases frame with
          | search frame =>
              rcases hframe with ⟨hfuel, hremaining⟩
              cases hmate : result.mate? with
              | none =>
                  simp only [kuhnEvalStep, hmate]
                  exact ⟨hfuel, hremaining, htail, by simp at hlength ⊢; omega⟩
              | some mate =>
                  simp only [kuhnEvalStep, hmate]
                  exact ⟨htail, by simp at hlength ⊢; omega⟩
          | build frame =>
              rcases frame with ⟨rows, fallback⟩
              change rows.length ≤ n at hframe
              cases hmate : result.mate? with
              | none =>
                  cases rows with
                  | nil => simp [kuhnEvalStep, hmate, KuhnEvalReachableBound]
                  | cons row rows =>
                      simp only [List.length_cons] at hframe
                      simp only [kuhnEvalStep, hmate]
                      refine ⟨by omega, by simp, ?_, by simp at hlength ⊢; omega⟩
                      intro next hnext
                      simp only [List.mem_cons] at hnext
                      rcases hnext with rfl | hnext
                      · change rows.length ≤ n
                        omega
                      · exact htail next hnext
              | some mate =>
                  cases rows with
                  | nil => simp [kuhnEvalStep, hmate, KuhnEvalReachableBound]
                  | cons row rows =>
                      simp only [List.length_cons] at hframe
                      simp only [kuhnEvalStep, hmate]
                      refine ⟨by omega, by simp, ?_, by simp at hlength ⊢; omega⟩
                      intro next hnext
                      simp only [List.mem_cons] at hnext
                      rcases hnext with rfl | hnext
                      · change rows.length ≤ n
                        omega
                      · exact htail next hnext

theorem kuhnBuildEvalState_reachableBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (mate : ColumnMate n) (hrows : rows.length ≤ n) :
    KuhnEvalReachableBound 0 (kuhnBuildEvalState A rows mate) := by
  cases rows with
  | nil => trivial
  | cons row rows =>
      simp only [List.length_cons] at hrows
      refine ⟨by omega, by simp, ?_, by simp⟩
      intro frame hframe
      simp only [List.mem_singleton] at hframe
      subst frame
      change rows.length ≤ n
      omega

theorem kuhnFullBuildEvalState_reachableBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    KuhnEvalReachableBound 0
      (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)) := by
  exact kuhnBuildEvalState_reachableBound A _ _ (by simp)

theorem kuhnEvalIterate_reachableBound {n steps : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n)
    (hstate : KuhnEvalReachableBound 0 state) :
    KuhnEvalReachableBound steps ((kuhnEvalStep A)^[steps] state) := by
  induction steps with
  | zero => simpa using! hstate
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.succ_eq_add_one] using!
        kuhnEvalStep_reachableBound A _ ih

/-! ## Length of canonical control words -/

theorem finUnaryCode_length_le {n : ℕ} (i : Fin n) :
    (finUnaryCode i).length ≤ n := by
  simp [finUnaryCode]

theorem finListUnaryCode_length_le {n : ℕ} (xs : List (Fin n)) :
    (finListUnaryCode xs).length ≤ xs.length * (2 * n + 2) := by
  induction xs with
  | nil => simp [finListUnaryCode, binaryListCode]
  | cons i xs ih =>
      simp only [finListUnaryCode, binaryListCode, pair_length,
        List.length_cons]
      have hi := finUnaryCode_length_le i
      change 2 * (finUnaryCode i).length + 2 +
          (binaryListCode finUnaryCode xs).length ≤
        (xs.length + 1) * (2 * n + 2)
      change (binaryListCode finUnaryCode xs).length ≤
          xs.length * (2 * n + 2) at ih
      nlinarith

@[simp] theorem boolVectorCode_length (v : List Bool) :
    (boolVectorCode v).length = 4 * v.length := by
  induction v with
  | nil => simp [boolVectorCode, binaryListCode]
  | cons bit v ih =>
      change (binaryListCode boolElementCode v).length = 4 * v.length at ih
      simp [boolVectorCode, binaryListCode, boolElementCode, ih]
      omega

theorem mateVectorCode_columnMate_length_le {n : ℕ}
    (mate : ColumnMate n) :
    (mateVectorCode (columnMateList mate)).length ≤ n * (2 * n + 4) := by
  rw [mateVectorCode, binaryListCode_length_eq_sum]
  have heach : ∀ value ∈ columnMateList mate,
      2 * (mateValueCode value).length + 2 ≤ 2 * n + 4 := by
    intro value hvalue
    rw [columnMateList] at hvalue
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hvalue
    cases hmate : mate j with
    | none => simp [mateValueCode, hmate]
    | some row =>
        simp [mateValueCode, hmate]
        omega
  calc
    ((columnMateList mate).map
        (fun value ↦ 2 * (mateValueCode value).length + 2)).sum ≤
        (columnMateList mate).length * (2 * n + 4) := by
      simpa [Nat.nsmul_eq_mul] using!
        List.sum_le_card_nsmul
          ((columnMateList mate).map
            (fun value ↦ 2 * (mateValueCode value).length + 2))
          (2 * n + 4) (by
            intro value hvalue
            obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hvalue
            exact heach source hsource)
    _ = n * (2 * n + 4) := by simp

theorem kuhnFrameCode_length_le {n : ℕ} (frame : KuhnFrame n)
    (hframe : KuhnFrameDataBound n frame) :
    (kuhnFrameCode frame).length ≤ 16 * (n + 1) ^ 2 := by
  cases frame with
  | search frame =>
      rcases hframe with ⟨hfuel, hremaining⟩
      have hrem := finListUnaryCode_length_le frame.remaining
      have hrem' : (finListUnaryCode frame.remaining).length ≤
          n * (2 * n + 2) := by
        exact hrem.trans (Nat.mul_le_mul_right (2 * n + 2) hremaining)
      have hrow := finUnaryCode_length_le frame.row
      have hcol := finUnaryCode_length_le frame.column
      have hmate := mateVectorCode_columnMate_length_le frame.mate
      simp only [kuhnFrameCode, kuhnSearchFrameCode,
        machineKuhnSearchFramePack, pair_length]
      simp only [List.length_singleton, List.length_replicate]
      nlinarith [sq_nonneg (n : ℤ)]
  | build frame =>
      have hrem := finListUnaryCode_length_le frame.rows
      have hrem' : (finListUnaryCode frame.rows).length ≤
          n * (2 * n + 2) := by
        exact hrem.trans (Nat.mul_le_mul_right (2 * n + 2) hframe)
      have hmate := mateVectorCode_columnMate_length_le frame.fallback
      simp only [kuhnFrameCode, kuhnBuildFrameCode,
        machineKuhnBuildFramePack, pair_length, List.length_singleton]
      nlinarith [sq_nonneg (n : ℤ)]

theorem kuhnStackCode_length_le {n : ℕ} (stack : List (KuhnFrame n))
    (hstack : KuhnStackDataBound stack) :
    (kuhnStackCode stack).length ≤
      34 * (n + 1) ^ 2 * stack.length := by
  induction stack with
  | nil => simp [kuhnStackCode, binaryListCode]
  | cons frame stack ih =>
      have hframe := kuhnFrameCode_length_le frame (hstack frame (by simp))
      have htail : KuhnStackDataBound stack :=
        kuhnStackDataBound_tail hstack
      have ih' := ih htail
      simp only [kuhnStackCode, binaryListCode, pair_length,
        List.length_cons]
      change 2 * (kuhnFrameCode frame).length + 2 +
          (binaryListCode kuhnFrameCode stack).length ≤
        34 * (n + 1) ^ 2 * (stack.length + 1)
      change (binaryListCode kuhnFrameCode stack).length ≤
          34 * (n + 1) ^ 2 * stack.length at ih'
      have hone : 1 ≤ (n + 1) ^ 2 :=
        Nat.one_le_pow 2 (n + 1) (by omega)
      have hframeContribution :
          2 * (kuhnFrameCode frame).length + 2 ≤
            34 * (n + 1) ^ 2 := by nlinarith
      calc
        2 * (kuhnFrameCode frame).length + 2 +
            (binaryListCode kuhnFrameCode stack).length ≤
            34 * (n + 1) ^ 2 +
              34 * (n + 1) ^ 2 * stack.length := by omega
        _ = 34 * (n + 1) ^ 2 * (stack.length + 1) := by ring

theorem kuhnControlCode_length_le {n steps : ℕ}
    (state : KuhnEvalState n)
    (hstate : KuhnEvalReachableBound steps state) :
    (kuhnControlCode state).length ≤
      50 * (steps + 1) * (n + 1) ^ 2 := by
  cases state with
  | call fuel remaining row seen mate stack =>
      rcases hstate with ⟨hfuel, hremaining, hstack, hstackLength⟩
      have hrem := finListUnaryCode_length_le remaining
      have hrem' : (finListUnaryCode remaining).length ≤
          n * (2 * n + 2) :=
        hrem.trans (Nat.mul_le_mul_right (2 * n + 2) hremaining)
      have hrow := finUnaryCode_length_le row
      have hseen : (boolVectorCode (seenBoolList seen)).length = 4 * n := by
        simp
      have hmate := mateVectorCode_columnMate_length_le mate
      have hstackCode := kuhnStackCode_length_le stack hstack
      have hstackCode' : (kuhnStackCode stack).length ≤
          34 * (n + 1) ^ 2 * (steps + 1) :=
        hstackCode.trans
          (Nat.mul_le_mul_left (34 * (n + 1) ^ 2) hstackLength)
      simp only [kuhnControlCode, machineKuhnControlCall,
        machineKuhnCallPack, pair_length, List.length_singleton,
        List.length_replicate]
      nlinarith [sq_nonneg (n : ℤ)]
  | ret result stack =>
      rcases hstate with ⟨hstack, hstackLength⟩
      have hseen : (boolVectorCode (seenBoolList result.seen)).length =
          4 * n := by simp
      have hmate : (kuhnSearchResultMateCode result).length ≤
          n * (2 * n + 4) := by
        cases hmateEq : result.mate? with
        | none => simp [kuhnSearchResultMateCode, hmateEq]
        | some mate => simpa [kuhnSearchResultMateCode, hmateEq] using!
            mateVectorCode_columnMate_length_le mate
      have hstackCode := kuhnStackCode_length_le stack hstack
      have hstackCode' : (kuhnStackCode stack).length ≤
          34 * (n + 1) ^ 2 * (steps + 1) :=
        hstackCode.trans
          (Nat.mul_le_mul_left (34 * (n + 1) ^ 2) hstackLength)
      simp only [kuhnControlCode, machineKuhnControlReturn,
        machineKuhnReturnPack, pair_length, List.length_cons,
        List.length_nil]
      nlinarith [sq_nonneg (n : ℤ)]
  | done mate =>
      have hmate := mateVectorCode_columnMate_length_le mate
      simp only [kuhnControlCode, machineKuhnControlDone, pair_length,
        List.length_cons, List.length_nil]
      nlinarith [sq_nonneg (n : ℤ)]

/-! ## The fixed octic envelope -/

def kuhnMachineStepBudget (n : ℕ) : ℕ :=
  3 * (n * (n + (n + 1) * n)) + 2 * n

theorem kuhnFullBuildSteps_le_budget {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    kuhnBuildSteps A (List.finRange n) (emptyColumnMate n) ≤
      kuhnMachineStepBudget n := by
  exact kuhnFullBuildSteps_le A

theorem kuhnMachineInputBound_eighthPower (word : List Bool) :
    (word.length + 16) ^ 8 ≤ (machineKuhnInputBound word).length := by
  simp only [machineKuhnInputBound, machineListUpdateInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  ring_nf
  omega

theorem kuhnControlPolynomial_le_eighthPower (n : ℕ) :
    50 * (kuhnMachineStepBudget n + 1) * (n + 1) ^ 2 ≤
      (n + 16) ^ 8 := by
  simp only [kuhnMachineStepBudget]
  ring_nf
  omega

theorem kuhnQuadraticContext_le_eighthPower (n : ℕ) :
    n * (2 * n + 2) ≤ (n + 16) ^ 8 := by
  ring_nf
  omega

theorem kuhnLinearContext_le_eighthPower (n : ℕ) :
    4 * n ≤ (n + 16) ^ 8 := by
  ring_nf
  omega

theorem kuhnMatrixLength_le_eighthPower (length : ℕ) :
    length ≤ (length + 16) ^ 8 := by
  ring_nf
  omega

theorem kuhnControlCode_length_le_inputBound {n steps : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n)
    (hstate : KuhnEvalReachableBound steps state)
    (hsteps : steps ≤ kuhnMachineStepBudget n) :
    (kuhnControlCode state).length ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  have hcontrol := kuhnControlCode_length_le state hstate
  have hstepFactor :
      50 * (steps + 1) * (n + 1) ^ 2 ≤
        50 * (kuhnMachineStepBudget n + 1) * (n + 1) ^ 2 := by
    have := Nat.mul_le_mul_left 50 (Nat.add_le_add_right hsteps 1)
    exact Nat.mul_le_mul_right ((n + 1) ^ 2) this
  have hn : n + 16 ≤ matrix.length + 16 := by
    exact Nat.add_le_add_right (matrix_dimension_le_code_length A) 16
  exact hcontrol.trans <| hstepFactor.trans <|
    (kuhnControlPolynomial_le_eighthPower n).trans <|
      (Nat.pow_le_pow_left hn 8).trans <|
        kuhnMachineInputBound_eighthPower matrix

theorem kuhnMatrixCode_length_le_inputBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (rationalMatrixBinaryEncoding.encode ⟨n, A⟩).length ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  exact (kuhnMatrixLength_le_eighthPower matrix.length).trans
    (kuhnMachineInputBound_eighthPower matrix)

theorem kuhnDimensionCode_length_le_inputBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (List.replicate n true).length ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  have hn := matrix_dimension_le_code_length A
  simpa using! hn.trans (kuhnMatrixCode_length_le_inputBound A)

theorem kuhnColumnsCode_length_le_inputBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (finRangeUnaryCode n).length ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  have hcolumns : (finRangeUnaryCode n).length ≤ n * (2 * n + 2) := by
    simpa [finRangeUnaryCode, finListUnaryCode] using!
      finListUnaryCode_length_le (List.finRange n)
  have hn : n + 16 ≤ matrix.length + 16 := by
    exact Nat.add_le_add_right (matrix_dimension_le_code_length A) 16
  exact hcolumns.trans <| (kuhnQuadraticContext_le_eighthPower n).trans <|
    (Nat.pow_le_pow_left hn 8).trans <|
      kuhnMachineInputBound_eighthPower matrix

theorem kuhnFalseSeenCode_length_le_inputBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (boolVectorCode (List.replicate n false)).length ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  have hfalse : (boolVectorCode (List.replicate n false)).length = 4 * n := by
    simp
  have hn : n + 16 ≤ matrix.length + 16 := by
    exact Nat.add_le_add_right (matrix_dimension_le_code_length A) 16
  rw [hfalse]
  exact (kuhnLinearContext_le_eighthPower n).trans <|
    (Nat.pow_le_pow_left hn 8).trans <|
      kuhnMachineInputBound_eighthPower matrix

theorem machineKuhnClamp_stateCode_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n)
    (candidate : List Bool)
    (hcandidate : candidate.length ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length) :
    machineKuhnClamp (kuhnMachineStateCode A state) candidate = candidate := by
  simp only [machineKuhnClamp, machineKuhnBound_stateCode]
  exact List.take_of_length_le hcandidate

theorem machineKuhnStep_encode {n steps : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n)
    (hstate : KuhnEvalReachableBound steps state)
    (hnextSteps : steps + 1 ≤ kuhnMachineStepBudget n) :
    machineKuhnStep (kuhnMachineStateCode A state) =
      kuhnMachineStateCode A (kuhnEvalStep A state) := by
  have hnext := kuhnEvalStep_reachableBound A state hstate
  have hcontrol := kuhnControlCode_length_le_inputBound A
    (kuhnEvalStep A state) hnext hnextSteps
  rw [machineKuhnStep, machineKuhnNextControl_encode]
  simp only [machineKuhnWithControl]
  rw [machineKuhnClamp_stateCode_eq A state _ hcontrol]
  simp only [machineKuhnMatrix_stateCode, machineKuhnDimension_stateCode,
    machineKuhnColumns_stateCode, machineKuhnFalseSeen_stateCode,
    machineKuhnBound_stateCode]
  rw [machineKuhnClamp_stateCode_eq A state _
    (kuhnMatrixCode_length_le_inputBound A)]
  rw [machineKuhnClamp_stateCode_eq A state _
    (kuhnDimensionCode_length_le_inputBound A)]
  rw [machineKuhnClamp_stateCode_eq A state _
    (kuhnColumnsCode_length_le_inputBound A)]
  rw [machineKuhnClamp_stateCode_eq A state _
    (kuhnFalseSeenCode_length_le_inputBound A)]
  simp [kuhnMachineStateCode]

/-! ## Exact bounded execution -/

theorem machineKuhnIterate_encode {n iterations : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (initial : KuhnEvalState n)
    (hinitial : KuhnEvalReachableBound 0 initial)
    (hiterations : iterations ≤ kuhnMachineStepBudget n) :
    (machineKuhnStep^[iterations]) (kuhnMachineStateCode A initial) =
      kuhnMachineStateCode A ((kuhnEvalStep A)^[iterations] initial) := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
      have hprefix : iterations ≤ kuhnMachineStepBudget n := by omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih hprefix]
      apply machineKuhnStep_encode A
      · exact kuhnEvalIterate_reachableBound A initial hinitial
      · simpa [Nat.succ_eq_add_one] using! hiterations

@[simp] theorem kuhnEvalIterate_done {n iterations : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (mate : ColumnMate n) :
    (kuhnEvalStep A)^[iterations] (.done mate) = .done mate := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem kuhnFullEval_budget {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (kuhnEvalStep A)^[kuhnMachineStepBudget n]
        (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)) =
      .done (kuhnColumnMate A) := by
  let exactSteps :=
    kuhnBuildSteps A (List.finRange n) (emptyColumnMate n)
  have hexact : exactSteps ≤ kuhnMachineStepBudget n :=
    kuhnFullBuildSteps_le_budget A
  rw [show kuhnMachineStepBudget n =
      (kuhnMachineStepBudget n - exactSteps) + exactSteps by omega,
    Function.iterate_add_apply]
  rw [show (kuhnEvalStep A)^[exactSteps]
        (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)) =
      .done (kuhnColumnMate A) by
        simpa [exactSteps] using! kuhnFullBuildEvalState_iterate A]
  simp

theorem machineKuhnFullIterate_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (machineKuhnStep^[kuhnMachineStepBudget n])
        (kuhnMachineStateCode A
          (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n))) =
      kuhnMachineStateCode A (.done (kuhnColumnMate A)) := by
  rw [machineKuhnIterate_encode A _
    (kuhnFullBuildEvalState_reachableBound A) (le_rfl),
    kuhnFullEval_budget]

theorem machineKuhnStep_done_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (mate : ColumnMate n) :
    machineKuhnStep (kuhnMachineStateCode A (.done mate)) =
      kuhnMachineStateCode A (.done mate) := by
  have hcontrol := kuhnControlCode_length_le_inputBound A (.done mate)
    (by trivial) (Nat.zero_le _)
  rw [machineKuhnStep, machineKuhnNextControl_encode]
  simp only [kuhnEvalStep, machineKuhnWithControl]
  rw [machineKuhnClamp_stateCode_eq A (.done mate) _ hcontrol]
  simp only [machineKuhnMatrix_stateCode, machineKuhnDimension_stateCode,
    machineKuhnColumns_stateCode, machineKuhnFalseSeen_stateCode,
    machineKuhnBound_stateCode]
  rw [machineKuhnClamp_stateCode_eq A (.done mate) _
    (kuhnMatrixCode_length_le_inputBound A)]
  rw [machineKuhnClamp_stateCode_eq A (.done mate) _
    (kuhnDimensionCode_length_le_inputBound A)]
  rw [machineKuhnClamp_stateCode_eq A (.done mate) _
    (kuhnColumnsCode_length_le_inputBound A)]
  rw [machineKuhnClamp_stateCode_eq A (.done mate) _
    (kuhnFalseSeenCode_length_le_inputBound A)]
  simp [kuhnMachineStateCode]

theorem kuhnMachineStepBudget_le_inputBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    kuhnMachineStepBudget n ≤
      (machineKuhnInputBound
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  have hsmall : kuhnMachineStepBudget n ≤
      50 * (kuhnMachineStepBudget n + 1) * (n + 1) ^ 2 := by
    have hone : 1 ≤ (n + 1) ^ 2 :=
      Nat.one_le_pow 2 (n + 1) (by omega)
    nlinarith
  have hn : n + 16 ≤ matrix.length + 16 := by
    exact Nat.add_le_add_right (matrix_dimension_le_code_length A) 16
  exact hsmall.trans <| (kuhnControlPolynomial_le_eighthPower n).trans <|
    (Nat.pow_le_pow_left hn 8).trans <|
      kuhnMachineInputBound_eighthPower matrix

theorem machineKuhnFullBoundIterate_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let iterations := (machineKuhnInputBound
      (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length
    (machineKuhnStep^[iterations])
        (kuhnMachineStateCode A
          (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n))) =
      kuhnMachineStateCode A (.done (kuhnColumnMate A)) := by
  dsimp only
  let iterations := (machineKuhnInputBound
    (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length
  have hbudget : kuhnMachineStepBudget n ≤ iterations :=
    kuhnMachineStepBudget_le_inputBound A
  change (machineKuhnStep^[iterations])
      (kuhnMachineStateCode A
        (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n))) =
    kuhnMachineStateCode A (.done (kuhnColumnMate A))
  rw [show iterations =
      (iterations - kuhnMachineStepBudget n) + kuhnMachineStepBudget n by
        omega,
    Function.iterate_add_apply, machineKuhnFullIterate_encode]
  induction (iterations - kuhnMachineStepBudget n) with
  | zero => rfl
  | succ remaining ih =>
      rw [Function.iterate_succ_apply', ih, machineKuhnStep_done_encode]

end BeyondBethe

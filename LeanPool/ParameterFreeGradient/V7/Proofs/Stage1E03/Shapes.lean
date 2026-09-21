/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Refinement

/-!
The early-failure and complete shapes of source Euclidean reports.
-/

namespace V7
namespace Stage1E03

/-- Classical proposition decisions used locally in the report-shape proofs. -/
noncomputable local instance shapesPropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

/-- The alternating query and accelerated-point observations of an estimate-phase segment. -/
noncomputable def phaseATraceFrom (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k fuel : ℕ) : List (Observation d) :=
  (List.range fuel).flatMap fun j =>
    [inst.oracle.observe (estimateQuery M x0 (k + j)
      (sourceEstimateState inst.oracle M x0 (k + j))),
     inst.oracle.observe
      (sourceEstimateState inst.oracle M x0 (k + j + 1)).accelerated]

/-- The upper-model guards corresponding to an estimate-phase segment. -/
noncomputable def phaseAGuardsFrom (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k fuel : ℕ) : List (ObservableGuardCheck d) :=
  (List.range fuel).map fun j =>
    upperCheck
      (inst.oracle.observe (estimateQuery M x0 (k + j)
        (sourceEstimateState inst.oracle M x0 (k + j))))
      (inst.oracle.observe
        (sourceEstimateState inst.oracle M x0 (k + j + 1)).accelerated)

@[simp] theorem phaseATraceFrom_zero (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k : ℕ) : phaseATraceFrom inst M k 0 = [] := by
  simp [phaseATraceFrom]

@[simp] theorem phaseAGuardsFrom_zero (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k : ℕ) : phaseAGuardsFrom inst M k 0 = [] := by
  simp [phaseAGuardsFrom]

theorem phaseATraceFrom_succ (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k fuel : ℕ) :
    phaseATraceFrom inst M k (fuel + 1) =
      [inst.oracle.observe (estimateQuery M x0 k
        (sourceEstimateState inst.oracle M x0 k)),
       inst.oracle.observe
        (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated] ++
      phaseATraceFrom inst M (k + 1) fuel := by
  unfold phaseATraceFrom
  rw [List.range_succ_eq_map]
  simp only [List.flatMap_cons, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro a ha
  rw [show k + (a + 1) = k + 1 + a by omega]

theorem phaseAGuardsFrom_succ (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k fuel : ℕ) :
    phaseAGuardsFrom inst M k (fuel + 1) =
      [upperCheck
        (inst.oracle.observe (estimateQuery M x0 k
          (sourceEstimateState inst.oracle M x0 k)))
        (inst.oracle.observe
          (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated)] ++
      phaseAGuardsFrom inst M (k + 1) fuel := by
  unfold phaseAGuardsFrom
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  change upperCheck
      (inst.oracle.observe (estimateQuery M x0 (k + (a + 1))
        (sourceEstimateState inst.oracle M x0 (k + (a + 1)))))
      (inst.oracle.observe
        (sourceEstimateState inst.oracle M x0 (k + (a + 1) + 1)).accelerated) = _
  rw [show k + (a + 1) = k + 1 + a by omega]

@[simp] theorem phaseATraceFrom_length (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k fuel : ℕ) :
    (phaseATraceFrom inst M k fuel).length = 2 * fuel := by
  simp [phaseATraceFrom]
  omega

@[simp] theorem phaseAGuardsFrom_length (inst : PositiveInstance 2 d x0)
    (M : ℝ) (k fuel : ℕ) :
    (phaseAGuardsFrom inst M k fuel).length = fuel := by
  simp [phaseAGuardsFrom]

/-- The report records precisely the first failed guard after a prefix of accepted guards. -/
def FailureLedger (p M : ℝ) (report : TrialReport d)
    (failed : ObservableGuardCheck d) : Prop :=
  report.outcome = .scale failed ∧
  report.checkedGuards.getLast? = some failed ∧
  (∀ check ∈ report.checkedGuards.dropLast, CheckHolds p M check) ∧
  ¬ CheckHolds p M failed

/-- Every observation used in a checked guard occurs in the report's trace. -/
def GuardPairsInTrace (report : TrialReport d) : Prop :=
  ∀ check ∈ report.checkedGuards,
    check.xPair ∈ report.trace ∧ check.yPair ∈ report.trace

theorem prepend_failureLedger (p M : ℝ)
    (history : List (Observation d))
    (guards : List (ObservableGuardCheck d)) (tail : TrialReport d)
    (failed : ObservableGuardCheck d)
    (hguards : ∀ check ∈ guards, CheckHolds p M check)
    (htail : FailureLedger p M tail failed) :
    FailureLedger p M (prependReport history guards tail) failed := by
  rcases htail with ⟨hout, hlast, hprior, hfailed⟩
  refine ⟨hout, ?_, ?_, hfailed⟩
  · simp only [prependReport]
    have hne : tail.checkedGuards ≠ [] := by
      intro he
      rw [he] at hlast
      simp at hlast
    simpa [List.getLast?_append, hne] using hlast
  · intro check hmem
    have hne : tail.checkedGuards ≠ [] := by
      intro he
      rw [he] at hlast
      simp at hlast
    simp only [prependReport] at hmem
    rw [List.dropLast_append_of_ne_nil hne] at hmem
    rcases List.mem_append.mp hmem with hg | ht
    · exact hguards check hg
    · exact hprior check ht

theorem sourcePhaseAReport_shape (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) : ∀ fuel k, k + fuel = n →
    let report := sourcePhaseAReport inst eps M n k fuel
    (∃ r < fuel, ∃ failed,
      FailureLedger 2 M report failed ∧
      GuardPairsInTrace report ∧
      report.trace <+: phaseATraceFrom inst M k fuel ∧
      report.checkedGuards <+: phaseAGuardsFrom inst M k fuel ∧
      report.trace.length = 2 * (r + 1) ∧
      report.checkedGuards.length = r + 1 ∧
      failed.kind = .upperModel) ∨
    ((∀ check ∈ phaseAGuardsFrom inst M k fuel, CheckHolds 2 M check) ∧
      report = prependReport (phaseATraceFrom inst M k fuel)
        (phaseAGuardsFrom inst M k fuel)
        (sourcePhaseBReport inst eps M n
          (sourceEstimateState inst.oracle M x0 n).accelerated)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hkn
      have hk : k = n := by omega
      subst k
      right
      constructor
      · simp
      · simp [sourcePhaseAReport, prependReport]
  | succ fuel ih =>
      intro k hkn
      let oy := inst.oracle.observe (estimateQuery M x0 k
        (sourceEstimateState inst.oracle M x0 k))
      let ox := inst.oracle.observe
        (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated
      let check := upperCheck oy ox
      have htail := ih (k + 1) (by omega)
      simp only [sourcePhaseAReport]
      dsimp only [oy, ox, check] at htail ⊢
      let g := upperCheck
        (inst.oracle.observe (estimateQuery M x0 k
          (sourceEstimateState inst.oracle M x0 k)))
        (inst.oracle.observe
          (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated)
      by_cases hg : CheckHolds 2 M g
      · dsimp only [g] at hg
        simp only [hg, ↓reduceIte]
        rcases htail with hfail | hpass
        · left
          rcases hfail with ⟨r, hr, failed, hledger, hpairs, htp, hgp,
            htlen, hglen, hkind⟩
          refine ⟨r + 1, by omega, failed, ?_, ?_, ?_, ?_, ?_, ?_, hkind⟩
          · apply prepend_failureLedger 2 M _ [g] _ failed
            · dsimp only [g]
              simpa using hg
            · exact hledger
          · intro q hq
            simp only [prependReport, List.mem_append, List.mem_singleton] at hq ⊢
            rcases hq with rfl | hq
            · dsimp only [upperCheck]
              constructor <;> simp
            · rcases hpairs q hq with ⟨hx, hy⟩
              exact ⟨Or.inr hx, Or.inr hy⟩
          · rw [phaseATraceFrom_succ]
            rcases htp with ⟨rest, hrest⟩
            refine ⟨rest, ?_⟩
            simp only [prependReport]
            rw [List.append_assoc, hrest]
          · rw [phaseAGuardsFrom_succ]
            rcases hgp with ⟨rest, hrest⟩
            refine ⟨rest, ?_⟩
            simp only [prependReport]
            rw [List.append_assoc, hrest]
          · simp [prependReport, htlen]
            omega
          · simp [prependReport, hglen]
        · right
          rcases hpass with ⟨hall, heq⟩
          constructor
          · rw [phaseAGuardsFrom_succ]
            intro q hq
            simp only [List.mem_append, List.mem_singleton] at hq
            rcases hq with rfl | hq
            · exact hg
            · exact hall q hq
          · rw [heq, phaseATraceFrom_succ, phaseAGuardsFrom_succ]
            simp [prependReport]
      · dsimp only [g] at hg
        simp only [hg, ↓reduceIte]
        left
        refine ⟨0, by omega, g, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · dsimp only [g]
          exact ⟨rfl, by simp, by simp, hg⟩
        · intro q hq
          simp only [List.mem_singleton] at hq
          subst q
          simp [upperCheck]
        · rw [phaseATraceFrom_succ]
          exact List.prefix_append _ _
        · rw [phaseAGuardsFrom_succ]
          exact List.prefix_append _ _
        · rfl
        · rfl

theorem sourcePhaseBReport_shape (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (U : Point d) :
    let cfg := O3.stage9ExecutionConfig n inst.oracle M U
    let newTrace := (List.range n).map fun j =>
      inst.oracle.observe (O3.ogmgState cfg (j + 1)).current
    let checks := allInterpolationChecks n fun i =>
      inst.oracle.observe (O3.ogmgState cfg i).current
    let terminal := terminalCheck
      (inst.oracle.observe (O3.ogmgState cfg n).current)
      (inst.oracle.observe (O3.ogmgV cfg n))
    let report := sourcePhaseBReport inst eps M n U
    (∃ failed, FailureLedger 2 M report failed ∧
      ((failed.kind = .interpolation ∧ report.trace = newTrace ∧
        report.checkedGuards <+: checks) ∨
       (failed.kind = .terminalDescent ∧
        report.trace = newTrace ++ [inst.oracle.observe (O3.ogmgV cfg n)] ∧
        report.checkedGuards = checks ++ [terminal]))) ∨
    (∃ on, report.outcome = .success on ∧
      on = inst.oracle.observe (O3.ogmgState cfg n).current ∧
      report.trace = newTrace ++ [inst.oracle.observe (O3.ogmgV cfg n)] ∧
      report.checkedGuards = checks ++ [terminal] ∧
      (∀ check ∈ report.checkedGuards, CheckHolds 2 M check) ∧
      lpNorm 2 on.gradient ≤ eps) ∨
    (∃ on, report.outcome = .radius on ∧
      on = inst.oracle.observe (O3.ogmgState cfg n).current ∧
      report.trace = newTrace ++ [inst.oracle.observe (O3.ogmgV cfg n)] ∧
      report.checkedGuards = checks ++ [terminal] ∧
      (∀ check ∈ report.checkedGuards, CheckHolds 2 M check) ∧
      eps < lpNorm 2 on.gradient) := by
  dsimp only
  unfold sourcePhaseBReport sourcePhaseBSuffix
  dsimp only
  cases heval : evaluateChecks 2 M
      (allInterpolationChecks n fun i => inst.oracle.observe
        (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).current) with
  | error err =>
      rcases err with ⟨prior, failed⟩
      simp only []
      left
      refine ⟨failed, ?_, Or.inl ?_⟩
      · have hc := evaluateChecks_error_characterization 2 M _ prior failed heval
        exact ⟨rfl, hc.2.1, hc.2.2.1, hc.2.2.2⟩
      · refine ⟨?_, ?_, evaluateChecks_error_prefix 2 M heval⟩
        · have hmem := List.getLast?_eq_some_iff.mp
            (evaluateChecks_error_last 2 M heval)
          rcases hmem with ⟨front, hfront⟩
          have hm : failed ∈ allInterpolationChecks n fun i =>
              inst.oracle.observe (O3.ogmgState
                (O3.stage9ExecutionConfig n inst.oracle M U) i).current := by
            exact List.IsPrefix.mem (by rw [hfront]; simp)
              (evaluateChecks_error_prefix 2 M heval)
          simp only [allInterpolationChecks, List.mem_flatMap, List.mem_map] at hm
          rcases hm with ⟨i, hi, j, hj, rfl⟩
          rfl
        · simp [prependReport]
  | ok passed =>
      have hok := (evaluateChecks_ok_iff 2 M _ passed).1 heval
      obtain ⟨rfl, hall⟩ := hok
      unfold sourceTerminalReport
      dsimp only
      let terminal := terminalCheck
        (inst.oracle.observe (O3.ogmgState
          (O3.stage9ExecutionConfig n inst.oracle M U) n).current)
        (inst.oracle.observe (O3.ogmgV
          (O3.stage9ExecutionConfig n inst.oracle M U) n))
      by_cases ht : CheckHolds 2 M terminal
      · by_cases hs : lpNorm 2 (inst.oracle.observe
            (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current).gradient ≤ eps
        · right; left
          dsimp only [terminal] at ht ⊢
          simp only [ht, hs, ↓reduceIte]
          refine ⟨_, ?_, rfl, ?_, ?_, ?_, hs⟩
          · simp [prependReport]
          · simp [prependReport]
          · simp [prependReport]
          · intro check hmem
            simp only [prependReport, List.nil_append, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hmem
            rcases hmem with hc | hc
            · exact hall check hc
            · subst check
              exact ht
        · right; right
          dsimp only [terminal] at ht ⊢
          simp only [ht, hs, ↓reduceIte]
          refine ⟨_, ?_, rfl, ?_, ?_, ?_, lt_of_not_ge hs⟩
          · simp [prependReport]
          · simp [prependReport]
          · simp [prependReport]
          · intro check hmem
            simp only [prependReport, List.nil_append, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hmem
            rcases hmem with hc | hc
            · exact hall check hc
            · subst check
              exact ht
      · left
        dsimp only [terminal] at ht ⊢
        simp only [ht, ↓reduceIte]
        refine ⟨terminal, ?_, Or.inr ?_⟩
        · refine ⟨?_, ?_, ?_, ht⟩
          · simp [prependReport, terminal]
          · simp [prependReport, terminal]
          · intro check hmem
            simp only [prependReport] at hmem
            simp only [List.nil_append] at hmem
            rw [List.dropLast_append_of_ne_nil (by simp :
              [terminalCheck
                (inst.oracle.observe (O3.ogmgState
                  (O3.stage9ExecutionConfig n inst.oracle M U) n).current)
                (inst.oracle.observe (O3.ogmgV
                  (O3.stage9ExecutionConfig n inst.oracle M U) n))] ≠ [])] at hmem
            simp only [List.dropLast_singleton, List.append_nil] at hmem
            exact hall check hmem
        · refine ⟨rfl, ?_, ?_⟩
          · simp [prependReport]
          · simp [prependReport]

end Stage1E03
end V7
